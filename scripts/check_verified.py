#!/usr/bin/env python3
"""verified.json と Lean の中身を突き合わせる（`lake build` のあとに走らせる）。

1. verified.json の各項目に必要な欄がそろっているか・level が L0/L1/L2 のどれか・id が重ならないか。
2. `file` が実在し、`lean_decl` の名前（最後の部分）がそのファイルに書いてあるか。
3. MathGarden/ の下の .lean ファイルが全部 MathGarden.lean から import されているか
   （import されていないファイルは `lake build` で型検査されない）。
4. 各 `lean_decl` に `#print axioms` をかけ、使っている公理が許可リスト
   （propext, Classical.choice, Quot.sound）の中だけか。sorryAx（証明の穴）や
   Lean.ofReduceBool（native_decide）が混ざっていれば失敗。宣言が存在しなくても失敗。

4 は先に「わざと鳴る入力」（対照）で、穴のある宣言と存在しない宣言を確かに捕まえることを確かめる。
"""

from __future__ import annotations

import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
LEVELS = {"L0", "L1", "L2"}
REQUIRED = [
    "id",
    "article_slug",
    "article_section",
    "article_quote_ja",
    "claim_ja",
    "lean_statement",
    "lean_decl",
    "file",
    "level",
    "not_covered_ja",
]
TMP = ROOT / ".lake" / "check_verified_tmp.lean"
AXIOM_LINE = re.compile(
    r"^'(?P<name>.+?)' (?:depends on axioms: \[(?P<axioms>[^\]]*)\]|does not depend on any axioms)",
    re.MULTILINE,
)


def run_print_axioms(imports: list[str], decls: list[str], prelude: str = "") -> tuple[int, str]:
    src = "".join(f"import {m}\n" for m in imports)
    src += prelude
    src += "".join(f"#print axioms {d}\n" for d in decls)
    TMP.parent.mkdir(parents=True, exist_ok=True)
    TMP.write_text(src, encoding="utf-8")
    r = subprocess.run(
        ["lake", "env", "lean", str(TMP)],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    return r.returncode, r.stdout + r.stderr


def axiom_problems(decls: list[str], output: str) -> list[str]:
    found: dict[str, set[str]] = {}
    for m in AXIOM_LINE.finditer(output):
        axioms = m.group("axioms") or ""
        found[m.group("name")] = {a.strip() for a in axioms.split(",") if a.strip()}
    problems = []
    for d in decls:
        if d not in found:
            problems.append(f"{d}: no `#print axioms` result (unknown declaration?)")
            continue
        extra = found[d] - ALLOWED_AXIOMS
        if extra:
            problems.append(f"{d}: uses axioms outside the allowlist: {sorted(extra)}")
    return problems


def control() -> None:
    """対照：穴のある宣言と存在しない宣言を、確かに問題として挙げるか。"""
    bad = "MathGardenControl.hole"
    missing = "MathGardenControl.doesNotExist"
    prelude = "theorem MathGardenControl.hole : 1 = 2 := by sorry\n"
    rc, out = run_print_axioms([], [bad, missing], prelude)
    problems = axiom_problems([bad, missing], out)
    ok = (
        rc != 0
        and any(p.startswith(bad + ":") and "sorryAx" in p for p in problems)
        and any(p.startswith(missing + ":") for p in problems)
    )
    if not ok:
        print(out)
        print("control problems:", problems)
        sys.exit("::error::control failed: the axiom check did not catch the deliberately bad input")
    print(f"control: caught {len(problems)}/2 deliberately bad declarations")


def module_of(path: pathlib.Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def main() -> None:
    data = json.loads((ROOT / "verified.json").read_text(encoding="utf-8"))
    claims = data["claims"]
    errors: list[str] = []
    if not claims:
        errors.append("verified.json has no claims")

    seen_ids = set()
    for c in claims:
        cid = c.get("id", "?")
        for k in REQUIRED:
            if not str(c.get(k, "")).strip():
                errors.append(f"{cid}: missing field `{k}`")
        if cid in seen_ids:
            errors.append(f"{cid}: duplicate id")
        seen_ids.add(cid)
        if c.get("level") not in LEVELS:
            errors.append(f"{cid}: level must be one of {sorted(LEVELS)}")
        f = ROOT / c.get("file", "")
        if not f.is_file():
            errors.append(f"{cid}: file not found: {c.get('file')}")
            continue
        short = c["lean_decl"].split(".")[-1]
        if short not in f.read_text(encoding="utf-8"):
            errors.append(f"{cid}: `{short}` does not appear in {c['file']}")

    root_text = (ROOT / "MathGarden.lean").read_text(encoding="utf-8")
    imported = set(re.findall(r"^import\s+(\S+)", root_text, re.MULTILINE))
    lean_files = sorted((ROOT / "MathGarden").rglob("*.lean"))
    for p in lean_files:
        if module_of(p) not in imported:
            errors.append(f"{module_of(p)} is not imported by MathGarden.lean")

    if errors:
        print("\n".join(errors))
        sys.exit("::error::verified.json / layout check failed")
    print(f"layout: {len(claims)} claims, {len(lean_files)} files under MathGarden/, all imported")

    control()

    decls = [c["lean_decl"] for c in claims]
    rc, out = run_print_axioms(["MathGarden"], decls)
    print(out.strip())
    problems = axiom_problems(decls, out)
    if rc != 0 or problems:
        print("\n".join(problems))
        sys.exit("::error::axiom check failed")
    print(f"OK: {len(decls)} declarations in verified.json use only {sorted(ALLOWED_AXIOMS)}")


if __name__ == "__main__":
    main()
