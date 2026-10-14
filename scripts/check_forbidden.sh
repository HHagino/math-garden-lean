#!/usr/bin/env bash
# MathGarden/ の下（と MathGarden.lean）に、証明の穴や信頼の外し方を表す語が1つも無いことを確かめる。
#   sorry / admit        … 証明の穴
#   native_decide        … コンパイルしたコードを信じる（カーネルの外）
#   axiom                … 自前の公理の宣言
# 判定を単純にするため、コメントや文字列の中の語も数える（Lean のファイルではこれらの語を書かない）。
# 1件でもあれば失敗する。先に「わざと鳴る入力」（対照）で検査が鳴ることを確かめてから本番を走らせる。
set -euo pipefail
cd "$(dirname "$0")/.."

PATTERN='\b(sorry|admit|native_decide|axiom)\b'

scan() {
  # grep は 1件も無いと終了コード 1 を返すので、ここでは止めない
  grep -rnE --include='*.lean' "$PATTERN" "$@" || true
}

# --- 対照：4つの語を1行ずつ含むファイルで、4件とも拾うこと ---
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
cat > "$tmp/Control.lean" <<'EOF'
theorem c1 : 1 = 2 := by sorry
axiom c2 : False
example : 2 + 2 = 4 := by native_decide
example : True := by admit
example : True := trivial -- axioms / sorryAx / admitted は語の境界で数えない
EOF
n_control="$(scan "$tmp" | wc -l)"
if [ "$n_control" -ne 4 ]; then
  echo "::error::control failed: expected 4 hits, got $n_control"
  scan "$tmp"
  exit 2
fi
echo "control: 4/4 hits (the check fires on deliberately bad input)"

# --- 本番 ---
n_files="$(find MathGarden MathGarden.lean -name '*.lean' | wc -l)"
if [ "$n_files" -eq 0 ]; then
  echo "::error::no .lean files found under MathGarden/ (a green result would be meaningless)"
  exit 2
fi
hits="$(scan MathGarden MathGarden.lean)"
if [ -n "$hits" ]; then
  echo "$hits"
  echo "::error::forbidden words found (sorry / admit / native_decide / axiom)"
  exit 1
fi
echo "OK: 0 forbidden words in $n_files .lean files"
