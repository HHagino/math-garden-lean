# math-garden-lean

[![CI](https://github.com/HHagino/math-garden-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/HHagino/math-garden-lean/actions/workflows/ci.yml)

数学解説サイト「知識の庭」（<https://hhagino.github.io/math-garden/>）の記事に書いた主張を、
Lean 4 と Mathlib で確かめるためのリポジトリ。

**Lean が確かめるのは「形式化した主張」であって、記事の文章そのものではない。**
記事の文と Lean の主張は同じではないので、下の表と `verified.json` で必ず並べて示し、
「確かめていないこと」も書く。

## 確かめた主張

| 記事（slug・節） | 記事の文 | Lean の主張 | レベル | 確かめていないこと |
|---|---|---|---|---|
| `pythagoras-sqrt2-p-adic-mod-8` §3 | 「標準公式によれば、(2/p) = (-1)^{(p²-1)/8}」と表の列「(p²-1)/8 の偶奇」 | `odd_sq_mod_eight (n : Nat) (hn : n % 2 = 1) : n ^ 2 % 8 = 1`（奇数の平方は 8 で割ると 1 余る＝(p²-1)/8 は整数） | L1 | 公式 (2/p) = (-1)^{(p²-1)/8} そのもの・表の偶奇の列・Hensel の補題・√2 ∈ Q_p の判定 |
| `pythagoras-sqrt2-p-adic-mod-8` 導入 | 「対角線の長さは √2。…これは整数比では表せない(通約不能)」 | Mathlib の `irrational_sqrt_two : Irrational (√2)` と、`∀ a b : ℤ, √2 ≠ a / b` | L0 | 対角線の長さが √2 であること（ピタゴラスの定理の部分）・§2 の「x² = 2 は Q で解を持たない」という言い方・史実 |
| `truncated-multiple-zeta-sum-hoffman-duality` §4 | 「p=11 で和を直接計算すると ζ_{<11}(1,4,1)≡9、ζ_{<11}(2,1,1,2)≡4 (mod 11) で、9≢±4 である」 | `zetaLT_eleven`：`zetaLT 11 11 [1, 4, 1] = 9 ∧ zetaLT 11 11 [2, 1, 1, 2] = 4 ∧`（前者 ≠ 後者）`∧`（前者 ≠ −後者）。`zetaLT p N ks` は §2 の和を `ZMod p` の中の入れ子の和として書いたもの | L1 | Hoffman 双対の計算 (1,4,1)^∨=(2,1,1,2)・star 版の双対性（Theorem 4.6）と non-star 版の式（Theorem 4.7）・p = 11 以外・「符号付き合同式はない」の一般形・N → ∞ の側 |
| `離散直線はRnに埋め込めない_2026-06-02` §10 | 「命題. 第二可算空間の任意の離散部分空間は、高々可算である。」 | `countable_of_discrete_subspace`：`[SecondCountableTopology X] (D : Set X) [DiscreteTopology D] : D.Countable`（証明は記事 §5 の「各点が基底要素を独占する」論法） | L1 | §4 の遺伝は Mathlib のインスタンス・§9 の境界の例・距離空間での同値・別証明 (ii) |
| `離散直線はRnに埋め込めない_2026-06-02` 冒頭・§6 | 「離散直線 ℝ_disc はどんな次元の ℝ^n にも位相的には埋め込めない」 | `realDisc_not_isEmbedding (n : ℕ) (f : RealDisc → EuclideanSpace ℝ (Fin n)) : ¬ IsEmbedding f`（`RealDisc` ＝ ℝ に離散位相 `⊥`） | L1 | ℝ の非可算性と ℝ^n の第二可算性は Mathlib のインスタンス・§1 の濃度・§2・§7 の locale・§8 の ℤ_disc ↪ ℝ・§9 |

ファイル：`MathGarden/PythagorasSqrt2PadicMod8/OddSquareModEight.lean`（L1）、
`MathGarden/PythagorasSqrt2PadicMod8/SqrtTwoIrrational.lean`（L0）、
`MathGarden/TruncatedMultipleZetaSumHoffmanDuality/NonStarValuesModEleven.lean`（L1）、
`MathGarden/DiscreteLineNotEmbeddableInRn/SecondCountableDiscrete.lean`（L1）。

## レベル

| レベル | 意味 |
|---|---|
| **L0** | 記事の主張に当たる **Mathlib の宣言を参照**し、その型が主張と一致することを Lean に確かめさせた。このリポジトリで新しく証明したものはない。 |
| **L1** | 記事の計算・補題を、このリポジトリで**自前に証明**した（Mathlib は使ってよい）。 |
| **L2** | 記事の主張の文に近い形で**主定理を形式化**し、証明した。（まだ無い） |

## `verified.json` は約束（記事やエディタが読む）

`verified.json` は、記事のページや編集の道具が読むための**約束のファイル**。
1項目が1つの主張で、欄は次のとおり（欄を消したり意味を変えたりするときは `schema_version` を上げる）。

| 欄 | 中身 |
|---|---|
| `id` | `<記事の slug>/<主張の短い名前>`。重ならない |
| `article_slug` | 庭の記事の slug（記事のファイル名から `.md` を除いたもの） |
| `article_section` | 記事の節の見出し |
| `article_quote_ja` | 記事の文（写し） |
| `claim_ja` | Lean で確かめた主張を日本語で書いたもの |
| `lean_statement` | Lean の主張の文 |
| `lean_decl` | Lean の宣言名（L0 では Mathlib の宣言名） |
| `file` | その主張を書いた Lean のファイル |
| `level` | `L0`／`L1`／`L2` |
| `not_covered_ja` | 記事の文のうち、確かめていないこと |

読む側は `article_quote_ja` と `claim_ja` を**並べて**出し、`not_covered_ja` を省かないこと
（「Lean で検証済み」とだけ書くと、記事の文全体が確かめられたように読めてしまう）。

## CI（GitHub Actions）がやること

1. `scripts/check_forbidden.sh`：`MathGarden/` と `MathGarden.lean` に `sorry`・`admit`・`native_decide`・`axiom`
   の語が1つも無いこと（grep。コメントの中の語も数えるので、Lean のファイルにはこれらの語を書かない）。
   先に、わざと4語を入れたファイルで4件とも拾うこと（対照）を確かめる。
2. [`leanprover/lean-action@v1`](https://github.com/leanprover/lean-action)：`lake exe cache get`（Mathlib のビルド済みファイル）→ `lake build`。
3. `scripts/check_verified.py`：`verified.json` の欄がそろっているか、ファイルが全部 `MathGarden.lean` から
   import されているか、各 `lean_decl` の `#print axioms` が `propext`・`Classical.choice`・`Quot.sound`
   だけか（`sorryAx` や `native_decide` 由来の `Lean.ofReduceBool` があれば失敗）。
   これも先に、穴のある宣言と存在しない宣言を捕まえること（対照）を確かめる。

## 版

- Lean：`leanprover/lean4:v4.30.0`（`lean-toolchain`）
- Mathlib：タグ `v4.30.0`（commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`、`lake-manifest.json` に固定）

## 手元で型検査するとき

- **メモリ 4GB の PC では `import Mathlib`（全体）を使わない。** 各ファイルは必要なモジュールだけを
  import する（例：`import Mathlib.NumberTheory.Real.Irrational`）。
- `lake exe cache get` は Mathlib のビルド済みファイルを数GB 取ってくる。ディスクの空きを先に見る。
  このフォルダを OneDrive など同期されるフォルダの下に置かない（`.lake/` が数GB になる）。
- Mathlib を使わないファイル（例：`OddSquareModEight.lean`）は、Lake を通さず
  `lean MathGarden/PythagorasSqrt2PadicMod8/OddSquareModEight.lean` だけで型検査できる
  （Lean v4.30.0 が入っていれば。`.lake/` も作らない）。
- Mathlib を使うファイルは、Mathlib v4.30.0 がビルド済みの環境で `lake env lean <ファイル>` を使う。

## 公開とライセンス

- いまは **private**。公開するかは本人が決める。公開するときは1コマンド：
  `gh repo edit HHagino/math-garden-lean --visibility public --accept-visibility-change-consequences`
- **ライセンスはまだ付けていない**（本人が決める）。

## English

This repository checks claims made in the articles of *Knowledge Garden*
(<https://hhagino.github.io/math-garden/>), a Japanese mathematics exposition site, with Lean 4 and Mathlib.
Lean checks the **formal statement**, not the prose of the article: every entry in `verified.json` puts the
article's sentence (`article_quote_ja`), the formal claim (`claim_ja`, `lean_statement`) and what is *not*
covered (`not_covered_ja`) side by side, and consumers should show all three.
Levels: **L0** = a Mathlib declaration is referenced and its type is checked against the claim;
**L1** = a lemma or computation from the article is proved here; **L2** = the article's main statement is
formalized and proved (none yet). CI (GitHub Actions) greps `MathGarden/` for `sorry`/`admit`/`native_decide`/`axiom`,
builds with `leanprover/lean-action`, and checks with `#print axioms` that every declaration in `verified.json`
uses only `propext`, `Classical.choice` and `Quot.sound`. Lean `v4.30.0`, Mathlib `v4.30.0`.
No license has been chosen yet.
