import Mathlib.NumberTheory.Real.Irrational

/-!
# 記事 `pythagoras-sqrt2-p-adic-mod-8`：√2 は整数比で表せない（L0）

記事「ピタゴラス派は p 進数を見ていたのか? ── √2、通約不能性、そして mod 8 の局所数論」
「導入」の文（記事から写す）：

> 辺の長さを 1 とすれば、対角線の長さは $\sqrt{2}$。ピタゴラスの定理から $\sqrt{2}$ は出てくる
> ── しかし、これは整数比では表せない(通約不能、incommensurable)。

L0 ＝ Mathlib にある宣言を参照し、その型が下の主張と一致することを Lean に確かめさせる
（このリポジトリで新しく証明したものはない）。参照する宣言：

* `irrational_sqrt_two : Irrational (√2)`（`Mathlib/NumberTheory/Real/Irrational.lean`）。
  `Irrational x` の定義は「`x` は有理数（`ℚ → ℝ` の像）のどれとも等しくない」。
* `Irrational.ne_rational : Irrational x → ∀ a b : ℤ, x ≠ a / b`（同じファイル）。
  これで記事の言い方「整数比では表せない」の形にそろえる。

* 確かめたこと：実数の平方根 `Real.sqrt 2` は、どの整数 `a, b` についても `a / b` と等しくない
  （`b = 0` のときの `a / 0 = 0` も含む）。
* 確かめていないこと：正方形の対角線の長さが $\sqrt 2$ であること（ピタゴラスの定理の部分）、
  記事 §2 の「方程式 $x^2 = 2$ は $\mathbb{Q}$ で解を持たない」という言い方、史実についての記述。
-/

namespace MathGarden.PythagorasSqrt2PadicMod8

/- Mathlib の宣言の名前と型を確かめる：`irrational_sqrt_two : Irrational (Real.sqrt 2)`。 -/
example : Irrational (Real.sqrt 2) := irrational_sqrt_two

/- 記事の言い方にそろえた形：どの整数 `a, b` についても `√2 ≠ a / b`。 -/
example (a b : ℤ) : Real.sqrt 2 ≠ a / b := irrational_sqrt_two.ne_rational a b

end MathGarden.PythagorasSqrt2PadicMod8
