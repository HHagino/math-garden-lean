import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# 記事 `何を解と呼ぶのか_2026-06-02`：ガンマ関数の漸化式と特殊値（L0）

記事「第2節」の文（記事から写す）：

> 部分積分すると … $\Gamma(z+1) = z\,\Gamma(z)$、そして $\Gamma(1)=1$。この漸化式を回すと $\Gamma(n+1)=n!$。
> … $\Gamma(\tfrac12)=\sqrt\pi$ のように階乗が「半分」の点でも値を持つ。

L0 ＝ Mathlib にある宣言を参照し、その型が下の主張と一致することを Lean に確かめさせる
（このリポジトリで新しく証明したものはない）。参照する宣言（実数版）：

* `Real.Gamma_add_one`、`Real.Gamma_one`、`Real.Gamma_nat_eq_factorial`
  （`Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`）
* `Real.Gamma_one_half_eq`（`Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`）

Mathlib の `Real.Gamma` は積分で定義したものを解析接続した関数で、記事の
「Re z > 0 での積分」と同じ値を取るが、定義の書き方は違う。
-/

namespace MathGarden.WhatIsCalledASolution

/- 漸化式：`s ≠ 0` のとき `Γ(s+1) = s Γ(s)`。 -/
example (s : ℝ) (hs : s ≠ 0) : Real.Gamma (s + 1) = s * Real.Gamma s :=
  Real.Gamma_add_one hs

/- `Γ(1) = 1`。 -/
example : Real.Gamma 1 = 1 := Real.Gamma_one

/- `Γ(n+1) = n!`。 -/
example (n : ℕ) : Real.Gamma (n + 1) = (n.factorial : ℝ) := Real.Gamma_nat_eq_factorial n

/- `Γ(1/2) = √π`。 -/
example : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq

end MathGarden.WhatIsCalledASolution
