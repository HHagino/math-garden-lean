import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# 記事 `Euler因子は局所Mellin変換である_ガンマ因子だけ形が違って見える理由_2026-08-15` §2・§3：局所因子の計算

記事の文（記事から写す）：

> $$Z_p(s) = \int_{\mathbb{Q}_p^\times}\mathbf{1}_{\mathbb{Z}_p}(x)\,|x|_p^{s}\,d^\times x = \sum_{n\ge 0} … \bigl(p^{-n}\bigr)^{s} = \sum_{n\ge 0} p^{-ns}.$$
> 等比級数だから、$\operatorname{Re} s > 0$ で $Z_p(s) = \frac{1}{1-p^{-s}}$（§2）

> $$Z_\infty(s) = \int_{\mathbb{R}^\times} e^{-\pi x^2}\,|x|^{s}\,\frac{dx}{|x|} \;=\; 2\int_0^\infty e^{-\pi x^2}\,x^{s-1}\,dx$$
> … $Z_\infty(s) = \pi^{-s/2}\,\Gamma(s/2)$（§3）

> そして両者を掛ければ、$\operatorname{Re} s>1$ で
> $\prod_v Z_v(s) = \pi^{-s/2}\Gamma(s/2)\prod_p(1-p^{-s})^{-1} = \pi^{-s/2}\Gamma(s/2)\,\zeta(s) = \xi(s).$（§3）

参照する宣言（Mathlib v4.30.0 のタグのソースで名前と型を確かめた）：

* `integral_rpow_mul_exp_neg_mul_rpow`（`Mathlib/MeasureTheory/Integral/Gamma.lean`）：
  ∫_0^∞ x^q e^{−b x^p} dx ＝ b^{−(q+1)/p}·(1/p)·Γ((q+1)/p)（p > 0, q > −1, b > 0。実数）。
* `tsum_geometric_of_norm_lt_one`（`Mathlib/Analysis/SpecificLimits/Normed.lean`）・
  `Complex.norm_natCast_cpow_of_pos`・`Real.rpow_lt_one_of_one_lt_of_neg`（`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`）。
* `riemannZeta_eulerProduct_tprod`（`Mathlib/NumberTheory/EulerProduct/DirichletLSeries.lean`）：Re s > 1 で ∏_p (1 − p^{−s})^{−1} ＝ ζ(s)。
* `Complex.Gammaℝ_def`（`Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean`）：Γ_ℝ(s) ＝ π^{−s/2} Γ(s/2)。
* `riemannZeta_def_of_ne_zero`（`Mathlib/NumberTheory/LSeries/RiemannZeta.lean`）：s ≠ 0 で ζ(s) ＝ Λ(s) / Γ_ℝ(s)。

`archimedean_local_factor`・`finite_local_factor`（L1）は記事 §3・§2 の最後の等式を、上の宣言から数行で出したもの。
p 進の積分（ℚ_p^× の Haar 測度）としての $Z_p$ は書いていない（級数の形だけ）。
-/

namespace MathGarden.EulerFactorLocalMellin

open Real Set MeasureTheory

/-- §3：実数 s > 0 で $2\int_0^\infty e^{-\pi x^2} x^{s-1}\,dx = \pi^{-s/2}\Gamma(s/2)$。 -/
theorem archimedean_local_factor {s : ℝ} (hs : 0 < s) :
    2 * ∫ x in Ioi (0 : ℝ), x ^ (s - 1) * Real.exp (-π * x ^ (2 : ℝ))
      = π ^ (-s / 2) * Real.Gamma (s / 2) := by
  rw [integral_rpow_mul_exp_neg_mul_rpow (q := s - 1) two_pos (by linarith) Real.pi_pos]
  have h : s - 1 + 1 = s := by ring
  rw [h]
  ring

/-- §2：素数（一般に 1 < p の自然数）p と Re s > 0 で $\sum_{n\ge0} (p^{-s})^n = (1-p^{-s})^{-1}$。 -/
theorem finite_local_factor {p : ℕ} (hp : 1 < p) {s : ℂ} (hs : 0 < s.re) :
    ∑' n : ℕ, ((p : ℂ) ^ (-s)) ^ n = (1 - (p : ℂ) ^ (-s))⁻¹ := by
  apply tsum_geometric_of_norm_lt_one
  rw [Complex.norm_natCast_cpow_of_pos (by omega) (-s), Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp) (by linarith)

/- §3：Euler 積 ∏_p (1 − p^{−s})^{−1} ＝ ζ(s)（Re s > 1）。 -/
example {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s :=
  riemannZeta_eulerProduct_tprod hs

/- §3：Γ_ℝ(s) ＝ π^{−s/2} Γ(s/2)（複素数 s）。 -/
example (s : ℂ) : Complex.Gammaℝ s = (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) :=
  Complex.Gammaℝ_def s

/- §3：ζ(s) ＝ Λ(s) / Γ_ℝ(s)（s ≠ 0。Mathlib の Λ は記事の ξ を「π^{−s/2}Γ(s/2)ζ(s)」と読んだもの）。 -/
example {s : ℂ} (hs : s ≠ 0) : riemannZeta s = completedRiemannZeta s / Complex.Gammaℝ s :=
  riemannZeta_def_of_ne_zero hs

end MathGarden.EulerFactorLocalMellin
