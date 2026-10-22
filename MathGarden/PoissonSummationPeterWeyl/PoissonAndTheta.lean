import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# 記事 `Poisson和公式は格子で割ったPeter-Weylである_関数等式はどこから来るのか_2026-08-15` §3・§5：Poisson 和公式とテータの変換公式

記事の文（記事から写す）：

> **定理.** $f:\mathbb{R}\to\mathbb{C}$ が十分速く減衰する滑らかな関数（Schwartz 級で十分）なら
> $$\sum_{n\in\mathbb{Z}} f(n) \;=\; \sum_{k\in\mathbb{Z}} \hat f(k), \qquad \hat f(\xi) = \int_{\mathbb{R}} f(x)\,e^{-2\pi i x\xi}\,dx.$$
> （§3「Poisson 和公式と、その 3 行の証明」）

> $\theta(t) := \sum_{n\in\mathbb{Z}} e^{-\pi n^2 t}$ と置けば … $\theta(1/t) = \sqrt{t}\,\theta(t)$。
> （§5「Gauss 関数を入れる ── テータの変換公式」）

参照する宣言（Mathlib v4.30.0 のタグのソースで名前と型を確かめた）：

* `SchwartzMap.tsum_eq_tsum_fourier`（`Mathlib/Analysis/Fourier/PoissonSummation.lean`）：
  Schwartz 関数 f と実数 x について Σ_n f(x+n) ＝ Σ_n 𝓕f(n)·e^{2πinx}（x で平行移動した形）。
  Schwartz 関数の 𝓕 は `SchwartzMap.fourier_coe`（定義から rfl）で関数としてのフーリエ変換と同じで、
  その規約は `Real.fourier_eq`：𝓕f(w) ＝ ∫ 𝐞(−⟪v,w⟫)·f(v) dv（𝐞(x) ＝ e^{2πix}）＝ 記事の $\hat f$ と同じ符号と 2π の置き方。
* `fourier_eval_zero`（`Mathlib/Analysis/Fourier/AddCircle.lean`）：e^{2πin·0} ＝ 1。
* `jacobiTheta_S_smul`（`Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean`）：
  上半平面の τ について θ(−1/τ) ＝ (−iτ)^{1/2}·θ(τ)。ここで θ(τ) ＝ Σ_n exp(πin²τ)。

`poisson_summation_at_zero`（L1）は、Mathlib の平行移動つきの式に x ＝ 0 を入れて記事の形にしたもの（数行）。
-/

namespace MathGarden.PoissonSummationPeterWeyl

open scoped SchwartzMap FourierTransform UpperHalfPlane

/- Mathlib の形：平行移動 x つきの Poisson 和公式。 -/
example (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 f n * fourier n (x : UnitAddCircle) :=
  SchwartzMap.tsum_eq_tsum_fourier f x

/-- 記事 §3 の形：Schwartz 関数 f について $\sum_n f(n) = \sum_k \hat f(k)$。 -/
theorem poisson_summation_at_zero (f : 𝓢(ℝ, ℂ)) :
    ∑' n : ℤ, f n = ∑' n : ℤ, 𝓕 f n := by
  have h := SchwartzMap.tsum_eq_tsum_fourier f 0
  simpa [fourier_eval_zero] using h

/- 記事 §5 の元になる形：θ(−1/τ) ＝ (−iτ)^{1/2} θ(τ)（τ は上半平面）。記事の実数 t > 0 は τ ＝ it に当たる。 -/
example (τ : ℍ) :
    jacobiTheta ↑(ModularGroup.S • τ) = (-Complex.I * τ) ^ (1 / 2 : ℂ) * jacobiTheta τ :=
  jacobiTheta_S_smul τ

end MathGarden.PoissonSummationPeterWeyl
