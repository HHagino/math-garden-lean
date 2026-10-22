import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

/-!
# 記事 `hyperbolic-circle-apollonius-cayley` §3・§5：i 中心の双曲円はユークリッド円・上端と下端

記事の文（記事から写す）：

> $$\cosh d_{\mathbb{H}}(z,w) = 1 + \frac{|z-w|^2}{2\,\operatorname{Im}z\,\operatorname{Im}w}$$（§2）

> 双曲半径 $r$ の円、すなわち「$i$ からの双曲距離がちょうど $r$ である点の集合」… 結論はこうだ。
> $$\text{中心 } (0,\ \cosh r), \qquad \text{半径 } \sinh r$$（§3「i を中心とする双曲円の方程式」）

> $$y = \cosh r - \sinh r = e^{-r}, \qquad y = \cosh r + \sinh r = e^{r}$$
> 円の下端は $ie^{-r}$、上端は $ie^{r}$ である。（§5）

参照する宣言（Mathlib v4.30.0 のタグのソースで名前と型を確かめた）：

* `UpperHalfPlane.cosh_dist`（`Mathlib/Analysis/Complex/UpperHalfPlane/Metric.lean`）：§2 の距離の式。
* `UpperHalfPlane.center`・`center_re`・`center_im`（同じファイル）：中心 w・双曲半径 r の円のユークリッド中心
  ＝ (Re w, Im w·cosh r)。
* `UpperHalfPlane.dist_eq_iff_dist_coe_center_eq`（同じファイル）：
  双曲距離 d(z, w) ＝ r ⇔ z とユークリッド中心との普通の距離 ＝ Im w·sinh r。
* `UpperHalfPlane.I`・`I_re`・`I_im`（`Mathlib/Analysis/Complex/UpperHalfPlane/Basic.lean`）。
* `Real.cosh_add_sinh`・`Real.cosh_sub_sinh`（`Mathlib/Analysis/Complex/Trigonometric.lean`）。

`hyperbolic_circle_at_i`（L1）は、Mathlib の一般の中心 w の式に w ＝ i を入れて記事の形
（中心 (0, cosh r)・半径 sinh r）にしたもの。
-/

namespace MathGarden.HyperbolicCircleApolloniusCayley

open UpperHalfPlane

/- §2：cosh d(z, w) ＝ 1 + |z − w|² / (2 Im z Im w)。 -/
example (z w : ℍ) :
    Real.cosh (dist z w) = 1 + dist (z : ℂ) w ^ 2 / (2 * z.im * w.im) :=
  UpperHalfPlane.cosh_dist z w

/-- §3：i からの双曲距離が r の点 z は、ちょうどユークリッド中心 (0, cosh r)・半径 sinh r の円の上にある。 -/
theorem hyperbolic_circle_at_i (z : ℍ) (r : ℝ) :
    dist z UpperHalfPlane.I = r ↔ dist (z : ℂ) ⟨0, Real.cosh r⟩ = Real.sinh r := by
  rw [UpperHalfPlane.dist_eq_iff_dist_coe_center_eq]
  have hc : ((UpperHalfPlane.center UpperHalfPlane.I r : ℍ) : ℂ) = ⟨0, Real.cosh r⟩ := by
    apply Complex.ext <;> simp
  rw [hc, UpperHalfPlane.I_im, one_mul]

/- §5：上端 cosh r + sinh r ＝ e^r、下端 cosh r − sinh r ＝ e^{−r}。 -/
example (r : ℝ) : Real.cosh r + Real.sinh r = Real.exp r := Real.cosh_add_sinh (x := r)
example (r : ℝ) : Real.cosh r - Real.sinh r = Real.exp (-r) := Real.cosh_sub_sinh (x := r)

end MathGarden.HyperbolicCircleApolloniusCayley
