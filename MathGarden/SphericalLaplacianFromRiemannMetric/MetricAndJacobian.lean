import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-!
# 記事 `spherical-laplacian-from-riemann-metric` §2・§4・§6：球座標の計量・逆計量・行列式とヤコビアン

記事の文（記事から写す）：

> 3 次元ユークリッド空間を球座標 $x = r\sin\theta\cos\varphi,\ y = r\sin\theta\sin\varphi,\ z = r\cos\theta$ で表す。
> 微小変位を計算すると(連鎖律と三角公式を素直に展開すれば)、
> $$ds^2 = dr^2 + r^2\,d\theta^2 + r^2\sin^2\theta\,d\varphi^2.$$
> したがって計量テンソルは $g_{ij} = \mathrm{diag}(1, r^2, r^2\sin^2\theta)$、
> 逆計量(逆行列)は $g^{ij} = \mathrm{diag}(1, 1/r^2, 1/(r^2\sin^2\theta))$。（§2）

> $$|g| = \det(g_{ij}) = 1\cdot r^2 \cdot r^2\sin^2\theta = r^4\sin^2\theta.$$ したがって $\sqrt{|g|} = r^2\sin\theta.$
> ここで一拍置く。**$r^2\sin\theta$ は、球座標で体積要素を書いたときに出てくる、あのヤコビアン**である（§4）

> 計量と逆計量、行列式は $g_{ij} = \mathrm{diag}(1, r^2)$、$g^{ij} = \mathrm{diag}(1, 1/r^2)$、$\sqrt{|g|} = r$.（§6 2 次元極座標）

参照する宣言（Mathlib v4.30.0 のタグのソースで名前と型を確かめた）：

* `Matrix.inv_eq_right_inv`（`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`）：A * B ＝ 1 なら A⁻¹ ＝ B。
* `Matrix.diagonal_mul_diagonal`（`Mathlib/Data/Matrix/Mul.lean`）・`Matrix.diagonal_one`（`Mathlib/Data/Matrix/Diagonal.lean`）。
* `Matrix.det_diagonal`・`Matrix.det_fin_three`（`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`）。
* `Real.sqrt_sq`（`Mathlib/Data/Real/Sqrt.lean`）・`Real.sin_nonneg_of_nonneg_of_le_pi`
  （`Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean`）・`Real.sin_sq_add_cos_sq`
  （`Mathlib/Analysis/Complex/Trigonometric.lean`）。
* `fderivPolarCoordSymm`・`hasFDerivAt_polarCoord_symm`・`det_fderivPolarCoordSymm`
  （`Mathlib/Analysis/SpecialFunctions/PolarCoord.lean`）：(r, θ) ↦ (r cos θ, r sin θ) の微分とその行列式 ＝ r。

このファイルの定理は L1（このリポジトリで証明した）。3 次元の球座標のヤコビ行列 `jacobian` は、連鎖律で
手で偏微分して書いたもの（それが本当に写像の微分であることは Lean では確かめていない）。
-/

noncomputable section

namespace MathGarden.SphericalLaplacianFromRiemannMetric

/-- 球座標の計量 g_ij ＝ diag(1, r², r² sin²θ)（座標の順は r, θ, φ）。 -/
def metric (r θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![1, r ^ 2, r ^ 2 * Real.sin θ ^ 2]

/-- §2：dx・dy・dz を連鎖律で dr・dθ・dφ の一次式に書くと、dx² + dy² + dz² ＝ dr² + r² dθ² + r² sin²θ dφ²。 -/
theorem line_element (r θ φ dr dθ dφ : ℝ) :
    (Real.sin θ * Real.cos φ * dr + r * Real.cos θ * Real.cos φ * dθ
        - r * Real.sin θ * Real.sin φ * dφ) ^ 2
      + (Real.sin θ * Real.sin φ * dr + r * Real.cos θ * Real.sin φ * dθ
        + r * Real.sin θ * Real.cos φ * dφ) ^ 2
      + (Real.cos θ * dr - r * Real.sin θ * dθ) ^ 2
      = dr ^ 2 + r ^ 2 * dθ ^ 2 + r ^ 2 * Real.sin θ ^ 2 * dφ ^ 2 := by
  have h1 := Real.sin_sq_add_cos_sq θ
  have h2 := Real.sin_sq_add_cos_sq φ
  linear_combination
    (dr ^ 2 * Real.sin θ ^ 2 + dθ ^ 2 * r ^ 2 * Real.cos θ ^ 2 + dφ ^ 2 * r ^ 2 * Real.sin θ ^ 2
      + 2 * dr * dθ * r * Real.sin θ * Real.cos θ) * h2
    + (dr ^ 2 + dθ ^ 2 * r ^ 2) * h1

/-- §2：逆計量 g^ij ＝ diag(1, 1/r², 1/(r² sin²θ)) は計量の逆行列（r ≠ 0・sin θ ≠ 0 のとき）。 -/
theorem inverse_metric {r θ : ℝ} (hr : r ≠ 0) (hθ : Real.sin θ ≠ 0) :
    (metric r θ)⁻¹ = Matrix.diagonal ![1, 1 / r ^ 2, 1 / (r ^ 2 * Real.sin θ ^ 2)] := by
  apply Matrix.inv_eq_right_inv
  rw [metric, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i
  · show (1 : ℝ) * 1 = 1
    exact one_mul 1
  · show r ^ 2 * (1 / r ^ 2) = 1
    exact mul_one_div_cancel (pow_ne_zero 2 hr)
  · show r ^ 2 * Real.sin θ ^ 2 * (1 / (r ^ 2 * Real.sin θ ^ 2)) = 1
    exact mul_one_div_cancel (mul_ne_zero (pow_ne_zero 2 hr) (pow_ne_zero 2 hθ))

/-- §4：|g| ＝ det g_ij ＝ r⁴ sin²θ。 -/
theorem det_metric (r θ : ℝ) : (metric r θ).det = r ^ 4 * Real.sin θ ^ 2 := by
  rw [metric, Matrix.det_diagonal, Fin.prod_univ_three]
  show (1 : ℝ) * r ^ 2 * (r ^ 2 * Real.sin θ ^ 2) = r ^ 4 * Real.sin θ ^ 2
  ring

/-- §4：√|g| ＝ r² sin θ（余緯度 θ は 0 ≤ θ ≤ π なので sin θ ≥ 0）。 -/
theorem sqrt_det_metric (r : ℝ) {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    Real.sqrt (metric r θ).det = r ^ 2 * Real.sin θ := by
  rw [det_metric]
  have hs : 0 ≤ r ^ 2 * Real.sin θ :=
    mul_nonneg (sq_nonneg r) (Real.sin_nonneg_of_nonneg_of_le_pi h0 hπ)
  rw [show r ^ 4 * Real.sin θ ^ 2 = (r ^ 2 * Real.sin θ) ^ 2 by ring]
  exact Real.sqrt_sq hs

/-- 球座標 (r, θ, φ) ↦ (x, y, z) のヤコビ行列（行が x, y, z、列が r, θ, φ での偏微分。手で微分して書いた）。 -/
def jacobian (r θ φ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.sin θ * Real.cos φ, r * Real.cos θ * Real.cos φ, -(r * Real.sin θ * Real.sin φ);
     Real.sin θ * Real.sin φ, r * Real.cos θ * Real.sin φ, r * Real.sin θ * Real.cos φ;
     Real.cos θ, -(r * Real.sin θ), 0]

/-- §4：ヤコビアン（ヤコビ行列の行列式）は r² sin θ。 -/
theorem det_jacobian (r θ φ : ℝ) : (jacobian r θ φ).det = r ^ 2 * Real.sin θ := by
  rw [Matrix.det_fin_three]
  simp only [jacobian, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]
  have h1 := Real.sin_sq_add_cos_sq θ
  have h2 := Real.sin_sq_add_cos_sq φ
  linear_combination
    (r ^ 2 * Real.sin θ * (Real.sin θ ^ 2 + Real.cos θ ^ 2)) * h2 + (r ^ 2 * Real.sin θ) * h1

/-- §4：|g| ＝ r⁴ sin²θ、√|g| ＝ r² sin θ、そしてそれは球座標のヤコビアンに等しい（0 ≤ θ ≤ π）。 -/
theorem det_sqrt_eq_jacobian (r : ℝ) {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) (φ : ℝ) :
    (metric r θ).det = r ^ 4 * Real.sin θ ^ 2 ∧
    Real.sqrt (metric r θ).det = r ^ 2 * Real.sin θ ∧
    Real.sqrt (metric r θ).det = (jacobian r θ φ).det :=
  ⟨det_metric r θ, sqrt_det_metric r h0 hπ,
    (sqrt_det_metric r h0 hπ).trans (det_jacobian r θ φ).symm⟩

/-- §6：2 次元極座標の計量 diag(1, r²) の行列式の平方根は r（r ≥ 0）。 -/
theorem sqrt_det_polar_metric {r : ℝ} (hr : 0 ≤ r) :
    Real.sqrt (Matrix.diagonal ![1, r ^ 2] : Matrix (Fin 2) (Fin 2) ℝ).det = r := by
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  show Real.sqrt (1 * r ^ 2) = r
  rw [one_mul]
  exact Real.sqrt_sq hr

/- §6（Mathlib）：(r, θ) ↦ (r cos θ, r sin θ) の微分は `fderivPolarCoordSymm`。 -/
example (p : ℝ × ℝ) : HasFDerivAt polarCoord.symm (fderivPolarCoordSymm p) p :=
  hasFDerivAt_polarCoord_symm p

/-- §6：2 次元でも √|g| ＝ r は、極座標の写像の微分の行列式（ヤコビアン）r と一致する（r ≥ 0）。 -/
theorem polar_sqrt_det_eq_jacobian {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    Real.sqrt (Matrix.diagonal ![1, r ^ 2] : Matrix (Fin 2) (Fin 2) ℝ).det = r ∧
    (fderivPolarCoordSymm (r, θ)).det = r :=
  ⟨sqrt_det_polar_metric hr, det_fderivPolarCoordSymm (r, θ)⟩

end MathGarden.SphericalLaplacianFromRiemannMetric

end
