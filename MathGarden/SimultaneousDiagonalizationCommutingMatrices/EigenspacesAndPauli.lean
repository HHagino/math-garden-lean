import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-!
# 記事 `simultaneous-diagonalization-commuting-matrices` §4・§8：可換なら固有空間を保つ・Pauli 行列の反例

記事の文（記事から写す）：

> ここで $AB = BA$ が効く。$v \in V_i$($Av = \lambda_i v$)とすると、$A(Bv) = B(Av) = B(\lambda_i v) = \lambda_i (Bv).$
> つまり $Bv$ もまた $V_i$ に入り … **$B$ は $A$ の各固有空間を不変に保つ。**（§4）

> Pauli 行列 $\sigma_x=\begin{pmatrix}0&1\\1&0\end{pmatrix},\ \sigma_z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}$ …
> $\sigma_x\sigma_z \neq\sigma_z\sigma_x$ で **非可換**。… $\sigma_x e_1=e_2\notin\mathrm{span}(e_1)$ ──
> $\sigma_x$ は $\sigma_z$ の固有空間を保たない。実際、両者に共通の固有ベクトルは存在しない。（§8）

参照する宣言（Mathlib v4.30.0 のタグのソースで名前と型を確かめた）：

* `Module.End.mem_eigenspace_iff`（`Mathlib/LinearAlgebra/Eigenspace/Basic.lean`）：x ∈ eigenspace f μ ⇔ f x ＝ μ • x。
* `Module.End.mul_apply`（`Mathlib/Algebra/Module/LinearMap/End.lean`）：(f * g) x ＝ f (g x)。
* `Module.End.mapsTo_genEigenspace_of_comm`（Eigenspace/Basic.lean）：可換なら一般固有空間も保つ（Mathlib のほうが一般）。

このファイルの定理はすべて L1（このリポジトリで証明した）。記事 §2 の定理そのもの（可換な対角化可能行列の同時対角化）は
Mathlib に一般の形が見つからず（対称作用素の版 `LinearMap.IsSymmetric.directSum_isInternal_of_commute` だけ）、入れていない。
-/

namespace MathGarden.SimultaneousDiagonalizationCommutingMatrices

/-- §4：f と g が可換なら、g は f の固有空間（固有値 μ）を保つ。 -/
theorem eigenspace_invariant_of_commute {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {f g : Module.End R M} (h : Commute f g) (μ : R) {x : M}
    (hx : x ∈ f.eigenspace μ) : g x ∈ f.eigenspace μ := by
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  rw [← Module.End.mul_apply, h.eq, Module.End.mul_apply, hx, map_smul]

/- Mathlib の一般の形（一般固有空間・k は ℕ∞）。 -/
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {f g : Module.End R M} (h : Commute f g) (μ : R) (k : ℕ∞) :
    Set.MapsTo g (f.genEigenspace μ k) (f.genEigenspace μ k) :=
  Module.End.mapsTo_genEigenspace_of_comm h μ k

/-- Pauli 行列 σ_x。 -/
def σx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli 行列 σ_z。 -/
def σz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- §8：σ_x σ_z ≠ σ_z σ_x（(0,1) 成分が −1 と 1）。 -/
theorem pauli_not_commute : σx * σz ≠ σz * σx := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [σx, σz, Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num at h01

/-- §8：σ_x と σ_z に共通の固有ベクトルはない（両方の固有ベクトルなら 0）。 -/
theorem pauli_no_common_eigenvector (v : Fin 2 → ℂ) (a b : ℂ)
    (hx : Matrix.mulVec σx v = a • v) (hz : Matrix.mulVec σz v = b • v) : v = 0 := by
  have e1 : v 1 = a * v 0 := by
    simpa [σx, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hx 0
  have e2 : v 0 = a * v 1 := by
    simpa [σx, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hx 1
  have e3 : v 0 = b * v 0 := by
    simpa [σz, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hz 0
  have e4 : -v 1 = b * v 1 := by
    simpa [σz, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hz 1
  have h1 : v 1 = 0 := by
    linear_combination (1 - b) / 2 * e1 + a / 2 * e3 - e4 / 2
  have h0 : v 0 = 0 := by rw [e2, h1, mul_zero]
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1

end MathGarden.SimultaneousDiagonalizationCommutingMatrices
