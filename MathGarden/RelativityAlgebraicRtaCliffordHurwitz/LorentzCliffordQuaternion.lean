import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# 記事 `relativity-algebraic-rta-clifford-hurwitz` §2・§3・§4：Lorentz 二次形式・Clifford 代数・四元数の積

記事の文（記事から写す）：

> 時空 $\mathbb{R}^{1,3}$ 上の二次形式 $Q(t, \mathbf{x}) = c^2 t^2 - |\mathbf{x}|^2$ を考える。…
> たとえば $T=2I$ は光円錐を保つが $Q(Tv)=4Q(v)$ で、…（§2）

> Clifford 代数 $\mathrm{Cl}(V, Q)$ は、$V$ の元 $v$ が $v^2 = Q(v)$ をみたすような最も自由な結合代数として定義される。（§3）

> 3 次元外積は **四元数 $\mathbb{H}$ の虚部** $\mathrm{Im}\,\mathbb{H} \cong \mathbb{R}^3$ の積から自然に出る。
> $u, v \in \mathrm{Im}\,\mathbb{H}$ に対して、$uv = -\langle u, v \rangle + u \times v$ と分解できる。
> スカラー部分が内積、ベクトル部分が外積。（§4）

参照する宣言（Mathlib v4.30.0 のタグのソースで名前と型を確かめた）：

* `CliffordAlgebra`・`CliffordAlgebra.ι`・`CliffordAlgebra.ι_sq_scalar`（`ι Q m * ι Q m = algebraMap R _ (Q m)`）
  （`Mathlib/LinearAlgebra/CliffordAlgebra/Basic.lean`）。
* `QuadraticMap.weightedSumSquares`・`QuadraticMap.weightedSumSquares_apply`・`QuadraticMap.map_smul`
  （`Mathlib/LinearAlgebra/QuadraticForm/Basic.lean`）。
* `Quaternion`（記法 `ℍ[ℝ]`）・`Quaternion.ext`・`Quaternion.re_mul`・`imI_mul`・`imJ_mul`・`imK_mul`
  （`Mathlib/Algebra/Quaternion.lean`）。
* `crossProduct`（記法 `⨯₃`）・`cross_apply`（`Mathlib/LinearAlgebra/CrossProduct.lean`）・`Matrix.vec3_dotProduct`
  （`Mathlib/LinearAlgebra/Matrix/Notation.lean`）。

`clifford_sq_lorentz` は Mathlib の `ι_sq_scalar` に記事の Lorentz 形式を入れて Q(v) を書き下したもの（L0 の参照に
数行の計算を足したので L1 とした）。`pure_quaternion_mul` は L1。
-/

noncomputable section

namespace MathGarden.RelativityAlgebraicRtaCliffordHurwitz

open Matrix Quaternion

/-- Lorentz の二次形式 Q(t, x) ＝ c²t² − |x|²（座標は (t, x₁, x₂, x₃)）。 -/
def lorentzForm (c : ℝ) : QuadraticForm ℝ (Fin 4 → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ ![c ^ 2, -1, -1, -1]

theorem lorentzForm_apply (c : ℝ) (v : Fin 4 → ℝ) :
    lorentzForm c v = c ^ 2 * v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by
  rw [lorentzForm, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, smul_eq_mul]
  ring

/-- §2：T ＝ 2I では Q(Tv) ＝ 4 Q(v)（光円錐 Q ＝ 0 は保つが Q そのものは保たない）。 -/
theorem lorentzForm_two_smul (c : ℝ) (v : Fin 4 → ℝ) :
    lorentzForm c ((2 : ℝ) • v) = 4 * lorentzForm c v := by
  rw [QuadraticMap.map_smul, smul_eq_mul]
  norm_num

/-- §3：Lorentz 形式の Clifford 代数の中で、ベクトル v は v² ＝ Q(v) ＝ c²t² − |x|² をみたす。 -/
theorem clifford_sq_lorentz (c : ℝ) (v : Fin 4 → ℝ) :
    CliffordAlgebra.ι (lorentzForm c) v * CliffordAlgebra.ι (lorentzForm c) v =
      algebraMap ℝ (CliffordAlgebra (lorentzForm c))
        (c ^ 2 * v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2)) := by
  rw [CliffordAlgebra.ι_sq_scalar, lorentzForm_apply]

/-- 3 次元ベクトル u を純虚四元数 u₀ i + u₁ j + u₂ k と見る。 -/
def pureQuat (u : Fin 3 → ℝ) : ℍ[ℝ] := QuaternionAlgebra.mk 0 (u 0) (u 1) (u 2)

/-- §4：純虚四元数 u, v の積は uv ＝ −⟨u, v⟩ + u × v（実部が内積の符号を変えたもの、虚部が外積）。 -/
theorem pure_quaternion_mul (u v : Fin 3 → ℝ) :
    pureQuat u * pureQuat v =
      (QuaternionAlgebra.mk (-(u ⬝ᵥ v)) ((u ⨯₃ v) 0) ((u ⨯₃ v) 1) ((u ⨯₃ v) 2) : ℍ[ℝ]) := by
  ext <;> simp [pureQuat, cross_apply, Matrix.vec3_dotProduct] <;> ring

end MathGarden.RelativityAlgebraicRtaCliffordHurwitz

end
