import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FinCases

/-!
# 記事 `縮約密度行列_部分トレースと同じか_2026-06-02` §0・§1：Bell 状態の部分トレースと、部分トレースの再現性

記事の文（記事から写す）：

> 二量子ビット系 … の最大エンタングル状態 $\lvert\Phi^+\rangle=\tfrac{1}{\sqrt2}(\lvert 0\rangle_A\lvert 0\rangle_B+\lvert 1\rangle_A\lvert 1\rangle_B)$
> をとる。全系は純粋状態 $\rho=\lvert\Phi^+\rangle\langle\Phi^+\rvert$ で、行列で書けば $\{00,01,10,11\}$ を基底とする
> $4\times4$ 行列の四隅だけに $\tfrac12$ が立つ。
> 部分トレース $\operatorname{Tr}_B$ は … $(\rho_A)_{a a'}=\sum_b \rho_{(a,b),(a',b)}$。… 結果は
> $\rho_A=\operatorname{Tr}_B\rho=\tfrac12\lvert 0\rangle\langle 0\rvert+\tfrac12\lvert 1\rangle\langle 1\rvert=\frac{I}{2}.$（§0）

> 射影 $O_A=\lvert 0\rangle\langle 0\rvert$ に対し $\operatorname{Tr}(\rho_A O_A)=\tfrac12$、一方
> $\langle\Phi^+\rvert(O_A\otimes I_B)\lvert\Phi^+\rangle=\tfrac12$。両者は一致する。（§0）

> $A$ だけにはたらく任意の観測量 $O_A$ について
> $\operatorname{Tr}_{\mathcal H_A}(\rho_A\, O_A)=\operatorname{Tr}_{\mathcal H_A\otimes\mathcal H_B}(\rho\,(O_A\otimes I_B)).$（§1）

参照する宣言（Mathlib v4.30.0 のタグのソースで名前と型を確かめた）：

* `Matrix.kroneckerMap`・`Matrix.kroneckerMap_apply`・記法 `⊗ₖ`（`open Kronecker`）
  （`Mathlib/LinearAlgebra/Matrix/Kronecker.lean`）。
* `Matrix.trace`（`Mathlib/LinearAlgebra/Matrix/Trace.lean`）・`Matrix.diag`・`Matrix.one_apply_eq`・`Matrix.one_apply_ne`
  （`Mathlib/Data/Matrix/Diagonal.lean`）・`Matrix.vecMulVec`・`Matrix.mulVec`・`dotProduct`（`Mathlib/Data/Matrix/Mul.lean`）。
* `Fintype.sum_prod_type`・`Finset.sum_eq_single`・`Finset.sum_comm`・`Real.mul_self_sqrt`。

Mathlib に部分トレースの宣言は見つからなかった（下調べ：`partialTrace`・`traceLeft` 0 件）ので、記事 §0 の式
(ρ_A)_{aa'} ＝ Σ_b ρ_{(a,b),(a',b)} をそのまま定義 `ptraceB` にした。定理はすべて L1。
Bell 状態の計算は係数を実数で書いた（|Φ⁺⟩ の成分は実数なので、転置共役は転置と同じ）。
-/

noncomputable section

namespace MathGarden.ReducedDensityMatrixPartialTrace

open Matrix Kronecker

/-- 部分トレース Tr_B：(ρ_A)_{a a'} ＝ Σ_b ρ_{(a,b),(a',b)}（記事 §0 の式）。 -/
def ptraceB {α β R : Type*} [Fintype β] [AddCommMonoid R]
    (ρ : Matrix (α × β) (α × β) R) : Matrix α α R :=
  Matrix.of fun i i' => ∑ j, ρ (i, j) (i', j)

/-- §1：A だけにはたらく任意の O_A について Tr(ρ_A O_A) ＝ Tr(ρ (O_A ⊗ I_B))。 -/
theorem trace_ptraceB_mul {α β R : Type*} [Fintype α] [Fintype β] [DecidableEq β] [CommRing R]
    (ρ : Matrix (α × β) (α × β) R) (O : Matrix α α R) :
    Matrix.trace (ptraceB ρ * O) = Matrix.trace (ρ * (O ⊗ₖ (1 : Matrix β β R))) := by
  have key : ∀ (i : α) (j : β),
      (ρ * (O ⊗ₖ (1 : Matrix β β R))) (i, j) (i, j) = ∑ k, ρ (i, j) (k, j) * O k i := by
    intro i j
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_eq_single j]
    · simp only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, mul_one]
    · intro l _ hl
      simp only [Matrix.kroneckerMap_apply, Matrix.one_apply_ne hl, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  calc Matrix.trace (ptraceB ρ * O)
      = ∑ i, ∑ k, (∑ j, ρ (i, j) (k, j)) * O k i := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, ptraceB, Matrix.of_apply]
    _ = ∑ i, ∑ j, ∑ k, ρ (i, j) (k, j) * O k i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [Finset.sum_mul]
        exact Finset.sum_comm
    _ = Matrix.trace (ρ * (O ⊗ₖ (1 : Matrix β β R))) := by
        rw [Matrix.trace, Fintype.sum_prod_type]
        simp only [Matrix.diag, key]

/-- 1/√2。 -/
def bellCoeff : ℝ := (Real.sqrt 2)⁻¹

theorem bellCoeff_mul_self : bellCoeff * bellCoeff = 1 / 2 := by
  rw [bellCoeff, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_div]

/-- |Φ⁺⟩ ＝ (|00⟩ + |11⟩)/√2（添字は (A の添字, B の添字)）。 -/
def bellState : Fin 2 × Fin 2 → ℝ := fun p => if p.1 = p.2 then bellCoeff else 0

/-- ρ ＝ |Φ⁺⟩⟨Φ⁺|。 -/
def bellDensity : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  Matrix.vecMulVec bellState bellState

/-- §0：ρ は 4×4 行列の四隅（添字が 00 と 11 の組）だけに 1/2 が立つ。 -/
theorem bellDensity_apply (p q : Fin 2 × Fin 2) :
    bellDensity p q = if p.1 = p.2 ∧ q.1 = q.2 then 1 / 2 else 0 := by
  by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;>
    simp [bellDensity, bellState, Matrix.vecMulVec_apply, hp, hq, bellCoeff_mul_self]

/-- §0：Tr_B ρ ＝ I/2（A は最大混合状態）。 -/
theorem bell_ptraceB : ptraceB bellDensity = (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i i'
  fin_cases i <;> fin_cases i' <;>
    simp [ptraceB, bellDensity_apply, Fin.sum_univ_two]

/-- 射影 O_A ＝ |0⟩⟨0|。 -/
def proj0 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- §0：Tr(ρ_A O_A) ＝ 1/2。 -/
theorem bell_trace_reduced : Matrix.trace (ptraceB bellDensity * proj0) = 1 / 2 := by
  rw [bell_ptraceB]
  simp [Matrix.trace, Fin.sum_univ_two, proj0]

/-- §0：⟨Φ⁺|(O_A ⊗ I_B)|Φ⁺⟩ ＝ 1/2。 -/
theorem bell_expectation_full :
    bellState ⬝ᵥ ((proj0 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ bellState) = 1 / 2 := by
  simp [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two, bellState, proj0,
    Matrix.one_apply, bellCoeff_mul_self]

/-- §0：A だけで測った期待値 Tr(ρ_A O_A) と全系で測った期待値 ⟨Φ⁺|(O_A ⊗ I_B)|Φ⁺⟩ はどちらも 1/2 で一致し、
全系のトレースの形 Tr(ρ (O_A ⊗ I_B)) も 1/2（§1 の定理から）。 -/
theorem bell_measurement_reproduced :
    Matrix.trace (ptraceB bellDensity * proj0) = 1 / 2 ∧
    bellState ⬝ᵥ ((proj0 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ bellState) = 1 / 2 ∧
    Matrix.trace (bellDensity * (proj0 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ))) = 1 / 2 :=
  ⟨bell_trace_reduced, bell_expectation_full,
    (trace_ptraceB_mul bellDensity proj0).symm.trans bell_trace_reduced⟩

end MathGarden.ReducedDensityMatrixPartialTrace

end
