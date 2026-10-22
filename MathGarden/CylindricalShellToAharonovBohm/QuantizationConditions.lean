import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination

/-!
# 記事 `cylindrical-shell-to-aharonov-bohm` §2・§4・§6：角度の一価性・境界条件の行列式・磁束の周期

記事の文（記事から写す）：

> 波動関数の**一価性**から $\Phi(\varphi + 2\pi) = \Phi(\varphi)$ を要求する。これは $e^{2\pi i\alpha} = 1$、
> つまり $\alpha = m, \ m \in \mathbb{Z}$ を意味する。（§2）

> $A\,J_m(ka) + B\,N_m(ka) = 0,\quad A\,J_m(kb) + B\,N_m(kb) = 0.$ $(A,B)$ についての斉次連立 1 次方程式だ。
> 非自明解 $(A,B)\ne(0,0)$ が存在するには、係数行列の行列式が消える必要がある：…
> $J_m(ka)\,N_m(kb) - J_m(kb)\,N_m(ka) = 0.$（§4）

> エネルギーは $E_m(\Phi_B) = \frac{\hbar^2}{2MR^2}\left(m - \frac{q\Phi_B}{h}\right)^2$ となり、…
> 磁束を変化させると、エネルギー準位(の集合)が周期 $h/|q|$ で振動する（§6）

参照する宣言（Mathlib v4.30.0 のタグのソースで名前と型を確かめた）：

* `Matrix.exists_mulVec_eq_zero_iff`（`(∃ v ≠ 0, M *ᵥ v = 0) ↔ M.det = 0`、整域上）
  （`Mathlib/LinearAlgebra/Matrix/ToLinearEquiv.lean`）・`Matrix.det_fin_two_of`。
* `Complex.exp_eq_one_iff`（`exp x = 1 ↔ ∃ n : ℤ, x = n * (2 * π * I)`）
  （`Mathlib/Analysis/SpecialFunctions/Complex/Log.lean`）・`Complex.exp_add`・`Complex.exp_zero`
  （`Mathlib/Analysis/Complex/Exponential.lean`）・`Complex.ofReal_intCast`・`Complex.I_ne_zero`。
* `mul_inv_cancel₀`（`Mathlib/Algebra/GroupWithZero/Defs.lean`）。

ベッセル関数は Mathlib に見つからなかった（下調べ）。§4 はベッセル関数の値を任意の実数 Ja, Na, Jb, Nb に置いた
（記事の主張は係数が何であっても成り立つ線形代数）。定理はすべて L1。
-/

noncomputable section

namespace MathGarden.CylindricalShellToAharonovBohm

open Matrix

/-- §2：e^{iαφ} が φ ↦ φ + 2π で元に戻る（すべての φ で）ことと、α が整数であることは同値。 -/
theorem single_valued_iff_integer (α : ℝ) :
    (∀ φ : ℝ, Complex.exp (Complex.I * α * (φ + 2 * Real.pi)) = Complex.exp (Complex.I * α * φ)) ↔
      ∃ m : ℤ, α = m := by
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have key : ∀ φ : ℝ, Complex.exp (Complex.I * α * (φ + 2 * Real.pi)) =
      Complex.exp (Complex.I * α * φ) * Complex.exp (α * (2 * Real.pi * Complex.I)) := by
    intro φ
    rw [← Complex.exp_add]
    congr 1
    ring
  constructor
  · intro h
    have h0 := h 0
    rw [key, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h0
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h0
    refine ⟨n, ?_⟩
    have hαn : (α : ℂ) = n := mul_right_cancel₀ hne hn
    exact_mod_cast hαn
  · rintro ⟨m, rfl⟩ φ
    rw [key]
    have h1 : Complex.exp (((m : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) = 1 :=
      Complex.exp_eq_one_iff.mpr ⟨m, by simp⟩
    rw [h1, mul_one]

/-- §4：(A, B) についての連立方程式 A·Ja + B·Na ＝ 0, A·Jb + B·Nb ＝ 0（係数行列 [[Ja, Na], [Jb, Nb]]）に
(A, B) ≠ 0 の解があることと、Ja Nb − Jb Na ＝ 0 は同値。 -/
theorem nontrivial_solution_iff_det (Ja Na Jb Nb : ℝ) :
    (∃ v ≠ 0, !![Ja, Na; Jb, Nb] *ᵥ v = 0) ↔ Ja * Nb - Jb * Na = 0 := by
  rw [Matrix.exists_mulVec_eq_zero_iff, Matrix.det_fin_two_of, mul_comm Na Jb]

/-- リング模型のエネルギー E_m(Φ) ＝ ħ²/(2MR²)·(m − qΦ/h)²。 -/
def ringEnergy (hbar M R q h : ℝ) (m : ℤ) (Φ : ℝ) : ℝ :=
  hbar ^ 2 / (2 * M * R ^ 2) * ((m : ℝ) - q * Φ / h) ^ 2

/-- 磁束を h/q だけ増やすと、準位 m は準位 m − 1 に移る。 -/
theorem ringEnergy_shift (hbar M R q h : ℝ) (hq : q ≠ 0) (hh : h ≠ 0) (m : ℤ) (Φ : ℝ) :
    ringEnergy hbar M R q h m (Φ + h / q) = ringEnergy hbar M R q h (m - 1) Φ := by
  have hqinv : q * q⁻¹ = 1 := mul_inv_cancel₀ hq
  have hhinv : h * h⁻¹ = 1 := mul_inv_cancel₀ hh
  have e : q * (Φ + h / q) / h = q * Φ / h + 1 := by
    linear_combination (h * h⁻¹) * hqinv + hhinv
  unfold ringEnergy
  rw [e, Int.cast_sub, Int.cast_one]
  ring

/-- §6：エネルギー準位の集合 {E_m(Φ) | m ∈ ℤ} は、磁束 Φ について周期 h/q をもつ。 -/
theorem energy_levels_periodic (hbar M R q h : ℝ) (hq : q ≠ 0) (hh : h ≠ 0) (Φ : ℝ) :
    Set.range (fun m : ℤ => ringEnergy hbar M R q h m (Φ + h / q)) =
      Set.range (fun m : ℤ => ringEnergy hbar M R q h m Φ) := by
  ext E
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m - 1, (ringEnergy_shift hbar M R q h hq hh m Φ).symm⟩
  · rintro ⟨m, rfl⟩
    refine ⟨m + 1, ?_⟩
    show ringEnergy hbar M R q h (m + 1) (Φ + h / q) = ringEnergy hbar M R q h m Φ
    rw [ringEnergy_shift hbar M R q h hq hh, add_sub_cancel_right]

end MathGarden.CylindricalShellToAharonovBohm

end
