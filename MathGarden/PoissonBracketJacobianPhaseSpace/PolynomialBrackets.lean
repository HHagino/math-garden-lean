import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring

/-!
# 記事 `poisson-bracket-jacobian-phase-space` §1〜§9：ポアソン括弧（多項式の物理量で）

記事の文（記事から写す）：

> $$[F, G]= \frac{\partial F}{\partial q} \frac{\partial G}{\partial p} - \frac{\partial G}{\partial q} \frac{\partial F}{\partial p}
> = \begin{vmatrix} F_q & F_p \\ G_q & G_p \end{vmatrix}= \frac{\partial(F, G)}{\partial(q, p)}.$$（§1）

> $F=q,G=p$ を入れると $\{q,p\}=q_qp_p-q_pp_q=1$、同様に $\{p,q\}=-1,\ \{q,q\}=\{p,p\}=0$。（§5–6）

> $F=q$ で $\dot q=\{q,H\}=\partial H/\partial p$、$F=p$ で $\dot p=\{p,H\}=-\partial H/\partial q$
> ── ハミルトン方程式が再現される。（§7）

> $\{q^3,p^3\}=9q^2p^2$ から $q^2p^2$ を量子化した結果と、$\{q^2p,qp^2\}=3q^2p^2$ から量子化した結果が
> $\hbar^2$ の項だけ食い違う。（§9）

参照する宣言（Mathlib v4.30.0 のタグのソースで名前と型を確かめた）：

* `MvPolynomial.pderiv`（偏微分。`Derivation`）・`pderiv_X_self`・`pderiv_X_of_ne`
  （`Mathlib/Algebra/MvPolynomial/PDeriv.lean`）。積とべきの偏微分は simp（Mathlib の simp 補題）で計算した。
* `Matrix.det_fin_two_of`（`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`）。

物理量 F, G は q, p の実係数多項式に限った（記事は滑らかな関数）。q は変数 0、p は変数 1。定理はすべて L1。
-/

noncomputable section

namespace MathGarden.PoissonBracketJacobianPhaseSpace

open MvPolynomial

/-- 位置 q（変数 0）。 -/
abbrev coordQ : MvPolynomial (Fin 2) ℝ := X 0

/-- 運動量 p（変数 1）。 -/
abbrev coordP : MvPolynomial (Fin 2) ℝ := X 1

/-- ポアソン括弧 {F, G} ＝ F_q G_p − F_p G_q。 -/
def bracket (F G : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 2) ℝ :=
  pderiv 0 F * pderiv 1 G - pderiv 1 F * pderiv 0 G

/-- §1：{F, G} は行列式 |F_q F_p; G_q G_p|（写像 (q, p) ↦ (F, G) のヤコビ行列式）。 -/
theorem bracket_eq_det (F G : MvPolynomial (Fin 2) ℝ) :
    bracket F G = Matrix.det !![pderiv 0 F, pderiv 1 F; pderiv 0 G, pderiv 1 G] := by
  rw [Matrix.det_fin_two_of, bracket]

/-- §5–6：{q, p} ＝ 1、{p, q} ＝ −1、{q, q} ＝ {p, p} ＝ 0。 -/
theorem canonical_brackets :
    bracket coordQ coordP = 1 ∧ bracket coordP coordQ = -1 ∧
    bracket coordQ coordQ = 0 ∧ bracket coordP coordP = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [bracket, coordQ, coordP]

/-- §7：{q, H} ＝ ∂H/∂p、{p, H} ＝ −∂H/∂q（ハミルトン方程式の右辺）。 -/
theorem hamilton_equations (H : MvPolynomial (Fin 2) ℝ) :
    bracket coordQ H = pderiv 1 H ∧ bracket coordP H = -pderiv 0 H := by
  constructor <;> simp [bracket, coordQ, coordP]

/-- §9：{q³, p³} ＝ 9q²p²、{q²p, qp²} ＝ 3q²p²。 -/
theorem cubic_brackets :
    bracket (coordQ ^ 3) (coordP ^ 3) = 9 * coordQ ^ 2 * coordP ^ 2 ∧
    bracket (coordQ ^ 2 * coordP) (coordQ * coordP ^ 2) = 3 * coordQ ^ 2 * coordP ^ 2 := by
  constructor <;>
    simp [bracket, coordQ, coordP] <;>
    ring

end MathGarden.PoissonBracketJacobianPhaseSpace

end
