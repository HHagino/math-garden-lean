import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# 記事 `noether-theorem-finite-to-infinitesimal` §6：自由粒子で g ＝ 0 と g ≠ 0 を見る

記事の文（記事から写す）：

> 自由粒子 $L=\tfrac12 m\dot q^2$ で、二つの対称性を実際に回す。
> **(a) 空間並進(g=0).** $q_s=q+s$、$\delta q=1$。… 保存量は $Q=\frac{\partial L}{\partial\dot q}\cdot1-0=m\dot q$(運動量)。

> **(b) ガリレイ・ブースト(g≠0).** $q_s=q+s\,t$、$\delta q=t$。$\dot q_s=\dot q+s$ なので
> $$L_s=\tfrac12 m(\dot q+s)^2=\tfrac12 m\dot q^2+m\dot q\,s+\tfrac12 m s^2,\qquad
> \delta L=\left.\frac{dL_s}{ds}\right|_0=m\dot q.$$
> … $g=mq$ と取れて $\delta L=dg/dt$ が成り立つ … 保存量は $Q=\frac{\partial L}{\partial\dot q}\,\delta q-g=m\dot q\cdot t-mq=m(\dot q\,t-q).$
> 検算:$\dot Q=m(\ddot q\,t+\dot q-\dot q)=m\ddot q\,t=0$(自由粒子 $\ddot q=0$)。保存する。…
> **もし $g$ を落としていたら $m\dot q\,t$ だけが残り、保存しない。**

参照する宣言（Mathlib v4.30.0 のタグのソースで名前と型を確かめた）：

* `hasDerivAt_id'`・`HasDerivAt.congr_deriv`（`Mathlib/Analysis/Calculus/Deriv/Basic.lean`）・`HasDerivAt.const_add`・
  `HasDerivAt.sub`（`Mathlib/Analysis/Calculus/Deriv/Add.lean`）・`HasDerivAt.mul`・`HasDerivAt.const_mul`
  （`Mathlib/Analysis/Calculus/Deriv/Mul.lean`）・`HasDerivAt.pow`（`Mathlib/Analysis/Calculus/Deriv/Pow.lean`）。

軌道は q : ℝ → ℝ、速度は v : ℝ → ℝ で「q の微分が v」（HasDerivAt q (v t) t）、自由粒子の運動方程式 q̈ ＝ 0 は
「v の微分が 0」と書いた。定理はすべて L1。
-/

namespace MathGarden.NoetherTheoremFiniteToInfinitesimal

/-- §6(b)：L_s ＝ ½m(q̇+s)² ＝ ½mq̇² + mq̇ s + ½ms²、そして δL ＝ dL_s/ds|₀ ＝ mq̇。 -/
theorem boost_lagrangian_variation (m qdot : ℝ) :
    (∀ s : ℝ, 1 / 2 * m * (qdot + s) ^ 2 = 1 / 2 * m * qdot ^ 2 + m * qdot * s + 1 / 2 * m * s ^ 2) ∧
    HasDerivAt (fun s : ℝ => 1 / 2 * m * (qdot + s) ^ 2) (m * qdot) 0 := by
  refine ⟨fun s => by ring, ?_⟩
  have h := (((hasDerivAt_id' (0 : ℝ)).const_add qdot).pow 2).const_mul (1 / 2 * m)
  exact h.congr_deriv (by norm_num <;> ring)

/-- §6(a)：並進の保存量 Q ＝ mq̇ は、自由粒子（q̈ ＝ 0）の運動で時間によらない（微分が 0）。 -/
theorem translation_momentum_conserved (m : ℝ) (v : ℝ → ℝ) (hv : ∀ t, HasDerivAt v 0 t) (t : ℝ) :
    HasDerivAt (fun t => m * v t) 0 t :=
  ((hv t).const_mul m).congr_deriv (by ring)

/-- §6(b)：ブーストの保存量 Q ＝ m(q̇ t − q) は自由粒子の運動で保存する（微分が 0）。
一方、境界項 g ＝ mq を落とした m q̇ t の微分は m q̇ で、m ≠ 0・q̇ ≠ 0 なら 0 でない（保存しない）。 -/
theorem boost_charge_conserved (m : ℝ) (q v : ℝ → ℝ)
    (hq : ∀ t, HasDerivAt q (v t) t) (hv : ∀ t, HasDerivAt v 0 t) (t : ℝ) :
    HasDerivAt (fun t => m * (v t * t - q t)) 0 t ∧
    HasDerivAt (fun t => m * (v t * t)) (m * v t) t := by
  constructor
  · have h := (((hv t).mul (hasDerivAt_id' t)).sub (hq t)).const_mul m
    exact h.congr_deriv (by ring)
  · have h := ((hv t).mul (hasDerivAt_id' t)).const_mul m
    exact h.congr_deriv (by ring)

end MathGarden.NoetherTheoremFiniteToInfinitesimal
