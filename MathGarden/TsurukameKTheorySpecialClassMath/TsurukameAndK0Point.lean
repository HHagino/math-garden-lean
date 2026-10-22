import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# 記事 `tsurukame-k-theory-special-class-math` §2・§4：鶴亀算の連立方程式と K⁰(pt) ≅ ℤ

記事の文（記事から写す）：

> 鶴亀算は、形式的には次の連立方程式を解く問題である: $x + y = n, \qquad 2x + 4y = m.$
> ここで $x$ は鶴の頭数、$y$ は亀の頭数。…
> **差分:** 鶴を亀に置き換えると脚数が 2 本増える。（§2）

> $X$ を一点空間 $\mathrm{pt}$ に取ると、一点上のベクトル束はただの有限次元複素ベクトル空間にほかならない。
> 同型類は次元 $\dim V \in \mathbb{N}$ で決まり、Grothendieck 群化すれば $K^0(\mathrm{pt}) \cong \mathbb{Z}.$（§4）

参照する宣言（Mathlib v4.30.0 のタグのソースで名前と型を確かめた）：

* `Algebra.GrothendieckAddGroup`・`Algebra.GrothendieckAddGroup.of`・`Algebra.GrothendieckAddGroup.lift`
  （`(M →+ G) ≃ (GrothendieckAddGroup M →+ G)`）・`Algebra.GrothendieckAddGroup.lift_symm_apply`
  （`lift.symm f = f.comp of`）（`Mathlib/GroupTheory/MonoidLocalization/GrothendieckGroup.lean`。
  乗法の版に `to_additive` で作られた加法の版）。
* `Nat.castAddMonoidHom`（`Mathlib/Data/Nat/Cast/Basic.lean`）・`AddMonoidHom.ext_nat`
  （`Mathlib/Algebra/Group/Nat/Hom.lean`）・`AddMonoidHom.ext_int`（`Mathlib/Data/Int/Cast/Lemmas.lean`）・
  `AddMonoidHom.toAddEquiv`（`MonoidHom.toMulEquiv` の加法の版、`Mathlib/Algebra/Group/Equiv/Defs.lean`）。

Mathlib には Grothendieck 群の定義と普遍性はあるが、「ℕ の Grothendieck 群 ≅ ℤ」の宣言は見つからなかった
（2026-10-14 の下調べ）。このファイルで普遍性から同型を作った（L1）。
-/

noncomputable section

namespace MathGarden.TsurukameKTheorySpecialClassMath

open Algebra

/-- §2：鶴 x・亀 y で頭が n・脚が m（x + y = n かつ 2x + 4y = m）であることと、
x = (4n − m)/2・y = (m − 2n)/2 であることは同値（有理数の範囲で解がただ一つ）。 -/
theorem tsurukame_solution (x y n m : ℚ) :
    (x + y = n ∧ 2 * x + 4 * y = m) ↔ (x = (4 * n - m) / 2 ∧ y = (m - 2 * n) / 2) := by
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    constructor <;> ring

/-- §2：鶴を一羽、亀に置き換えると脚の数は 2 本増える。 -/
theorem crane_to_turtle (x y : ℤ) : 2 * (x - 1) + 4 * (y + 1) = (2 * x + 4 * y) + 2 := by
  ring

/-- (ℕ, +) の Grothendieck 群から ℤ への準同型（自然数 n を整数 n と見る写像を普遍性で持ち上げたもの）。 -/
def toInt : GrothendieckAddGroup ℕ →+ ℤ :=
  GrothendieckAddGroup.lift (Nat.castAddMonoidHom ℤ)

theorem toInt_of (n : ℕ) : toInt (GrothendieckAddGroup.of n) = n := by
  have h := GrothendieckAddGroup.lift.symm_apply_apply (Nat.castAddMonoidHom ℤ)
  rw [GrothendieckAddGroup.lift_symm_apply] at h
  exact DFunLike.congr_fun h n

/-- ℤ から (ℕ, +) の Grothendieck 群への準同型 k ↦ k • [1]。 -/
def ofInt : ℤ →+ GrothendieckAddGroup ℕ where
  toFun k := k • GrothendieckAddGroup.of (1 : ℕ)
  map_zero' := zero_zsmul _
  map_add' a b := add_zsmul _ a b

theorem ofInt_comp_toInt : ofInt.comp toInt = AddMonoidHom.id (GrothendieckAddGroup ℕ) := by
  apply GrothendieckAddGroup.lift.symm.injective
  simp only [GrothendieckAddGroup.lift_symm_apply]
  apply AddMonoidHom.ext_nat
  show ofInt (toInt (GrothendieckAddGroup.of (1 : ℕ))) = GrothendieckAddGroup.of (1 : ℕ)
  rw [toInt_of]
  show ((1 : ℕ) : ℤ) • GrothendieckAddGroup.of (1 : ℕ) = GrothendieckAddGroup.of (1 : ℕ)
  rw [Nat.cast_one, one_zsmul]

theorem toInt_comp_ofInt : toInt.comp ofInt = AddMonoidHom.id ℤ := by
  apply AddMonoidHom.ext_int
  show toInt ((1 : ℤ) • GrothendieckAddGroup.of (1 : ℕ)) = 1
  rw [one_zsmul, toInt_of, Nat.cast_one]

/-- (ℕ, +) の Grothendieck 群と ℤ の同型。 -/
def grothendieckNatEquivInt : GrothendieckAddGroup ℕ ≃+ ℤ :=
  AddMonoidHom.toAddEquiv toInt ofInt ofInt_comp_toInt toInt_comp_ofInt

/-- §4：K⁰(pt)、すなわち次元のなす可換モノイド (ℕ, +) の Grothendieck 群は ℤ と同型で、
同型は [n] ↦ n で与えられる。 -/
theorem k0_point_equiv_int :
    ∃ e : GrothendieckAddGroup ℕ ≃+ ℤ, ∀ n : ℕ, e (GrothendieckAddGroup.of n) = n :=
  ⟨grothendieckNatEquivInt, toInt_of⟩

end MathGarden.TsurukameKTheorySpecialClassMath

end
