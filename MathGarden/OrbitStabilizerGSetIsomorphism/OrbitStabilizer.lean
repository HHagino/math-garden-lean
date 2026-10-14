import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# 記事 `軌道固定群はG集合版の準同型定理_2026-06-02`：軌道・固定群の同型と原始的作用（L0）

記事の文（記事から写す）：

> 群 $G$ が集合 $\Omega$ に作用していて、点 $x$ の軌道を $\mathrm{Orb}(x)$、固定群を $G_x$ とすると、
> $\mathrm{Orb}(x)\cong G/G_x$ が成り立つ。有限群なら $|\mathrm{Orb}(x)|=[G:G_x]$ という数え上げ公式として使うことが多い。

L0 ＝ Mathlib にある宣言を参照し、その型が下の主張と一致することを Lean に確かめさせる
（このリポジトリで新しく証明したものはない）。参照する宣言（`Mathlib/GroupTheory/GroupAction/` の下）：

* `MulAction.orbitEquivQuotientStabilizer`（`Quotient.lean`）：軌道と剰余類の集合の全単射。
* `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`（`Quotient.lean`）：軌道の元の数 × 固定群の位数 ＝ 群の位数。
* `MulAction.isCoatom_stabilizer_iff_preprimitive`（`Primitive.lean`）：原始的 ⇔ 点固定群が極大。
* `MulAction.isPreprimitive_of_is_two_pretransitive`（`MultipleTransitivity.lean`）：2重推移なら原始的。
-/

namespace MathGarden.OrbitStabilizerGSetIsomorphism

open MulAction

/- 軌道と剰余類の集合の全単射（集合としての同値）。 -/
example {G X : Type*} [Group G] [MulAction G X] (x : X) :
    Nonempty (orbit G x ≃ G ⧸ stabilizer G x) :=
  ⟨orbitEquivQuotientStabilizer G x⟩

/- 数え上げ公式。 -/
example {G X : Type*} [Group G] [MulAction G X] (x : X) [Fintype G] [Fintype (orbit G x)]
    [Fintype (stabilizer G x)] :
    Fintype.card (orbit G x) * Fintype.card (stabilizer G x) = Fintype.card G :=
  card_orbit_mul_card_stabilizer_eq_card_group G x

/- 推移的で `X` が2点以上なら、点固定群が極大 ⇔ 作用が原始的。 -/
example {G X : Type*} [Group G] [MulAction G X] [IsPretransitive G X] [Nontrivial X] (x : X) :
    IsCoatom (stabilizer G x) ↔ IsPreprimitive G X :=
  isCoatom_stabilizer_iff_preprimitive G x

/- 2重推移なら原始的。 -/
example {G X : Type*} [Group G] [MulAction G X] (h2 : IsMultiplyPretransitive G X 2) :
    IsPreprimitive G X :=
  isPreprimitive_of_is_two_pretransitive h2

end MathGarden.OrbitStabilizerGSetIsomorphism
