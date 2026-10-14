import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Heyting.Basic
import Mathlib.Data.Set.Lattice.Image

/-!
# 記事 `de-morgan-as-categorical-complement-duality`：補集合と ⋃・⋂、像 ⊣ 逆像 ⊣ ∀像、Heyting での片側（L0）

記事の文（記事から写す）：

> $X\setminus\bigcup_i U_i=\bigcap_i(X\setminus U_i)$（§5）

> $f_!\dashv f^{-1}\dashv\forall_f$ ($f_!=\exists,\ f^{-1}=$代入$,\ \forall_f=\forall$)（§6）

> ド・モルガンの片方 $\neg(U\cup V)=\neg U\cap\neg V$ は任意の Heyting 代数で …（§7）

L0 ＝ Mathlib にある宣言を参照し、その型が下の主張と一致することを Lean に確かめさせる
（このリポジトリで新しく証明したものはない）。参照する宣言：

* `compl_iSup`（`Mathlib/Order/CompleteBooleanAlgebra.lean`）、`Set.compl_iUnion`
* `Set.image_preimage`・`Set.preimage_kernImage`（`Mathlib/Data/Set/Lattice/Image.lean`）。
  `Set.kernImage f s` は `∀` 側（`f x = y` となる `x` がすべて `s` に入るような `y` の集合）。
* `compl_sup`・`compl_sup_compl_le`（`Mathlib/Order/Heyting/Basic.lean`）
-/

namespace MathGarden.DeMorganAsCategoricalComplementDuality

/- 完備ブール代数での補集合は、上限と下限を交換する。 -/
example {α ι : Type*} [CompleteBooleanAlgebra α] (f : ι → α) : (⨆ i, f i)ᶜ = ⨅ i, (f i)ᶜ :=
  compl_iSup

/- 集合の和集合の補集合は、補集合の共通部分。 -/
example {α ι : Type*} (U : ι → Set α) : (⋃ i, U i)ᶜ = ⋂ i, (U i)ᶜ := by
  rw [Set.compl_iUnion]

/- 像 ⊣ 逆像。 -/
example {X Y : Type*} (f : X → Y) : GaloisConnection (Set.image f) (Set.preimage f) :=
  Set.image_preimage

/- 逆像 ⊣ `∀` 像（`kernImage`）。 -/
example {X Y : Type*} (f : X → Y) : GaloisConnection (Set.preimage f) (Set.kernImage f) :=
  Set.preimage_kernImage

/- Heyting 代数でも成り立つ側：`¬(a ∨ b) = ¬a ∧ ¬b`。 -/
example {α : Type*} [HeytingAlgebra α] (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ := compl_sup

/- Heyting 代数で一般には不等号だけの側：`¬a ∨ ¬b ≤ ¬(a ∧ b)`。 -/
example {α : Type*} [HeytingAlgebra α] (a b : α) : aᶜ ⊔ bᶜ ≤ (a ⊓ b)ᶜ := compl_sup_compl_le

end MathGarden.DeMorganAsCategoricalComplementDuality
