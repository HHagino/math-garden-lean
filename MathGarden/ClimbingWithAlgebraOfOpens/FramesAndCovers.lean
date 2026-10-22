import Mathlib.Topology.Order.Category.FrameAdjunction
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.Set.Countable

/-!
# 記事 `開集合の代数で登る_Rdiscと Zariski étale_2026-06-02` §2：フレーム・点は下流・可算生成は商に遺伝

記事の文（記事から写す）：

> 位相空間 $X$ から、その**開集合全体のなす束** $\mathcal O(X)$ を取り出す。… こういう束を**フレーム**と呼び、
> フレームを「空間そのもの」とみなして扱う対象を **locale**(ロケール、点なし位相)という。
> 驚くのは、**点をフレームから復元できる**ことだ。点とは、フレーム $\mathcal O(X)$ から二元フレーム $\{0,1\}$ への準同型 … に対応する。

> 部分空間は、locale の言葉では**商フレーム**(sublocale、フレームの全射準同型 $\mathcal O(X)\twoheadrightarrow M$)に対応する。
> フレームの全射は join を保つので、**可算生成性は商に遺伝する**:$S$ が $\mathcal O(X)$ を join 生成すれば、その像が商を join 生成する。
> 一方、$\mathbb R_{\mathrm{disc}}$ のフレームは冪集合 $\mathcal P(\mathbb R)$ で、各一点集合 $\{x\}$ は … (原子)。
> 原子は生成系に必ず**自分自身が入っていなければならない**から、非可算個の原子をもつ $\mathcal P(\mathbb R)$ は可算生成ではない。

参照する宣言（Mathlib v4.30.0 のタグのソースで名前と型を確かめた）：

* `topToLocale`（`Mathlib/Topology/Category/Locale.lean`）：位相空間に開集合のフレームを対応させる関手 TopCat ⥤ Locale。
* `Locale.PT`・`Locale.pt`・`Locale.adjunctionTopToLocalePT`（`Mathlib/Topology/Order/Category/FrameAdjunction.lean`）：
  locale L の点＝フレーム準同型 L → Prop（Prop が二元フレーム）、点の空間をとる関手 pt、随伴 topToLocale ⊣ pt。
* `map_sSup`（フレーム準同型は任意の join を保つ）・`Set.Countable.image`・`Set.Countable.preimage`・
  `Set.singleton_injective`・`Cardinal.not_countable_real`。

`countably_generated_of_surjective`・`powerset_real_not_countably_generated`（L1）は §2 の発展の 2 文を証明したもの。
記事自身が「family resemblance であって、定理による同一視ではない」と書いている部分（§5・§6）は扱わない。
-/

universe u

namespace MathGarden.ClimbingWithAlgebraOfOpens

open CategoryTheory

/- §2：位相空間 → 開集合のフレーム（locale）の関手と、点の空間をとる関手との随伴。 -/
noncomputable example : topToLocale.{u} ⊣ Locale.pt.{u} :=
  Locale.adjunctionTopToLocalePT

/- §2：locale の点はフレーム準同型 L → Prop（二元フレーム）。 -/
example (L : Type*) [CompleteLattice L] : Locale.PT L = FrameHom L Prop := rfl

/-- フレーム α が S で join 生成される（どの元も S の部分集合の join）。 -/
def JoinGenerates {α : Type*} [CompleteLattice α] (S : Set α) : Prop :=
  ∀ a : α, ∃ T ⊆ S, a = sSup T

/-- §2：フレームの全射準同型で、S が join 生成するなら、その像が商を join 生成する。 -/
theorem joinGenerates_image {α β : Type*} [Order.Frame α] [Order.Frame β] (f : FrameHom α β)
    (hf : Function.Surjective f) {S : Set α} (hS : JoinGenerates S) : JoinGenerates (f '' S) := by
  intro b
  obtain ⟨a, rfl⟩ := hf b
  obtain ⟨T, hTS, rfl⟩ := hS a
  exact ⟨f '' T, Set.image_mono hTS, map_sSup f T⟩

/-- §2：可算生成性はフレームの全射（商）に遺伝する。 -/
theorem countably_generated_of_surjective {α β : Type*} [Order.Frame α] [Order.Frame β] (f : FrameHom α β)
    (hf : Function.Surjective f) (h : ∃ S : Set α, S.Countable ∧ JoinGenerates S) :
    ∃ S : Set β, S.Countable ∧ JoinGenerates S := by
  obtain ⟨S, hSc, hS⟩ := h
  exact ⟨f '' S, hSc.image f, joinGenerates_image f hf hS⟩

/-- §2：ℝ の冪集合のフレーム 𝒫(ℝ)（ℝ_disc の開集合）は可算生成ではない。 -/
theorem powerset_real_not_countably_generated :
    ¬ ∃ S : Set (Set ℝ), S.Countable ∧ JoinGenerates S := by
  rintro ⟨S, hSc, hS⟩
  -- 一点集合はすべて S に入る（原子は生成系に自分自身が入る）。
  have hsing : ∀ x : ℝ, ({x} : Set ℝ) ∈ S := by
    intro x
    obtain ⟨T, hTS, hT⟩ := hS {x}
    have hx : x ∈ sSup T := by
      rw [← hT]
      exact Set.mem_singleton x
    rw [Set.sSup_eq_sUnion] at hx
    obtain ⟨t, htT, hxt⟩ := Set.mem_sUnion.mp hx
    have hle : t ⊆ {x} := by
      rw [hT]
      exact le_sSup htT
    have ht : t = {x} := Set.Subset.antisymm hle (Set.singleton_subset_iff.mpr hxt)
    rw [← ht]
    exact hTS htT
  have hpre : (fun x : ℝ => ({x} : Set ℝ)) ⁻¹' S = Set.univ :=
    Set.eq_univ_of_forall hsing
  have hcount : (Set.univ : Set ℝ).Countable := by
    rw [← hpre]
    exact hSc.preimage Set.singleton_injective
  exact Cardinal.not_countable_real hcount

end MathGarden.ClimbingWithAlgebraOfOpens
