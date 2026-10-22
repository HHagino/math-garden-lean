import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Topology.Category.TopCat.EffectiveEpi
import Mathlib.Topology.Order

/-!
# 記事 `epic-surjection-cover-distinction`：離散 ℕ → 密着 ℕ の恒等写像（L1）

記事「epic・全射・cover はなぜ一致しないのか」§4「例 2:離散 $\mathbb{N}$ から密着 $\mathbb{N}$ への恒等写像
── 全射 epic だが cover でない」の文（記事から写す）：

> **$f$ は連続である。** … **$f$ は monic である。** … **$f$ は epic である。** …
> **$f$ は同相写像(iso)ではない。** 逆向きの台恒等写像 … は連続ではない。

> もっと本質的なのは、$f$ が全射連続写像であるにもかかわらず、**商写像(quotient map)ではない**ことだ。

> $\mathbf{Top}$ で cover を商写像(この圏の effective epi に当たる)と読めば、全射 epic であっても
> cover とは限らない ── この例がそれを示している。

Lean では台集合 `ℕ` の型の別名を二つ作り、`DiscNat` に離散位相 `⊥`、`IndiscNat` に密着位相 `⊤` を載せる
（Mathlib の位相の順序では `⊥` が最も細かい＝離散、`⊤` が最も粗い＝密着）。台の上で恒等の連続写像
`toIndisc` を作り、位相空間の圏 `TopCat` の射 `idDiscToIndisc` にして、次を確かめる：

* 全射・単射、したがって `TopCat` で epic（`TopCat.epi_iff_surjective`）かつ monic（`TopCat.mono_iff_injective`）。
* 逆向きの台恒等写像は連続でない（一点集合 `{0}` が密着位相で開でない）。
* `TopCat` で同型でない（`TopCat.isIso_iff_isHomeomorph` で同相に言い換え、開写像でないことから）。
* 商写像でない。したがって `TopCat` で effective epi でない（`TopCat.effectiveEpi_iff_isQuotientMap`）。

確かめていないこと：記事 §5 以降の「cover ≈ 降下の一意性＋存在」の読み・図の包含関係、
`TopCat` が balanced でないという一般の主張（ここではこの一例だけ）。
-/

namespace MathGarden.EpicSurjectionCoverDistinction

open CategoryTheory Topology

/-- 台集合 `ℕ` に離散位相（すべての部分集合が開）を載せたもの。 -/
def DiscNat : Type := ℕ

instance : TopologicalSpace DiscNat := ⊥

instance : DiscreteTopology DiscNat := ⟨rfl⟩

/-- 台集合 `ℕ` に密着位相（開集合は空集合と全体だけ）を載せたもの。 -/
def IndiscNat : Type := ℕ

instance : TopologicalSpace IndiscNat := ⊤

/-- 密着位相の開集合は空集合と全体だけ。 -/
theorem indisc_isOpen_iff (U : Set IndiscNat) : IsOpen U ↔ U = ∅ ∨ U = Set.univ :=
  TopologicalSpace.isOpen_top_iff U

/-- 離散 ℕ の点 0。 -/
def zD : DiscNat := (0 : ℕ)

/-- 密着 ℕ の点 0。 -/
def zI : IndiscNat := (0 : ℕ)

/-- 密着 ℕ の点 1。 -/
def oneI : IndiscNat := (1 : ℕ)

/-- 一点集合 `{0}` は密着位相で開でない。 -/
theorem singleton_zero_not_open : ¬ IsOpen ({zI} : Set IndiscNat) := by
  rw [indisc_isOpen_iff]
  rintro (h | h)
  · exact Set.singleton_ne_empty _ h
  · have h1 : oneI ∈ ({zI} : Set IndiscNat) := h ▸ Set.mem_univ oneI
    exact Nat.one_ne_zero (Set.mem_singleton_iff.mp h1)

/-- 台の上で恒等の連続写像 離散 ℕ → 密着 ℕ（定義域が離散なので連続）。 -/
def toIndisc : C(DiscNat, IndiscNat) := ⟨fun n => n, continuous_of_discreteTopology⟩

/-- 位相空間の圏 `TopCat` の射としての `toIndisc`。 -/
abbrev idDiscToIndisc : TopCat.of DiscNat ⟶ TopCat.of IndiscNat := TopCat.ofHom toIndisc

/-- 逆向きの台恒等写像 密着 ℕ → 離散 ℕ。 -/
def fromIndisc : IndiscNat → DiscNat := fun n => n

/-- 逆向きの台恒等写像は連続でない（離散側で開な `{0}` の逆像 `{0}` が密着位相で開でない）。 -/
theorem inverse_not_continuous : ¬ Continuous fromIndisc := by
  intro h
  have h1 := h.isOpen_preimage ({zD} : Set DiscNat) (isOpen_discrete _)
  have e : fromIndisc ⁻¹' ({zD} : Set DiscNat) = ({zI} : Set IndiscNat) :=
    Set.ext fun _ => Iff.rfl
  rw [e] at h1
  exact singleton_zero_not_open h1

/-- `toIndisc` は開写像でない（`{0}` は離散位相で開だが、像 `{0}` は密着位相で開でない）。 -/
theorem toIndisc_not_isOpenMap : ¬ IsOpenMap toIndisc := by
  intro h
  have h1 := h ({zD} : Set DiscNat) (isOpen_discrete _)
  have e : ⇑toIndisc '' ({zD} : Set DiscNat) = ({zI} : Set IndiscNat) := Set.image_singleton
  rw [e] at h1
  exact singleton_zero_not_open h1

/-- `toIndisc` は商写像でない（単射な商写像は開写像になるため）。 -/
theorem toIndisc_not_isQuotientMap : ¬ IsQuotientMap toIndisc := fun h =>
  toIndisc_not_isOpenMap (h.isCoinducing.isOpenMap_of_injective (fun _ _ hab => hab))

theorem idDiscToIndisc_surjective : Function.Surjective idDiscToIndisc := fun y => ⟨y, rfl⟩

theorem idDiscToIndisc_injective : Function.Injective idDiscToIndisc := fun _ _ hab => hab

/-- `TopCat` で epic（全射だから）。 -/
theorem idDiscToIndisc_epi : Epi idDiscToIndisc :=
  (TopCat.epi_iff_surjective _).mpr idDiscToIndisc_surjective

/-- `TopCat` で monic（単射だから）。 -/
theorem idDiscToIndisc_mono : Mono idDiscToIndisc :=
  (TopCat.mono_iff_injective _).mpr idDiscToIndisc_injective

/-- `TopCat` で同型でない。 -/
theorem idDiscToIndisc_not_isIso : ¬ IsIso idDiscToIndisc := by
  rw [TopCat.isIso_iff_isHomeomorph]
  intro h
  exact toIndisc_not_isOpenMap h.isOpenMap

/-- `TopCat` で effective epi でない（商写像でないから）。 -/
theorem idDiscToIndisc_not_effectiveEpi : ¬ EffectiveEpi idDiscToIndisc := by
  rw [TopCat.effectiveEpi_iff_isQuotientMap]
  exact toIndisc_not_isQuotientMap

/-- 記事 §4 の例 2 のまとめ：離散 ℕ → 密着 ℕ の恒等写像は、`TopCat` で epic かつ monic だが、
同型でなく、effective epi（＝商写像）でもない。 -/
theorem discrete_to_indiscrete_summary :
    Epi idDiscToIndisc ∧ Mono idDiscToIndisc ∧ ¬ IsIso idDiscToIndisc ∧
      ¬ EffectiveEpi idDiscToIndisc :=
  ⟨idDiscToIndisc_epi, idDiscToIndisc_mono, idDiscToIndisc_not_isIso,
    idDiscToIndisc_not_effectiveEpi⟩

end MathGarden.EpicSurjectionCoverDistinction
