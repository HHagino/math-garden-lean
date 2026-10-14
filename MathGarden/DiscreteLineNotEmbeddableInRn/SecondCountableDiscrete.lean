import Mathlib.Topology.Bases
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# 記事 `離散直線はRnに埋め込めない_2026-06-02`：離散直線 ℝ_disc は ℝⁿ に埋め込めない（L1）

記事「濃度では入るのに、位相が拒む ── 離散直線 ℝ_disc は ℝⁿ に埋め込めない」の文（記事から写す）。

冒頭「主張と、その不思議さ」：

> 主張は、離散直線 $\mathbb R_{\mathrm{disc}}$ はどんな次元の $\mathbb R^n$ にも位相的には埋め込めない、
> というものだ。

§5「心臓部 ── 離散かつ第二可算なら、高々可算」：

> **離散空間が第二可算なら、その点集合は高々可算**である。

§10「一般化」：

> **命題.** 第二可算空間の任意の離散部分空間は、高々可算である。

ここで Lean が確かめること（記事の §4・§5・§6 の組み上げの順に）：

* `countable_of_discrete_of_secondCountable`（§5）：離散かつ第二可算な空間は高々可算。
  証明は記事の論法のまま：可算基底 $\mathcal B$ をとると、各点 $x$ の一点集合 $\{x\}$ は開なので
  $x \in B \subseteq \{x\}$ となる $B \in \mathcal B$ があり $B = \{x\}$。$x \mapsto \{x\}$ は
  $\mathcal B$ への単射。
* `countable_of_discrete_subspace`（§10 の命題）：第二可算空間の離散部分空間は高々可算。
  §4 の「第二可算は部分空間に遺伝する」は Mathlib の `TopologicalSpace.Subtype.secondCountableTopology`
  を使う。
* `countable_of_isEmbedding`（§6 の組み上げ）：離散空間から第二可算空間への位相的埋め込みがあれば、
  もとの空間は高々可算。
* `realDisc_not_isEmbedding`（冒頭の主張・§6 の結論）：`RealDisc`（`ℝ` に離散位相を入れたもの）から
  `EuclideanSpace ℝ (Fin n)`（標準位相の ℝⁿ）への位相的埋め込みは、どの `n` についても無い
  （`n = 0` も含む）。ℝ が非可算であることは Mathlib の `Uncountable ℝ`（`Cardinal.mk_real` から）を使う。

確かめていないこと：§1 の「濃度は障害にならない」（$|\mathbb R| = |\mathbb R^n|$ と単射の存在）、
§2 の「離散空間からの写像はすべて連続」、§7 の locale（フレーム）による言い直し、§8 の
$\mathbb Z_{\mathrm{disc}} \hookrightarrow \mathbb R$、§9 の境界の例（$\{0,1\}^{\mathbb R}$ が可分で
$\mathbb R_{\mathrm{disc}}$ を含むこと、補有限位相の例、距離空間で第二可算・可分・Lindelöf が同値なこと）、
「査読・限界」の別証明 (ii)。
-/

namespace MathGarden.DiscreteLineNotEmbeddableInRn

open Topology TopologicalSpace

/-- 記事 §5：離散かつ第二可算な空間は高々可算。

各点 `x` について、一点集合 `{x}` は開（離散）なので、可算基底 `B` の元 `b` で `x ∈ b ⊆ {x}`、
つまり `b = {x}` となるものがある。その `b` を `g x` とすると、`x ↦ g x` は `B` への単射。 -/
theorem countable_of_discrete_of_secondCountable (D : Type*) [TopologicalSpace D]
    [SecondCountableTopology D] [DiscreteTopology D] : Countable D := by
  obtain ⟨B, hBc, -, hB⟩ := exists_countable_basis D
  have key : ∀ x : D, ∃ b ∈ B, b = {x} := by
    intro x
    obtain ⟨b, hbB, hxb, hbx⟩ :=
      hB.exists_subset_of_mem_open (Set.mem_singleton x) (isOpen_discrete {x})
    exact ⟨b, hbB, Set.Subset.antisymm hbx (Set.singleton_subset_iff.mpr hxb)⟩
  choose g hgB hg using key
  haveI : Countable B := hBc.to_subtype
  have hinj : Function.Injective (fun x : D => (⟨g x, hgB x⟩ : B)) := by
    intro x y hxy
    have h : g x = g y := congrArg Subtype.val hxy
    rw [hg x, hg y] at h
    exact Set.singleton_injective h
  exact hinj.countable

/-- 記事 §10 の命題：第二可算空間の任意の離散部分空間は、高々可算である。 -/
theorem countable_of_discrete_subspace {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] (D : Set X) [DiscreteTopology D] : D.Countable :=
  Set.countable_coe_iff.mp (countable_of_discrete_of_secondCountable D)

/-- 記事 §6 の組み上げ：離散空間 `X` から第二可算空間 `Y` への位相的埋め込み `f` があれば、
`X` は高々可算（`X` の位相は `f` で引き戻した位相なので第二可算、あとは §5）。 -/
theorem countable_of_isEmbedding {X Y : Type*} [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace Y] [SecondCountableTopology Y] {f : X → Y} (hf : IsEmbedding f) :
    Countable X := by
  haveI : SecondCountableTopology X := by
    have h := secondCountableTopology_induced X Y f
    rw [← hf.eq_induced] at h
    exact h
  exact countable_of_discrete_of_secondCountable X

/-- 記事の $\mathbb R_{\mathrm{disc}}$：実数全体に離散位相（位相の束の最小元 `⊥`）を入れた空間。 -/
def RealDisc : Type := ℝ

instance : TopologicalSpace RealDisc := ⊥

instance : DiscreteTopology RealDisc := ⟨rfl⟩

instance : Uncountable RealDisc := inferInstanceAs (Uncountable ℝ)

/-- 記事の主張：離散直線 $\mathbb R_{\mathrm{disc}}$ は、どんな次元の $\mathbb R^n$ にも位相的に
埋め込めない。 -/
theorem realDisc_not_isEmbedding (n : ℕ) (f : RealDisc → EuclideanSpace ℝ (Fin n)) :
    ¬ IsEmbedding f :=
  fun hf => not_countable (countable_of_isEmbedding hf)

end MathGarden.DiscreteLineNotEmbeddableInRn
