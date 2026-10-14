import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Algebra.Category.Ring.Instances
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Topology.Category.TopCat.EffectiveEpi

/-!
# 記事 `epic-surjection-cover-distinction`：epic と全射・商写像の判定（L0）

記事の文（記事から写す）：

> 集合の圏 $\mathbf{Set}$ では、射 $f: X \to Y$ が **epic**(エピ射)であることと、$f$ が**全射**であることは一致する。

> 可換環 $A$ と乗法的集合 $S$ に対し、局所化の射 $A \to S^{-1}A$ はつねに $\mathbf{CRing}$ で epic である。
> （§3 の見出し「例 1:$\mathbb{Z} \hookrightarrow \mathbb{Q}$ ── epic だが全射でない」）

L0 ＝ Mathlib にある宣言を参照し、その型が下の主張と一致することを Lean に確かめさせる
（このリポジトリで新しく証明したものはない）。参照する宣言：

* `CategoryTheory.epi_iff_surjective`（`Mathlib/CategoryTheory/Types/Basic.lean`）：集合の圏で epic ⇔ 全射。
* `IsLocalization.epi`（`Mathlib/Algebra/Category/Ring/Instances.lean`）：局所化の射は可換環の圏で epic。
  下では `ℤ → ℚ`（`ℚ` は `ℤ` の非零因子による局所化）に当てた。
* `TopCat.epi_iff_surjective`（`Mathlib/Topology/Category/TopCat/EpiMono.lean`）：位相空間の圏で epic ⇔ 全射。
* `TopCat.effectiveEpi_iff_isQuotientMap`（`Mathlib/Topology/Category/TopCat/EffectiveEpi.lean`）：
  位相空間の圏で effective epic ⇔ 商写像。
-/

namespace MathGarden.EpicSurjectionCoverDistinction

open CategoryTheory

universe u

/- 集合の圏で epic ⇔ 全射。 -/
example {X Y : Type u} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f :=
  CategoryTheory.epi_iff_surjective f

/- `ℤ → ℚ` は可換環の圏で epic（`ℚ` は `ℤ` の局所化）。 -/
example : Epi (CommRingCat.ofHom (algebraMap ℤ ℚ)) :=
  IsLocalization.epi (nonZeroDivisors ℤ) ℚ

/- 位相空間の圏で epic ⇔ 全射。 -/
example {X Y : TopCat.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f :=
  TopCat.epi_iff_surjective f

/- 位相空間の圏で effective epic ⇔ 商写像。 -/
example {B X : TopCat.{u}} (π : X ⟶ B) : EffectiveEpi π ↔ Topology.IsQuotientMap π :=
  TopCat.effectiveEpi_iff_isQuotientMap π

end MathGarden.EpicSurjectionCoverDistinction
