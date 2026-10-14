import Mathlib.InformationTheory.Hamming
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# 記事 `nielsen-taxonomy-distances-divergences-map`：Hamming 距離は三角不等式を満たす・KL は 0 ⇔ 一致（L0）

記事の文（記事から写す）：

> 三角不等式:$d(x, z) \leq d(x, y) + d(y, z)$。（距離の条件の一つ）

> 一方、KL divergence のような **divergence** は、… 三角不等式を満たさない、…

L0 ＝ Mathlib にある宣言を参照し、その型が下の主張と一致することを Lean に確かめさせる
（このリポジトリで新しく証明したものはない）。参照する宣言：

* `hammingDist_triangle`（`Mathlib/InformationTheory/Hamming.lean`）：Hamming 距離の三角不等式。
* `InformationTheory.klDiv_eq_zero_iff`（`Mathlib/InformationTheory/KullbackLeibler/Basic.lean`）：
  有限測度の KL ダイバージェンスが 0 ⇔ 二つの測度が等しい。

KL が非対称であること・三角不等式を満たさないことを述べる宣言は、ここでは参照していない。
-/

namespace MathGarden.NielsenTaxonomyDistancesDivergencesMap

open MeasureTheory

/- Hamming 距離の三角不等式。 -/
example {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, DecidableEq (β i)] (x y z : ∀ i, β i) :
    hammingDist x z ≤ hammingDist x y + hammingDist y z :=
  hammingDist_triangle x y z

/- 有限測度の KL ダイバージェンスが 0 ⇔ 測度が等しい。 -/
example {α : Type*} [MeasurableSpace α] {μ ν : Measure α} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : InformationTheory.klDiv μ ν = 0 ↔ μ = ν :=
  InformationTheory.klDiv_eq_zero_iff

end MathGarden.NielsenTaxonomyDistancesDivergencesMap
