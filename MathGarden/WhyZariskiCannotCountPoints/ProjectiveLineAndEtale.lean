import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# 記事 `なぜZariskiでは点が数えられないか_Weil予想とGrothendieck位相_2026-06-19` §2・§5：ℙ¹ の点の数・Zariski ≤ étale

記事の文（記事から写す）：

> 有限体 $\mathbb F_q$ 上の射影直線の点の数は、数えるまでもない: $\#\mathbb P^1(\mathbb F_{q^n})=q^n+1$
> ($\mathbb F_{q^n}$ の元が $q^n$ 個、それに無限遠点を一つ足す)。（§2「まず手で」）

> Zariski の「開部分集合への制限」をやめ、**étale 射**(平坦かつ不分岐 …)の族を「被覆」とみなす。
> これが **Grothendieck 位相**で、その舞台が **étale site**。… まさに Zariski に欠けていた被覆を、外から足す。（§5）

参照する宣言（Mathlib v4.30.0 のタグのソースで名前と型を確かめた）：

* `Projectivization.card_of_finrank_two`（`Mathlib/LinearAlgebra/Projectivization/Cardinality.lean`）：
  有限体 k と 2 次元の k ベクトル空間 V について #ℙ(V) ＝ #k + 1。
* `Module.finrank_fin_fun`（`Mathlib/LinearAlgebra/Dimension/Constructions.lean`）：dim (Fin n → k) ＝ n。
* `AlgebraicGeometry.Scheme.etaleTopology`・`AlgebraicGeometry.Scheme.zariskiTopology_le_etaleTopology`
  （`Mathlib/AlgebraicGeometry/Sites/Etale.lean`）：スキームの圏の上の étale 位相（Grothendieck 位相）と、
  Zariski 位相 ≤ étale 位相（Zariski の被覆は étale の被覆でもある）。

`card_projective_line`（L1）は、`card_of_finrank_two` に V ＝ k² を入れて記事の形（有限体 F について #ℙ¹(F) ＝ #F + 1）にしたもの。
-/

universe u

namespace MathGarden.WhyZariskiCannotCountPoints

open scoped LinearAlgebra.Projectivization

/-- §2：有限体 F 上の射影直線 ℙ¹(F) ＝ ℙ(F²) の点の数は #F + 1（F ＝ 𝔽_{q^n} なら q^n + 1）。 -/
theorem card_projective_line (F : Type*) [Field F] [Finite F] :
    Nat.card (ℙ F (Fin 2 → F)) = Nat.card F + 1 :=
  Projectivization.card_of_finrank_two F (Fin 2 → F) (by simp)

/- §5：Zariski 位相 ≤ étale 位相（Grothendieck 位相として。étale 位相のほうが被覆が多い）。 -/
example : AlgebraicGeometry.Scheme.zariskiTopology.{u} ≤ AlgebraicGeometry.Scheme.etaleTopology.{u} :=
  AlgebraicGeometry.Scheme.zariskiTopology_le_etaleTopology

end MathGarden.WhyZariskiCannotCountPoints
