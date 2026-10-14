import Mathlib.FieldTheory.AbelRuffini
import Mathlib.GroupTheory.Solvable

/-!
# 記事 `solvable-group-radical-solvability-galois`：冪根で解ける ⇒ ガロア群は可解、S₅ は非可解（L0）

記事の文（記事から写す）：

> 方程式が根号で解ける $\Longrightarrow$ そのガロア群が可解群

> $S_5$ を可解にしようと、正規部分群列を作ろうとすると、$A_5$ … が現れる。… 困るのは、$A_5$ から先である。

L0 ＝ Mathlib にある宣言を参照し、その型が下の主張と一致することを Lean に確かめさせる
（このリポジトリで新しく証明したものはない）。参照する宣言：

* `isSolvable_gal_of_irreducible`（`Mathlib/FieldTheory/AbelRuffini.lean`）：冪根で表せる根をもつ既約多項式のガロア群は可解。
* `Equiv.Perm.fin_5_not_solvable`（`Mathlib/GroupTheory/Solvable.lean`）：5 文字の対称群は可解でない。

記事は逆向き（可解 ⇒ 冪根で解ける）も説明しているが、ここで参照したのは片向きだけ。
-/

namespace MathGarden.SolvableGroupRadicalSolvabilityGalois

open Polynomial

/- 根が冪根で表せる（`solvableByRad`）既約多項式のガロア群は可解。 -/
example {F E : Type*} [Field F] [Field E] [Algebra F E] {x : E}
    (hx : x ∈ solvableByRad F E) {q : F[X]} (q_irred : Irreducible q)
    (q_aeval : aeval x q = 0) : IsSolvable q.Gal :=
  isSolvable_gal_of_irreducible hx q_irred q_aeval

/- 5 文字の対称群 `S₅` は可解でない。 -/
example : ¬ IsSolvable (Equiv.Perm (Fin 5)) := Equiv.Perm.fin_5_not_solvable

end MathGarden.SolvableGroupRadicalSolvabilityGalois
