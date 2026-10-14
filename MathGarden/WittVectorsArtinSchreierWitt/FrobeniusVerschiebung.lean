import Mathlib.RingTheory.WittVector.Identities

/-!
# 記事 `witt-vectors-artin-schreier-witt` §3.3：Frobenius と Verschiebung の関係 FV = VF = p（L0）

記事の文（記事から写す）：

> A が標数 p のとき： $FV = VF = p \cdot \text{id}$

L0 ＝ Mathlib にある宣言を参照し、その型が下の主張と一致することを Lean に確かめさせる
（このリポジトリで新しく証明したものはない）。参照する宣言（`Mathlib/RingTheory/WittVector/Identities.lean`）：

* `WittVector.frobenius_verschiebung`：`F (V x) = x * p`（可換環ならどれでも）。
* `WittVector.verschiebung_frobenius`：`V (F x) = x * p`（標数 `p` の環）。
-/

namespace MathGarden.WittVectorsArtinSchreierWitt

/- `F V = p`（任意の可換環の Witt ベクトルで）。 -/
example (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] (x : WittVector p R) :
    WittVector.frobenius (WittVector.verschiebung x) = x * p :=
  WittVector.frobenius_verschiebung x

/- `V F = p`（標数 `p` の環で）。 -/
example (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [CharP R p] (x : WittVector p R) :
    WittVector.verschiebung (WittVector.frobenius x) = x * p :=
  WittVector.verschiebung_frobenius x

end MathGarden.WittVectorsArtinSchreierWitt
