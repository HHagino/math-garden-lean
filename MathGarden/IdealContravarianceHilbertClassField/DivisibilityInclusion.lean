import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.Ideal.Span

/-!
# 記事 `ideal-contravariance-hilbert-class-field` §3：割り切りとイデアルの包含は向きが逆（L0）

記事の文（記事から写す）：

> 整数環で、割り切り関係とイデアルの包含関係を並べてみる。… つまり $(6) \subset (2)$。**向きが逆になっている。**
> $a \mid b \Leftrightarrow (b) \subset (a)$。

L0 ＝ Mathlib にある宣言を参照し、その型が下の主張と一致することを Lean に確かめさせる
（このリポジトリで新しく証明したものはない）。参照する宣言：

* `Ideal.span_singleton_le_span_singleton`（`Mathlib/RingTheory/Ideal/Span.lean`）：
  `(x) ≤ (y) ⇔ y ∣ x`（可換な環で、元の生成するイデアル）。
* `Ideal.dvd_iff_le`（`Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`）：
  デデキント整域のイデアルでは、`I ∣ J ⇔ J ≤ I`（割る ⇔ 含む）。
-/

namespace MathGarden.IdealContravarianceHilbertClassField

/- 元の生成するイデアルの包含は、割り切りの逆向き。 -/
example {α : Type*} [CommSemiring α] (x y : α) :
    Ideal.span ({x} : Set α) ≤ Ideal.span ({y} : Set α) ↔ y ∣ x :=
  Ideal.span_singleton_le_span_singleton

/- デデキント整域のイデアルでは、割り切り ⇔ 包含の逆向き。 -/
example {A : Type*} [CommRing A] [IsDedekindDomain A] {I J : Ideal A} : I ∣ J ↔ J ≤ I :=
  Ideal.dvd_iff_le

end MathGarden.IdealContravarianceHilbertClassField
