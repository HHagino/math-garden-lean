import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# 記事 `pythagoras-sqrt2-p-adic-mod-8` §3：2 が mod p の平方 ⇔ p ≡ ±1 (mod 8)（L0）

記事の文（記事から写す）：

> $p$ が奇素数 ($p \neq 2$) のときは、… 合同式 $x^2 \equiv 2 \pmod{p}$ が解を持つか、
> つまり 2 が $p$ を法として平方剰余かどうかと同値である。
> … $\sqrt{2} \in \mathbb{Q}_p \iff p \equiv 1, 7 \pmod{8}$（表は $p \bmod 8$ の場合分け）

L0 ＝ Mathlib にある宣言を参照し、その型が下の主張と一致することを Lean に確かめさせる
（このリポジトリで新しく証明したものはない）。参照する宣言：

* `ZMod.exists_sq_eq_two_iff`（`Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`）。

確かめたのは「2 が `ZMod p` の平方 ⇔ `p % 8 = 1 ∨ p % 8 = 7`」まで。
`√2 ∈ ℚ_p` との同値（Hensel の補題から組む部分）は含まない。
-/

namespace MathGarden.PythagorasSqrt2PadicMod8

/- 奇素数 `p` について、`2` が `ZMod p` の平方 ⇔ `p ≡ 1, 7 (mod 8)`。 -/
example (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7 :=
  ZMod.exists_sq_eq_two_iff hp

end MathGarden.PythagorasSqrt2PadicMod8
