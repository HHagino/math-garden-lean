import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Algebra.Group.Nat.Even

/-!
# 記事 `素数の足し算は人類に向いていない_2026-06-02`：算術級数定理と局所障害（L0）

記事の文（記事から写す）：

> **算術級数定理(ディリクレの定理)**。「初項と公差が互いに素な等差数列には素数が無限に含まれる」。

> $n(n+1)$ は連続整数の積で常に偶数、固定素数 $2$ が障害 ── 両方素数は $(2,3)$ の一度きり。

L0 ＝ Mathlib にある宣言を参照し、その型が下の主張と一致することを Lean に確かめさせる
（このリポジトリで新しく証明したものはない）。参照する宣言：

* `Nat.infinite_setOf_prime_and_modEq`（`Mathlib/NumberTheory/LSeries/PrimesInAP.lean`）
* `Nat.even_mul_succ_self`（`Mathlib/Algebra/Group/Nat/Even.lean`）
-/

namespace MathGarden.PrimeAdditionNotForHumans

/- ディリクレの算術級数定理：`q ≠ 0` で `a` と `q` が互いに素なら、`p ≡ a (mod q)` の素数 `p` は無限にある。 -/
example {q a : ℕ} (hq : q ≠ 0) (h : a.Coprime q) :
    Set.Infinite {p : ℕ | p.Prime ∧ Nat.ModEq q p a} :=
  Nat.infinite_setOf_prime_and_modEq hq h

/- 隣り合う整数の積 `n(n+1)` はいつも偶数（局所障害の例）。 -/
example (n : ℕ) : Even (n * (n + 1)) := Nat.even_mul_succ_self n

end MathGarden.PrimeAdditionNotForHumans
