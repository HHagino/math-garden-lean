import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Nat.Factorization.Basic

/-!
# 記事 `division-algebra-1248-projective-cohomology`：中間の二項係数がすべて偶数 ⇔ 2 のべき（L1）

記事「割り算できる $\mathbb{R}^n$ はなぜ珍しいのか — 射影空間のコホモロジーが教えてくれること」
§7「中間二項係数がすべて偶数なら、$n$ は $2$ のべき」の文（記事から写す）：

> **補題.** $\displaystyle\binom{n}{k}\equiv 0 \pmod 2$ が $0<k<n$ のすべての $k$ で成り立つことと、
> $n=2^{r}$（ある $r\ge 0$）であることは同値である。

ここで Lean が確かめること（`two_dvd_choose_iff_eq_two_pow`）：`0 < n` の自然数 `n` について、
`(∀ k, 0 < k → k < n → 2 ∣ n.choose k) ↔ ∃ r, n = 2 ^ r`。

* `0 < n` を仮定に置いた。記事では `n` は ℝⁿ の次元（`n ≥ 1`）。`n = 0` では左辺が（`0 < k < 0` と
  なる `k` が無いので）成り立ち、右辺は成り立たない（0 は 2 のべきでない）ので、この仮定は要る。
* ⇐（`n = 2^r` なら中間の二項係数はすべて偶数）：Mathlib の `Nat.Prime.dvd_choose_pow`
  （素数 `p` について `k ≠ 0`、`k ≠ p^r` なら `p ∣ (p^r).choose k`）に `p = 2` を入れる。
  記事は $\mathbb F_2[t]$ の中の $(1+t)^{2^r} = 1 + t^{2^r}$（Frobenius の繰り返し）で示している。
* ⇒（2 のべきでなければ、偶数でない中間の二項係数がある）：記事と同じく $n = 2^r m$（$m$ は奇数）と書き、
  $m > 1$ なら $k = 2^r$ が $0 < k < n$ で $\binom{2^r m}{2^r} \equiv m \equiv 1 \pmod 2$ になることを示す。
  記事は $(1+t)^n = (1+t^{2^r})^m$ の $t^{2^r}$ の係数を見ているが、ここでは Lucas の定理の一段
  （Mathlib の `Choose.choose_modEq_choose_mod_mul_choose_div_nat`：
  $\binom{2a}{2b} \equiv \binom{0}{0}\binom{a}{b} \pmod 2$）を $r$ 回使う。

確かめていないこと：§6 までの部分（ℝⁿ の除法的な双線形積から射影空間の写像を作り、
$\mathbb Z_2$ 係数のコホモロジーで $(\alpha_1+\alpha_2)^n = 0$ から中間の二項係数が偶数になること）、
記事の結論「ℝⁿ に除法的な双線形積が存在する ⇒ $n = 2^r$」、§8 以降の複素版・$n = 16$ の話・
1, 2, 4, 8 への絞り込み。補題の証明の道筋も記事（多項式の係数）とは違う（上の ⇐・⇒ を参照）。
-/

namespace MathGarden.DivisionAlgebra1248ProjectiveCohomology

/-- Lucas の定理の一段（`p = 2`）：`(2a).choose (2b)` と `a.choose b` は 2 で割った余りが等しい。 -/
theorem choose_two_mul_mod_two (a b : ℕ) : (2 * a).choose (2 * b) % 2 = a.choose b % 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2 * a) (k := 2 * b) (p := 2)
  rw [Nat.mul_mod_right, Nat.mul_mod_right, Nat.mul_div_cancel_left a Nat.two_pos,
    Nat.mul_div_cancel_left b Nat.two_pos, Nat.choose_self, one_mul] at h
  exact h

/-- `(2^r * m).choose (2^r)` を 2 で割った余りは `m` を 2 で割った余りに等しい
（記事 §7 の「$t^{2^r}$ の係数は $\binom{m}{1} = m$」に当たる）。 -/
theorem choose_two_pow_mul_mod_two (r m : ℕ) : (2 ^ r * m).choose (2 ^ r) % 2 = m % 2 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', mul_assoc, choose_two_mul_mod_two, ih]

/-- 記事 §7 の補題：`0 < n` について、`0 < k < n` のすべての `k` で `n.choose k` が偶数であることと、
`n` が 2 のべきであることは同値。 -/
theorem two_dvd_choose_iff_eq_two_pow (n : ℕ) (hn : 0 < n) :
    (∀ k, 0 < k → k < n → 2 ∣ n.choose k) ↔ ∃ r : ℕ, n = 2 ^ r := by
  constructor
  · intro h
    obtain ⟨r, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
    refine ⟨r, ?_⟩
    have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
    by_contra hne
    have hm1 : 1 < m := by
      rcases Nat.lt_trichotomy m 1 with h1 | h1 | h1
      · omega
      · subst h1
        simp at hne
      · exact h1
    have hk0 : 0 < 2 ^ r := Nat.two_pow_pos r
    have hkn : 2 ^ r < 2 ^ r * m := lt_mul_of_one_lt_right hk0 hm1
    have hdvd := h (2 ^ r) hk0 hkn
    have hmod := choose_two_pow_mul_mod_two r m
    omega
  · rintro ⟨r, rfl⟩ k hk hkn
    exact Nat.Prime.dvd_choose_pow Nat.prime_two hk.ne' hkn.ne

end MathGarden.DivisionAlgebra1248ProjectiveCohomology
