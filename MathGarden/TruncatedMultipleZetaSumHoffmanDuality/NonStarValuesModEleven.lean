import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# 記事 `truncated-multiple-zeta-sum-hoffman-duality`：p = 11 での non-star 版の値（L1）

記事「有限切断多重ゼータ和 ζ_{<N} ── N=∞ と N=p、二つの双対性の母体」の文（記事から写す）。

§2「有限切断多重ゼータ和 $\zeta_{<N}$」の定義：

> 正整数列(指数列)$\mathbf{k} = (k_1, \dots, k_r)$ に対して、
> $$\zeta_{<N}(k_1, \dots, k_r) = \sum_{0 < n_1 < n_2 < \cdots < n_r < N} \frac{1}{n_1^{k_1}\, n_2^{k_2}\cdots n_r^{k_r}}$$

§4「N=p:有限多重ゼータ値と、Hoffman 双対性」の文：

> 一項どうしが符号 $-1$ で結ばれるのは star 版で、non-star 版の $\zeta_{<p}$ そのものには、
> ひとつの双対値との符号付き合同式はない。たとえば $(1,4,1)^{\vee}=(2,1,1,2)$ について、
> $p=11$ で和を直接計算すると $\zeta_{<11}(1,4,1)\equiv 9$、$\zeta_{<11}(2,1,1,2)\equiv 4 \pmod{11}$ で、
> $9\not\equiv\pm4$ である。

ここで Lean が確かめること：

* `zetaLT p N ks`：§2 の和を `ZMod p` の中で計算したもの（§4 の「$\bmod\ p$ で見たもの」）。
  和の範囲 $0 < n_1 < \cdots < n_r < N$ を、$n_1 \in (0, N)$、$n_2 \in (n_1, N)$、… の入れ子の和として
  書く（深さ 3 のときの形を `zetaLT_three` が定義の展開だけで示す）。$1/(n_1^{k_1} \cdots n_r^{k_r})$ は、
  各因子の逆元 $(n_i^{k_i})^{-1}$ の積として書く（$1 \le n_i \le 10$ は `ZMod 11` で 0 でないので同じもの）。
* 確かめたこと（`zetaLT_eleven`）：`zetaLT 11 11 [1, 4, 1] = 9`、`zetaLT 11 11 [2, 1, 1, 2] = 4`、
  そして `ZMod 11` で `zetaLT 11 11 [1, 4, 1]` は `zetaLT 11 11 [2, 1, 1, 2]` にも、その符号を変えたものにも
  等しくない（$9 \not\equiv \pm 4$）。
* 確かめていないこと：Hoffman 双対の計算 $(1,4,1)^{\vee}=(2,1,1,2)$（ここでは記事の組をそのまま使った）、
  star 版の Hoffman 双対性（Hoffman の Theorem 4.6）と non-star 版の式（Theorem 4.7）、$p = 11$ 以外の素数、
  「non-star 版には一項の符号付き合同式はない」という一般の言い方（確かめたのは $p = 11$ のこの一組だけ）、
  $N \to \infty$ の側（多重ゼータ値とその双対性）。

計算の方法：`ZMod 11` では `x⁻¹ = x ^ 9`（Fermat の小定理 $x^{10} = 1$。$x = 0$ でも両辺 0）。
逆元をこの形に書き換えてから、和を Lean のカーネルに評価させる（`decide +kernel`）。
-/

namespace MathGarden.TruncatedMultipleZetaSumHoffmanDuality

open Finset

/-- `zetaFrom p N m [k₁, …, k_r]` ＝ `m < n₁ < ⋯ < n_r < N` にわたる
`(n₁ ^ k₁)⁻¹ * ⋯ * (n_r ^ k_r)⁻¹` の和（`ZMod p` の中）。空の列では 1。 -/
def zetaFrom (p N : ℕ) : ℕ → List ℕ → ZMod p
  | _, [] => 1
  | m, k :: ks => ∑ n ∈ Ioo m N, ((n : ZMod p) ^ k)⁻¹ * zetaFrom p N n ks

/-- 記事 §2 の有限切断多重ゼータ和 $\zeta_{<N}(k_1, \dots, k_r)$ を `ZMod p` で見たもの：
$0 < n_1 < \cdots < n_r < N$ にわたる和。 -/
def zetaLT (p N : ℕ) (ks : List ℕ) : ZMod p :=
  zetaFrom p N 0 ks

/-- 深さ 3 のとき、`zetaLT` は記事 §2 の和を入れ子に書いたものそのもの（定義を展開しただけ）。 -/
theorem zetaLT_three (p N a b c : ℕ) :
    zetaLT p N [a, b, c] =
      ∑ n₁ ∈ Ioo 0 N, ((n₁ : ZMod p) ^ a)⁻¹ *
        ∑ n₂ ∈ Ioo n₁ N, ((n₂ : ZMod p) ^ b)⁻¹ *
          ∑ n₃ ∈ Ioo n₂ N, ((n₃ : ZMod p) ^ c)⁻¹ * 1 :=
  rfl

/-- `ZMod 11` では、逆元は 9 乗に等しい（`x = 0` も含めて）。
`x ≠ 0` なら Fermat の小定理 `x ^ 10 = 1` から `x * x ^ 9 = 1`。 -/
theorem inv_eq_pow_nine (x : ZMod 11) : x⁻¹ = x ^ 9 := by
  haveI : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
  by_cases hx : x = 0
  · subst hx
    exact (ZMod.inv_zero 11).trans (by decide +kernel)
  · apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ']
    exact ZMod.pow_card_sub_one_eq_one hx

/-- 記事 §4：$\zeta_{<11}(1,4,1) \equiv 9 \pmod{11}$。 -/
theorem zetaLT_eleven_one_four_one : zetaLT 11 11 [1, 4, 1] = 9 := by
  simp only [zetaLT, zetaFrom, inv_eq_pow_nine]
  decide +kernel

/-- 記事 §4：$\zeta_{<11}(2,1,1,2) \equiv 4 \pmod{11}$。 -/
theorem zetaLT_eleven_two_one_one_two : zetaLT 11 11 [2, 1, 1, 2] = 4 := by
  simp only [zetaLT, zetaFrom, inv_eq_pow_nine]
  decide +kernel

/-- 記事 §4 の文の主張（p = 11 のこの一組）：
$\zeta_{<11}(1,4,1) \equiv 9$、$\zeta_{<11}(2,1,1,2) \equiv 4 \pmod{11}$ で、
$\zeta_{<11}(1,4,1) \not\equiv \pm\,\zeta_{<11}(2,1,1,2)$（$9 \not\equiv \pm 4$）。 -/
theorem zetaLT_eleven :
    zetaLT 11 11 [1, 4, 1] = 9 ∧ zetaLT 11 11 [2, 1, 1, 2] = 4 ∧
      zetaLT 11 11 [1, 4, 1] ≠ zetaLT 11 11 [2, 1, 1, 2] ∧
      zetaLT 11 11 [1, 4, 1] ≠ -zetaLT 11 11 [2, 1, 1, 2] := by
  have h₁ := zetaLT_eleven_one_four_one
  have h₂ := zetaLT_eleven_two_one_one_two
  refine ⟨h₁, h₂, ?_, ?_⟩ <;> rw [h₁, h₂] <;> decide +kernel

end MathGarden.TruncatedMultipleZetaSumHoffmanDuality
