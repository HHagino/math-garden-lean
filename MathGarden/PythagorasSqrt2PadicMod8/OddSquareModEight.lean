/-!
# 記事 `pythagoras-sqrt2-p-adic-mod-8`：奇数の平方は 8 で割ると 1 余る（L1）

記事「ピタゴラス派は p 進数を見ていたのか? ── √2、通約不能性、そして mod 8 の局所数論」
§3「奇素数の場合:ルジャンドル記号と mod 8」の文（記事から写す）：

> 標準公式によれば、
> $$\left(\frac{2}{p}\right) = (-1)^{(p^2-1)/8}.$$
> ここから、$p$ を 8 で割った余りで場合分けすると:
> | $p \bmod 8$ | $(p^2-1)/8$ の偶奇 | … |

この式と表の列は、奇素数 $p$ について $(p^2-1)/8$ が**整数である**こと、
すなわち $p^2 \equiv 1 \pmod 8$ を前提にしている。ここで Lean が確かめるのは**この前提だけ**：

* 確かめたこと：奇数 `n`（`n % 2 = 1` の自然数。素数に限らない）について `n ^ 2 % 8 = 1`。
* 確かめていないこと：ルジャンドル記号の公式 $\left(\frac{2}{p}\right) = (-1)^{(p^2-1)/8}$ そのもの、
  表の「偶奇」の列、Hensel の補題、$\sqrt 2 \in \mathbb{Q}_p$ の判定。

このファイルは Lean の core だけで型検査できる（Mathlib を読み込まない）。
-/

namespace MathGarden.PythagorasSqrt2PadicMod8

/-- 奇数の平方は 8 で割ると 1 余る：`n % 2 = 1 → n ^ 2 % 8 = 1`。

証明：`n` を 8 で割った余りは 1, 3, 5, 7 のどれか（`omega`）。
`n ^ 2 % 8 = (n % 8) ^ 2 % 8`（`Nat.pow_mod`）なので、
$1^2, 3^2, 5^2, 7^2 = 1, 9, 25, 49$ を 8 で割った余りを見ればよく、どれも 1。 -/
theorem odd_sq_mod_eight (n : Nat) (hn : n % 2 = 1) : n ^ 2 % 8 = 1 := by
  have h : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  rw [Nat.pow_mod]
  rcases h with h | h | h | h <;> simp [h]

/-- 記事 §3 の式の形に合わせた言い換え：奇数 `p` について `8 ∣ p ^ 2 - 1`
（したがって `(p ^ 2 - 1) / 8` は割り切れた商＝整数）。 -/
theorem eight_dvd_odd_sq_sub_one (p : Nat) (hp : p % 2 = 1) : 8 ∣ p ^ 2 - 1 := by
  have h := odd_sq_mod_eight p hp
  omega

end MathGarden.PythagorasSqrt2PadicMod8
