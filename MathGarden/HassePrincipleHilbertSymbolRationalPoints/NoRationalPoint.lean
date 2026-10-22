import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# 記事 `hasse-principle-hilbert-symbol-rational-points`：3x² − 5y² = 1 は有理数解を持たない（L1）

記事「ハッセ原理が"使える道具"に変わる瞬間 ── ヒルベルト記号と有理点判定」§8「手で動かす ── $a=3,\ b=-5$ を判定する」の文（記事から写す）：

> 実際に機械を回す。$3x^2-5y^2=1$、すなわち $z^2=3x^2-5y^2$ に有理点はあるか。

> $p=2$ と $p=5$ で $(3,-5)_v=-1$ が出た。**すべての $v$ で $+1$ ではないので、
> ハッセ=ミンコフスキーにより $3x^2-5y^2=1$ は有理数解を持たない。**

表の $p=5$ の行の理由（記事から写す）：「$5$ 進局所計算:$3$ は $5$ の平方非剰余 $\Rightarrow$ 解なし」。

ここで Lean が確かめるのは**結論**（有理数解が無いこと）と、表の $p=5$ の行の理由のうち
「3 は 5 を法として平方でない」の部分だけ。証明は Hilbert 記号もハッセ＝ミンコフスキーも使わない：

* 有理数解 $(x, y)$ があれば、分母を払って整数 $a, b$ と $c \ne 0$ で $3a^2 - 5b^2 = c^2$。
* 5 を法として $3a^2 \equiv c^2$。3 は平方非剰余なので $5 \mid a$ かつ $5 \mid c$。
  すると $5 \mid b^2$、よって $5 \mid b$。三つとも 5 で割れて、同じ式が $|c|$ の小さい解で成り立つ。
* $|c|$ についての強い帰納法（無限降下）で矛盾。

確かめていないこと：Hilbert 記号 $(3,-5)_v$ の各値（表の 4 行）、積公式、ハッセ＝ミンコフスキーの定理そのもの、
$p = 2$ の行（mod 8 の計算）。Mathlib v4.30.0 に Hilbert 記号は見つからなかった（下調べ 2026-10-14）。
-/

namespace MathGarden.HassePrincipleHilbertSymbolRationalPoints

/-- 5 を法として 3 は平方でない（記事 §8 の表の $p=5$ の行の理由）。 -/
theorem three_not_square_mod_five : ∀ r : ZMod 5, r ^ 2 ≠ 3 := by decide

/-- 5 を法として $3x^2 \equiv z^2$ なら $x \equiv z \equiv 0$（3 が平方非剰余であることの言い換え）。 -/
theorem mod_five_key : ∀ x z : ZMod 5, 3 * x ^ 2 - z ^ 2 = 0 → x = 0 ∧ z = 0 := by decide

/-- 5 を法として $y^2 \equiv 0$ なら $y \equiv 0$。 -/
theorem sq_eq_zero_mod_five : ∀ y : ZMod 5, y ^ 2 = 0 → y = 0 := by decide

theorem five_dvd_of_cast_eq_zero {a : ℤ} (h : (a : ZMod 5) = 0) : (5 : ℤ) ∣ a := by
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd a 5).mp h
  exact_mod_cast this

theorem cast_eq_zero_of_five_dvd {a : ℤ} (h : (5 : ℤ) ∣ a) : (a : ZMod 5) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd a 5).mpr (by exact_mod_cast h)

/-- 整数版：$c \ne 0$ なら $3a^2 - 5b^2 = c^2$ は解を持たない（$|c| = n$ についての強い帰納法＝無限降下）。 -/
theorem no_int_solution (n : ℕ) :
    ∀ a b c : ℤ, c.natAbs = n → c ≠ 0 → 3 * a ^ 2 - 5 * b ^ 2 ≠ c ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b c hn hc h
  -- 5 を法として 3a² ≡ c²
  have h1 : (5 : ℤ) ∣ 3 * a ^ 2 - c ^ 2 := ⟨b ^ 2, by linarith⟩
  have h2 := cast_eq_zero_of_five_dvd h1
  push_cast at h2
  obtain ⟨ha, hc5⟩ := mod_five_key _ _ h2
  obtain ⟨a', rfl⟩ := five_dvd_of_cast_eq_zero ha
  obtain ⟨c', rfl⟩ := five_dvd_of_cast_eq_zero hc5
  -- すると b² = 5(3a'² − c'²)
  have h3 : (5 : ℤ) ∣ b ^ 2 := ⟨3 * a' ^ 2 - c' ^ 2, by linarith⟩
  have h4 := cast_eq_zero_of_five_dvd h3
  push_cast at h4
  obtain ⟨b', rfl⟩ := five_dvd_of_cast_eq_zero (sq_eq_zero_mod_five _ h4)
  -- 三つとも 5 で割って、同じ式の |c| の小さい解
  have hc' : c' ≠ 0 := by
    rintro rfl
    simp at hc
  have h5 : 3 * a' ^ 2 - 5 * b' ^ 2 = c' ^ 2 := by linarith
  have hlt : c'.natAbs < n := by
    rw [← hn, Int.natAbs_mul]
    have h6 : (5 : ℤ).natAbs = 5 := rfl
    have h7 : c'.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hc'
    rw [h6]
    omega
  exact ih _ hlt a' b' c' rfl hc' h5

/-- 記事 §8 の結論：$3x^2 - 5y^2 = 1$ は有理数解を持たない。 -/
theorem no_rat_solution (x y : ℚ) : 3 * x ^ 2 - 5 * y ^ 2 ≠ 1 := by
  intro h
  have hc : ((x.den * y.den : ℕ) : ℤ) ≠ 0 := by simp [x.den_nz, y.den_nz]
  have hx := Rat.mul_den_eq_num x
  have hy := Rat.mul_den_eq_num y
  have key : ((3 * (x.num * y.den) ^ 2 - 5 * (y.num * x.den) ^ 2 : ℤ) : ℚ)
      = (((((x.den * y.den : ℕ) : ℤ)) ^ 2 : ℤ) : ℚ) := by
    push_cast
    rw [← hx, ← hy]
    linear_combination ((x.den : ℚ) * y.den) ^ 2 * h
  exact no_int_solution _ (x.num * y.den) (y.num * x.den) ((x.den * y.den : ℕ) : ℤ) rfl hc
    (by exact_mod_cast key)

end MathGarden.HassePrincipleHilbertSymbolRationalPoints
