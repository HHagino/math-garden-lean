import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# 記事 `special-relativity-as-completion-of-electromagnetism` §4・§5・§6：ガリレイ変換とローレンツ変換での光速

記事の文（記事から写す）：

> ニュートン力学では、別の慣性系へ移るときに **ガリレイ変換** を使う：時間 $t$ は同じ、位置だけ
> $\mathbf{x}' = \mathbf{x} - \mathbf{v} t$。この変換のもとでは、速度は単純に足し算で変わる。…
> $c$ という速度が、観測者によって変わってしまうことになる。（§4）

> $$t' = \gamma\left(t - \frac{v x}{c^2}\right), \quad x' = \gamma(x - v t), \quad y' = y, \quad z' = z,
> \qquad \gamma = \frac{1}{\sqrt{1 - v^2/c^2}}.$$（§5）

> $c$ が不変であるとは、それを生み出す媒質ではなく、**時空そのものの構造から来る不変量** だ、ということになる。（§6）

参照する宣言（Mathlib v4.30.0 のタグのソースで名前と型を確かめた）：

* `Real.sq_sqrt`（`Mathlib/Data/Real/Sqrt.lean`）・`div_lt_one`（`Mathlib/Algebra/Order/Field/Basic.lean`）・
  `one_div_mul_cancel`（`Mathlib/Algebra/GroupWithZero/Units/Basic.lean`）。

このファイルの定理はすべて L1（このリポジトリで証明した）。Maxwell 方程式は扱っていない（Mathlib に無い）。
-/

noncomputable section

namespace MathGarden.SpecialRelativityAsCompletionOfElectromagnetism

/-- ローレンツ因子 γ ＝ 1/√(1 − v²/c²)。 -/
def lorentzFactor (c v : ℝ) : ℝ := 1 / Real.sqrt (1 - v ^ 2 / c ^ 2)

/-- ローレンツ変換（x 方向）の時刻：t' ＝ γ(t − vx/c²)。 -/
def boostT (c v t x : ℝ) : ℝ := lorentzFactor c v * (t - v * x / c ^ 2)

/-- ローレンツ変換（x 方向）の位置：x' ＝ γ(x − vt)。 -/
def boostX (c v t x : ℝ) : ℝ := lorentzFactor c v * (x - v * t)

theorem lorentzFactor_sq_mul (c v : ℝ) (hc : 0 < c) (hv : v ^ 2 < c ^ 2) :
    lorentzFactor c v ^ 2 * (1 - v ^ 2 / c ^ 2) = 1 := by
  have hpos : 0 < 1 - v ^ 2 / c ^ 2 := by
    rw [sub_pos, div_lt_one (pow_pos hc 2)]
    exact hv
  rw [lorentzFactor, div_pow, one_pow, Real.sq_sqrt hpos.le]
  exact one_div_mul_cancel hpos.ne'

/-- c²t'² − x'² ＝ c²t² − x²（|v| < c）。 -/
theorem interval_invariant (c v t x : ℝ) (hc : 0 < c) (hv : v ^ 2 < c ^ 2) :
    c ^ 2 * boostT c v t x ^ 2 - boostX c v t x ^ 2 = c ^ 2 * t ^ 2 - x ^ 2 := by
  have h := lorentzFactor_sq_mul c v hc hv
  have hc0 : c ≠ 0 := hc.ne'
  have key : c ^ 2 * (t - v * x / c ^ 2) ^ 2 - (x - v * t) ^ 2
      = (1 - v ^ 2 / c ^ 2) * (c ^ 2 * t ^ 2 - x ^ 2) := by
    field_simp
    ring
  calc c ^ 2 * boostT c v t x ^ 2 - boostX c v t x ^ 2
      = lorentzFactor c v ^ 2 * (c ^ 2 * (t - v * x / c ^ 2) ^ 2 - (x - v * t) ^ 2) := by
        unfold boostT boostX
        ring
    _ = lorentzFactor c v ^ 2 * (1 - v ^ 2 / c ^ 2) * (c ^ 2 * t ^ 2 - x ^ 2) := by
        rw [key]
        ring
    _ = c ^ 2 * t ^ 2 - x ^ 2 := by
        rw [h, one_mul]

/-- 光が x 方向に進む（x ＝ ct）なら、変換後も x' ＝ ct'。 -/
theorem light_speed_invariant (c v t : ℝ) (hc : 0 < c) :
    boostX c v t (c * t) = c * boostT c v t (c * t) := by
  have hc0 : c ≠ 0 := hc.ne'
  unfold boostT boostX
  field_simp
  ring

/-- 光の信号（x² + y² + z² ＝ c²t²）は、ローレンツ変換（y' ＝ y, z' ＝ z）のあとも x'² + y'² + z'² ＝ c²t'²。 -/
theorem light_cone_preserved (c v t x y z : ℝ) (hc : 0 < c) (hv : v ^ 2 < c ^ 2)
    (hlight : x ^ 2 + y ^ 2 + z ^ 2 = c ^ 2 * t ^ 2) :
    boostX c v t x ^ 2 + y ^ 2 + z ^ 2 = c ^ 2 * boostT c v t x ^ 2 := by
  have h := interval_invariant c v t x hc hv
  linear_combination hlight - h

/-- §5・§6：記事のローレンツ変換（|v| < c）では、光の速さ c は変わらない：x 方向の光 x ＝ ct は x' ＝ ct' に、
どの向きの光（x² + y² + z² ＝ c²t²）も x'² + y'² + z'² ＝ c²t'² に写る。 -/
theorem lorentz_keeps_light_speed (c v t x y z : ℝ) (hc : 0 < c) (hv : v ^ 2 < c ^ 2) :
    boostX c v t (c * t) = c * boostT c v t (c * t) ∧
    (x ^ 2 + y ^ 2 + z ^ 2 = c ^ 2 * t ^ 2 →
      boostX c v t x ^ 2 + y ^ 2 + z ^ 2 = c ^ 2 * boostT c v t x ^ 2) :=
  ⟨light_speed_invariant c v t hc, light_cone_preserved c v t x y z hc hv⟩

/-- §4：ガリレイ変換 x' ＝ x − vt, t' ＝ t では、光の信号 x ＝ ct は x' ＝ (c − v)t' になり、
v ≠ 0 なら（t ≠ 0 の時刻で）x' ≠ ct'。 -/
theorem galilean_changes_light_speed (c v t : ℝ) (hv : v ≠ 0) (ht : t ≠ 0) :
    c * t - v * t = (c - v) * t ∧ c * t - v * t ≠ c * t := by
  refine ⟨by ring, ?_⟩
  intro h
  have hvt : v * t = 0 := by linarith
  rcases mul_eq_zero.mp hvt with h1 | h1
  · exact hv h1
  · exact ht h1

end MathGarden.SpecialRelativityAsCompletionOfElectromagnetism

end
