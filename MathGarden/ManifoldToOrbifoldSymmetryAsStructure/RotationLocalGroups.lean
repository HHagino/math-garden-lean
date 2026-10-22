import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# 記事 `manifold-to-orbifold-symmetry-as-structure` §4・§5：回転群 ℤ/n の作用の局所群と z ↦ zⁿ

記事の文（記事から写す）：

> $\mathbb{C} / (\mathbb{Z}/n)$(回転群で割った平面)は、中心が尖った **円錐** の絵になる
> (… 位相空間としては $z \mapsto z^n$ により平面と同相)。（§4）

> 具体例:円盤 $D^2 = \{z \in \mathbb{C} \mid |z| \leq 1\}$ に、回転群 $\Gamma = \mathbb{Z}/n$ を
> $z \mapsto e^{2\pi i/n} z$ で作用させる。
> - 中心 $0$ は唯一の **固定点**:$\Gamma \cdot 0 = \{0\}$。
> - それ以外の点 $z \neq 0$ では、$\Gamma$ は自由に作用する($\gamma z = z$ なら $\gamma = e$)。
> … 中心は局所群 $\mathbb{Z}/n$ を背負った特別な点、それ以外の点は局所群自明の普通の点。（§5）

参照する宣言（Mathlib v4.30.0 のタグのソースで名前と型を確かめた）：

* `Complex.isPrimitiveRoot_exp`（`IsPrimitiveRoot (exp (2 * π * I / n)) n`、n ≠ 0）
  （`Mathlib/RingTheory/RootsOfUnity/Complex.lean`）。
* `IsPrimitiveRoot.pow_eq_one`・`IsPrimitiveRoot.pow_eq_one_iff_dvd`・`IsPrimitiveRoot.eq_pow_of_pow_eq_one`
  （`Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean`）。
* `mul_right_cancel₀`・`div_mul_cancel₀`・`div_self`・`zero_pow`・`pow_eq_zero_iff`・`div_pow`。

ℤ/n の元 [k] は回転 z ↦ ζ^k z（ζ ＝ e^{2πi/n}）で表し、「[k] ＝ e」は「n ∣ k」と書いた。
作用は |z| を変えないので、円盤 D² の上でも同じことが言える（D² への制限は書いていない）。定理はすべて L1。
-/

noncomputable section

namespace MathGarden.ManifoldToOrbifoldSymmetryAsStructure

/-- 回転の生成元 ζ ＝ e^{2πi/n}。 -/
def rot (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- §5：中心 0 はどの回転でも動かない（局所群は ℤ/n 全体）。0 でない点 z では ζ^k z ＝ z ⇔ n ∣ k
（[k] ＝ e のときだけ z が動かない＝局所群は自明）。 -/
theorem local_groups (n : ℕ) (hn : n ≠ 0) :
    (∀ k : ℕ, rot n ^ k * 0 = 0) ∧
    (∀ z : ℂ, z ≠ 0 → ∀ k : ℕ, (rot n ^ k * z = z ↔ n ∣ k)) := by
  have hζ : IsPrimitiveRoot (rot n) n := Complex.isPrimitiveRoot_exp n hn
  refine ⟨fun k => mul_zero _, fun z hz k => ?_⟩
  rw [← hζ.pow_eq_one_iff_dvd k]
  constructor
  · intro h
    have h' : rot n ^ k * z = 1 * z := by
      rw [one_mul]
      exact h
    exact mul_right_cancel₀ hz h'
  · intro h
    rw [h, one_mul]

/-- §4：z ↦ zⁿ はちょうど回転の軌道を同一視する：wⁿ ＝ zⁿ ⇔ ある k で w ＝ ζ^k z。 -/
theorem pow_eq_pow_iff_same_orbit (n : ℕ) (hn : n ≠ 0) (z w : ℂ) :
    w ^ n = z ^ n ↔ ∃ k : ℕ, w = rot n ^ k * z := by
  have hζ : IsPrimitiveRoot (rot n) n := Complex.isPrimitiveRoot_exp n hn
  haveI : NeZero n := ⟨hn⟩
  constructor
  · intro h
    by_cases hz : z = 0
    · subst hz
      rw [zero_pow hn] at h
      have hw : w = 0 := (pow_eq_zero_iff hn).mp h
      exact ⟨0, by rw [hw, mul_zero]⟩
    · have h1 : (w / z) ^ n = 1 := by
        rw [div_pow, h, div_self (pow_ne_zero n hz)]
      obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one h1
      refine ⟨i, ?_⟩
      rw [hi, div_mul_cancel₀ w hz]
  · rintro ⟨k, rfl⟩
    rw [mul_pow, ← pow_mul, mul_comm k n, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

end MathGarden.ManifoldToOrbifoldSymmetryAsStructure

end
