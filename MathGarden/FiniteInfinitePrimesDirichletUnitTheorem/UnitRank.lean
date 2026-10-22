import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.RamificationInertia.Basic

/-!
# 記事 `finite-infinite-primes-dirichlet-unit-theorem`：単数定理の階数・r₁+2r₂・Σeᵢfᵢ（L0）

記事「有限素点と無限素点 ── Dirichlet の単数定理から見える代数的整数論の風景」の文（記事から写す）：

> - $[K:\mathbb{Q}] = r_1 + 2r_2$
> - **Dirichlet の単数定理**:$E_K / W_K \cong \mathbb{Z}^{\,r_1 + r_2 - 1}$
> （§1 の板書。$W_K$ は単元群の**ねじれ部分**(有限位数の元全体)）

> $$\sum_{i=1}^{g} e_i f_i = [K : \mathbb{Q}]$$
> （§5「素数の分解」）

L0 ＝ Mathlib にある宣言を参照し、その型が下の主張と一致することを Lean に確かめさせる。参照する宣言
（Mathlib v4.30.0 のタグのソースで名前と型を確かめた）：

* `NumberField.Units.rank_modTorsion`（`Mathlib/NumberTheory/NumberField/Units/DirichletTheorem.lean`）：
  単元群をねじれ部分で割った群（加法的に見たもの）の ℤ 上の階数は `NumberField.Units.rank K`。
* `NumberField.Units.rank`（同じファイル）：定義は「無限素点の数 − 1」。
* `NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces`
  （`Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean`）：無限素点の数 ＝ 実素点の数 ＋ 複素素点の数。
* `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank`（同じファイル）：r₁ + 2r₂ = [K:ℚ]。
* `NumberField.Units.basisModTorsion`（DirichletTheorem.lean）：その商に `Fin (rank K)` で添字づけた ℤ 基底がある。
* `Ideal.sum_ramification_inertia`（`Mathlib/NumberTheory/RamificationInertia/Basic.lean`）：
  極大イデアル p の上の素イデアル P にわたって Σ e(P|p)·f(P|p) = [L:K]。
  v4.30.0 では `Ideal.ramificationIdx`・`Ideal.inertiaDeg`（docs の最新版の `ramificationIdx'`・`inertiaDeg'` ではない）。

上の三つを合成して、記事の形「階数 ＝ r₁ + r₂ − 1」を一つの定理にした（`units_modTorsion_finrank`）。
-/

namespace MathGarden.FiniteInfinitePrimesDirichletUnitTheorem

open NumberField

/-- 単数定理の階数：$\mathcal{O}_K^\times / W_K$ の ℤ 上の階数は $r_1 + r_2 - 1$。 -/
theorem units_modTorsion_finrank (K : Type*) [Field K] [NumberField K] :
    Module.finrank ℤ (Additive ((NumberField.RingOfIntegers K)ˣ ⧸ NumberField.Units.torsion K)) =
      NumberField.InfinitePlace.nrRealPlaces K + NumberField.InfinitePlace.nrComplexPlaces K - 1 := by
  rw [NumberField.Units.rank_modTorsion, NumberField.Units.rank, NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]

/-- その商は自由：`Fin (rank K)` で添字づけた ℤ 基底がある（記事の「≅ ℤ^{r₁+r₂−1}」の自由の部分）。 -/
noncomputable example (K : Type*) [Field K] [NumberField K] :
    Module.Basis (Fin (NumberField.Units.rank K)) ℤ (Additive ((NumberField.RingOfIntegers K)ˣ ⧸ NumberField.Units.torsion K)) :=
  NumberField.Units.basisModTorsion K

/-- $[K:\mathbb{Q}] = r_1 + 2r_2$。 -/
theorem degree_eq_r1_add_two_r2 (K : Type*) [Field K] [NumberField K] :
    NumberField.InfinitePlace.nrRealPlaces K + 2 * NumberField.InfinitePlace.nrComplexPlaces K = Module.finrank ℚ K :=
  NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K

open scoped Classical in
/-- $\sum_i e_i f_i = [L:K]$（記事は $R = \mathbb{Z}$, $S = \mathcal{O}_K$ の場合。Mathlib は一般のデデキント整域の拡大）。 -/
theorem sum_ramification_inertia_eq_degree {R : Type*} [CommRing R] (S : Type*) [CommRing S]
    [Algebra R S] [IsDedekindDomain S] (K L : Type*) [Field K] [Field L] [IsDedekindDomain R]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L] [Algebra K L]
    [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L] [Module.Finite R S]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset p S, Ideal.ramificationIdx p P * Ideal.inertiaDeg p P
      = Module.finrank K L :=
  Ideal.sum_ramification_inertia S K L hp0

end MathGarden.FiniteInfinitePrimesDirichletUnitTheorem
