import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import MathGarden.FiniteInfinitePrimesDirichletUnitTheorem.UnitRank

/-!
# 記事 `dedekind-e-extension-f-norm`：拡大は e、ノルムは f、Σ e·f = [L:K]（L0）

記事の文（記事から写す）：

> $$\mathfrak p B \;=\; \prod_{\mathfrak P \mid \mathfrak p} \mathfrak P^{e_{\mathfrak P}}, \qquad e_{\mathfrak P} = e(\mathfrak P/\mathfrak p).$$
> （§2「拡大 $\mathfrak p B$ には分岐指数 $e$ が出る」）

> $$N_{L/K}(\mathfrak P) \;=\; \mathfrak p^{f_{\mathfrak P}}, \qquad f_{\mathfrak P} = [B/\mathfrak P : A/\mathfrak p].$$
> （§3「ノルム $N_{L/K}(\mathfrak P)$ には剰余体次数 $f$ が出る」）

> $$\sum_{\mathfrak P \mid \mathfrak p} e_{\mathfrak P} f_{\mathfrak P} \;=\; [L:K]$$
> （§5「合成すると $[L:K]$ が回収される」）

L0 ＝ Mathlib にある宣言を参照し、その型が下の主張と一致することを Lean に確かめさせる
（このリポジトリで新しく証明したものはない）。参照する宣言（Mathlib v4.30.0 のタグのソースで名前と型を確かめた）：

* `Ideal.map_algebraMap_eq_finsetProd_pow`（`Mathlib/RingTheory/DedekindDomain/Factorization.lean`）：
  B がデデキント整域で A 上整、p が A の極大イデアルで p ≠ 0 なら、pB ＝ ∏_{P ∈ primesOver p B} P^{e(P|p)}。
* `Ideal.relNorm_eq_pow_of_isMaximal`（`Mathlib/RingTheory/Ideal/Norm/RelNorm.lean`）：
  A ⊂ B がデデキント整域の有限拡大で A の分数体が完全体、P が p の上の極大イデアルなら、相対ノルム relNorm A P ＝ p^{f(P|p)}。
* Σe·f は記事 `finite-infinite-primes-dirichlet-unit-theorem` のために入れた
  `MathGarden.FiniteInfinitePrimesDirichletUnitTheorem.sum_ramification_inertia_eq_degree`
  （中身は `Ideal.sum_ramification_inertia`）をそのまま使う。
-/

namespace MathGarden.DedekindEExtensionFNorm

/- §2：pB ＝ ∏ P^e（p は極大で 0 でない。B はデデキント整域で A 上整。A はデデキントでなくてよい）。 -/
example {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Algebra.IsIntegral A B] [Module.IsTorsionFree A B] {p : Ideal A} [p.IsMaximal] (hp : p ≠ 0) :
    Ideal.map (algebraMap A B) p = ∏ P ∈ p.primesOver B, P ^ p.ramificationIdx P :=
  Ideal.map_algebraMap_eq_finsetProd_pow hp

/- §3：相対ノルム N_{L/K}(P) ＝ p^f（A の分数体が完全体、P と p は極大、P は p の上にある）。 -/
example {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [IsIntegrallyClosed A] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [IsDedekindDomain A] [IsDedekindDomain B]
    [PerfectField (FractionRing A)] (P : Ideal B) (p : Ideal A) [P.LiesOver p]
    [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm A P = p ^ p.inertiaDeg P :=
  Ideal.relNorm_eq_pow_of_isMaximal P p

/- §5：Σ e·f ＝ [L:K]（記事 finite-infinite-primes-dirichlet-unit-theorem の項目と同じ宣言）。 -/
open scoped Classical in
example {R : Type*} [CommRing R] (S : Type*) [CommRing S]
    [Algebra R S] [IsDedekindDomain S] (K L : Type*) [Field K] [Field L] [IsDedekindDomain R]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L] [Algebra K L]
    [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L] [Module.Finite R S]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset p S, Ideal.ramificationIdx p P * Ideal.inertiaDeg p P
      = Module.finrank K L :=
  MathGarden.FiniteInfinitePrimesDirichletUnitTheorem.sum_ramification_inertia_eq_degree S K L hp0

end MathGarden.DedekindEExtensionFNorm
