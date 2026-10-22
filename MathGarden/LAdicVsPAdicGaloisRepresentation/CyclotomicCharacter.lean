import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-!
# 記事 `l-adic-vs-p-adic-galois-representation` §2.4：円分指標

記事の文（記事から写す）：

> 特に重要な 1 次元表現が **円分指標** (cyclotomic character) $\chi_l \colon G_K \to \mathbb{Z}_l^\times$ で、
> これは $G_K$ の 1 のべき乗根への作用 $\sigma(\zeta_{l^n}) = \zeta_{l^n}^{\chi_l(\sigma) \bmod l^n}$
> によって定義される。（§2.4）

参照する宣言（Mathlib v4.30.0 のタグのソースで名前と型を確かめた）：

* `cyclotomicCharacter`（`(L : Type*) [CommRing L] [IsDomain L] (p : ℕ) [Fact p.Prime] : (L ≃+* L) →* ℤ_[p]ˣ`）・
  `cyclotomicCharacter.spec`（`[∀ i, HasEnoughRootsOfUnity L (p ^ i)]` のもとで
  `g t = t ^ ((cyclotomicCharacter L p g).val.toZModPow n).val`、`t ^ p ^ n = 1`）・
  `cyclotomicCharacter.continuous`（Gal(L/K) に制限すると連続）
  （`Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean`）。

`cyclotomic_character_spec` は Mathlib の `cyclotomicCharacter.spec` に記事の記号を当てたもの（L0）。
Mathlib の円分指標は L のすべての環自己同型の群の上で定義され、記事の G_K ＝ Gal(K^sep/K) はその部分群として
`MulSemiringAction.toRingAut` で入る。
-/

noncomputable section

namespace MathGarden.LAdicVsPAdicGaloisRepresentation

/- §2.4（Mathlib）：円分指標は群準同型 χ_l：(L の環自己同型) → ℤ_l^×。 -/
example (L : Type*) [CommRing L] [IsDomain L] (l : ℕ) [Fact l.Prime] :
    (L ≃+* L) →* ℤ_[l]ˣ :=
  cyclotomicCharacter L l

/-- §2.4：l^n 乗して 1 になる ζ（1 の l^n 乗根）について σ(ζ) ＝ ζ^{χ_l(σ) mod l^n}
（L が 1 の原始 l^i 乗根をすべての i について持つとき）。 -/
theorem cyclotomic_character_spec {L : Type*} [CommRing L] [IsDomain L] (l : ℕ) [Fact l.Prime]
    [∀ i, HasEnoughRootsOfUnity L (l ^ i)] (σ : L ≃+* L) {n : ℕ} (ζ : L) (hζ : ζ ^ l ^ n = 1) :
    σ ζ = ζ ^ ((cyclotomicCharacter L l σ).val.toZModPow n).val :=
  cyclotomicCharacter.spec l σ ζ hζ

/- §2.4（Mathlib）：K ⊆ L のとき、Gal(L/K) に制限した円分指標は（Krull 位相で）連続。 -/
example (l : ℕ) [Fact l.Prime] (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Continuous ((cyclotomicCharacter L l).comp (MulSemiringAction.toRingAut Gal(L/K) L)) :=
  cyclotomicCharacter.continuous l K L

end MathGarden.LAdicVsPAdicGaloisRepresentation

end
