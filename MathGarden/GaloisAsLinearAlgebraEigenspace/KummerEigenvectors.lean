import Mathlib.FieldTheory.KummerExtension
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# 記事 `galois-as-linear-algebra-eigenspace` §3・§4・§9：Kummer 拡大の固有ベクトル・指標の一次独立・円分体

記事の文（記事から写す）：

> $K$ を体とし、**1 の原始 $n$ 乗根 $\zeta_n$ が $K$ に含まれている** と仮定する … $x^n - a$ が $K$ 上既約だとして、
> その根の一つを $\alpha = \sqrt[n]{a}$ と書く。… Galois 群 $G$ は位数 $n$ の **巡回群** になる。
> … $\sigma(\alpha^j) = \sigma(\alpha)^j = (\zeta_n \alpha)^j = \zeta_n^{\,j} \cdot \alpha^j.$
> **$\alpha^j$ は演算子 $\sigma$ の固有ベクトルで、固有値は $\zeta_n^{\,j}$**。（§3「Kummer 拡大:対角化される演算子」）

> **円分拡大。** $\mathbb Q(\zeta_n)$ の Galois 群は $(\mathbb Z/n\mathbb Z)^\times$ と同型で …（§9「展望」）

参照する宣言（Mathlib v4.30.0 のタグのソースで名前と型を確かめた）：

* `autAdjoinRootXPowSubCEquiv`（`Mathlib/FieldTheory/KummerExtension.lean`）：K が 1 の原始 n 乗根を含み
  X^n − a が既約なら、K の 1 の n 乗根の群と Aut_K(K[X]/(X^n − a)) が群として同型。
* `autAdjoinRootXPowSubCEquiv_root`・`autAdjoinRootXPowSubCEquiv_symm_smul`（同じファイル）：
  1 の n 乗根 η に当たる自己同型は根 α を η·α に写す／どの自己同型 σ も σ(α) ＝ (対応する η)·α。
* `linearIndependent_monoidHom`（`Mathlib/LinearAlgebra/LinearIndependent/Basic.lean`）：
  モノイドから整域への準同型（指標）たちは一次独立（Dedekind）。
* `IsCyclotomicExtension.autEquivPow`（`Mathlib/NumberTheory/Cyclotomic/Gal.lean`）と
  `Polynomial.cyclotomic.irreducible_rat`（`Mathlib/RingTheory/Polynomial/Cyclotomic/Roots.lean`）：
  ℚ(ζ_n)（`CyclotomicField n ℚ`）の Galois 群は (ℤ/n)^× と同型。

`root_eigenvector`・`root_pow_eigenvector`（L1）は、記事の「α^j は固有ベクトル」を、Mathlib の
`autAdjoinRootXPowSubCEquiv_symm_smul` から数行で出したもの。
-/

namespace MathGarden.GaloisAsLinearAlgebraEigenspace

open Polynomial

variable {K : Type*} [Field K] {n : ℕ} [NeZero n]

/- §3：Galois 群は 1 の n 乗根の群と同型（記事の「位数 n の巡回群」の、群の同定の部分）。 -/
noncomputable example (hζ : (primitiveRoots n K).Nonempty) {a : K} (H : Irreducible (X ^ n - C a)) :
    rootsOfUnity n K ≃* (AdjoinRoot (X ^ n - C a) ≃ₐ[K] AdjoinRoot (X ^ n - C a)) :=
  autAdjoinRootXPowSubCEquiv hζ H

/-- §3：根 α ＝ ⁿ√a は、どの自己同型 σ についても固有ベクトル（σ(α) ＝ c·α となる c ∈ K がある）。 -/
theorem root_eigenvector (hζ : (primitiveRoots n K).Nonempty) {a : K} (H : Irreducible (X ^ n - C a))
    (σ : AdjoinRoot (X ^ n - C a) ≃ₐ[K] AdjoinRoot (X ^ n - C a)) :
    ∃ c : K, σ (AdjoinRoot.root (X ^ n - C a)) = c • AdjoinRoot.root (X ^ n - C a) :=
  ⟨(((autAdjoinRootXPowSubCEquiv hζ H).symm σ : Kˣ) : K), by
    rw [← Units.smul_def, autAdjoinRootXPowSubCEquiv_symm_smul]⟩

/-- §3：α^j も固有ベクトルで、固有値は c^j（記事の σ(α^j) ＝ ζ^j α^j）。 -/
theorem root_pow_eigenvector (hζ : (primitiveRoots n K).Nonempty) {a : K}
    (H : Irreducible (X ^ n - C a))
    (σ : AdjoinRoot (X ^ n - C a) ≃ₐ[K] AdjoinRoot (X ^ n - C a)) (j : ℕ) :
    ∃ c : K, σ (AdjoinRoot.root (X ^ n - C a) ^ j) = c ^ j • AdjoinRoot.root (X ^ n - C a) ^ j := by
  obtain ⟨c, hc⟩ := root_eigenvector hζ H σ
  exact ⟨c, by rw [map_pow, hc, smul_pow]⟩

/- §3：1 の n 乗根 η に当たる自己同型は α を η·α に写す（固有値は η）。 -/
example (hζ : (primitiveRoots n K).Nonempty) {a : K} (H : Irreducible (X ^ n - C a))
    (η : rootsOfUnity n K) :
    autAdjoinRootXPowSubCEquiv hζ H η (AdjoinRoot.root (X ^ n - C a))
      = ((η : Kˣ) : K) • AdjoinRoot.root (X ^ n - C a) :=
  autAdjoinRootXPowSubCEquiv_root hζ H η

/- §4：指標（モノイド準同型）たちは一次独立（Dedekind）。 -/
example (G : Type*) [MulOneClass G] (L : Type*) [CommRing L] [IsDomain L] :
    LinearIndependent L (M := G → L) (fun f => f : (G →* L) → G → L) :=
  linearIndependent_monoidHom G L

/- §9：ℚ(ζ_n) の Galois 群は (ℤ/n)^×。 -/
noncomputable example : Gal(CyclotomicField n ℚ/ℚ) ≃* (ZMod n)ˣ :=
  IsCyclotomicExtension.autEquivPow (CyclotomicField n ℚ)
    (cyclotomic.irreducible_rat (Nat.pos_of_ne_zero (NeZero.ne n)))

end MathGarden.GaloisAsLinearAlgebraEigenspace
