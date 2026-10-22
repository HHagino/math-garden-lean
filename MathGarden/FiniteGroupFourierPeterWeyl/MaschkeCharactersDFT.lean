import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Character
import Mathlib.Analysis.Fourier.ZMod

/-!
# 記事 `有限群のフーリエはPeter-Weylである_指標表はどこから来るのか_2026-08-15` §2・§3・§7：Maschke・指標の直交・DFT

記事の文（記事から写す）：

> 実際に直交しているか、手で確かめる。内積は $\langle \chi,\psi\rangle = \frac{1}{|G|}\sum_{g} \chi(g)\overline{\psi(g)}$ …
> 前者が $1$ であることが $V$ の既約性、後者が $0$ であることが $\mathbf{1}$ と $\mathrm{sgn}$ の非同値である。
> （§2「まず手で分解する」）

> $$\hat f(j) = \sum_{k} f(k)\,\omega^{jk}, \qquad f(k) = \frac{1}{n}\sum_{j} \hat f(j)\,\omega^{-jk}$$
> ── 離散フーリエ変換と反転公式。（§3「可換なら、これは高校で見たフーリエになる」）

> $\mathbb{C}[G]$ が半単純である（＝ブロック対角に割れる）ことに全面的に依存していた。それを保証しているのが Maschke の定理で、
> 条件は「体 $k$ の標数が $|G|$ を割らない」である。（§7「どこで全部が崩れるか」）

参照する宣言（Mathlib v4.30.0 のタグのソースで名前と型を確かめた）：

* `MonoidAlgebra.Submodule.exists_isCompl`（`Mathlib/RepresentationTheory/Maschke.lean`）：
  有限群 G と、|G| が 0 にならない体 k（`NeZero (Nat.card G : k)`）について、k[G] 加群の部分加群は補部分加群をもつ。
  同じファイルの instance から k[G] は半単純環（`IsSemisimpleRing`）。
* `Representation.char_orthonormal`（`Mathlib/RepresentationTheory/Character.lean`）：
  代数閉体 k・|G| が k で可逆のとき、既約表現 ρ, σ について |G|⁻¹ Σ_g χ_ρ(g) χ_σ(g⁻¹) は σ ≅ ρ なら 1、そうでなければ 0。
* `ZMod.dft`・`ZMod.invDFT_apply`（`Mathlib/Analysis/Fourier/ZMod.lean`）：ℤ/N 上の DFT は線形同型で、
  逆は Ψ ↦ N⁻¹ Σ_j e(jk) Ψ(j)。Mathlib の DFT は 𝓕Φ(k) ＝ Σ_j e(−jk) Φ(j)（`ZMod.dft_apply`）で、記事の $\hat f$ と ω の符号が逆。

`dft_inversion`（L1）は、Mathlib の「逆写像を当てると戻る」を記事の反転公式の形（足し算で書いた形）に書き直したもの。
-/

namespace MathGarden.FiniteGroupFourierPeterWeyl

/- §7 Maschke：標数が |G| を割らなければ、k[G] 加群の部分加群は補部分加群をもつ。 -/
example {k G V : Type*} [Field k] [Group G] [Finite G] [NeZero (Nat.card G : k)]
    [AddCommGroup V] [Module (MonoidAlgebra k G) V] (p : Submodule (MonoidAlgebra k G) V) :
    ∃ q : Submodule (MonoidAlgebra k G) V, IsCompl p q :=
  MonoidAlgebra.Submodule.exists_isCompl p

/- §7：その結果、k[G] は半単純環。 -/
example {k G : Type*} [Field k] [Group G] [Finite G] [NeZero (Nat.card G : k)] :
    IsSemisimpleRing (MonoidAlgebra k G) :=
  inferInstance

/- §2・§5 指標の直交関係（代数閉体・|G| 可逆・既約表現）。 -/
open scoped Classical in
example {G k V W : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W)
    [Fintype G] [Invertible (Nat.card G : k)] [IsAlgClosed k]
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ] :
    (Nat.card G : k)⁻¹ * ∑ g : G, ρ.character g * σ.character g⁻¹ =
      if Nonempty (Representation.Equiv σ ρ) then ↑1 else ↑0 :=
  Representation.char_orthonormal ρ σ

open ZMod

/-- §3 DFT の反転公式：ℤ/N 上の関数 Φ は、その DFT から $\Phi(k) = N^{-1}\sum_j e(jk)\,\hat\Phi(j)$ で戻る
（Mathlib の DFT は $\hat\Phi(j) = \sum_k e(-jk)\Phi(k)$。$e(x) = \exp(2\pi i x/N)$）。 -/
theorem dft_inversion {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (k : ZMod N) :
    Φ k = (N : ℂ)⁻¹ • ∑ j : ZMod N, stdAddChar (j * k) • 𝓕 Φ j := by
  have h := invDFT_apply (𝓕 Φ) k
  rw [LinearEquiv.symm_apply_apply] at h
  exact h

end MathGarden.FiniteGroupFourierPeterWeyl
