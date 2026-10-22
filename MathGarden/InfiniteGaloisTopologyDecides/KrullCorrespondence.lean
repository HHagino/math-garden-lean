import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite

/-!
# 記事 `無限次Galois対応は位相が決める_2026-06-19` §3・§4・§5：固定体は閉包しか見ない・Krull の対応・射有限

記事の文（記事から写す）：

> $L/K$ を(無限次でもよい)Galois 拡大、$G=\mathrm{Gal}(L/K)$ とする。任意の部分群 $H\le G$ に対し、
> Krull 位相での閉包を $\overline H$ と書くと、$L^{H}=L^{\overline H}$.
> （§3「なぜ破れたか：固定体は閉包しか見ない」）

> $L/K$ を任意の Galois 拡大、$G=\mathrm{Gal}(L/K)$ に Krull 位相を入れる。
> $\{K\subseteq M\subseteq L \text{ 中間体}\} \to \{H\le G \text{ 閉部分群}\}$, $M\mapsto \mathrm{Gal}(L/M)$
> は包含反転の全単射で、逆は $H\mapsto L^H$。
> （§5「直された辞書：閉部分群との全単射」）

> この位相で $G$ は **射有限群**になる:有限群の逆極限 $G\cong\varprojlim_{M}\mathrm{Gal}(M/K)$ … として書け、コンパクト・ハウスドルフ・完全不連結。
> （§4「Krull 位相：何を開集合と呼ぶか」）

参照する宣言（Mathlib v4.30.0 のタグのソースで名前と型を確かめた）：

* `InfiniteGalois.IntermediateFieldEquivClosedSubgroup`（`Mathlib/FieldTheory/Galois/Infinite.lean`）：
  `IntermediateField k K ≃o (ClosedSubgroup Gal(K/k))ᵒᵈ`。順序の双対への順序同型＝包含反転の全単射。
  行きは `L ↦ L.fixingSubgroup`、戻りは `H ↦ fixedField H`（定義に書いてある）。
* `InfiniteGalois.fixedField_fixingSubgroup`・`InfiniteGalois.fixingSubgroup_fixedField`（同じファイル）：二つの合成が恒等。
* `InfiniteGalois.fixingSubgroup_isClosed`（同じファイル）：中間体を固定する部分群は Krull 位相で閉。
* `IntermediateField.le_iff_le`・`IntermediateField.fixedField_antitone`（`Mathlib/FieldTheory/Galois/Basic.lean`）。
* `Subgroup.le_topologicalClosure`・`Subgroup.topologicalClosure_minimal`（`Mathlib/Topology/Algebra/Group/Basic.lean`）。
* `InfiniteGalois.continuousMulEquivToLimit`（`Mathlib/FieldTheory/Galois/Profinite.lean`）：
  Gal(K/k) と、有限次 Galois 中間体 L にわたる Gal(L/k) の極限との、位相群としての同型。
* `krullTopology_t2`（`Mathlib/FieldTheory/KrullTopology.lean`）と、同じファイル・Profinite.lean の
  `TotallySeparatedSpace`・`CompactSpace` の instance。

`fixedField_topologicalClosure`（L1）は記事 §3 の $L^{H}=L^{\overline H}$ をこのリポジトリで証明したもの
（Mathlib では見つからなかった形。証明は記事の理由と同じ：固定する部分群は閉なので閉包を含む）。
-/

namespace MathGarden.InfiniteGaloisTopologyDecides

open IntermediateField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- 記事 §3：固定体は閉包しか見ない。Galois 拡大 K/k と Gal(K/k) の任意の部分群 H について、
H の Krull 位相での閉包の固定体は H の固定体に等しい。 -/
theorem fixedField_topologicalClosure [IsGalois k K] (H : Subgroup Gal(K/k)) :
    fixedField H.topologicalClosure = fixedField H := by
  apply le_antisymm
  · exact fixedField_antitone H.le_topologicalClosure
  · rw [IntermediateField.le_iff_le]
    exact H.topologicalClosure_minimal ((IntermediateField.le_iff_le H (fixedField H)).mp le_rfl)
      (InfiniteGalois.fixingSubgroup_isClosed (fixedField H))

/- 記事 §5：中間体と閉部分群の包含反転の全単射（順序の双対への順序同型）。 -/
noncomputable example [IsGalois k K] : IntermediateField k K ≃o (ClosedSubgroup Gal(K/k))ᵒᵈ :=
  InfiniteGalois.IntermediateFieldEquivClosedSubgroup

/- 記事 §5：行き（中間体 ↦ それを固定する部分群）のあとに戻り（固定体）をとると元に戻る。 -/
example [IsGalois k K] (L : IntermediateField k K) : fixedField L.fixingSubgroup = L :=
  InfiniteGalois.fixedField_fixingSubgroup L

/- 記事 §5：閉部分群 H の固定体を固定する部分群は H。 -/
example [IsGalois k K] (H : ClosedSubgroup Gal(K/k)) : (fixedField H).fixingSubgroup = H.1 :=
  InfiniteGalois.fixingSubgroup_fixedField H

/- 記事 §4：Gal(K/k) は有限次 Galois 部分拡大の Galois 群の極限と、位相群として同型（射有限）。 -/
noncomputable example [IsGalois k K] :=
  InfiniteGalois.continuousMulEquivToLimit k K

/- 記事 §4：コンパクト・ハウスドルフ・完全不連結（完全分離）。 -/
example [IsGalois k K] : CompactSpace Gal(K/k) := inferInstance
example [IsGalois k K] : T2Space Gal(K/k) := krullTopology_t2
example [IsGalois k K] : TotallySeparatedSpace Gal(K/k) := inferInstance

end MathGarden.InfiniteGaloisTopologyDecides
