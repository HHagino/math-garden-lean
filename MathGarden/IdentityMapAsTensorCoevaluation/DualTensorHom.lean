import Mathlib.LinearAlgebra.Contraction

/-!
# 記事 `identity-map-as-tensor-coevaluation` §2：V* ⊗ V ≅ End(V)（L0）

記事の文（記事から写す）：

> $V$ を体 $k$ 上の有限次元ベクトル空間、$V^*=\operatorname{Hom}(V,k)$ をその双対空間とする。このとき標準的な同型
> $V\otimes V^* \cong \operatorname{End}(V)$ がある。… $v\otimes\varphi \longmapsto (x\mapsto \varphi(x)\,v)$。

L0 ＝ Mathlib にある宣言を参照し、その型が下の主張と一致することを Lean に確かめさせる
（このリポジトリで新しく証明したものはない）。参照する宣言：

* `dualTensorHomEquiv`（`Mathlib/LinearAlgebra/Contraction.lean`）：`Dual R M ⊗ N ≃ₗ[R] (M →ₗ[R] N)`。

Mathlib はテンソルの順序が `V* ⊗ W`（記事は `V ⊗ V*`）。`W = V` を入れると記事の `End(V)` の形になる。
-/

namespace MathGarden.IdentityMapAsTensorCoevaluation

open TensorProduct

/- 有限次元ベクトル空間 `V` について、`V* ⊗ V` と `End(V)` の間に線形同型がある。 -/
example (K V : Type*) [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V] :
    Nonempty (Module.Dual K V ⊗[K] V ≃ₗ[K] (V →ₗ[K] V)) :=
  ⟨dualTensorHomEquiv K V V⟩

end MathGarden.IdentityMapAsTensorCoevaluation
