import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# 記事 `linear-algebra-as-k-theory-of-point` §3：有限次元ベクトル空間は次元で決まり、直和で次元は足される（L0）

記事の文（記事から写す）：

> 有限次元ベクトル空間は、体 $\mathbb{C}$ が固定されていれば次元によって完全に分類される(同型を除いて)。
> $\{\text{有限次元 }\mathbb{C}\text{-ベクトル空間の同型類}\} \cong \mathbb{N},\ [V] \mapsto \dim V$。

L0 ＝ Mathlib にある宣言を参照し、その型が下の主張と一致することを Lean に確かめさせる
（このリポジトリで新しく証明したものはない）。参照する宣言：

* `FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq`（`Mathlib/LinearAlgebra/Dimension/Free.lean`）
* `Module.finrank_prod`（`Mathlib/LinearAlgebra/Dimension/Constructions.lean`）：直積（有限直和）の次元は次元の和。

Mathlib は任意の体で述べている（記事は ℂ）。
-/

namespace MathGarden.LinearAlgebraAsKTheoryOfPoint

universe u v

/- 有限次元ベクトル空間 `V, W` が線形同型 ⇔ 次元が等しい。 -/
example (K : Type u) (V W : Type v) [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W] [Module.Finite K W] :
    Nonempty (V ≃ₗ[K] W) ↔ Module.finrank K V = Module.finrank K W :=
  FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq

/- 直積（有限直和）の次元は次元の和。 -/
example (K : Type u) (V W : Type v) [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W] [Module.Finite K W] :
    Module.finrank K (V × W) = Module.finrank K V + Module.finrank K W :=
  Module.finrank_prod

end MathGarden.LinearAlgebraAsKTheoryOfPoint
