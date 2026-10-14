import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Contractible

/-!
# 記事 `弧状連結単連結可縮_不変量は何を見て何を見落とすか_2026-06-19` §2：可縮 ⇒ 単連結 ⇒ 弧状連結（L0）

記事の文（記事から写す）：

> 四つの性質には、次の一方向の含意がある。可縮 $\Longrightarrow$ 単連結 $\Longrightarrow$ 弧状連結 $\Longrightarrow$ 連結。

L0 ＝ Mathlib にある宣言を参照し、その型が下の主張と一致することを Lean に確かめさせる
（このリポジトリで新しく証明したものはない）。参照する宣言：

* `SimplyConnectedSpace.ofContractible`（`Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean`）
* 単連結空間が弧状連結であること：Mathlib の型クラスのインスタンス（下では `inferInstance` で取り出す）。
-/

namespace MathGarden.ArcConnectedSimplyConnectedContractible

/- 可縮な空間は単連結。 -/
example (X : Type*) [TopologicalSpace X] [ContractibleSpace X] : SimplyConnectedSpace X :=
  SimplyConnectedSpace.ofContractible X

/- 単連結な空間は弧状連結。 -/
example (X : Type*) [TopologicalSpace X] [SimplyConnectedSpace X] : PathConnectedSpace X :=
  inferInstance

end MathGarden.ArcConnectedSimplyConnectedContractible
