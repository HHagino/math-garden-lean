import Mathlib.FieldTheory.AbelRuffini
import Mathlib.GroupTheory.Solvable

/-!
# 記事 `galois-quintic-solvable-classification`：x⁵ − 2 は解ける側・S₅ は解けない側（L0）

記事の文（記事から写す）：

> 「一般の」5次方程式が解けないことと、「あらゆる」5次方程式が解けないことは、まったく別のことである。
> 後で具体的に見るように、x⁵ − 2 = 0 はれっきとした5次方程式で …（§7 の見出し「x⁵ − 2 は5次だが冪根で解ける」）

> **S₅（位数120）。** 5次の対称群。A₅ を指数2の正規部分群として含むので、A₅ が非可解である以上、S₅ も非可解だ。

L0 ＝ Mathlib にある宣言を参照し、その型が下の主張と一致することを Lean に確かめさせる
（このリポジトリで新しく証明したものはない）。参照する宣言：

* `gal_X_pow_sub_C_isSolvable`（`Mathlib/FieldTheory/AbelRuffini.lean`）：`X ^ n - C x` のガロア群は可解。
* `Equiv.Perm.fin_5_not_solvable`（`Mathlib/GroupTheory/Solvable.lean`）：`S₅` は可解でない。
-/

namespace MathGarden.GaloisQuinticSolvableClassification

open Polynomial

/- `x ^ n - c` のガロア群は可解（任意の体 `F`・任意の `n`）。 -/
example {F : Type*} [Field F] (n : ℕ) (c : F) : IsSolvable (X ^ n - C c).Gal :=
  gal_X_pow_sub_C_isSolvable n c

/- 記事 §7 の例 `x ^ 5 - 2`（有理数体上）。 -/
example : IsSolvable (X ^ 5 - C (2 : ℚ)).Gal := gal_X_pow_sub_C_isSolvable 5 2

/- `S₅` は可解でない。 -/
example : ¬ IsSolvable (Equiv.Perm (Fin 5)) := Equiv.Perm.fin_5_not_solvable

end MathGarden.GaloisQuinticSolvableClassification
