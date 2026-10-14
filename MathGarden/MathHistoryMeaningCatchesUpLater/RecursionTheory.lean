import Mathlib.Computability.Halting

/-!
# 記事 `math-history-meaning-catches-up-later` §7：Kleene の再帰定理・Rice の定理・S^m_n 定理（L0）

記事の文（記事から写す）：

> **再帰定理:** 任意の全域的な計算可能関数 $f$ について、$\varphi_e \simeq \varphi_{f(e)}$ をみたす $e$ が存在する。
> **Rice の定理:** プログラムが計算する関数についての非自明な意味論的性質を、一般に判定するプログラムは存在しない。
> **$S^m_n$ 定理:** プログラムの一部の変数を定数として焼き込んだ新しいプログラムを、機械的・効果的に作れる。

L0 ＝ Mathlib にある宣言を参照し、その型が下の主張と一致することを Lean に確かめさせる
（このリポジトリで新しく証明したものはない）。参照する宣言：

* `Nat.Partrec.Code.fixed_point`（`Mathlib/Computability/PartrecCode.lean`）
* `ComputablePred.rice`（`Mathlib/Computability/Halting.lean`）
* `Nat.Partrec.Code.eval_curry`（`Mathlib/Computability/PartrecCode.lean`）。`S^m_n` の `m = n = 1` 版に当たる。
-/

namespace MathGarden.MathHistoryMeaningCatchesUpLater

open Nat.Partrec (Code)

/- 再帰定理：計算可能な `f : Code → Code` について `eval (f c) = eval c` となる `c` がある。 -/
example {f : Code → Code} (hf : Computable f) : ∃ c : Code, Code.eval (f c) = Code.eval c :=
  Nat.Partrec.Code.fixed_point hf

/- Rice の定理：`eval c ∈ C` を判定する計算可能な述語があり、`C` に属する部分再帰関数 `f` があるなら、
任意の部分再帰関数 `g` も `C` に属する（つまり性質 `C` は自明）。 -/
example (C : Set (ℕ →. ℕ)) (h : ComputablePred fun c => Code.eval c ∈ C) {f g : ℕ →. ℕ}
    (hf : Nat.Partrec f) (hg : Nat.Partrec g) (fC : f ∈ C) : g ∈ C :=
  ComputablePred.rice C h hf hg fC

/- `S^m_n` 定理（`m = n = 1`）：プログラム `c` の第1引数を `n` に固定したプログラム `curry c n` が作れる。 -/
example (c : Code) (n x : ℕ) : Code.eval (Code.curry c n) x = Code.eval c (Nat.pair n x) :=
  Nat.Partrec.Code.eval_curry c n x

end MathGarden.MathHistoryMeaningCatchesUpLater
