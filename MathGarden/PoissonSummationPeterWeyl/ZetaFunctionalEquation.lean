import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# 記事 `Poisson和公式は格子で割ったPeter-Weylである_関数等式はどこから来るのか_2026-08-15` §1：ゼータの関数等式（L0）

記事の文（記事から写す）：

> $\zeta(s)$ の関数等式 $\xi(s) = \xi(1-s)$ は、たいてい「Riemann が示した驚くべき対称性」として登場する。

L0 ＝ Mathlib にある宣言を参照し、その型が下の主張と一致することを Lean に確かめさせる
（このリポジトリで新しく証明したものはない）。参照する宣言：

* `completedRiemannZeta_one_sub`（`Mathlib/NumberTheory/LSeries/RiemannZeta.lean`）：
  完備ゼータ `Λ(s) = π^{-s/2} Γ(s/2) ζ(s)` について `Λ(1 - s) = Λ(s)`（全ての複素数 `s`）。

Mathlib の `completedRiemannZeta` は `Λ(s)`（極をもつ）で、記事の `ξ(s)`（`s(s-1)/2` を掛けて極を消したもの）とは
定数でない因子だけ違う。記事の `ξ` そのものを述べた宣言は参照していない。
-/

namespace MathGarden.PoissonSummationPeterWeyl

/- 完備ゼータ関数の関数等式 `Λ(1 - s) = Λ(s)`。 -/
example (s : ℂ) : completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

end MathGarden.PoissonSummationPeterWeyl
