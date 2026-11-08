# Blind reading

Written after reading only the SAP definitions and Challenge files, plus the
Mathlib definitions they use. Neither `claims.json` nor `record.json` has been
opened at this stage.

## Objects and expanded definitions

The general helper definitions take a finite type `I` and functions
`d,w,y : I → ℝ`. Both theorem statements specialize the type to
`Fin N = {0,…,N−1}`. All sums below run over all these indices, exactly once
(`Finset.sum Finset.univ`), not just a separately supplied respondent set.
All displayed arithmetic, including subtraction, is real arithmetic; `N` is
cast from a natural number to a real number wherever it appears in a formula.

Write

* `n = Σᵢ dᵢ` (`groupCount`);
* `W = Σᵢ dᵢ wᵢ` (`groupWeight`);
* `p = (Σᵢ dᵢ wᵢ yᵢ)/W` (`weightedProportion`);
* `rᵢ = dᵢ wᵢ (yᵢ−p)` (`ratioResidual`);
* `S = (Σᵢ dᵢ wᵢ² (yᵢ−p)²)/W²` (`squaredWeightTerm`);
* `L = [(Σᵢ rᵢ²)/(N(N−1))]/(W/N)²`
  (`linearisationVariance`);
* `V₀ = p(1−p)/n` (`referenceVariance`);
* `Q = Σᵢ dᵢ wᵢ (yᵢ−p)²` (`weightedResidualSumSquares`);
* `C = Q/[(n−1)W]` (`classicalWlsVariance`).

Here squares have natural exponent two. Mathlib's `ℝ` is the usual real
ordered field, with total division (in particular, division by zero is zero).
The assertions below are subject to hypotheses that imply every displayed
denominator is nonzero; the helpers considered on their own have no such
guards. In particular, `N−1` and `n−1` in the formulas are real subtraction,
not truncated natural subtraction. The names of these definitions do not
themselves assert any statistical interpretation.

Mathlib sources followed: `Algebra/BigOperators/Group/Finset/Defs.lean`
(finite sums), `Data/Fintype/Defs.lean` and `Data/Fintype/Basic.lean`
(the universal finite set and `Fin.fintype`), `Data/Fintype/Fin.lean`
(identification of the indices with numbers less than `N`),
`Data/Real/Basic.lean` → `Basic/Real/Basic.lean`
(real arithmetic, casts, and the field instance), and
`Algebra/GroupWithZero/Defs.lean` (zero inverse).

## `SAP.P054.T1`

The theorem asserts the proposition `T1Statement`, which expands as follows.

For every natural number `N`, if `2 ≤ N`, then for every ordered triple of
functions `d,w,y : Fin N → ℝ`, if

1. for every index `i`, `dᵢ = 0` or `dᵢ = 1`;
2. for every index `i`, `yᵢ = 0` or `yᵢ = 1`;
3. for every index `i`, `wᵢ > 0`;
4. `n > 0`;

then all of the following hold together:

1. `Σᵢ rᵢ = 0`;
2. `L = [N/(N−1)] S`;
3. for every real number `c`, if `c > 0` and the entire weight function is
   the constant function `i ↦ c`, then both `S = V₀` and
   `L = [N/(N−1)] V₀`.

The quantifier over `c` is inside the conclusion for the previously fixed
`N,d,w,y`; equal weights are an additional premise only of the third conjunct.
The constant-weight condition is equality on every index, including those
with `dᵢ=0`. Positivity of weights and binary responses also apply to those
unselected indices. There are no random variables, probability distributions,
sampling plans, independence assumptions, coverage assertions, or claims of
historical procedure in this proposition. `N` is the full index size, whereas
`n` is the selected count. The assumptions imply `1 ≤ n ≤ N` and `W > 0`;
`N ≥ 2` makes the other variance denominators nonzero.

## `SAP.P054.T2`

The theorem asserts the proposition `T2Statement`, which expands as follows.

For every natural number `N`, if `2 ≤ N`, then for every ordered triple of
functions `d,w,y : Fin N → ℝ`, if

1. for every index `i`, `dᵢ = 0` or `dᵢ = 1`;
2. for every index `i`, `yᵢ = 0` or `yᵢ = 1`;
3. for every index `i`, `wᵢ > 0`;
4. `2 ≤ n` (an inequality of real numbers);

then all of the following hold together:

1. `Q = W p(1−p)`;
2. `C = p(1−p)/(n−1)`;
3. `C = [n/(n−1)] V₀`.

Again the binary and positive-weight assumptions apply to all `N` indices.
They imply `W > 0`, `n > 0`, and `n−1 > 0`. There is no equal-weight
hypothesis. There are no stochastic, inverse-variance-model, historical, or
confidence-interval assertions. The statement defines and relates algebraic
expressions; it does not identify `C` with a variance under an unstated
sampling or regression model.
