# Blind reading of the Lean statements

This file was written after reading only the supplied Defs and Challenge Lean files and the relevant Mathlib definitions, before opening `claims.json` or `record.json`. The Challenge contains exactly two theorem stubs, `SAP.P054.T1` and `SAP.P054.T2`. Each asserts a proposition defined in `SAP/P054/Defs/Part1.lean`; the aggregate files only import their respective Part1 files.

## Shared definitions and interpretation

Mathlib's `ℝ` is the real field. Sums here are `Finset.sum` over `Finset.univ`, hence ordinary finite sums with each index included once. `Fin N` has indices 0 through N−1. Natural numbers cast to reals have their usual values. Subtraction in these formulas is real subtraction, including `N−1` after casting and `n−1`; it is not truncated natural subtraction. Powers are ordinary squares. Division in Lean is total, with inverse zero equal to zero, but all denominators appearing in these theorems are nonzero under their hypotheses, as checked below. Equality of functions means equality at every index.

For a finite type I and functions d,w,y : I → ℝ, the SAP definitions expand to the following:

* `groupCount d`: n = Σᵢ dᵢ.
* `groupWeight d w`: W = Σᵢ dᵢwᵢ.
* `weightedProportion d w y`: p = (Σᵢ dᵢwᵢyᵢ)/W.
* `ratioResidual d w y i`: rᵢ = dᵢwᵢ(yᵢ−p).
* `squaredWeightTerm d w y`: Q = (Σᵢ dᵢwᵢ²(yᵢ−p)²)/W².
* `linearisationVariance d w y`, for I = Fin N: L = [(Σᵢ rᵢ²)/(N(N−1))]/(W/N)². All occurrences of N in this formula are real casts.
* `referenceVariance d w y`: V₀ = p(1−p)/n.
* `weightedResidualSumSquares d w y`: R = Σᵢ dᵢwᵢ(yᵢ−p)².
* `classicalWlsVariance d w y`: C = R/((n−1)W).

The general definitions alone do not enforce binary indicators, positive weights, or nonzero denominators. Those are theorem hypotheses. There is no probability space, stochastic independence, sampling design, model for the observations, variance operator, regression estimator, interval procedure, or coverage assertion encoded in these definitions. In particular, L and C are specified numerical formulas bearing variance-related names.

## `SAP.P054.T1`

The theorem asserts `T1Statement`, with this quantifier and implication order:

For every natural number N, if N ≥ 2, then for every three functions d,w,y : {0,…,N−1} → ℝ, if

1. for every index i, dᵢ = 0 or dᵢ = 1;
2. for every index i, yᵢ = 0 or yᵢ = 1;
3. for every index i, wᵢ > 0;
4. n = Σᵢdᵢ > 0;

then all of the following hold:

* Σᵢrᵢ = 0;
* L = [N/(N−1)] Q;
* for every real number c, if c > 0 and w equals the constant function i ↦ c at every index, then both Q = V₀ and L = [N/(N−1)] V₀.

The universal quantifier over c belongs only to the third conjunct. Thus the first two conclusions apply to arbitrary positive weight vectors. Constancy of weights is a conditional premise for the last two identities, not a premise for the entire theorem. Constancy and positivity are required on the whole Fin N, including indices with dᵢ = 0. The response is also binary on the whole Fin N. N is the full index count; n is the possibly smaller selected count.

The assumptions imply at least one dᵢ = 1 and therefore W > 0; N ≥ 2 gives N > 0 and N−1 > 0. Consequently W, W², n, N(N−1), and (W/N)² are all strictly positive. The allowed case n = 1 causes no zero denominator in T1 and necessarily gives p ∈ {0,1} and Q = L = V₀ = 0. The index type cannot be empty.

This is a deterministic identity theorem. It does not assert that L equals a statistical sampling variance, that the specified formulas were historically used, or that any confidence interval has its claimed coverage. Its docstring explicitly presents it as conditional reconstruction algebra.

## `SAP.P054.T2`

The theorem asserts `T2Statement`, with this quantifier and implication order:

For every natural number N, if N ≥ 2, then for every three functions d,w,y : {0,…,N−1} → ℝ, if

1. for every index i, dᵢ = 0 or dᵢ = 1;
2. for every index i, yᵢ = 0 or yᵢ = 1;
3. for every index i, wᵢ > 0;
4. n = Σᵢdᵢ ≥ 2;

then all of the following hold:

* R = W p(1−p);
* C = p(1−p)/(n−1);
* C = [n/(n−1)] V₀.

Here n is a real sum, but the binary dᵢ make it an integer count. There are at least two selected indices, W > 0, n > 0, and n−1 > 0. Thus the W used to define p, the n used to define V₀, and (n−1)W used to define C are all positive. N ≥ 2 also rules out an empty index type. There is no equal-weight premise in T2. Responses and positive weights are required at all indices, including unselected indices.

This is again a deterministic identity about the formula C defined above. It does not assert any error distribution, inverse-variance relation, standard-error validity, statistical compatibility criterion, or actual historical use of weighted least squares. The docstring describes compatibility with a reported calculation as an interpretation of this algebra, while expressly declining historical-use and inverse-variance assertions.

## Initial mathematical checks, independent of the claims

The hypotheses of both theorems can be jointly satisfied with N = 2, d₀ = d₁ = 1, w₀ = w₁ = 1, y₀ = 0, y₁ = 1. Then n = W = 2, p = 1/2, r = (−1/2,1/2), Q = V₀ = 1/8, L = 1/4, R = 1/2, and C = 1/4. This also exercises the equal-weight clause with c = 1 and gives positive, nondegenerate variance values.

Algebraically, Σrᵢ = Σdᵢwᵢyᵢ−pW = 0. Binary dᵢ give dᵢ² = dᵢ, so cancelling the positive N and W denominators gives L = [N/(N−1)]Q. Under constant weights, Q = (Σdᵢ(yᵢ−p)²)/n²; binary responses and Σdᵢyᵢ = np give Q = p(1−p)/n. Similarly, binary responses and Σdᵢwᵢyᵢ = pW give R = Wp(1−p), and the T2 identities follow by cancelling W. No hypothesis assumes one of the conclusions.

Mathlib sources consulted for interpretation: `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean` (finite sums and their notation), `Mathlib/Data/Fintype/Defs.lean` (finite exhaustive universal index set), `Mathlib/Data/Real/Basic.lean` and its `Mathlib/Basic/Real/Basic.lean` import (real arithmetic), and `Mathlib/Algebra/GroupWithZero/Defs.lean` (total inverse, including inverse zero).
