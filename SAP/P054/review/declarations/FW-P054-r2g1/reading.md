# Blind reading

This document was written from `closure.json`, all four Defs/Challenge source
files, and Lean `#print` output, before opening `claims.json` or `record.json`.
The theorem bodies are certified externally as specified in the task; this
reading concerns their elaborated statements.

## SAP.P054.T1

Source: `SAP/P054/Challenge/Part1.lean:6-12`; its proposition is
`SAP/P054/Defs/Part1.lean:50-62`.

**Objects, quantifiers, and hypotheses.** For every natural number `N`, assume
`2 ≤ N`. For every three functions `d,w,y : Fin N → ℝ`, assume, in this order:

1. For each index `i`, `d i = 0` or `d i = 1`.
2. For each index `i`, `y i = 0` or `y i = 1`.
3. For each index `i`, `0 < w i`.
4. The real sum `n = ∑ i : Fin N, d i` is strictly positive.

Here `Fin N` is the finite type of natural indices less than `N`, and each sum
is Mathlib's finite sum over every element of that type. Write `a = (N : ℝ)`
for the natural-to-real cast. The following notation expands *all* SAP
definitions in the statement to real arithmetic and finite sums:

- `groupCount d`: `n = ∑ i, d i`.
- `groupWeight d w`: `W = ∑ i, d i * w i`.
- `weightedProportion d w y`: `p = (∑ i, d i * w i * y i) / W`.
- `ratioResidual d w y i`: `r_i = d i * w i * (y i - p)`.
- `squaredWeightTerm d w y`:
  `Q = (∑ i, d i * (w i)^2 * (y i - p)^2) / W^2`.
- `linearisationVariance d w y`:
  `L = ((∑ i, (d i * w i * (y i - p))^2) / (a * (a - 1))) / (W/a)^2`.
- `referenceVariance d w y`: `V0 = p * (1 - p) / n`.

These letters are abbreviations only: in each formula substitute the displayed
finite sums for `n`, `W`, and `p`. There is no probability space, sampling law,
expectation, or population parameter in the proposition.

**Conclusion and quantifier order.** Under all the preceding universally
quantified data and assumptions, the statement is a conjunction of:

1. `∑ i, d i * w i * (y i - p) = 0`.
2. `L = (a / (a - 1)) * Q`.
3. For **every** real number `c`, if `0 < c` and the whole function `w` is
   identically `c` (including indices with `d i = 0`), then both
   `Q = p * (1 - p) / n` and
   `L = (a / (a - 1)) * (p * (1 - p) / n)`.

The positive constant `c` is quantified inside the last conjunct, after all
data and hypotheses. Neither existence of a constant weight nor equality of
weights is assumed for the first two conclusions. The correction factor uses
the full index count `N`, not the selected count `n`. Selection indicators and
responses are required to be binary even on unselected indices; weights must
be positive there too. A selected count of one is allowed.

**Closure read.** `T1Statement` (line 50), `groupCount` (14), `groupWeight`
(17), `linearisationVariance` (33), `ratioResidual` (24), `referenceVariance`
(38), `squaredWeightTerm` (28), and `weightedProportion` (20), all in
`SAP/P054/Defs/Part1.lean`, were read completely. The source line numbers in
the closure point to the declarations' docstrings. The Challenge docstring
describes conditional reconstruction identities and explicitly disclaims a
historical procedure, survey-design validity, and national interval coverage.

**Junk-value and boundary conventions.** All divisions are divisions in `ℝ`;
Mathlib defines `x / 0 = 0`. In isolation, `weightedProportion` permits `W=0`
and returns zero; `squaredWeightTerm` also returns zero when `W=0`;
`referenceVariance` returns zero when `n=0`; and `linearisationVariance`
returns zero for `N=0`, `N=1`, or `W=0`. `ratioResidual` inherits any zero-weight
ratio convention. None of these cases occurs in T1: binary `d` and `n>0`
give at least one selected index, so positive weights imply `W>0`; `N≥2`
implies `a>0` and `a-1>0`. Thus `n`, `W`, `W^2`, `a*(a-1)`, `(W/a)^2`, and
`a-1` are all nonzero. The equal-weight branch has a positive `c`, and it is
consistent with the main hypotheses.

Every subtraction here is real subtraction, including `(N : ℝ) - 1`, not
truncated natural subtraction. The natural-to-real cast is the exact
embedding, and the squares are natural powers with exponent two. An empty
finite type would give an empty sum of zero, but `N≥2` excludes it; binary
`d` and `n>0` also exclude an empty selected set. There are no logarithms,
square roots, real powers, integrals, nonintegrable means, extended-real
conversions, infima/suprema, limits, or default-valued partial functions.

The hypotheses are visibly consistent: take `N=2`, all `d_i=1`, all `w_i=1`,
and responses `y_0=0`, `y_1=1`. This also makes the equal-weight branch
applicable and the variances nonzero. A Lean instance is to be compiled at
the next stage.

## SAP.P054.T2

Source: `SAP/P054/Challenge/Part1.lean:14-19`; its proposition is
`SAP/P054/Defs/Part1.lean:64-75`.

**Objects, quantifiers, and hypotheses.** For every natural number `N`, assume
`2 ≤ N`. For every `d,w,y : Fin N → ℝ`, assume, in order:

1. Each `d_i` is zero or one.
2. Each `y_i` is zero or one.
3. Every `w_i` is strictly positive.
4. `2 ≤ ∑ i : Fin N, d_i`, with this inequality in `ℝ`.

Thus there are at least two selected indices. There is no assumption of equal
weights, independence, a regression-error model, or a sampling design.

To unfold every SAP definition in this statement, set

- `n = ∑ i : Fin N, d_i` (`groupCount`),
- `W = ∑ i : Fin N, d_i*w_i` (`groupWeight`),
- `p = (∑ i : Fin N, d_i*w_i*y_i) / W` (`weightedProportion`),
- `S = ∑ i : Fin N, d_i*w_i*(y_i-p)^2`
  (`weightedResidualSumSquares`),
- `C = S / ((n-1)*W)` (`classicalWlsVariance`),
- `V0 = p*(1-p)/n` (`referenceVariance`).

All sums are Mathlib finite sums, with ordinary real arithmetic. These
abbreviations are fully specified by the sums above and carry no additional
statistical content.

**Conclusion.** For every set of data satisfying all preceding assumptions,
all three equalities hold:

1. `S = W*p*(1-p)`.
2. `C = p*(1-p)/(n-1)`.
3. `C = (n/(n-1))*(p*(1-p)/n)`.

The correction factor and the divisor `n-1` use the selected count. The defined
quantity `C` is the stated classical intercept-only WLS variance formula;
the theorem does not claim that it is an actual design variance or that its
statistical assumptions hold.

**Closure read.** `T2Statement` (line 64), `classicalWlsVariance` (46),
`groupCount` (14), `groupWeight` (17), `referenceVariance` (38),
`weightedProportion` (20), and `weightedResidualSumSquares` (42), all in
`SAP/P054/Defs/Part1.lean`, were read completely. The generated declaration
`SAP.P054.T2Statement._proof_1` (closure line 0) was inspected by Lean
`#print`: its type is `(1 + 1).AtLeastTwo` and its value is
`Nat.instAtLeastTwoHAddOfNat 1`. It provides the implementation-level instance
for the numeral two, and contributes no substantive assumption or conclusion.
The Challenge docstring describes the three conditional algebraic identities
and disclaims historical use and the inverse-variance assumptions required
for classical standard errors.

**Junk-value and boundary conventions.** Real division has `x/0=0`.
`weightedProportion` is defined even for `W=0`, `referenceVariance` even for
`n=0`, and `classicalWlsVariance` even for `(n-1)*W=0`; the latter then returns
zero. `weightedResidualSumSquares` inherits the ratio's convention if `W=0`.
These conventions cannot affect T2: binary `d` and `n≥2` guarantee a selected
index, positive weights imply `W>0`, and `n≥2` implies `n>0` and `n-1>0`.
Consequently all displayed denominators are nonzero. Subtraction is real
subtraction, with no natural truncation. The index type cannot be empty, and
the selected set has at least two elements. Any natural casts are exact.
There are no logarithms, square roots, real powers, integrals, nonintegrable
means, extended-real conversions, infima/suprema, limits, or default-valued
partial functions.

The hypotheses are consistent with nonzero quantities: `N=2`, `d_i=1`,
`w_i=1`, `y_0=0`, and `y_1=1` gives `n=W=2`, `p=1/2`, `S=1/2`,
`C=1/4`, and `V0=1/8`. A Lean instance is to be compiled at the next stage.
