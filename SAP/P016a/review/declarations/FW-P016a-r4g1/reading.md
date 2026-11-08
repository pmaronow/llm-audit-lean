# Blind reading

This file was saved before opening `claims.json` or `record.json`.

## SAP.P016a.T6 (P016-T6)

Location: `SAP/P016a/Challenge/Part1.lean:25–28`. Fingerprint:
`e4ed81ac50db315562603137361f9be9a52dbe9890e51ff6ea15f4c1abadd12e`.

### Mathematical statement, with SAP definitions unfolded

The statement is the conjunction of the following two assertions.

1. Universally quantify, in this order:
   - a natural number n and a proof that 2 ≤ n;
   - a type Ω with a finite enumeration (`Fintype Ω`) and at least one element;
   - an arbitrary function assign : Ω → (Fin n → Bool), where Fin n is the set of natural numbers less than n;
   - a real matrix Γ : Fin n → Fin n → ℝ;
   - the assumptions that Γ has nonnegative entries, is symmetric, has zero diagonal, and satisfies Γ(i,k) ≤ Γ(i,j) + Γ(j,k) for all i,j,k;
   - an arbitrary function g : (Fin n → ℝ) → (Fin n → ℝ);
   - the assumption described below that g has sample variance one on the exposure vector for every ω ∈ Ω;
   - a baseline vector y₀ : Fin n → ℝ, an outcome table y : Ω → (Fin n → ℝ), and real numbers b₁,b₂;
   - the generation identity below, for every ω and i.

   Write zω(i) = assign(ω)(i), B(true) = 1, B(false) = 0, and

   eω(i) = ∑_{j ∈ Fin n} Γ(i,j) B(zω(j)),
   hω = g(eω),
   mω = (∑_{i ∈ Fin n} hω(i))/(n : ℝ).

   The assumption on g is, for every ω,

   (∑_{i ∈ Fin n} (hω(i) − mω)²)/((n : ℝ) − 1) = 1.

   The generation assumption is, for every ω and i,

   y(ω)(i) = y₀(i) + b₁ B(zω(i)) + b₂ hω(i).

   The conclusion is, for every ω, equality of the following two real vectors:

   (i ↦ y(ω)(i) − B(zω(i)) b₁ − b₂ hω(i)) = y₀.

   The conclusion therefore asserts pointwise algebraic recovery using the same exposure vector and coefficients as in the generation assumption. The subtraction uses B(z)b₁ whereas generation uses b₁B(z); these coincide over ℝ.

2. Independently, for every real number p, the proposition called printedReject(p), defined as p < (1 : ℝ)/20, is equivalent to p < (1 : ℝ)/20.

There is no probability measure on Ω, uniformity assertion, injectivity or completeness assumption on assign, fixed treatment count, or requirement that both treatment groups occur. Repeated assignments are allowed. Γ need not separate distinct units: this is a pseudometric distance matrix, with no requirement Γ(i,j) > 0 for i ≠ j. No affine, componentwise, centering, monotonicity, invertibility, or raw-exposure-dependence condition is imposed on g beyond its type and the displayed variance assumption. In particular a constant map to a fixed unit-variance vector is allowed. The theorem does not construct g or assert that every chosen normalization satisfies the variance assumption.

The p assertion has no condition 0 ≤ p ≤ 1 and does not construct a p-value, statistic, reference law, or rejection proportion. Both sides simply use the same strict inequality on ℝ.

### Complete closure inventory

Every declaration listed for T6 in `closure.json` was read in source; the two synthetic numeral proofs were additionally inspected by Lean `#print` in `scratch/Blind.lean` (successful compilation).

| Declaration | Source | Meaning |
| --- | --- | --- |
| Outcome | `Defs/Part1.lean:10` | Fin n → ℝ |
| Assignment | `Defs/Part1.lean:12` | Fin n → Bool |
| bit | `Defs/Part1.lean:14` | Boolean indicator B, taking values 1 and 0 in ℝ |
| pooledMean | `Defs/Part1.lean:25` | Finite sum divided by the real cast of n |
| exposureSum | `Defs/Part2.lean:11` | Row-i weighted sum ∑j Γ(i,j) B(z(j)) |
| sampleVariance | `Defs/Part2.lean:31` | Sum of squared deviations from pooledMean, divided by (n : ℝ) − 1 |
| applicationAdjust | `Defs/Part2.lean:43` | Pointwise subtraction Y(i) − B(Z(i))b₁ − b₂e(i) |
| printedReject | `Defs/Part2.lean:49` | p < (1 : ℝ)/20 |
| printedReject._proof_1 | `Defs/Part2.lean`, generated | Proof `(19 + 1).AtLeastTwo`, built by `Nat.instAtLeastTwoHAddOfNat 19`; supports the numeral 20, with no additional mathematical hypothesis |
| IsDistanceMatrix | `Defs/Part2.lean:64` | Nonnegativity, symmetry, zero diagonal, triangle inequality |
| T6Statement | `Defs/Part5.lean:11` | The conjunction expanded above |
| T6Statement._proof_1 | `Defs/Part5.lean`, generated | The same numeral-support proof `(19 + 1).AtLeastTwo` |

All `Defs/...` paths in this table are under `SAP/P016a/`.

### Totalization and edge cases

- Real division is total, so a/0 = 0 in Lean. In pooledMean the denominator is n, and in sampleVariance it is (n : ℝ) − 1. Both denominators are strictly positive under 2 ≤ n, so this convention cannot affect T6. Outside its hypotheses, pooledMean on n = 0 is the empty sum divided by zero, hence 0; sampleVariance on n = 0 is 0/(−1) = 0, and on n = 1 is 0/0 = 0.
- The subtraction `(n : ℝ) − 1` occurs in ℝ, not in ℕ; there is no truncated natural subtraction. The cast from ℕ to ℝ is the usual exact nonnegative integer cast. Numerals, including 20, have their ordinary real values; 20 is nonzero.
- All sums are finite sums over `Fin n`. Such a sum is 0 for an empty index set, but n ≥ 2 excludes an empty unit set. `Nonempty Ω` excludes a vacuous design-index quantifier. A fixed design and g can fail the variance hypothesis, in which case that particular implication has no application; satisfiability needs a separate check.
- Boolean assignment is total. `bit` has no exceptional branch or default outside true and false. All vectors, matrices, and g are total functions, with no partial-function default values.
- Γ may have off-diagonal zeros, and assign may treat nobody or everybody; these cases are permitted, rather than exceptional-value conventions. Unit variance is required of g's output, not of raw exposure, so a constant raw vector alone does not make the hypothesis impossible for an arbitrary g.
- No logarithm, square root, real power, Bochner integral, probabilistic mean, extended-real conversion, infimum, supremum, limit superior, limit inferior, or choice of a default optimizer occurs in the statement's dependency closure. The power in sampleVariance is the ordinary square in ℝ.

### Docstring reading

The docstring describes recovery for any g satisfying the specified across-unit sample-variance condition and identifies the strict printed rejection convention. Its restriction paragraph explicitly limits the result to algebraic consistency, omits an affine-normalization condition and a claim of linearity in raw distance sums, fixes the variance convention to divisor n−1 separately on every assignment, and omits the full regression/testing procedure and empirical rejection proportions. Whether that is an accurate restriction of the canonical claim is intentionally left for the next stage.
