# Blind reading of SAP.P044.T13

This file was written before opening `claims.json` or `record.json`.

## Statement and complete dependency expansion

The declaration is at `SAP/P044/Challenge/Part1.lean:89–95`; its proposition is
`T13Statement` at `SAP/P044/Defs/Part8.lean:62–64`.

Quantifiers, in their actual order:

1. For every natural number `N`;
2. for every function `A : Fin N → Fin N → Bool`;
3. assuming `A i i = false` for every `i : Fin N`;
4. assuming `0 < N`;
5. it is **not** the case that, for every `i : Fin N`, the measure
   `baselineLaw (degreeScale A i : ℝ)` equals `halfNormalLaw`.

Here `Fin N` is the finite type of natural numbers strictly below `N`, with its
usual finite enumeration. `Adjacency N` (`Defs/Part1.lean:21`) is precisely the
Boolean function type in item 2. There is no symmetry hypothesis, no prohibition
on isolated vertices, no probabilistic law on `A`, and no fixed network size.
The diagonal hypothesis is the only graph condition. The conclusion is equivalent
to existence of at least one vertex whose two measures differ; it does not assert
the stronger statement that the measures differ at every vertex.

For each vertex `i`, define these natural numbers, expanding the definitions at
`Defs/Part2.lean:65–72`:

- `d_i = ∑ (j : Fin N), (if A i j = true then 1 else 0)`.
- `q_i` is the cardinality of the finite set of `j : Fin N` such that `j ≠ i`
  and there exists `k : Fin N` with `A i k = true` and `A k j = true`.
  Each endpoint is counted once, regardless of the number of two-step walks.
  An endpoint adjacent directly to `i` is still counted if such a walk exists.
- `a_i = d_i + q_i + d_i q_i`, then cast from the natural numbers into the reals.

`baseline a g e` (`Defs/Part2.lean:74`) is the real number `a |g| + e`.

`normalPair` (`Defs/Part2.lean:79–80`) is the product probability measure
`γ₀ ⊗ γ₁`, where `γ₀ = gaussianReal 0 1` and
`γ₁ = gaussianReal 1 (1/16)`. Mathlib's second Gaussian parameter is **variance**.
Thus the coordinate random variables are independent, with laws
`G ~ Normal(0,1)` and `E ~ Normal(1,1/16)` (standard deviation `1/4` for `E`).
For example, the product assigns a Borel rectangle `S × T` the value
`γ₀(S) γ₁(T)`.

`baselineLaw a` (`Defs/Part2.lean:82–83`) is the pushforward of this product by
the continuous function `(g,e) ↦ a |g| + e`. For every Borel set `S ⊆ ℝ`,

`baselineLaw a (S) = (γ₀ ⊗ γ₁) {(g,e) | a |g| + e ∈ S}`.

`halfNormalLaw` (`Defs/Part2.lean:85`) is the pushforward of `γ₀` by absolute
value: its value at `S` is `γ₀ {g | |g| ∈ S}`. It is the actual absolute standard
normal probability law on the reals, with support in `[0,∞)`.

At the Mathlib level, for either strictly positive variance `v`, `gaussianReal μ v`
is Lebesgue measure with density

`x ↦ (sqrt (2 π v))⁻¹ exp (−(x−μ)² / (2v))`,

converted to a nonnegative extended-real density. In particular the two
Gaussian measures here are ordinary nondegenerate probability measures.
All equality and inequality assertions in the conclusion concern complete Borel
measures, rather than densities, moments, samples, or approximations.

The remaining closure declaration, `normalPair._proof_1`, was inspected by
compiling `scratch/BlindCheck.lean` with `#print` and proof printing enabled.
It proves `(15 + 1).AtLeastTwo` using `Nat.instAtLeastTwoHAddOfNat 15`.
It is elaboration support for the denominator numeral `16`, not an extra
statistical or graph assumption. Every entry in `closure.json` has been read.

In plain mathematics the assertion is therefore:

For every positive finite size and every loopless Boolean adjacency array of that
size, not all of the laws of `a_i |G| + E`, with the independent Gaussian laws
specified above, are the law of `|G|`.

The docstring calls this a refutation of the printed baseline-law claim, says only
that conjunct is negated, and explicitly leaves identification of the ideal model
with the generator source code to external provenance. The proposition itself
contains no identification with source code and no other generator assertions.

## Totalization and junk-value audit

- **Finite sums, filters, and empty sets:** empty sums and cardinalities are zero.
  In particular a vertex with no outgoing edges has `d_i = q_i = a_i = 0`, giving
  baseline law exactly `Normal(1,1/16)`. This is ordinary arithmetic with a real
  noise term, not a division-by-zero surrogate. Empty endpoint sets are legitimate.
- **Empty index type:** `Fin 0` is empty, but `0 < N` excludes it. Without that
  condition the negation of the universal conclusion would fail. The hypotheses
  permit positive sizes and loopless graphs; nothing forces an empty domain.
- **Casts and arithmetic:** the scale is a finite natural number cast injectively
  into the reals. All sums and products are exact; there is no overflow, truncated
  subtraction, integer truncation, or partial indexing. `j ≠ i` is an inequality of
  valid finite indices, not subtraction of their labels.
- **Division:** `1/16` is formed in the nonnegative reals with the nonzero
  denominator `16`. In the Gaussian density the denominators are `2v` and
  `sqrt (2πv)` with `v = 1` or `1/16`, so neither is zero.
- **Square roots and powers:** the Gaussian normalization uses square roots of
  strictly positive real numbers. Squaring in the density is an ordinary natural
  power. There is no logarithm, fractional `rpow`, or use of a square root outside
  the positive domain.
- **Zero-variance Gaussian branch:** Mathlib defines `gaussianReal μ 0` to be
  the point mass at `μ`. Neither occurrence here uses variance zero.
- **Pushforward totalization:** the inspected Mathlib implementation of
  `Measure.map` can return a default Dirac mass for a non-almost-everywhere-
  measurable function and a nonzero source measure (and zero for a zero source
  measure). Both functions used here are continuous on the usual real Borel
  spaces, so this fallback is never used. The source measures are probability
  measures. The product measures are finite, hence σ-finite.
- **Integrals and other totalized operators:** the assertion defines no Bochner
  expectations, sample means, variances, `toReal` of extended values,
  `sInf`/`sSup`, limits, `limsup`/`liminf`, or partial functions. Lebesgue measure
  with Gaussian density is the standard genuine probability law; no undefined
  expectation is being set to zero. No junk-value convention changes the reading.

Blind scratch inspection compiled successfully. Its only warning concerns naming
an automatically generated auxiliary proof.
