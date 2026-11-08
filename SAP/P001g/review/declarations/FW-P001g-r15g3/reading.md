# Blind reading

This file was saved before opening either `claims.json` or `record.json`.
Only the Challenge declarations, their definitions, `closure.json`, and Mathlib
notions were used. The three targets and all entries of their Lean-computed
closures were read. The auxiliary closure declarations were also inspected with
`#print` in `scratch/BlindCheck.lean`.

Throughout, a measurable space Ω with a measure μ satisfying
`IsProbabilityMeasure μ` is a probability space. Write P(A) = μ(A), identified
with its finite real value, and E[Z] = the real Bochner integral of Z against μ.
Statements below quantify over all their displayed data, in the order given.

## SAP.P001g.T128

Source: `SAP/P001g/Challenge/Part1.lean:74–81`; underlying statement:
`SAP/P001g/Defs/Part6.lean:53–61`.

For every probability space (Ω, μ), every pair of sequences of real functions
Tₙ, Vₙ : Ω → ℝ, proofs that each Tₙ and Vₙ is measurable, and a proof that
Vₙ(ω) ≥ 0 for every natural n and every ω, take real numbers θ, φ, α, z, in
that order. Assume:

1. φ > 0.
2. 0 < α < 1.
3. The standard Gaussian probability of (-∞, z] is 1 − α/2.
4. For every real x at which the distribution function of N(0, φ²) is
   continuous, P(√n(Tₙ − θ) ≤ x) tends to N(0, φ²)((-∞, x]).
5. For every ε > 0, P(|nVₙ − φ²| ≥ ε) tends to zero.

Then there exists a real c such that c ≥ 1 − α and

    P(Tₙ − z√Vₙ < θ < Tₙ + z√Vₙ) → c.

The existential c is inside all the preceding universal quantifiers. The
statement asserts existence of a limit and its lower bound, not explicitly
c = 1 − α. Natural sample size zero is included in the sequences, but the
conclusion concerns n → ∞. No iid sampling hypothesis is imposed on Tₙ or Vₙ;
their asserted limits are the hypotheses. Nothing requires Vₙ > 0 at a fixed
positive sample size. The interval can therefore be empty at such a size.

Every SAP definition in the closure unfolds as follows:

- `prob μ A` = `(μ A).toReal`.
- `cdf μ Z x` = `(μ {ω | Z ω ≤ x}).toReal`.
- `CP μ Z c` says that for every real ε > 0, the real measures of
  `{ω | ε ≤ dist (Z n ω) c}` tend to 0. For real-valued functions this distance
  is |Zₙ − c|.
- `CD μ Z ν` says that for each continuity point x of
  t ↦ `(ν (Set.Iic t)).toReal`, `(μ {ω | Z n ω ≤ x}).toReal` tends to
  `(ν (Set.Iic x)).toReal`. Thus it is the real-line CDF formulation of
  convergence in distribution.
- `VarianceConsistent μ V v` means `CP μ (fun n ω => (n : ℝ) * V n ω) v`.
  It concerns a sampling-variance estimate scaled by n, not an unscaled
  estimate of the limiting variance.
- `T128Statement._proof_1` is `∀ φ : ℝ, 0 ≤ φ²`, used in constructing the
  nonnegative Gaussian variance parameter.
- `T125Statement._proof_1` is the numeral instance `(1 + 1).AtLeastTwo`.
  It adds no hypothesis or mathematical assertion.

Junk-value audit:

- `ENNReal.toReal ∞ = 0` is potentially hazardous in `prob` generally, but
  every measure used here is a probability measure, including both Gaussian
  laws. It cannot occur here.
- Measures apply to all sets by their outer-measure values. Here the relevant
  events are measurable because Tₙ and Vₙ are measurable and square root is
  continuous. The reference Gaussian CDF is also measurable and continuous.
- `Real.sqrt x = 0` for x ≤ 0. Natural casts n ≥ 0 and the nonnegative Vₙ
  keep all roots in the ordinary domain; Vₙ = 0 gives an actual empty open
  interval rather than an undefined root. The theorem allows this.
- N(0, 0) in Mathlib is a Dirac measure, but φ > 0 rules out that degeneration
  in the limiting law; the standard Gaussian also has positive variance.
- α/2 has nonzero denominator. Natural-to-real casts are exact. There is no
  truncated subtraction, nonintegrable integral, `log`, `rpow`, partial
  function, extremum, limsup, or liminf in this closure.
- An empty Ω cannot carry the stipulated probability measure.

The docstring explicitly disclaims strict ordering of endpoints at every
positive sample size, and describes the possible empty finite-sample sets.

## SAP.P001g.T129

Source: `SAP/P001g/Challenge/Part1.lean:83–86`; underlying statement:
`SAP/P001g/Defs/Part6.lean:63–104`.

The theorem is a conjunction of two independently universally quantified
assertions. The two probability spaces need not be the same.

### First conjunct: actual-product MLE consistency

For every probability space (Ω, μ), natural dimensions K and τ, sequences
Xᵢ : Ω → ℝᴷ and Yᵢ : Ω → ℝ, assume the pairs (Xᵢ, Yᵢ) are iid: each pair is
measurable; the family is independent in Mathlib's `iIndepFun` sense; and each
pair has the same pushforward measure as pair zero (with the corresponding
almost-everywhere measurability supplied by `IdentDistrib`).

Next quantify over a probability measure νX on ℝᴷ, an `SFinite` measure κ on
ℝ, a real function g(y, x, t) on ℝ × ℝᴷ × ℝᵗᵃᵘ, a parameter set Θ ⊆ ℝᵗᵃᵘ,
a proof that Θ is compact, and θ ∈ Θ. Assume:

1. For each t ∈ Θ, (x, y) ↦ g(y, x, t) is measurable.
2. For each t ∈ Θ, every y and x have g(y, x, t) ≥ 0.
3. For each t ∈ Θ and every x, ∫ g(y, x, t) dκ(y) = 1, expressed as a
   nonnegative extended integral of `ENNReal.ofReal (g y x t)`.
4. The law of (X₀, Y₀) is the measure with density g(y, x, θ) relative to
   νX ⊗ κ.
5. For every t ∈ Θ, log g(Y₀, X₀, t) is integrable under μ.
6. For every t ∈ Θ, g(Y₀, X₀, t) > 0 μ-almost surely. The null set may
   depend on t; this is not a single joint assertion for all t outside one
   fixed null set.
7. M(t) = E[log g(Y₀, X₀, t)] is continuous on Θ.
8. For every t ∈ Θ, M(t) ≤ M(θ), and equality implies t = θ.

Next quantify over an estimator sequence Tₙ : Ω → ℝᵗᵃᵘ. Assume each Tₙ is
measurable, every Tₙ(ω) belongs to Θ, and for every n, ω, t ∈ Θ,

    ∏_{i=0}^{n−1} g(Yᵢ(ω), Xᵢ(ω), t)
      ≤ ∏_{i=0}^{n−1} g(Yᵢ(ω), Xᵢ(ω), Tₙ(ω)).

Finally quantify over a real function Δ : ℕ → Ω → ℝ and assume, for every
n, ω, t ∈ Θ,

    | n⁻¹ ∑_{i=0}^{n−1} log g(Yᵢ(ω), Xᵢ(ω), t) − M(t) | ≤ Δₙ(ω),

and, for every ε > 0, P(|Δₙ| ≥ ε) → 0. There is no separate explicit
measurability hypothesis on Δ, although the docstring presupposes the usual
measurability conditions. Then for every ε > 0,

    P(dist(Tₙ, θ) ≥ ε) → 0.

The parameter distance is the PseudoMetricSpace distance on `Fin τ → ℝ`,
namely the finite sup metric. The uniform error bound is a premise, not a
conclusion of the iid or continuity assumptions. No assertion of a unique
sample maximizer is made, and the estimator is assumed given. Only unique
maximization of M is required.

### Second conjunct: maximum expected log likelihood

For every probability space (Ω, μ), natural dimensions K and τ, measurable
X : Ω → ℝᴷ and Y : Ω → ℝ, probability measure νX, `SFinite` κ, real g,
set Θ ⊆ ℝᵗᵃᵘ, and θ ∈ Θ, assume:

1. For every t ∈ Θ the same joint measurability, pointwise nonnegativity,
   and normalization in y for every x as above.
2. The law of (X, Y) is g(y, x, θ) times νX ⊗ κ.
3. For every t ∈ Θ, for (νX ⊗ κ)-almost every (x, y),
   g(y, x, θ) > 0 implies g(y, x, t) > 0.
4. For every t ∈ Θ, log g(Y, X, t) is μ-integrable.

Then, for every t ∈ Θ,

    E[log g(Y, X, t)] ≤ E[log g(Y, X, θ)],

with equality if and only if g(Y, X, t) = g(Y, X, θ) μ-almost surely.
This conjunct does not assume compactness, continuity, an iid sample,
identification, or the uniform envelope. Its equality is equality of density
values under the true observation law; it does not assert parameter equality.

Every SAP definition in the closure:

- `T129Statement` is the conjunction just expanded.
- `ProductMLEConsistencyStatement` and `ExpectedLogMaximumStatement` are
  precisely the first and second conjuncts above.
- `IID μ Z` is `(∀ i, Measurable (Z i)) ∧ iIndepFun Z μ ∧
  (∀ i, IdentDistrib (Z i) (Z 0) μ μ)`.
- `conditionalModelLaw νX κ g θ` is
  `(νX.prod κ).withDensity (fun xy => ENNReal.ofReal (g xy.2 xy.1 θ))`.
  For a measurable set A it integrates that density over A.
- `expectedLogLikelihood μ X Y g t` is the Bochner integral
  ∫ log(g(Y(ω), X(ω), t)) dμ(ω).
- `sampleLogLikelihood X Y g n ω t` is
  `(∑ i ∈ Finset.range n, log(g(Yᵢ(ω), Xᵢ(ω), t))) / (n : ℝ)`.
- `sampleLikelihood X Y g n ω t` is the actual finite product
  `∏ i ∈ Finset.range n, g (Y i ω) (X i ω) t`.
- `sampleMean Z n ω` is `(∑ i ∈ Finset.range n, Z i ω) / (n : ℝ)`.
- `mean` and `prob` are the Bochner integral and real measure given above;
  `CP` is the tail-probability criterion given under T128, now using the finite
  sup metric for the parameter and the ordinary absolute value for Δ.
- `ExpectedLogMaximumStatement._proof_1` is the standard Mathlib
  `OuterMeasureClass` instance for measures on ℝᴷ × ℝ. It adds no condition.

Junk-value audit:

- `Real.log 0 = 0`, and on negative inputs `Real.log x = log |x|`.
  Nonnegativity excludes negative model values at parameters in Θ. In the
  first conjunct, strict observed positivity is only parameterwise almost
  sure; zero values can still occur at null observations or for parameters
  selected depending on the observations. Thus the all-n/all-ω/all-t envelope
  literally uses totalized logs there. For any fixed true θ, iid sampling
  makes its finitely many observed density factors positive almost surely;
  actual-product maximization then forces the selected product to be positive
  almost surely for each n > 0. This prevents using log zero to turn an
  actual zero-likelihood estimator into a consistent MLE. The positive-support
  hypotheses also exclude log zero on positive-probability observations of
  every fixed parameter in the population calculations.
- In the second conjunct, the true density is positive under its own
  observation law almost surely; support domination ensures the same for
  every compared t. Thus observed logarithms have their ordinary meaning.
- Bochner integrals equal zero if integrability fails. Both conjuncts assume
  integrability of every population log they use. This convention cannot
  create a population-log maximum here.
- The product for n = 0 is the empty product 1; the sum is 0, and division
  by `(0 : ℝ)` makes the zero-sample average log exactly 0. The envelope must
  cover |M(t)| even at n = 0. Its real finite values therefore impose an
  actual bound. The asymptotic conclusions do not depend on size zero.
- `ENNReal.ofReal` truncates negative inputs to zero, but all model values
  used at admissible parameters are nonnegative. Nonnegative integrals are
  extended-valued; normalization requires the literal value 1, not `toReal`
  of an infinite integral.
- `prob` cannot take `toReal ∞`, since its μ is a probability measure.
  When a tail event involving Δ is not measurable, its literal probability
  is the outer-measure value. Other tail events are measurable.
- `Measure.map` has a zero default for non-a.e.-measurable maps, but all
  observation maps here are measurable by hypothesis or `IID`. It is not
  using that default.
- K = 0 or τ = 0 is allowed; a function from `Fin 0` is the unique empty
  vector. These are special permitted cases, not the only cases quantified.
  Θ is nonempty because it contains θ; Ω is nonempty because μ is a
  probability measure.
- No truncated subtraction, `sqrt`, `rpow`, `sInf`, `sSup`, limsup, or liminf
  occurs in these assertions. Real finite sums/products and natural casts
  have their usual meanings.

The docstring describes the actual-product premise and uniform error envelope
and lists several omitted conclusions. It does not claim these omitted
statements are proved here.

## SAP.P001g.T130

Source: `SAP/P001g/Challenge/Part1.lean:88–90`; underlying statement:
`SAP/P001g/Defs/Part6.lean:106–124`.

For every probability space (Ω, μ), sequences Yᵢ, Rᵢ : Ω → ℝ, proofs that
every Yᵢ and Rᵢ is measurable, real a and b with a ≤ b, assume:

1. For each i, a ≤ Yᵢ ≤ b μ-almost surely.
2. For each i, Rᵢ is either 0 or 1 μ-almost surely.
3. Both P(R₀ = 0) and P(R₀ = 1) are strictly positive.
4. The observable pairs (Yᵢ*, Rᵢ) are iid, where
   Yᵢ* = YᵢRᵢ − 99(1 − Rᵢ).

No independence of Rᵢ from Yᵢ is imposed. The unobserved outcomes across
different i need not themselves be iid: iid is required only for the
observable pairs. Set

    Lᵢ = Yᵢ* Rᵢ + a(1 − Rᵢ),
    Uᵢ = Yᵢ* Rᵢ + b(1 − Rᵢ),
    p₁ = P(R₀ = 1),  p₀ = P(R₀ = 0),
    m = (∫_{R₀ = 1} Y₀* dμ) / p₁,
    lower = m p₁ + a p₀,  upper = m p₁ + b p₀.

The conclusion, in order, is the conjunction

1. E[L₀] = lower.
2. E[U₀] = upper.
3. For every natural n > 0, E[n⁻¹∑_{i<n}Lᵢ] = lower and
   E[n⁻¹∑_{i<n}Uᵢ] = upper.
4. For every ε > 0, P(|n⁻¹∑_{i<n}Lᵢ − lower| ≥ ε) → 0.
5. For every ε > 0, P(|n⁻¹∑_{i<n}Uᵢ − upper| ≥ ε) → 0.

There is no additional assertion about sharpness of the bounds, identification
of E[Y₀], or a confidence region.

Every SAP definition in the closure:

- `T130Statement` is the proposition just expanded.
- `censored y r` is `y*r + (-99)*(1-r)`.
- `missingEndpoint ystar r c` is `ystar*r + c*(1-r)`.
- `conditionalMeanAt μ X Y x` is
  `(∫ ω in {ω | X ω = x}, Y ω ∂μ) / (μ {ω | X ω = x}).toReal`.
  This is conditioning on a positive-mass atom when that atom has positive
  probability; it is not a general regular conditional expectation.
- `mean`, `sampleMean`, `prob`, `CP`, and `IID` have the fully unfolded
  meanings stated above. The iid variables in this target are precisely the
  pairs with the -99 observation code.
- `censored._proof_1` is the numeral instance `(98 + 1).AtLeastTwo` and
  has no additional mathematical content.

Junk-value audit:

- `conditionalMeanAt` would be zero on a zero-probability conditioning atom
  because real division by zero is zero. The explicit support assumption
  p₁ > 0 rules this out. All sets `{R₀ = r}` are measurable.
- `prob` uses `toReal`, but μ is a probability measure, so no infinite value
  can be converted to zero.
- The integral is a Bochner integral. The bounded Yᵢ and binary Rᵢ imply
  that Yᵢ*, Lᵢ, and Uᵢ are bounded almost surely on a finite measure space,
  hence integrable. All finite sample means are also integrable. No
  nonintegrable-zero convention is used.
- The value -99 is a fixed missing-observation code, not a missing-value
  default built into Lean. It is multiplied by zero in Lᵢ and Uᵢ on Rᵢ = 0,
  and it vanishes on Rᵢ = 1. It may lie inside [a,b] without ambiguity,
  since Rᵢ is observed separately.
- The arithmetic formulas interpolate at nonbinary r, but such values occur
  only on null sets under the explicit assumptions and do not affect the
  conclusions. The countably many i allow one common full-measure set if
  needed.
- `sampleMean` at n = 0 is 0 by empty sum and division by zero. Unbiasedness
  is asserted only for n > 0, and convergence ignores n = 0.
- a = b is allowed. Both missingness probabilities are required positive,
  so the observable indicator is not degenerate. No empty Ω can satisfy
  the probability-measure assumption.
- There is no truncated natural subtraction, logarithm, root, `rpow`,
  extremum, limsup, liminf, or other partial operation in this closure.

The docstring describes unbiasedness at every positive sample size and
consistency for the displayed endpoints under iid observable pairs. It does
not mention the two positive missingness probabilities or boundedness
explicitly; whether they are inherited from the intended setting remains
to be compared after this blind reading.
