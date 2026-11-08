# Blind reading (stage 1)

This file was written before opening either `claims.json` or `record.json`.
I read all five Challenge declarations and every item in their `closure.json`
closures. `scratch/BlindPrint.lean` also checks the elaborated theorem types and
prints every generated auxiliary declaration in those closures.

Throughout, a probability space means a type with a sigma algebra and a Mathlib
measure `μ` satisfying `μ univ = 1`. An expectation is the real Bochner integral
`∫ ω, f ω ∂μ`. A probability of an event is `(μ event).toReal`. An almost-sure
assertion is with respect to Mathlib's `ae μ` filter. Real-valued measurable maps
use the Borel sigma algebra on the reals.

For clarity in the expansions below, saying that a function `m : E → ℝ` is a
conditional mean of `Z : Ω → ℝ` given `X : Ω → E` means exactly these four
conditions, with no additional SAP notion left implicit:

1. `m` is measurable;
2. `Z` is Bochner integrable under `μ`;
3. `ω ↦ m(X(ω))` is Bochner integrable under `μ`;
4. for every measurable `A ⊆ E`,
   `∫_{X⁻¹(A)} Z dμ = ∫_{X⁻¹(A)} m(X(ω)) dμ`.

This is the complete expansion of `IsConditionalMean` (Defs/Part1.lean:30–33).
Measurability of `X` is supplied separately in each statement using it.

## SAP.P001e.T82

Sources: Challenge/Part1.lean:52–54; Defs/Part3.lean:87–107;
Defs/Part1.lean:15–17,30–33,70.

The theorem is a conjunction. Its first conjunct universally quantifies, in
order, two types `Ω,E` (at independent universe levels), sigma algebras on both,
a probability measure `μ` on `Ω`, functions `X : Ω → E` and `R : Ω → Bool`, proofs
that both functions are measurable, and the assumptions
`0 < (μ {ω | R(ω)=true}).toReal < 1`.
No standard-Borel instance on `E` is explicitly required.

For each such input it asserts the existence, first, of `p : E → ℝ`, and then of
`κ : E → Measure Bool`, satisfying all the following:

- `p` is measurable and `0 ≤ p(x) ≤ 1` for every `x : E` (including points outside
  the observed support of `X`).
- Every `κ(x)` is a probability measure on the discrete measurable space `Bool`.
- For every measurable `B ⊆ Bool`, the extended-nonnegative-real function
  `x ↦ κ(x)(B)` is measurable.
- For every measurable `A ⊆ E` and measurable `B ⊆ Bool`,
  `μ {ω | X(ω)∈A ∧ R(ω)∈B} = ∫⁻_{x∈A} κ(x)(B) d(μ.map X)(x)`.
  The integral is a Mathlib nonnegative Lebesgue integral and `μ.map X` is the
  pushforward measure.
- For every `x`, `(κ(x) {true}).toReal = p(x)` and
  `∫ r, (if r then 1 else 0) dκ(x)(r) = p(x)`.
- For `Z(ω)=if R(ω) then 1 else 0`, `p` satisfies all four conditional-mean
  conditions expanded above: measurability, both integrabilities, and equality
  of the two set integrals on every `X⁻¹(A)`.
- Every `m : E → ℝ` satisfying those same four conditions for this `Z` has
  `m(X(ω))=p(X(ω))` for `μ`-almost every `ω`.
- For every real `q`, `¬(0 ≤ q ∧ q ≤ 1)` if and only if `1 < q ∨ q < 0`.

The second, independent conjunct of the theorem is
`∀ q : ℝ, 0 < q ∨ q < 1`. This is true for every real number; it does not assert
that a fitted probability actually violates `[0,1]`. The theorem does not
quantify an estimation procedure, a model, or a fitted regression.

The Challenge docstring describes existence of a bounded response-probability
version equal to the conditional mean, together with the characterization of
predictions outside `[0,1]`.

Junk-value audit: `(μ A).toReal` and `(κ(x) B).toReal` would turn infinity into
zero, but the probability-measure assumptions make all these masses finite.
The Bochner integral is zero for nonintegrable functions, but the response is
bounded, each `κ(x)` is a probability law, and conditional-mean predicates
expressly require integrability. The nonnegative integral permits infinity, but
the kernel identity and probability setting concern finite event masses. The
existential choices may differ off the law of `X`; their global probability and
range conditions rule out invalid off-support probabilities. There is no
division, truncated subtraction, logarithm, root, real power, extrema, limit,
or partial-function default here. An empty `Ω` cannot support `μ`; a measurable
map from a probability space also precludes an empty `E`. `Bool` is nonempty.

## SAP.P001e.T83

Sources: Challenge/Part1.lean:56–64; Defs/WholeW1.lean:191–210;
Defs/Part1.lean:15–17,30–41,56 and `recordedOutcome._proof_1`.

In order, the universal data are types `Ω,E` with sigma algebras, a probability
measure `μ` on `Ω`, a measurable `X : Ω → E`, and functions `Y,R : Ω → ℝ`.
The hypotheses are: `Y` and `R` are measurable; `Y` is integrable;
`R(ω)∈{0,1}` almost surely; both
`(μ {ω | R(ω)=0}).toReal > 0` and
`(μ {ω | R(ω)=1}).toReal > 0`.
Then, for every `p : E → ℝ`, the further hypotheses are:

- `p` is measurable, `R` and `p∘X` are integrable, and
  `∫_{X⁻¹(A)} R dμ = ∫_{X⁻¹(A)} p(X(ω)) dμ` for every measurable `A ⊆ E`;
- there is a real `ε>0` such that `ε < p(X(ω))` almost surely;
- `Y` and `R` are conditionally independent given `X`, rendered precisely as
  follows: for every pair of Borel sets `A,B ⊆ ℝ`, the Mathlib conditional
  expectation of `ω ↦ if Y(ω)∈A ∧ R(ω)∈B then 1 else 0`, with respect to
  `MeasurableSpace.comap X` of the sigma algebra on `E`, equals almost surely
  the product of the corresponding conditional expectations of the separate
  two event indicators. Each pair `A,B` has its own almost-sure equality.

Define the displayed real integrands purely arithmetically by
`Z(ω) = (Y(ω)R(ω) - 99(1-R(ω))) R(ω) / p(X(ω))` and
`W(ω) = Y(ω)R(ω)/p(X(ω))`.
The conclusion, in order, is: `Z` is integrable;
`∫ Y dμ = ∫ Z dμ`; and `∫ Z dμ = ∫ W dμ`.
Thus the recorded missing outcome is the sentinel `-99`, and multiplication
by the binary response erases it almost surely. No finite sample, fitted
propensity, or consistency claim occurs in this statement.

The Challenge docstring describes these expectation identities and
integrability under its stated MAR/positivity assumptions.

Junk-value audit: real division by zero is zero in Lean. The uniform lower
bound excludes it almost surely; arbitrary exceptional null-set values have
no effect on either integral. `W` is almost surely equal to the explicitly
integrable `Z`, so its integral also avoids the nonintegrable-integral default.
The unweighted outcome and the conditional-mean variables are explicitly
integrable. All event indicators used in conditional independence are bounded
and measurable. The conditioning sigma algebra is a sub-sigma-algebra because
`X` is measurable, and the trimmed probability measure is finite, hence
sigma-finite. Consequently none of Mathlib conditional expectation's zero
defaults (invalid sub-sigma-algebra, failure of sigma-finiteness, or failure of
integrability) apply. Probability-to-real conversions are finite. The recorded
formula uses ordinary real subtraction and the literal integer `-99`, not
truncated subtraction. Empty `Ω` or `E` cannot occur with these data. No log,
root, real power, extrema, asymptotic limit, or partial function occurs.
The generated `recordedOutcome._proof_1` is only the proof that the numeral
`99=98+1` is at least two, used by numeric elaboration; it adds no hypothesis.

## SAP.P001e.T84

Sources: Challenge/Part1.lean:66–69; Defs/Part4.lean:15–29;
Defs/Part2.lean:44–54 and all generated auxiliaries listed in the closure.

This is an unconditional finite example. Let the three indices be
`j : Fin 3`, their covariates be `x=(-1,0,1)`, their sizes be `N=(4,4,4)`, their
response counts be `r=(2,3,2)`, and their respondent outcome sums be
`S=(3/4,3/2,3/4)`. For real intercept `a` and slope `b`, put
`p_j(a,b)=exp(a+b x_j)/(1+exp(a+b x_j))` and
`L(a,b)=Σ_{j∈Fin 3} [r_j log(p_j(a,b))+(4-r_j)log(1-p_j(a,b))]`.
Every SAP definition in this theorem has now been replaced by explicit
functions, finite sums, and real operations.

The quantified and numerical conclusions, in order, are:

- For every `a,b : ℝ`, `L(a,b) ≤ L(log(7/5),0)`, and
  `L(a,b)=L(log(7/5),0)` if and only if `a=log(7/5) ∧ b=0`.
- For every `j : Fin 3`, `0<r_j<4` and `p_j(log(7/5),0)=7/12`.
- `(Σ_j S_j/p_j(log(7/5),0))/12=3/7`.
- `(Σ_j 4 S_j/r_j)/12=5/12`.
- `(3/7 : ℝ) ≠ 5/12`.
- `(3/7-5/12 : ℝ)=1/84`.

There are no hypotheses. The theorem specifies cell totals, rather than
constructing twelve individual observations or a data-generating distribution.
The docstring calls this a refutation of the interpretation of “logically
equivalent” as exact equality for arbitrary ML binary-choice propensity fits.

Junk-value audit: every exponential is strictly positive and finite, so each
`p_j(a,b)` lies strictly between zero and one for every real `a,b`. The
denominator `1+exp(...)` is positive. Both likelihood logarithm arguments are
positive, as is `7/5`, so the Mathlib conventions `log 0=0` and
`log(-t)=log t` do not change this example. Every estimator denominator is one
of `2,3,4,7,12,84` or a strictly positive logistic probability. Counts and
outcome sums are reals, so `N-r` is real subtraction. `Fin 3` has exactly three
indices and its vector indices have bound proofs, with no out-of-bounds default.
All rational literals elaborate in the reals, not by natural-number division.
There is no integral, probability conversion, infinite limit, extrema
operator, root, real power, or partial function. The closure's generated
proofs `T84Core._proof_1` through `_proof_4`, `T84Statement._proof_1`,
`cellSize._proof_1`, `exampleY._proof_2`, and `spikeResponse._proof_1` prove only
that the numeric literals `7,5,12,3,84,4,3,2`, respectively, are at least two.
Their source names do not introduce additional data or definitions.

## SAP.P001e.T85

Sources: Challenge/Part1.lean:71–77; Defs/WholeW2.lean:46–99;
Defs/Part1.lean:56 and `recordedOutcome._proof_1`.

In order, this statement universally quantifies a natural `n`, a type `E` with
decidable equality (not assumed finite), a proof `0<n`, covariates
`X : Fin n → E`, real responses `R : Fin n → ℝ`, and a real function
`q : E → ℝ`. Its hypotheses are:

- For every `i : Fin n`, `R_i=0 ∨ R_i=1`.
- For every `x` in the finite image `C={X_i | i∈Fin n}`, the real sum
  `r_x=Σ_i (if X_i=x then R_i else 0)` is strictly positive.
- For every `x∈C`, `q_x>0`. No upper bound or measurability is required of `q`.

Write `N_x=Σ_i (if X_i=x then 1 else 0)`, a real-valued cell count. For each
outcome vector `Y : Fin n → ℝ`, put
`z_i=(Y_i R_i-99(1-R_i)) R_i` and
`S_x=Σ_i (if X_i=x then z_i else 0)`.
All sample and cell SAP definitions expand to these finite expressions:

`I(Y)=(Σ_i z_i/q(X_i))/(n:ℝ)`;
`P(Y)=Σ_{x∈C} (S_x/r_x)(N_x/(n:ℝ))`;
`W=(Σ_i R_i/q(X_i))/(n:ℝ)`;
`H(Y)=((Σ_i Y_i R_i/q(X_i))/(n:ℝ))/W`.

The conclusion is a conjunction with this quantifier order:

1. For every `Y`, simultaneously
   `I(Y)=(Σ_{x∈C} S_x/q_x)/n`,
   `P(Y)=(Σ_{x∈C} N_x S_x/r_x)/n`, and
   `I(Y)-P(Y)=(Σ_{x∈C} S_x(1/q_x-N_x/r_x))/n`.
2. `(∀ Y, I(Y)=P(Y))` if and only if `∀ x∈C, q_x=r_x/N_x`.
   This quantifies all real outcome vectors, not merely the realized outcomes.
3. If `∀ x∈C, q_x=r_x/N_x`, then
   `W=(Σ_{x∈C} N_x)/n`, `W=1`, and for every `Y`, both `I(Y)=P(Y)` and
   `H(Y)=I(Y)`.

Here `n` in any division denotes its cast to a real number. The docstring
describes the same grouping formulas, universal equality criterion and
agreement of stabilized/IPW/plug-in estimators under saturation.

Junk-value audit: `n>0` implies its real cast is nonzero; the nonempty observed
cells have `N_x>0`; hypotheses require `r_x>0` and `q_x>0` on every cell used.
For the stabilization conclusion, `W=1` is explicitly asserted under the same
saturation condition, so the final division cannot use the division-by-zero
default. In fact a respondent per cell also makes `W>0` before saturation.
The finite set `C` cannot be empty: `n>0` supplies an observation. Consequently
the possibility that the ambient type `E` is empty is also excluded by `X`.
No value of `q` outside `C` is used. All counts are real sums of real values;
the sole natural-to-real cast preserves positive finite `n`. Subtractions are
in `ℝ`. The sentinel and its generated numeral proof have the same meaning as
in T83; exact binarity yields `z_i=Y_i R_i`. There is no integral,
nonmeasurable-function issue, log, root, real power, extrema, infinite limit,
or partial-function default in this finite algebra statement.

## SAP.P001e.T86

Sources: Challenge/Part1.lean:79–82; Defs/Part4.lean:58–67;
Defs/Part1.lean:17,30–33.

In order, the theorem quantifies types `Ω,E` with sigma algebras, a probability
measure `μ` on `Ω`, a measurable `X : Ω → E`, a measurable real function `R`,
the pointwise assumption `∀ ω, R(ω)=0 ∨ R(ω)=1`, and `p : E → ℝ` with the
following conditional-mean hypothesis: `p` is measurable, `R` and `p∘X` are
integrable, and for every measurable `A ⊆ E`,
`∫_{X⁻¹(A)} R dμ = ∫_{X⁻¹(A)} p(X(ω)) dμ`.
The final hypothesis is the existence of a real `ε>0` such that, for every
`ω`, `ε<p(X(ω))` and `p(X(ω))≤1`. These bounds concern the image of `X`, not
all points of `E`.

It concludes, in order:

- The constant function `m(x)=1` is measurable;
  `ω ↦ R(ω)/p(X(ω))` and the constant composition `ω ↦ 1` are integrable;
  for every measurable `A ⊆ E`,
  `∫_{X⁻¹(A)} R(ω)/p(X(ω)) dμ = ∫_{X⁻¹(A)} 1 dμ`.
- `∫ R(ω)/p(X(ω)) dμ=1`.
- `1 ≤ ∫ 1/p(X(ω)) dμ`.
- `∫ 1/p(X(ω)) dμ=1` if and only if
  `p(X(ω))=1` for `μ`-almost every `ω`.

There is no outcome variable, sample size, independence assumption, fitted
propensity sequence, limit, stabilized-estimator formula, or efficiency
statement. The docstring explicitly retains only these one-unit population
facts and says it omits the finite-sample and asymptotic/efficiency assertions.

Junk-value audit: every denominator `p(X(ω))` is strictly positive by the
pointwise lower bound. The reciprocal is measurable and bounded by `1/ε`, so
its Bochner integral is an ordinary finite expectation; the lower-bound and
equality conclusions do not use the nonintegrable-integral default. The first
conclusion explicitly includes the required integrabilities for `R/p`. The
conditional-mean hypothesis already includes integrability of `R` and `p∘X`.
No probability-to-real conversion occurs in this closure. There are no
truncated subtractions, logarithms, roots, real powers, extrema, infinite
limits, or partial functions. Empty `Ω` is incompatible with `μ` being a
probability measure, and then `X` prevents empty `E`. Pointwise rather than
almost-sure hypotheses constrain exceptional null-set values too.
