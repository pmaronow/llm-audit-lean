# Blind reading

Saved before opening `claims.json` or `record.json`. Sources read: the three
Challenge docstrings/statements, every declaration named in their `closure.json`
closures, and the relevant Mathlib definitions. The generated line-zero constants
were inspected with `#print` in `scratch/ClosurePrint.lean` (successful compilation).
No interpretation below is based on the canonical claims or architect's record.

## SAP.P029b.T25

The declaration at `SAP/P029b/Challenge/Part1.lean:108` has type
`T25Statement`, defined at `SAP/P029b/Defs/Part4.lean:21`. It is the
conjunction of a universal population result, an independent universal finite
sample identity, and fixed numerical identities.

**Population objects, definitions, and hypotheses (in binder order).** For any
types Ω and X with measurable spaces, any probability measure μ on Ω, any
function U from Ω to records `(x,d0,d1,y0,y1)` with x in X, d0,d1 Boolean, and
y0,y1 real, and any Boolean function Z on Ω, assume all of the following:

1. Each of x,d0,d1,y0,y1 as a function of ω, and Z, is measurable.
2. y0 and y1 are μ-integrable.
3. Z is independent, in Mathlib's measurable-preimage sense, of the entire joint
   vector `(x,d0,d1,y0,y1)`.
4. `0 < μ(Z=true) < 1` (the Lean expression takes the finite measure's `toReal`).
5. `μ{d0=true and d1=false}=0`.
6. The conditional receipt mean in the Z=true arm minus that in the Z=false arm
   is nonzero.

Here Boolean true is encoded as real 1 and false as real 0 (`bit`). A complier
is exactly `d0=false and d1=true`; a defier is exactly `d0=true and d1=false`.
The individual effect τ is `y1-y0`. Receipt D at assignment z is d1 if z=true,
and d0 otherwise. Observed outcome Y at z is y1 if that receipt is true and y0
otherwise. Thus exclusion/SUTVA is built into this individual record and the
observed-outcome function, rather than asserted as a separate predicate.

For a set A, `mP μ A` means `(μ A).toReal` and
`mCE μ v A = (∫_A v dμ)/(μ A).toReal`. For any real weight w, outcome-like
variable v and assignment value z,
`mArm μ Z w v z = mCE(w*v | Z=z)/mCE(w | Z=z)`.
`mWald μ U Z w` is the difference between these weighted Y arm means divided by
the difference between these weighted real-encoded D arm means. These definitions
use restricted Bochner integrals and real division, not a conditional-law primitive.

**Population conclusion.** All five statements hold simultaneously:

1. `E[D|Z=1]-E[D|Z=0] = P(C)`.
2. `E[Y|Z=1]-E[Y|Z=0] = E[1_C τ]`.
3. `E[1_C τ] = P(C) E[τ|C]`.
4. `E[τ|C] = mWald(1)`.
5. `E[τ|C] = (E[Y|Z=1]-E[Y|Z=0])/(E[D|Z=1]-E[D|Z=0])`.

**Finite sample objects and hypotheses.** Independently, for every natural n,
real vector Y indexed by `Fin n`, and Boolean vectors D,Z indexed by `Fin n`,
assume `0 < Σ bit(Z_i) < n` and a nonzero unweighted D arm-mean difference.
For any vector w, `sampleArm(w,V,Z,z)` is
`Σ_i w_i 1_{Z_i=z} V_i / Σ_i w_i 1_{Z_i=z}`.
`sampleWald(w,Y,D,Z)` is its Y arm difference divided by its D arm difference.
`sampleCross(Z,V) = Σ_i (bit(Z_i)-Σ_j bit(Z_j)/n)(V_i-Σ_j V_j/n)`.
The conclusion is
`sampleWald(1,Y,D,Z)=sampleCross(Z,Y)/sampleCross(Z,bit∘D)`.
This is an algebraic centered just-identified coefficient with an intercept; no
sampling model is hypothesized in this conjunct.

**Numerical conclusion (no binders or hypotheses).** The equal-mass weighted
average of effects 0 and 1 is 1/2; their average with weights additionally 3/4
and 1/10 is 2/17; `115/1000 ≤ 2/17 < 125/1000`; and inserting the respective
inverse factors 1/(3/4) and 1/(1/10) restores 1/2. There is no explicit gender
population or stochastic model in this numerical conjunct: it states exactly
those arithmetic formulas.

**Junk-value and boundary audit.**

- Real inverse/division is total, with inverse zero and division by zero equal to
  zero. The arm probabilities are positive by the probability-measure and
  assignment hypotheses. The first stage is explicitly nonzero, and the proved
  first identity then makes the complier probability positive. Unit weight arm
  normalizers are one. Thus population conditioning and the final ratio have
  genuine nonzero denominators.
- `ENNReal.toReal ∞=0`, but μ is a probability measure, so it never occurs here.
- Bochner integration returns zero for a nonintegrable function. Both potential
  outcomes are integrable and measurable, their difference and indicator products
  are integrable, and receipt is bounded. No displayed integral needs that fallback.
- `Fin 0` and empty sums exist in the definitions, and the sample means and
  centered cross products would then use 0/0. The two positive arm-count bounds
  rule out n=0 and n=1 and ensure both normalizers and n are positive. The first
  stage and the positive arm factor make the cross-product denominator nonzero.
- Natural casts to ℝ in the sample definitions are exact; there is no truncated
  natural subtraction in this closure. All numerical denominators are positive.
- No logarithm, square root, real power, partial-function default, infinite
  supremum/infimum, or limsup/liminf occurs in this statement's mathematical data.
- `PotentialUnit.mk` and all its fields are ordinary record construction and
  projection. The eight `T25Statement._proof_*` constants are merely proofs that
  the natural numeral bases 2,3,4,10,17,115,1000,125 are at least two; they add
  no hypotheses, choices, or numerical defaults.

The Challenge docstring describes the IV identities, centered sample coefficient,
and the three numerical gender-example values, consistently with this blind
syntactic reading. Whether this is the full intended claim remains to be checked.

## SAP.P029b.T26

The declaration at `SAP/P029b/Challenge/Part1.lean:114` has type
`T26Statement`, defined at `SAP/P029b/Defs/Part4.lean:53`. Its two conjuncts are
separate universal population and sample theorems.

**Population objects and hypotheses (in binder order).** For all measurable
spaces Ω,X, probability measures μ on Ω, records U=(x,d0,d1,y0,y1) as above,
and Boolean assignments Z, first assume `IVAssumptions`: all six coordinate
functions measurable; integrable y0,y1; Z independent of the complete joint
potential-data/covariate vector; `0<P(Z=true)<1`; no defiers almost surely;
and a nonzero receipt first stage. The meanings of D,Y,τ,C and the normalized
restricted integrals `mP,mCE,mArm,mWald` are exactly the formulas stated in the
T25 section above, with the same real/Boolean types.

Next quantify real functions c,m on X and assume `ScoreVersions`:

- c and m are measurable;
- `c(x(ω)) = E[1_C | σ(x)](ω)` μ-almost surely;
- `c(x(ω))*m(x(ω)) = E[1_C τ | σ(x)](ω)` μ-almost surely.

Here `covariateSigma U` is the pullback/comap of the measurable space on X along
x; `condExp` is Mathlib's real Bochner conditional expectation with respect to
that sub-σ-algebra. Thus c is a version of conditional compliance probability;
under positivity, m is the conditional complier mean effect. Next quantify a
real ε, assume ε>0 and `ε<c(x(ω))≤1` almost surely. There is no A1 hypothesis
for the first five population conclusions.

Write `W=E[1/c(x)]` and `M=E[m(x)]`. The conclusions are:

1. `P(C) E[τ|C]=E[c(x)m(x)]`.
2. `P(C)=E[c(x)]`.
3. The population 1/c-weighted Y arm difference is M/W.
4. The population 1/c-weighted D arm difference is 1/W.
5. The population 1/c-weighted Wald ratio is M.
6. If additionally `A1Versions`, meaning `m(x)=E[τ|σ(x)]` almost surely, that
   same Wald ratio is `E[τ]`.

**Sample objects and hypotheses (in binder order).** For all measurable Ω,X,
with X additionally a second-countable topological space whose measurable space
is its Borel σ-algebra; all probability measures μ; all sequences U_i of potential
records and Z_i of Boolean assignments on the common Ω; all real functions c,m
on X and triangular fitted-score arrays `s : ℕ → ℕ → Ω → ℝ`, assume the
structure `ICSWConditions μ U Z c m s`, consisting of:

1. The full IV assumptions just listed for every i.
2. Independence of the whole family of random vectors
   `J_i=(((x_i,d0_i,d1_i,y0_i,y1_i)),Z_i)`. In Mathlib `iIndepFun` means finite
   intersections of coordinate measurable-preimage events have the product of
   their measures.
3. `IdentDistrib J_i J_0 μ μ` for every i: both variables are almost everywhere
   measurable and have equal pushforward probability measures.
4. `ScoreVersions μ U_i c m` for every i, with the same c,m.
5. There exists ε>0 such that, for every i, `ε<c(x_i)≤1` almost surely. The
   ε is common to the whole family; the exceptional null set can depend on i.
6. Every `s n i` is measurable.
7. For every n, almost surely every i in `Fin(n+1)` has `0<s n i≤1`.
8. `max_{0≤i≤n}|s n i-c(x_i)| → 0` in μ-measure. `uniformScoreError` is the
   finite `sup'` over `Finset.range(n+1)`, with a proof that this range is nonempty.

After that structure quantify another real function a on X. Require a measurable;
for every i require `a(x_i)=E[τ_i|σ(x_i)]` almost surely; require m(x)=a(x)
for every x in the topological support S of the pushforward law of x_0; and
require a (possibly separately chosen) ε>0 such that `ε<c(x)≤1` for every x in
S. Mathlib's support is the set of points all of whose neighborhoods have
positive measure. These are pointwise requirements on chosen versions over S.

Finally assume `RatiosEventuallyDefined` for the inverse fitted scores. Its
quantifier order is `for μ-almost every ω, there exists N(ω), for all n≥N(ω)`:
both weighted assignment arm sums in the first n+1 observations are nonzero and
the difference between the two weighted receipt means is nonzero. More
explicitly `SampleDefined(w,D,Z)` is
`(∀z, Σ w_i 1_{Z_i=z} ≠ 0)` and
`sampleArm(w,bit∘D,Z,true)-sampleArm(w,bit∘D,Z,false) ≠ 0`.

**Sample conclusion.** `icswSequence U Z s n ω` is the sample Wald ratio using
the first n+1 units, weights `1/s n i ω`, receipt D_i=d1_i or d0_i according to
Z_i, and Y_i=y1_i or y0_i according to D_i. Its limit in μ-measure is the
constant `∫ τ_0 dμ`. On this probability space convergence in measure means
that, for every positive extended-real δ, the probability of
`δ≤edist(T_n,E[τ_0])` tends to zero (equivalently the usual convergence in
probability for real variables). There are no sample limits asserted separately
for the numerator or denominator arm differences.

**Junk-value and boundary audit.**

- `mP` uses `toReal` and `mCE,mArm,mWald` use total real division. Probability
  measures rule out infinite event masses. Assignment-arm probabilities and the
  receipt first stage are genuine. Population score positivity rules out inverse
  zeros almost surely; 1/c is bounded there and W is positive. The conditional
  moment versions and positive lower bound make m and all displayed weighted
  integrands integrable. Version values on null sets do not change integrals.
- Mathlib `condExp` is defined to be zero if the conditioning measurable space
  is not a subspace, its trimmed measure is not σ-finite, or the function is not
  integrable. Measurability of x makes its comap a sub-σ-algebra; probability
  implies finiteness of the trimmed measure; integrability of y0,y1 supplies
  integrability of τ and 1_C τ. Thus these defaults are excluded here.
- Conditional expectations themselves choose representatives of equivalence
  classes; all version equalities are almost everywhere except the expressly
  pointwise support restrictions on m,a,c.
- Every sample uses `Fin(n+1)`, never an empty sample. Either assignment arm can
  nevertheless be empty on small samples, and the sample first stage can be zero.
  Real division extends the resulting estimator to a real value, normally zero
  where a denominator vanishes. Positive fitted scores hold almost surely for
  all sampled indices, and the final additional hypothesis rules out all
  undefined sample ratios eventually along almost every sequence. No finite-N
  bound common to all ω is required.
- `uniformScoreError` is a maximum of a nonempty finite set of nonnegative
  real errors, so it has no empty/unbounded supremum convention. No `sInf`,
  `sSup`, limsup/liminf, logarithm, square root, real power, natural subtraction,
  cast overflow, or partial-function default is used. Finite-index casts are
  ordinary exact natural/real casts. The generated nonemptiness proof is harmless.
- `ICSWConditions.mk` is an ordinary structure constructor taking precisely the
  eight assumptions above. No field is the claimed estimator convergence itself.

The docstring discloses uniform in-sample consistency, additional regularity and
support hypotheses, omission of the two separate sample arm-contrast limits,
and almost-sure eventual definedness. It asserts population weighted identities
and final-ratio consistency with those additions.

## SAP.P029b.T27

The declaration at `SAP/P029b/Challenge/Part1.lean:129` has type
`T27WholeStatement`, defined at `SAP/P029b/Defs/WholeW2.lean:280`. It is an
unconditional conjunction about one explicitly fixed finite population law and
its infinite iid product sampling law, plus a universal fact about the normal CDF.

**Objects and fully unfolded fixed definitions.** A population atom is
`a=((x,k),z)` with x,z Boolean and k in `Fin 3`. Its probability is 1/12 under
the finite uniform PMF converted to a measure (`cancelLawW2`). Let s(x)=2 if
x=true and -2 otherwise. The potential record (`cancelUnitW2`) is

| k | d0 | d1 | y0 | y1 | τ |
|---|---|---|---|---|---|
| 0 | false | true | 0 | 0 | 0 |
| 1 | true | true | -s(x) | 0 | s(x) |
| 2 | false | false | 0 | s(x) | s(x) |

Its covariate is x. Receipt at assignment z is d1 if z, otherwise d0; outcome
is y1 if receipt, otherwise y0. Therefore every observed outcome equals zero.
The complier and defier predicates, real Boolean coding, effect, and measurable
IV assumptions have exactly the meanings detailed for T25 above. In particular
the IV assumptions include independence of assignment and the entire potential
record, positive mass in both assignment arms, no defiers, and a nonzero first
stage, as well as measurability and integrability.

The sample space is all functions ω from ℕ to these twelve atoms. Its measure
is `Measure.infinitePi (fun _ => cancelLawW2)`, the countable product of these
uniform laws. `cancelDrawW2 i ω` is the potential record of ω(i), and
`cancelZW2 i ω` is the last Boolean coordinate of ω(i).

For every n, cell (x,z), and sequence ω, the empirical receipt rate r_n(x,z)
is the sum of real-coded receipts in that cell among i=0,...,n divided by that
cell's count. `cancelFitGoodW2 n ω` means, for each Boolean x,
`0<r_n(x,false)<r_n(x,true)<1`. The fitted score at index i is
`r_n(x_i,true)-r_n(x_i,false)` on this event, and 1/3 otherwise. This is defined
also for i outside the first n+1 observations; it uses that index's profile.

`bernoulliFactor(p,d)` is `p^1(1-p)^0` for true d and `p^0(1-p)^1` for false d,
hence p or 1-p. `cancelLikelihoodW2(n,ω,q)` is its product over the first n+1
observations, with p=q(x_i,z_i) and d the observed receipt. The comparison
parameter type `ReceiptParameters` consists of all four real cell probabilities
such that `0<q(x,false)<q(x,true)<1` for both x. These are saturated interior
ordered receipt probabilities. The standard-normal CDF assertion guarantees
that every interior probability is achieved by a probit link.

`scoreAt μ U x` is `P(C and X=x)/P(X=x)`. `latentAt μ U x` is the equality
`(∫_{X=x}τ/P(X=x))=(∫_{C and X=x}τ/P(C and X=x))`.
`ScoreVersions μ U c m` requires measurable c,m and the almost-sure equalities
`c(X)=E[1_C|σ(X)]`, `c(X)m(X)=E[1_C τ|σ(X)]`.
`A1Versions μ U m` requires `m(X)=E[τ|σ(X)]` almost surely. The conditional
σ-algebra is the measurable-space comap along X, and `condExp` is Mathlib's
Bochner conditional expectation.

For samples, `SampleDefined` requires both weighted assignment-arm sums and
the weighted receipt-arm mean difference to be nonzero. `icswSequence` is the
Wald ratio of weighted Y and D arm differences, with inverse fitted scores and
the first n+1 units. Arm means are `Σ w_i 1_{Z_i=z} V_i/Σ w_i 1_{Z_i=z}`.

**Every asserted conjunct, in order.**

1. For every real p, if 0<p<1, there exists a real θ with the standard-normal
   CDF at θ equal to p (`ProbitCompleteW2`). The distribution is Mathlib's
   `gaussianReal 0 1`.
2. `CancellationPopulationW2`: the fixed uniform twelve-atom population satisfies
   the full IV assumptions. For each Boolean profile x, its probability is 1/2,
   compliance score is 1/3, conditional complier effect is zero, conditional
   population effect is 4/3 at true and -4/3 at false, and `latentAt` fails.
   For every x,z the receipt mean conditional on their joint cell is 2/3 if
   z=true and 1/3 otherwise. The population ATE is zero and every observed
   outcome is zero.
3. The infinite product sampling law is a probability measure.
4. The sequence of full joint potential-record/covariate/assignment variables
   is independent (`iIndepFun`).
5. For every i its joint vector has the same distribution as the zeroth one
   (including almost-everywhere measurability, as required by `IdentDistrib`).
6. For every i the full IV assumptions hold on the product sampling space.
7. For every i, the constant functions c=1/3 and m=0 satisfy `ScoreVersions`.
8. For every i, those m=0 functions fail `A1Versions`.
9. For every i the marginal expectation of its effect is zero.
10. `0<1/4<1/3≤1`, explicitly certifying a uniform positive overlap margin.
11. For every n,i the fitted-score function is measurable.
12. For every n,i,ω the fitted score is strictly positive and at most one.
13. For every fixed i the sequence of fitted scores tends to 1/3 in measure.
14. The (extended-real) probabilities of `cancelFitGoodW2 n` tend to one.
15. The probabilities that `SampleDefined` holds with the fitted inverse scores
    tend to one.
16. For every n,ω, if the fit-good event holds, then for every q in
    `ReceiptParameters`, its receipt likelihood is at most the likelihood at
    the empirical four-cell rates. This is a likelihood maximization assertion
    on that event, with no maximizer claim off the event.
17. For every n,ω, the real-division-defined sample ICSW value is zero
    (the estimator takes values in ℝ and its divisions are total).
18. The sample ICSW values converge in measure to the constant marginal ATE,
    i.e. zero. Convergence in measure has the ordinary probability-of-positive-
    error-events meaning described for T26.

All these assertions are conclusions; there are no outer data hypotheses that
could be incompatible. Internal universal binders occur in the order given
above, particularly n,ω,fit-good proof,q for the maximizer statement.

**Junk-value and boundary audit.**

- Each atom has positive mass; each profile has probability 1/2 and each
  profile/complier event has probability 1/6. Each assignment/profile cell has
  mass 1/4, assignment arms have mass 1/2, and the first stage is 1/3. Thus
  `scoreAt`, `latentAt`, and all population conditioning use genuine denominators.
- Both population and product laws are probability laws. All potential variables
  are bounded functions of a finite atom, so all integrals and conditional
  expectations exist. `toReal ∞=0`, undefined Bochner-integral zero, and the
  nonintegrable/non-sub-σ-algebra/non-σ-finite conditional-expectation zero
  defaults are excluded. All conditional-version assertions are almost surely.
- Empirical cell rates use 0/0=0 for empty cells. On the fit-good event the four
  cells are nonempty and all their rates are strictly interior. Off it the score
  is deliberately set to the strictly positive 1/3. That extension is not itself
  asserted to maximize likelihood. The bad event's probability tends to zero.
- A positive fitted score prevents inverse-score division by zero for every
  sample, but empty assignment arms or a zero sample first stage can still occur.
  The final Wald ratio uses real division's zero extension. The theorem also
  asserts that the probability of all ratios being defined tends to one, so
  its limiting equality is not just an assertion on undefined samples.
- The likelihood only compares interior probabilities (empirical rates on the
  good event). Boolean exponents are naturals 0 or 1; the generic `0^0=1`
  convention is present in the factor formula but does not alter this likelihood.
- Samples contain n+1 observations and the population/product index types are
  nonempty. Finite types, coordinate projections and natural casts introduce no
  default or truncation. There is no log, sqrt, real power, sInf/sSup or
  limsup/liminf in the assertion. The normal CDF uses an actual probability law.
- The generated closure proofs `CancellationCellLimitsW2._proof_1`,
  `logisticCDFW2._proof_1`, and `simCoordinateLawW2._proof_1` certify numeral
  bases 4,3,2, respectively. `cancelLawW2._proof_1` certifies nonemptiness of
  the twelve-atom type. These do not bring in any simulation/logistic assumptions
  or associated mathematical expressions. `PotentialUnit.mk` is the ordinary
  record constructor.

The Challenge and definition docstrings call this a refutation of an assertion
that failure of latent ignorability forces asymptotic bias. The fixed witness
has profile effects that cancel in the marginal target and an identically zero
observed outcome. Whether that contradicts the canonical assertion, rather
than one interpretation of it, is reserved for the claim stage.

## Post-blind Mathlib implementation addendum

Added during verification, without changing the saved blind mathematical reading
or any claim-stage classification. Two further totalization details are harmless
here: `Measure.infinitePi` is zero if any marginal fails to be a probability law;
the T27 marginals are genuine uniform PMF probability laws. `Measure.map` uses an
almost-everywhere measurable representative when available; otherwise it returns
zero for a zero source measure and an arbitrary Dirac mass for a nonzero source
measure. The T26 covariate pushforwards are along measurable maps by the IV
hypotheses, and all `IdentDistrib` fields explicitly require almost-everywhere
measurability. Neither fallback can affect these statements.
