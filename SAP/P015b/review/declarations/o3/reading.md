# Blind reading (written before opening claims.json / record.json)

Sources read: `SAP/P015b/Challenge/Part1.lean:104-112`, `SAP/P015b/Defs/Part1.lean` (whole),
`SAP/P015b/Defs/Part3.lean:17-19`, `SAP/P015b/Defs/Part6.lean` (whole), `SAP/P015b/Defs/Part7.lean` (whole).
Every closure entry in `closure.json` was read (the `_proof_n` entries are auxiliary proof terms of the
`![..]`/`!![..]` literals and `Fin` literals inside the listed defs; they carry no content).
Elaborated forms were checked with `#print` in `scratch/Print.lean`.

---

## 1. `SAP.P015b.T18 : T18Statement` (Challenge/Part1.lean:104-107)

Docstring: "The printed claim is false: P015-T18; pp. 264-265, Appendix C; pp. 256-257. Finite logistic ML fits
solve their residual equations, but a genuine square-link ML branch in the stated causal model refutes universal
mean-only first-order OLS scaling. Scope: Retains clause (A) and an explicit counterexample to universal clause (C);
omits an assessment of score substitution for every specifically listed nonlogistic family in (B), and does not
assert a separate counterexample for each named family."

`T18Statement := LogisticMLStationarity ∧ SquareLinkFailure` (Defs/Part6.lean:109).

### 1a. `LogisticMLStationarity` (Defs/Part6.lean:101-107)

For all `N K : ℕ`, every real design `W : ℝ^{N×(K+2)}` (so at least two columns, no intercept or treatment column
required), every outcome vector `Y ∈ {0,1}^N`, every `θ ∈ ℝ^{K+2}`:

if θ is a **global maximizer** over all of ℝ^{K+2} of the Bernoulli/logit log-likelihood

  ℓ(γ) = Σ_i [ Y_i log σ(W_i·γ) + (1 − Y_i) log(1 − σ(W_i·γ)) ],   σ = `Real.sigmoid` (`sigmoidMean`, Part1:73),

(`binaryLogLikelihood W 1 Y σ` = Σ_i `binomialLogLikelihoodSAP σ 1 (Y_i) (W_i·γ)`, Part1:77-86, with n_i = 1, k_i = Y_i)

then the residual (score) equations hold: for every column j, Σ_i W_ij (Y_i − σ(W_i·θ)) = 0
(`residualEquation W 1 Y σ θ = 0`, Part1:80-82).

Quantifier order: ∀N K W Y, (Y binary) → ∀θ, (∀γ, ℓ(γ) ≤ ℓ(θ)) → score(θ) = 0.

Junk values: `Real.log` is only applied to σ(·) ∈ (0,1) and 1 − σ(·) ∈ (0,1), so no junk. N = 0 gives empty sums,
statement trivially true and harmless. If no maximizer exists (separation) the implication is vacuous, which is the
correct content (the claim is about fitted ML solutions). Grouped binomial data (n_i > 1 trials) are not covered:
n is fixed to 1; this is a specialization only of the data format (grouped binomial data with k_i successes out of
n_i is equivalent to n_i Bernoulli rows, so nothing substantive is lost), but literally it is Bernoulli only.

### 1b. `SquareLinkFailure` (Defs/Part6.lean:67-98)

Objects (all concrete, Part6:17-64):
- six population cells i ∈ Fin 6 with covariate X_i = (−1,−1,0,0,1,1), treatment D_i = (0,1,0,1,0,1),
  cell probabilities p = (1/4, 1/12, 1/6, 1/6, 1/12, 1/4);
- propensity e(x) = 1/2 + x/4 (so e(−1)=1/4, e(0)=1/2, e(1)=3/4; consistent with p);
- baseline b_a(x) = 1/4 + a(3x² − 2);
- design row W_i = (1, D_i − e(X_i), X_i) (span equals span(1, D, X) since e is affine, so the coefficient on
  column 1 is the coefficient on D in a regression on intercept, D, X);
- cell success probability π_{a,ε}(i) = b_a(X_i) + ε(D_i − e(X_i));
- square link m(η) = η² (`squareMean`);
- population (expected) square-link log-likelihood
  L_{a,ε}(t) = Σ_i p_i [ π_i log((W_i·t)²) + (1 − π_i) log(1 − (W_i·t)²) ];
- admissible t: 0 < W_i·t < 1 for every i (so m(W_i·t) ∈ (0,1));
- `SquareMLDerivative a b`: there is a path θ : ℝ → ℝ³ with θ(0) = (1/2,0,0) and a radius r ∈ (0, 1/16] such that
  for all |ε| < r, θ(ε) is admissible and is the **unique** maximizer of L_{a,ε} over the admissible set, and
  ε ↦ θ(ε)_1 has derivative b at 0. (Because the maximizer is unique on (−r, r), b is determined by (a); no freedom.)
- a measure-theoretic unit model on (ℝ×ℝ)×ℝ: `squareUnitLaw` = Σ_i p_i · δ_{(X_i,D_i)} ⊗ Unif[0,1];
  unit profile X = s.1.1, treatment D = s.1.2, latent U = s.2; potential outcomes
  Y(d) = 1{U ≤ b_a(X) + ε(d − e(X))}; unit effect τ = Y(1) − Y(0).

`SquareLinkFailure` asserts (with the probability-measure instance supplied by the existential):
1. p is a finite law; E_p[W Wᵀ] = diag(1, 5/24, 2/3), and its determinant ≠ 0;
2. `SquareMLDerivative (1/16) (120/119)` and `SquareMLDerivative 0 1`;
3. for all |ε| ≤ 1/16: E_p[π_{1/16,ε}] = 1/4 and the population OLS coefficient on column 1 of π_{1/16,ε} on W is ε;
4. m'(1/2) = 1 (so m(1/2) = 1/4 = mean, and the mean-only first-order scale factor 1/m'(m⁻¹(E Y)) equals 1);
   120/119 ≠ 1;
5. Unif[0,1] and the unit law are probability measures;
6. for a ∈ {0, 1/16} and |ε| ≤ 1/16, the unit model satisfies: X uniform on {−1,0,1}; D ∈ {0,1} a.s.; U ∈ [0,1]
   a.s. with CDF u ↦ u; U ⫫ (X, D); (Y(0), τ) ⫫ D | σ(X) (conditional ignorability, `CondIndepFun`);
   E[D | X] = e(X) a.s.; Y = Y(0) + τ·D a.s.; E[Y | X, D] = b_a(X) + ε(D − e(X)) a.s.; E[Y] = 1/4.

Plain mathematics: in a binary-treatment, conditionally ignorable causal model with E[Y]=1/4 for both a=0 and
a=1/16 and population OLS treatment coefficient exactly ε in both, the square-link population ML treatment
coefficient has ε-derivative 1 at a=0 but 120/119 at a=1/16. Hence no rule that predicts the first-order ML
coefficient from the OLS coefficient and the outcome mean alone (in particular the rule β_ML ≈ β_OLS / m'(m⁻¹(E Y)),
which gives 1 here) can be correct for this link. (Item 3 is stated only for a = 1/16; for a = 0 the OLS
coefficient ε and mean 1/4 are not asserted as conjuncts, but they follow from item 6's E[Y|X,D] and E[Y].)

Junk values and their effect:
- `populationCoefficients` uses `Matrix.inv` (junk 0 if singular): the moment matrix is asserted equal to
  diag(1,5/24,2/3) with det ≠ 0, so the inverse is genuine.
- `Real.log` in `squareLogLikelihood`: only evaluated with any meaning at admissible t (η ∈ (0,1) ⇒ η² ∈ (0,1)).
  The maximization is restricted to admissible t, so log junk outside (0,1) never enters. Note: restricting the ML
  to the admissible region is the natural domain of the square link (m must map into (0,1)); the square link is
  not monotone on ℝ, but it is monotone on (0,1).
- `binomialLogLikelihoodSAP` with n = 1 and fractional k = π_i ∈ (0,1): this is the expected Bernoulli
  log-likelihood (population ML), genuine.
- `(p_i).toNNReal`: all p_i > 0, no truncation.
- conditional expectations `μ[f | m]` (junk 0 if non-integrable): the asserted values e(X) and b_a(X)+ε(D−e(X))
  are strictly positive, so these equalities can only hold genuinely.
- `∫ Y = 1/4` (Bochner junk 0): 1/4 ≠ 0, genuine.
- `deriv squareMean (1/2) = 1` (deriv junk 0): asserted 1, genuine.
- `HasDerivAt` is a genuine derivative.

Possible meaning issues to check against the claim: (i) is the square link a model covered by the claim's clause
(C); (ii) is the claim's (C) a universal "mean-only first-order scaling" assertion; (iii) the first-order rule is
assessed via the derivative at ε = 0 of the population ML coefficient — whether that is the paper's approximation.

---

## 2. `SAP.P015b.T17 : T17Statement.{u,v}` (Challenge/Part1.lean:109-112)

Docstring: "The printed claim is false: P015-T17; p. 261, positivity passage. Positive endpoint probabilities imply
positive variance on the exported domain, while small effective mass, zero fitted sample weights, and a literal
effective-law example refute the printed weight and pair-positivity implications. Scope: The positive implication
(A) requires countable covariates with measurable singletons and a global finite treatment second moment; omits its
remaining meaningful cases. Clauses (B) and (C) are refuted by explicit examples, without a universal
characterization of identification or an applied country-specific conclusion."

`T17Statement := DiscretePositivityImplications ∧ SmallWeightFamily ∧ SmallWeightConsistency ∧ FittedZeroFailure ∧
MissingPairFailure` (Defs/Part7.lean:134-135).

### 2a. `DiscretePositivityImplications` (Part7:84-90)

For every measurable space Ω (universe u), every countable measurable space B with measurable singletons
(universe v), every probability measure P on Ω, every measurable X : Ω → B, every measurable D : Ω → ℝ with
D ∈ L²(P), every x ∈ B with P(X = x) > 0, and every d ≠ d':
if P(D = d | X = x) > 0 and P(D = d' | X = x) > 0, then Var(D | X = x) > 0.

Unfolding: `profileLaw P X x = P(X=x)⁻¹ • P|_{X=x}` (Part7:17-18), the elementary conditional law;
`profileProbability P X D x d = (profileLaw P X x {D = d}).toReal` (Part7:26-27);
`profileMean = ∫ D d(profileLaw)`; `profileVariance = ∫ (D − profileMean)² d(profileLaw)` (Part7:20-24).

Junk: P(X=x)⁻¹ would be ∞ if P(X=x)=0 (and ∞·0 = 0 gives the zero measure), excluded by hypothesis. Given
P(X=x) > 0 and P a probability, profileLaw is a probability measure, toReal is of a finite value, and D ∈ L²(P)
gives D ∈ L²(profileLaw), so mean and variance are genuine (no Bochner junk). `Countable B` is not used by the
meaning (only P(X=x) > 0 matters); it is a restriction of scope (discrete covariates). The global `MemLp D 2 P`
is stronger than needed (conditional L² at x suffices); it is a disclosed restriction. Binary D is not required;
any two distinct values d ≠ d' with positive conditional probability suffice.

### 2b. `SmallWeightFamily` (Part7:93-105)

Four cells a ∈ Fin 4 with X = (0,0,1,1) (`binaryProfile`), D = (0,1,0,1) (`binaryTreatment`), and for ε ∈ (0,1/2)
cell probabilities p_ε = ((1−ε)/2, ε/2, 1/4, 1/4). Outcome Y(a,d) = 2X_a + (1+X_a)d (`smallWeightOutcome`).
For every ε ∈ (0, 1/2):
- p_ε is a finite law;
- Y(a,d) = Y(a,0) + (1+X_a)d (constant-effect-within-unit linear potential outcomes);
- `finiteUnconfounded`: for all x,u,d, P(X=x,U=u,D=d)·P(X=x) = P(X=x,U=u)·P(X=x,D=d) with U = (Y(·,0), 1+X),
  i.e. U ⫫ D | X (here U is a function of X, so it holds trivially but genuinely);
- for x ∈ {0,1}: E[D | X=x] = ε + (1/2−ε)x; P(D=0|X=x) > 0 and P(D=1|X=x) > 0 (strict positivity);
- the regression-effective mass of stratum X=0, Σ_{a: X_a=0} p_a w_a / E[w] with w = (D − E[D|X])², equals
  ε(1−ε)/(ε(1−ε)+1/4), is > 0, and is < 4ε.

So: strict positivity holds in every stratum, yet the effective (multiple-regression) weight of a stratum can be
made arbitrarily small (→ 0 as ε → 0), while the stratum's population share stays 1/2.

Junk: `finiteCellMean`/`finiteCellProbability` divide by stratum mass (=1/2 here, genuine);
`finiteEffective` divides by E[w] = ε(1−ε)/2 + 1/8 > 0 (genuine). For x ∉ {0,1} nothing is asserted.

### 2c. `SmallWeightConsistency` (Part7:107-111)

At ε = 10⁻⁶: E[1 + X] = 3/2 (the ATE), and for every δ > 0, P^n(|n⁻¹ Σ_i τ̂(a_i) − 3/2| ≥ δ) → 0 as n → ∞,
where a_1..a_n are iid from p_ε (`productMass` = product pmf on (Fin n → Fin 4), `finiteMass` = probability of an
event) and τ̂(a) = D Y/e(X) − (1−D) Y/(1−e(X)) with the true propensity e(x) = ε + (1/2−ε)x and Y = Y(a, D_a)
(`inverseWeightedOutcome`, `smallWeightIPW`, Part7:41-46). I.e. the IPW estimator with known propensity is
weakly consistent for the ATE despite the tiny regression weight.

Junk: `sampleMean` at n = 0 divides by 0 (value 0); irrelevant to a limit at ∞. Division by e and 1−e:
e ∈ {10⁻⁶, 1/2}, never 0 or 1. Genuine.

### 2d. `FittedZeroFailure` (Part7:62-81)

Uniform population on the four cells (X,D) ∈ {(0,0),(0,1),(1,0),(1,1)}: P(D=d|X=x) = 1/2 for x,d ∈ {0,1};
the stratum mean of w = (D − E[D|X])² is 1/4 in each stratum. The ordered iid sample of size 4 with cells
(0,0,2,3), i.e. (X,D) = (0,0),(0,0),(1,0),(1,1), has probability (1/4)⁴ = 1/256 > 0 (`productMass`). In that
sample: control design (1, X) with WᵀW = [[4,2],[2,2]] (det ≠ 0); sample OLS of D on (1,X) gives (0, 1/2)
(`sampleCoefficients` = (WᵀW)⁻¹WᵀD, genuine since det ≠ 0); residuals (0,0,−1/2,1/2); squared residuals
(0,0,1/4,1/4). The full regression design (1, D, X) has det(WᵀW) = 2 ≠ 0. The last conjunct links each sample
row to the drawn cells.

So: population strict positivity with equal stratum weights, but with positive probability a sample in which the
full OLS regression is well-defined and the X=0 stratum receives zero fitted (sample) regression weight.

Junk: `sampleCoefficients` uses `Matrix.inv`; det ≠ 0 asserted, genuine. Many conjuncts are arithmetic
certificates (e.g. (1/4)^4 = 1/256).

### 2e. `MissingPairFailure` (Part7:113-132)

P = uniform on Fin 4 (`(1/4)•Σ δ_i`), X = (0,0,1,1) ∈ Fin 2, D = (0,1,0,2) (three treatment values).
Asserts: X, D measurable; D ∈ L²(P); 0 ≠ 1; P(D=0) > 0; P(D=1) > 0; the weight w = (D − E[D|X])²
(`profileWeight`, = (1/4,1/4,1,1)) is integrable with ∫w dP > 0 (= 5/8); the effective law
`effectiveProfileLaw P X D = (∫ w dP)⁻¹ · w·P` (Part7:32-35) gives stratum X=1 positive mass (= 4/5); and the
effective-law conditional probability P_eff(D = 1 | X = 1) = 0.

So: both treatment values 0 and 1 have positive marginal probability, stratum X=1 has positive effective
regression weight, but the pair (0,1) is not jointly supported in stratum X=1 (D = 1 never occurs there, under
P or under the effective law). The "= 0" holds because {X=1, D=1} = ∅, hence genuinely, not by `toReal ∞`.

Junk: `effectiveProfileLaw` inverts ENNReal.ofReal ∫w (∞ if 0) — excluded since ∫w > 0 asserted and w integrable
asserted; `profileLaw` inverts eff{X=1} — asserted > 0 and it is ≤ 1, so finite; `toReal` of a finite value.
`profileMean` here is a Bochner integral of a bounded function over a finite measure, genuine.

### Points to check against the claim
- What exactly the printed "weight" implication (B) and "pair-positivity" implication (C) say: e.g. "positivity
  ⇒ every stratum receives positive (non-negligible) regression weight", "positivity ⇒ positive weight in every
  sample", "multivalued treatment: positive weight requires/ensures positivity for each pair". The witnesses must
  satisfy every condition of the printed reading (e.g. population vs sample positivity, binary vs multivalued
  treatment).
- (A): whether the paper states "positivity ⇔ positive conditional variance" (an iff) or only one direction;
  whether binary D is assumed (here any two distinct values).
- Whether `SmallWeightConsistency` is part of a claim clause or only an illustration (it refutes nothing by
  itself: it asserts a true positive fact about IPW).
