# Blind reading

This file was written and saved before opening `claims.json` or `record.json`.
The sources used were `closure.json`, the Challenge and Defs Lean sources, the
Mathlib definitions of conditional expectation, variance and KL, and the output
of `scratch/Inspect.lean`. That check prints all 56 distinct declarations in the
five dependency closures, including the generated proof declarations.

## SAP.P001a.T6

Source: `Challenge/Part1.lean:49–58`; definition:
`Defs/WholeW1.lean:82–169`. The theorem asserts a conjunction of six universal
propositions, not a single implication or an existence assertion about a
particular statistical experiment.

Throughout these propositions, a probability space means an arbitrary type Ω
with a sigma algebra and a Mathlib measure μ satisfying μ(Ω)=1. “IID” means
that every random variable is measurable, the entire sequence is jointly
independent (`iIndepFun`), and each variable has the same distribution as
variable 0. In the regression part this applies to the pairs (X_i,Y_i), and
does not assert independence of X_i from Y_i. A probability written below is
`(μ A).toReal`; expectations are real Bochner integrals. Convergence in
probability means, for each real ε>0,
`(μ {ω : ε ≤ dist(Z_n(ω),z)}).toReal → 0`. The domain metric on real
quantities is absolute difference.

A least-squares fit with degree cap J is a function from n∈ℕ and ω∈Ω to real
polynomials satisfying, for **every** n and ω, both natDegree(fit_n(ω))≤J(n)
and

    Σ_{i<n} (Y_i(ω) − fit_n(ω)(X_i(ω)))²
       ≤ Σ_{i<n} (Y_i(ω) − q(X_i(ω)))²

for every real polynomial q of natDegree at most J(n). No measurability is
included in this least-squares predicate itself.

1. For every measurable space Ω, sequences of measurable real X_i,Y_i, and
   arbitrary natural degree cap J(n), there exists such a fit for which every
   coefficient map ω↦coeff_k(fit_n(ω)) is measurable, for every n,k. There
   is no probability measure, rank condition, positive sample-size condition,
   or iid condition in this first proposition. Singular designs are included.

2. For every probability space, real sequences X,Y, real a,b,V and function
   m:ℝ→ℝ satisfying all the following:

   * iid pairs; a<b; X_0∈[a,b] almost surely; m continuous on [a,b];
   * Y_0 integrable, and conditional expectation of Y_0 given the sigma
     algebra pulled back by X_0 equals m(X_0) almost surely;
   * (Y_0−m(X_0))² integrable, and, for every Borel A⊆ℝ,
     `∫_{X_0∈A}(Y_0−m(X_0))² dμ ≤ V μ(X_0∈A)`;

   for every sequence p_k of real polynomials with natDegree(p_k)=k and
   `∫p_j(X_0)p_k(X_0)dμ = 1` if j=k and 0 otherwise; for every natural
   J(n)→∞ with (J(n)+1)/n→0; for every real c>0 such that the event

       ∀v∈ℝ^(J(n)+1),
       c Σ_k v_k² ≤ (1/n) Σ_{i<n}(Σ_k v_k p_k(X_i))²

   has probability tending to one; and for **every** least-squares fit with
   cap J, the squared prediction error is integrable in x for every n,ω,
   and its integral against the distribution μ.map(X_0) converges to zero
   in probability. Thus the norm is global L² with respect to the covariate
   distribution, not Lebesgue L² over the ambient line. V is not separately
   assumed nonnegative; the displayed bound for A=ℝ implies that fact.

3. For every a<b, every K∈ℕ, and K real polynomials p_k, the real supremum

       E(a,b,p) = sup { Σ_{k<K} p_k(x)² : a≤x≤b }

   is attained at some x∈[a,b], and bounds the displayed sum at every
   y∈[a,b]. This is the entire meaning of `wholeSieveEnvelope`.

4. For every probability space, iid real covariates, a<b with X_0∈[a,b]
   almost surely, every sequence of polynomials orthonormal in their
   covariate distribution, and every natural cap J, if

       E(a,b,(p_0,…,p_J(n))) (J(n)+1)/n → 0,

   then the quadratic-form event in proposition 2, with c=1/2, has
   probability tending to one. No degree assumption or J→∞ hypothesis is
   imposed in this separate sufficient-condition proposition.

5. For every iid real X_i with X_0 uniform on an arbitrary interval a<b,
   every positive natural K,n, and K polynomials of respective natural
   degrees 0,…,K−1 orthonormal in that uniform distribution,

       E(a,b,p) ≤ K²,
       Pr(||G_n−I||_(Euclidean operator) > 1/2) ≤ 4(K³−K)/n,
       (G_n)_{jk} = (1/n) Σ_{i<n} p_j(X_i)p_k(X_i).

   The norm is the actual operator norm of Mathlib's continuous linear
   operator on EuclideanSpace ℝ (Fin K), via `Matrix.toEuclideanCLM`.
   The uniform law is Lebesgue measure with density (b−a)⁻¹ on [a,b]
   and zero elsewhere, converted to ENNReal with `ofReal`.

6. For every iid uniform X_i on any a<b, every infinite polynomial sequence
   of natural degree k orthonormal in that law, and every cap J, the cubic
   rate (J(n)+1)³/n→0 implies the same Gram lower-bound probability limit
   with c=1/2. This proposition also does not assume J→∞.

Junk-value audit:

* Real division by zero sets sample Gram matrices, empirical quadratic
  forms and rate expressions to zero at n=0. All uses are limits at infinity
  or explicitly assume n>0; these values do not affect a conclusion.
* The zero polynomial has natDegree 0. It is correctly permitted even for
  degree cap 0; the degree and orthonormality assumptions together exclude
  a zero member in an orthonormal basis.
* The interval assumption a<b makes the envelope set nonempty and compact
  and its continuous image bounded. Real `sSup` on an empty or unbounded
  set would not express the intended supremum, but neither case occurs.
  With K=0 the image is the singleton {0}; the attainment clause remains
  meaningful. Finite-sample deviation bounds explicitly require K>0.
* μ(A).toReal would be 0 for μ(A)=∞; a probability measure excludes infinity.
* A Bochner integral defaults to 0 if its integrand is not integrable. The
  CEF predicate explicitly assumes Y integrable; the residual square is
  explicitly integrable; compact support and polynomial/continuous
  integrands ensure all basis and prediction-error integrals are genuine.
  The latter integrability is also an explicit conclusion.
* Conditional expectation defaults to zero for an invalid sub-sigma algebra,
  non-sigma-finite trimmed measure, or nonintegrable Y. Measurability of X,
  the probability measure, and the stated integrability prevent all three.
  Values of m outside the almost-sure compact domain have no effect.
* All casts from naturals are exact nonnegative real casts. J(n)+1 is natural
  addition before casting; no truncated subtraction occurs. K³−K is real
  subtraction. There is no log, square root, real power, limsup/liminf,
  partial-function default, or infinite sequence supremum here.

Closure auxiliaries were read with `#print`: the four T6 `_proof_*` declarations
supply continuous addition, commuting scalar actions, continuous scalar
multiplication, and completeness for Euclidean spaces. The T5WholeStatement
and wholeHolePDF auxiliary proofs only certify that small numeral denominators
are at least two. They add no statistical premise or semantic convention.

## SAP.P001a.T7

Source: `Challenge/Part1.lean:60–63`; definition `Defs/Part3.lean:102–159`.
There are two universally quantified implications about iid realizations;
the statement does not itself existentially construct an iid sequence.
Here and below, probability, mean, and convergence in probability have exactly
the unfolded Mathlib meanings described in T6. Variance means
`(∫⁻ω, ||Y(ω)−∫Y dμ||ₑ² dμ).toReal`.

First, for every probability space and jointly iid measurable real pairs
(X_i,Y_i) whose first-pair distribution has masses 3/8,1/8,1/8,3/8 at
(0,0),(0,1),(1,0),(1,1), the following conjunction holds. Set

    C(z)=max(1/10,min(9/10,z)),
    Ybar_n=(Σ_{i<n}Y_i)/n,
    D(p,t)=p log(p/t)+(1−p) log((1−p)/(1−t)).

* For p∈{1/4,3/4} and t∈[1/10,9/10], D(p,t)≥0 and D(p,t)=0 iff t=p.
* For every natural n>0 and every deterministic binary vector y∈{0,1}^n,
  the Bernoulli likelihood `∏_{i<n}(if y_i=1 then t else 1−t)` is maximized
  over t∈[1/10,9/10] at C((Σ_i y_i)/n). For every such t, equality of its
  likelihood with the latter maximum is equivalent to equality of t and
  that clipped mean. Both the maximization and uniqueness are asserted.
* E[Y_0]=1/2 and Var(Y_0)=1/4.
* For every n>0 and real ε>0,
  `Pr(ε≤|C(Ybar_n)−1/2|) ≤ 1/(4nε²)`.
* For every n>0, each of
  `Pr(1/8<|C(Ybar_n)−1/4|)` and
  `Pr(1/8<|C(Ybar_n)−3/4|)` is at least 1−16/n.
* C(Ybar_n) converges in probability to 1/2, and does not converge in
  probability to either 1/4 or 3/4.
* The averaged objective (D(1/4,t)+D(3/4,t))/2 is uniquely minimized over
  that same parameter interval at t=1/2. Both its global inequality and
  its equality characterization are stated.

Second, for every probability space, jointly iid measurable real pairs,
and real q∈[0,1], if the first-pair distribution has masses
3(1−q)/4,(1−q)/4,q/4,3q/4 at the same four points, put T_n=C(Ybar_n).
Then T_n converges in probability to 1/4+q/2. For every n>0, almost surely
T_n belongs to the parameter interval and is the unique maximizer of the
observed Bernoulli product over that interval. If additionally 0<q<1,

    (∫_{X_0=0}Y_0 dμ)/Pr(X_0=0)=1/4,
    (∫_{X_0=1}Y_0 dμ)/Pr(X_0=1)=3/4,

and T_n converges to neither of those two numbers. The event integrals divided
by atom probabilities are the complete unfolding of `conditionalMeanAt`.

The docstring describes this as a refutation of a printed fixed-covariate
target claim, and explicitly omits derivative formulas and an exact numerical
averaged-KL gap. The mathematical statement contains no independent abstract
claim-negation predicate.

Junk-value audit:

* All logarithm arguments in D are strictly positive under the stated p,t
  ranges; Real.log's zero/negative conventions cannot intervene. Its usual
  value at 1 is meaningful. Endpoints p=0 or 1 are never used in D.
* Sample means at n=0 are 0 by division-by-zero, so the clipped mean at n=0
  is 1/10. Finite-sample assertions require n>0 and limits ignore n=0.
  Empty products occur only in discarded sample size 0.
* Atom-conditioned ratios would default to 0 at zero-probability atoms.
  The conditional-mean conclusion is guarded by 0<q<1, which gives both
  atoms positive mass. Boundary q=0,1 is used only for the marginal-limit
  and likelihood statements, where it is legitimate.
* ENNReal.ofReal truncates negative weights to zero, but q∈[0,1] makes
  all specified weights nonnegative and their sum one. Finite atomic laws
  make means and variances finite, so neither Bochner default zero nor
  variance's toReal(∞)=0 affects the statement. All event masses are finite.
* 1−16/n can be negative for small n; it is then a valid weak lower bound,
  not an asserted positive probability. Every denominator in a finite
  probability bound is nonzero. No truncating natural subtraction,
  supremum, infimum, derivative, sqrt, rpow, or liminf is used.

The T5Statement auxiliary proofs in this closure and the T7 numeral proofs
only justify small denominators; T7Statement._proof_1 is the scalar-tower
instance for ENNReal scalar multiplication. None changes these hypotheses.

## SAP.P001a.T8

Source: `Challenge/Part1.lean:65–74`; definition
`Defs/WholeW1.lean:171–275`. This is a conjunction of five propositions.

The data type `WholeDensity A κ`, for a measurable type A and reference
measure κ on ℝ, consists of a Mathlib probability kernel F_x from A to ℝ,
a jointly measurable real density f(x,y)≥0 at every point, and the equality

    F_x = κ.withDensity (y↦ENNReal.ofReal(f(x,y)))   for every x.

The kernel is Markov, so F_x(ℝ)=1 for every x. There is no s-finiteness
assumption on κ in this structure. With ν a probability on A, write
P=ν⊗ₘF for the measure obtained by first drawing x from ν and then y from
the kernel F_x. This is a probability measure. Set

    H_f(x)=∫ f(x,y) log f(x,y) dκ(y),
    K(F,G)=∫⁻x klDiv(F_x,G_x) dν(x).

Mathlib's `klDiv(P,Q)` is ENNReal.ofReal of
`∫log(dP/dQ)dP + Q(ℝ).toReal − P(ℝ).toReal` when P≪Q and the
real log likelihood ratio is integrable under P, and is ∞ otherwise.
For the probability kernels the two mass terms cancel. This uses genuine
measure-theoretic KL, not simply a real integral of a density log ratio.

`WholeFiniteLog ν F G` means g(x,y)>0 P-almost surely AND log(g(x,y))
is Bochner integrable under P.

1. For every measurable type A, probability ν, reference κ, and densities
   F,G as above, assume f(x,·)log f(x,·) is κ-integrable for ν-almost every
   x, H_f is ν-integrable, and WholeFiniteLog holds. Then K(F,G)≠∞ and

       K(F,G).toReal = ∫H_f dν − ∫log g dP.

   Entropy here has the sign +∫f log f. The hypotheses are integrability
   of the sections and their real integrals, not explicitly absolute
   integrability of f log f on a product measure.

2. For every such A,ν,κ,F, natural τ, arbitrary set Θ⊆ℝ^τ, and family
   G_t indexed by the subtype Θ, assume the same entropy condition and
   WholeFiniteLog for every t. For every s∈Θ, being a global minimizer of
   t↦K(F,G_t) is equivalent to being a global maximizer of
   M(t)=∫log g_t dP. No existence or uniqueness of either optimizer is
   asserted in this proposition.

3. For every probability space, jointly iid measurable pairs
   (X_i,Y_i)∈ℝ^K×ℝ, probability ν on ℝ^K, reference κ, true F, set
   Θ⊆ℝ^τ and family G_t, assume the law of (X_0,Y_0) is ν⊗ₘF and
   WholeFiniteLog holds for each t. For every t*∈Θ, measurable sequence
   of Θ-valued statistics that_n, and real error statistics e_n with
   e_n≥0 almost surely for each n>0 and e_n→0 in probability, the following
   three additional premises imply that_n→t* in probability:

   * For each ε>0 there exists δ>0 such that, for every t∈Θ,
     ε≤dist(t,t*) implies M(t)≤M(t*)−δ.
   * Let L_n(t) be the extended-real quantity equal to
     `(1/n)Σ_{i<n}log g_t(X_i,Y_i)` if every factor is positive and to
     −∞ otherwise. Let D_n be the supremum over all t∈Θ of
     `ofReal(|(1/n)Σ log g_t−M(t)|)` when every factor is positive and
     ∞ otherwise. For each ε>0, Pr(ofReal(ε)≤D_n)→0.
   * Either, for every n>0, almost surely simultaneously for all t∈Θ,
     the observed product at t is at most the product at that_n; OR,
     with the same quantifiers, L_n(t)≤L_n(that_n)+e_n.

   Θ carries the metric inherited from the finite real coordinate space
   (its usual Pi/sup metric). This proposition does not assume finite
   entropy, finite KL, compactness, or continuity of M. The uniform
   criterion premise is a condition in probability, allowing infinite
   discrepancies on events whose probabilities vanish.

4. For every metric space E, compact Θ⊆E, θ∈Θ, and real M continuous on
   Θ, if M(t)≤M(θ) for every t∈Θ and equality implies t=θ, then the
   separation condition in proposition 3 holds for every ε>0, uniformly
   over t∈Θ. θ and the uniqueness premises are quantified before ε,δ.

5. For every A,ν,κ, finite-dimensional Θ and family G_t, and θ,t*∈Θ,
   assume t* globally minimizes K(G_θ,G_t) and equality to that minimum
   implies t=t*. Then K(G_θ,G_θ)=0, t*=θ, and K(G_θ,G_t)=0 iff t=θ.
   This is a separate identification statement. It does not by itself
   assert consistency, nor prove uniqueness of a minimizer without the
   uniqueness premise. No finite-log or entropy premise is imposed here.

Junk-value audit:

* Densities are everywhere nonnegative; ENNReal.ofReal never silently
  discards a negative modeled density. Kernel normalization excludes
  infinite or zero total mass. Reference κ can be non-s-finite, but the
  probability kernels and their joint measure are genuine finite measures.
* log 0=0 in Mathlib. In f log f at zeros this implements the correct
  convention 0 log 0=0. In log g, strict positivity P-almost surely is
  explicitly required. In sample logs a zero factor gives −∞, and in
  uniform discrepancies it gives ∞, so no zero-density observation is
  rewarded with the real log default zero.
* WholeFiniteLog excludes the Bochner default for expected model logs.
  Section entropy integrals are defined as real Bochner integrals at
  every x; nonintegrable exceptional sections may get zero, but the
  entropy hypotheses make the exceptional x set ν-null and assume outer
  integrability. The consistency part does not evaluate entropy at all.
* The first identity concludes K≠∞ before taking K.toReal, so
  toReal(∞)=0 does not assert a spurious finite KL. Other KL comparisons
  and the uniform supremum use ℝ≥0∞ directly; ∞ is meaningful there.
* For n=0 the positivity check is vacuous, the empty log sum divided by
  zero is 0, and the product is 1. Optimization conditions require n>0
  and convergence hypotheses are asymptotic, so these conventions cause
  no restriction. At positive n the cast denominator is strictly positive.
* For Θ empty the optimizer equivalence is universally quantified over
  an empty subtype. Consistency and identification explicitly select
  t*, or θ and t*, and therefore require nonempty Θ. An empty family has
  ENNReal supremum 0, an intentional complete-lattice convention.
* Unbounded uniform discrepancies produce ∞, with no real-supremum
  fallback. There is no sInf, real sSup, liminf/limsup, truncating natural
  subtraction, sqrt/rpow, or partial-function default here.

The WholeDensity constructor and projection declarations were read. Its
Markov field is a typeclass instance, not an additional hidden hypothesis.
WholeFiniteLog._proof_1 is only the measure's OuterMeasureClass instance.

## SAP.P001a.T9

Source: `Challenge/Part1.lean:76–79`; definition `Defs/Part3.lean:249–254`.
Parameters are vectors θ∈ℝ^7 with coordinates
(w_N,w_L,m_N,s_N,m_L,s_L,r). Admissibility means
w_N≥0, w_L≥0, w_N+w_L≤1, s_N>0,s_L>0,r>0. Means are unrestricted.
The three real functions are

    N(m,s;y)=exp(−(y−m)²/(2s²))/(s sqrt(2π)),
    LN(m,s;y)=N(m,s;log y)/y if y>0, and 0 otherwise,
    E(r;y)=r exp(−ry) if y≥0, and 0 otherwise.

The mixture density is
w_N N(m_N,s_N;y)+w_L LN(m_L,s_L;y)+(1−w_N−w_L)E(r;y).
For a deterministic finite real vector y∈ℝ^n, the likelihood is the finite
product of those densities over all i∈Fin n. These formulas completely
unfold `normalDensity`, `lognormalDensity`, `exponentialDensity`,
`mixtureDensity`, `MixtureAdmissible`, and `mixtureLikelihood`.

The statement is the conjunction:

* For **every** real B, there exists a real σ>0 such that
  θ(σ)=(1/2,1/4,1,σ,0,1,1) is admissible and the likelihood at the exact
  three-point vector y=(1,2,3) is larger than B.
* There does not exist an admissible θ whose likelihood on that same
  sample dominates that of every admissible θ′.

It asserts unboundedness along this particular scale-collapse path and
global nonattainment for this sample. There is no probability space or
random-sampling premise. The docstring calls it a refutation and explicitly
does not claim the quantitative lower bounds or the general-sample path.

Junk-value audit:

* Admissible s_N,s_L>0 ensure that no normalizing denominator or variance
  denominator vanishes. σ is never zero, although it may be arbitrarily
  small. sqrt(2π) is the positive real square root of a positive constant.
* The lognormal branch takes log only at positive y and divides only by
  positive y. Every sample entry is positive; zero/negative branch values
  are ordinary density support values. The exponential convention at 0
  is a permissible density version and is unused by this sample.
* All weights are nonnegative, including their real residual 1−w_N−w_L.
  Boundary zero weights are legitimate mixture parameters. The displayed
  witness has all weights strictly positive.
* Exponentials, logs of positive values, and positive-scale densities are
  finite reals at every admissible θ. Unboundedness therefore means a
  genuine real likelihood has no finite maximum, not evaluation at an
  infinite or undefined parameter value.
* Fin 3 and Fin 7 are nonempty; all tuple indices are within bounds.
  Generated Fin proof declarations and numeral-denominator proofs have
  no additional mathematical content. No Bochner integral, toReal,
  limit, supremum, rpow, truncated subtraction, or partial function occurs.

## SAP.P001a.T10

Source: `Challenge/Part1.lean:81–83`; definition `Defs/Part3.lean:256–269`.
The component densities, parameter meanings, admissibility, and likelihood
are exactly the formulas fully unfolded in T9. There are two independent
universal statements:

1. For every natural n>0 and every deterministic vector y∈ℝ^n with
   y_i>0 for every i, (a) for every real bound C there exists an admissible
   θ with likelihood greater than C, and (b) no admissible θ globally
   maximizes this sample's likelihood. The parameter witness may depend
   on both the sample and C; no particular collapse path or bound is
   specified.
2. For every natural n (including zero), positive-entry vector y∈ℝ^n,
   real B,S,δ,a,b with δ>0 and a>0, if the following subset of ℝ^7 is
   nonempty, then it is compact, the likelihood is continuous on it,
   and there exists θ in it dominating the likelihood of every θ′ in it:

       admissible θ,
       |m_N|≤B, |m_L|≤B,
       δ≤s_N≤S, δ≤s_L≤S, a≤r≤b.

   This is the entire definition of `mixtureRestriction B S δ a b`.
   There is no requirement that the component means, scales or weights be
   identified. There is no consistency or efficiency assertion.

Junk-value audit:

* Positive scales and rate and the positive lognormal sample domain
  prevent every division/log/sqrt problem listed in T9. In the restricted
  part the scales and rate are uniformly bounded away from zero.
* Nonemptiness, δ>0 and a>0 force B≥0, S≥δ and b≥a. Thus missing explicit
  order hypotheses for those other bounds do not admit a problematic
  rectangle or silently make the intended compactness result vacuous.
* n=0 is excluded for unboundedness/nonattainment. It is allowed in the
  compact attainment clause: the likelihood is then the empty product 1,
  a continuous function maximized at every member of a nonempty set.
  The positive-entry hypothesis is vacuous for that case, harmlessly.
* All differences are real subtraction. Natural and Fin casts are exact.
  There is no infinite integral, infinite-to-real conversion, supremum,
  infimum, asymptotic limit, power outside the ordinary natural powers,
  or partial/default choice in this theorem's definitions.
