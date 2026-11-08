# Blind reading

Saved before opening `claims.json` or `record.json`. Only the target Challenge
declarations, `closure.json`, their definition sources, and relevant Mathlib
definitions were consulted. The generated auxiliary declarations in the closure
were also inspected with `#print` in `scratch/BlindCheck.lean`.

## Shared notation, fully unfolded

These are mathematical abbreviations used in the sections below, not additional
assumptions. All scalar data and matrix entries are real.

For K controls, v(x)=(1,x_1,...,x_K) has K+1 coordinates and
q(d,x)=(1,d,x_1,...,x_K) has K+2 coordinates. The coordinate numbered 1 in Lean
is the treatment coordinate, with intercept numbered 0. For the first n units,
V_n has rows v(X_i) and W_n has rows q(D_i,X_i), with 0 <= i < n.
For any finite matrix A and response b, the coefficient vector is
(A' A)^(-1) A'b. Matrix inversion over the reals is the usual inverse when the
determinant is nonzero and the zero matrix when it is zero.
Thus the fitted treatment coefficient on controls is
omegaHat_n=(V_n'V_n)^(-1)V_n'D and the fitted residual is
rHat_ni=D_i-v(X_i)'omegaHat_n. The treatment estimator is coordinate 1 of
(W_n'W_n)^(-1)W_n'y, where y_i=Y0_i+tau_i D_i.
The fitted weighted mean for a variable Z is
sum_{i<n} rHat_ni^2 Z_i / sum_{i<n} rHat_ni^2.

For a measurable covariate random vector X on a probability space (Omega,P),
C_X is its inverse-image Borel sigma algebra and
w(s)=(D(s)-E_P[D|C_X](s))^2. Conditional expectations are Mathlib's real
conditional expectations, with equalities stated P-almost everywhere.
Convergence in probability here is literally: for every positive extended-real
epsilon, P{epsilon <= edist(f_n,c)} tends to 0 as n tends to infinity. For real
f_n and c this is the usual convergence in probability.

For a sequence H_i of real random variables, the abbreviation M(H) means BOTH:
(a) every H_i is Bochner integrable; (b) n^(-1)sum_{i<n}H_i converges in
probability to the constant E[H_0]. At n=0 that average is defined to be 0.

The eight-family regression regularity R(D,Y0,tau,X) means:

1. M(v_j v_k), for every j,k in Fin(K+1);
2. M(v_j D), for every j;
3. M(D^2);
4. M(D Y0);
5. M(v_j Y0), for every j;
6. M(D^2 tau);
7. M(v_j D tau), for every j;
8. M(v_j v_k tau), for every j,k;
9. det(E[v(X_0)v(X_0)']) != 0;
10. w_0 is integrable and E[w_0] > 0, where w_0 uses D_0 and X_0.

All products in a family use the same unit i. Thus this regularity assumes
convergence of empirical moments, not convergence of the estimator being
asserted. The intercept components ensure, among other things, integrability
of D_i, Y0_i, and tau_i.

The seven-family effective-mean regularity E(D,Z,X,omega) sets
r_i=D_i-v(X_i)'omega and means:

1. M(v_j v_k), for every j,k;
2. M(v_j D), for every j;
3. M(r^2 Z);
4. M(r^2);
5. M(r Z v_j), for every j;
6. M(r v_j), for every j;
7. M(Z v_j v_k), for every j,k;
8. det(E[v(X_0)v(X_0)']) != 0;
9. E[r_0^2] > 0.

Independence of an infinite sequence of tuples means independence of their
generated sigma algebras: probabilities of finite intersections of measurable
coordinate events equal products of their probabilities. Identical distribution
means a.e. measurability and equality of pushforward probability measures with
the tuple at index 0. Two-function independence has the corresponding
two-event product meaning.

The SAP conditional-independence predicate for U and D given X says, for every
Borel set A in the range of U and B in the range of D,
E[1_{U in A,D in B}|C_X] = E[1_{U in A}|C_X] E[1_{D in B}|C_X] a.e.
The exceptional null set may depend on A and B. In the targets the conditioned
variables take values in finite products of real spaces, so this is the usual
event-factorization definition of conditional independence.

## SAP.P015b.T11

Challenge: `SAP/P015b/Challenge/Part1.lean:60-62`.
Definitions: `Defs/Part5.lean:17-54` and `Defs/Part1.lean:73-82`.

This is a conjunction of concrete assertions without hypotheses. Put
g(a)=1/(1+exp(-a)), L=log(99), theta*=(-L,2L), and
A=((1,0),(1,1)). For a real vector theta=(theta_0,theta_1), define
ell(theta)=log g(theta_0)+99 log(1-g(theta_0))
+99 log g(theta_0+theta_1)+log(1-g(theta_0+theta_1)).
This is the Bernoulli log likelihood for 100 observations at each of D=0 and
D=1, respectively with 1 and 99 successes, omitting a parameter-independent
binomial coefficient. Define the degree-at-most-N Taylor polynomial
T_N(c,a)=sum_{k=0}^N g^(k)(c)(a-c)^k/k!, using Mathlib iterated derivatives
within the whole real line.

The exact assertions, in their conjunction order, are:

* For every real two-vector theta, ell(theta)<=ell(theta*).
* For every such theta, ell(theta)=ell(theta*) implies theta=theta*.
* g(-L)=1/100, g(L)=99/100, and
  log(((1+99)/200)/(1-(1+99)/200))=0.
* 9/2<L and pi<9/2.
* For every natural N, both |T_N(0,L)-g(L)| and
  |T_N(0,-L)-g(-L)| are >=49/100, and
  |100(99/100-T_N(0,L))|>=49.
* There exists a formal complex multilinear power series s at zero for
  z |-> (1+exp(-z))^(-1), converging to that function on some positive-radius
  ball, whose norm-coefficient convergence radius is exactly ofReal(pi).
  The latter radius is the extended-nonnegative-real supremum of radii r for
  which all ||s_n|| r^n have a common real bound.
* det(100 A'A)=10000; 0<1<100 and 0<99<100.
* For every coordinate j in Fin 2,
  sum_{i in Fin 2} A_ij(k_i-100 g((A theta*)_i))=0, with k=(1,99).
* The values of g, log odds, pi<9/2, and 9/2<L are repeated, and
  |T_0(0,L)-g(L)|=49/100.
* A theta*=(-L,L), (1+99)/200=1/2, and, for every natural N,
  sum_i A_i1(k_i-100 T_N(0,(A theta*)_i))
  =100(99/100-T_N(0,L)).

The docstring describes this as a full-rank binary 200-observation example
with a unique logistic fit outside Taylor radius pi and the all-degree error
bounds. The source represents the 200 observations by their two grouped
counts, not by a matrix with 200 separate rows.

Junk-value audit: all real denominators in the fixed data are positive;
1+exp(-a)>0 and 0<g(a)<1 for every real a, so every real logarithm used in
ell has positive argument. The log odds is evaluated only at 1/2 and L is
log of positive 99. Real.log's values at zero and negative inputs cannot
affect this statement. Every factorial is a positive natural cast, so Taylor
coefficients do not divide by zero. Iterated derivatives have the usual
totalization at nondifferentiable points, but g is smooth everywhere and the
within set is univ. Complex inversion assigns zero at poles of the totalized
complex sigmoid; the series assertion concerns a neighborhood of zero, and
its radius is finite and positive. No assertion that the function is defined
analytically at the poles is made. The ENNReal supremum defining the radius
is in a complete lattice and is fixed here to finite positive pi; ofReal does
not truncate a negative radius. N=0 is included deliberately. The fixed
matrix and vector index types are nonempty. All subtractions and fractions
displayed in the real formulas are real, not truncated natural subtraction.

Closure auxiliaries: TaylorFailure._proof_1,_2,_3,_4,_7 certify natural
numerals 2,200,9,49,10000 are at least two; _proof_5 and _proof_6 supply
continuous addition and constant scalar multiplication on the complexes.
twoCellLogLikelihood._proof_1,_3 certify 100 and 99 are at least two;
_proof_2 supplies NeZero 2. None adds an assumption or changes a value.

## SAP.P015b.T15

Challenge: `SAP/P015b/Challenge/Part1.lean:64-73`.
Definitions: `Defs/WholeW2.lean:18-126` plus the applicable shared definitions
from `Defs/Part1.lean` and `Defs/Part2.lean` above.

There are four conjuncts; each universal conjunct independently quantifies its
own data.

1. For every type Omega in the declared universe, measurable-space structure,
   probability measure P, natural K, real sequences D,Y0,tau and real
   K-vector sequence X, assume all coordinates of every sequence are
   measurable, the tuples (D_i,Y0_i,tau_i,X_i) are mutually independent and
   identically distributed with tuple 0, and (Y0_0,tau_0) is conditionally
   independent of D_0 given X_0 in the event sense stated above. Next, for
   every real vector omega of length K+1, assume
   E[D_0|C_X0]=v(X_0)'omega a.e. and R(D,Y0,tau,X). Then w_0 tau_0 is
   integrable and the actual treatment estimator converges in probability to
   E[w_0 tau_0]/E[w_0]. The outcome is defined as Y0_i+tau_i D_i, rather than
   a separately quantified arbitrary outcome.
2. For every Omega,P,K and the same sequence types, require only measurability
   of unit 0 (not iid here), its conditional independence, a vector omega with
   the same linear conditional-mean identity, and R. Set m=v(X_0)'omega,
   r=D_0-m, C=C_X0. Conclude all six identities:
   E[D_0 Y0_0|C]=E[D_0|C]E[Y0_0|C] a.e.; E[r|C]=0 a.e.;
   E[r tau_0|C]=E[r|C]E[tau_0|C] a.e.; E[r tau_0|C]=0 a.e.;
   E[D_0 Y0_0]-E[m Y0_0]=0; E[r m tau_0]=0.
3. For every type Omega (no measurable structure required), K, arbitrary
   D,Y0,tau,X sequences, and potential outcomes Y_i(s,d) with
   Y_i(s,d)=Y0_i(s)+tau_i(s)d for every i,s,d, and then every natural n and
   s in Omega, let y_i=Y_i(s,D_i(s)) and theta=(W_n'W_n)^(-1)W_n'y.
   Conclude theta equals that inverse expression and its coordinate 1 is
   the treatment estimator in the shared definition. The vector type has
   exactly K+2 coordinates. This particular conjunct is a definitional
   formula/substitution identity; the convergence and moment conjuncts are
   separate substantive assertions.
4. An unconditional finite confounding witness: A=Fin 2, p_0=p_1=1/2,
   D_i equal to the natural value i cast to real, X constant in Unit,
   r_i=D_i-1/2, Y0_i=tau_i=D_i, Y_i(d)=D_i+D_i d.
   Here finite expectation is sum_i p_i Z_i; finite event mass is
   sum_i 1_event(i)p_i; a finite cell mean is the weighted cell numerator
   divided by the cell mass. The statement asserts p_i>=0 and sum p_i=1;
   the displayed affine outcome identity; E[D|X]=1/2 in each cell;
   E[D^2]=1/2 whereas E[D]^2=1/4; E[rD|X]=1/4 whereas
   E[r|X]E[D|X]=0; failure of conditional independence of (D,D) and D
   given X (in the finite event-mass factorization sense);
   coordinate 1 of (E[qq'])^(-1)E[q(Y0+tau D)] is 2, with q=(1,D);
   E[r^2]=1/4 and E[r^2 D]/E[r^2]=1/2.

The docstring describes the convergence, moment factorizations, corrected
coefficient-column dimension, and a witness to insufficiency of conditions
numbered (1) and (3). It gives no standalone refutation label.

Junk-value audit: probability measures rule out the zero measure and make
conditional-expectation sigma-finiteness automatic on measurable subalgebras.
Measurability of X ensures C_X is a subalgebra. The intercept moment families
and finite linear combinations give the integrability of the conditional
expectation arguments and identity products, so conditional expectation and
Bochner-integral zero defaults do not account for the conclusions. The weight
denominator is explicitly finite and positive. Finite singular sample Gram
inverses really are zero, and n=0 is allowed; no eventual a.s. nonsingularity
at a fixed deterministic n is assumed. These conventions can change a finite
sample estimator, though the asserted limit is the ordinary probability limit.
The finite witness has cell mass 1, weight mean 1/4 and population Gram
determinant 1/4; it uses no singular or zero-denominator fallback. Empty
control types K=0 are allowed; the intercept and treatment spaces remain
nonempty. Fin n may be empty at n=0. All finite-data casts are ordinary exact
casts of 0 and 1. No sInf, sSup, log, sqrt, real powers, limsup, liminf, or
other partial-operation defaults occur in this closure, except those already
accounted for in Mathlib integration and matrix inversion.

Closure auxiliaries: WholeCoefficientFormula._proof_1 and
treatmentEstimate._proof_1 supply NeZero(K+2); WholeConfoundingWitness._proof_1
and _proof_2 are numeral certificates for 2 and 4, and _proof_3 is NeZero 2.
They impose no mathematical hypotheses.

## SAP.P015b.T22

Challenge: `SAP/P015b/Challenge/Part1.lean:75-83`.
Definitions: `Defs/WholeW2.lean:18-27,62-78,128-136`, with shared definitions
from `Defs/Part1.lean:16-18` and `Defs/Part2.lean:17-22,27-28,37-60`.

This is exactly conjunct 1 of T15, considered independently: for every
measurable Omega, probability measure P, natural K, measurable real sequences
D,Y0,tau and measurable real K-vector sequence X, with independent identically
distributed tuples (D_i,Y0_i,tau_i,X_i), conditional independence of
(Y0_0,tau_0) and D_0 given X_0, every omega satisfying
E[D_0|C_X0]=v(X_0)'omega a.e., and all ten clauses of R listed above, conclude
integrability of w_0 tau_0 and convergence in probability of coordinate 1 of
(W_n'W_n)^(-1)W_n'(Y0+tau D) to E[w_0 tau_0]/E[w_0].
The order is data, measurability, independence and identical distribution,
conditional independence, omega, linearity, regularity, then the conclusion.
All of these hypotheses are antecedents, not existential choices of data.

The docstring explicitly mentions iid data, affine outcomes, linear treatment
mean, unconfoundedness, regularity, integrable numerator, positive finite mean
weight, and completion on finite singular samples.

Junk-value audit, independently: C_X is measurable and P finite; D and all
integral arguments are integrable by the moment families (including intercept
coordinates and their linear combinations). Thus neither conditional
expectation nor the limiting integrals uses an undefined-input zero default.
E[w_0]>0 and integrability prohibit a zero or infinite ratio denominator.
The inverse formula returns zero coefficients on a singular W_n'W_n; n=0
is admitted, and the empirical moment averages also assign 0 at n=0. The
theorem promises convergence in probability, not a finite-n unique minimizer.
K=0 is admissible, but the intercept and treatment columns always exist.
There are no natural subtractions or problematic casts, extrema, logarithms,
square roots, real powers, limsups, or liminfs. The only generated auxiliary is
treatmentEstimate._proof_1, the unconditional NeZero(K+2) instance.

## SAP.P015b.T23

Challenge: `SAP/P015b/Challenge/Part1.lean:85-92`.
Definitions: `Defs/WholeW1.lean:16-46`, `Defs/Part2.lean:17,24-35,41-47,62-72`,
and `Defs/Part1.lean:16-18,70-71`.

For every measurable type Omega, probability measure P, natural K, sequences
of measurable real D_i,Z_i and measurable real K-vectors X_i, with the tuples
(D_i,Z_i,X_i) mutually independent and identically distributed with tuple 0,
and then every vector omega of length K+1, assume
E[D_0|C_X0]=v(X_0)'omega a.e. and all nine clauses of the seven-family
effective-mean regularity E(D,Z,X,omega) listed above. Conclude convergence
in probability of the actual fitted mean
sum_{i<n}(D_i-v(X_i)'(V_n'V_n)^(-1)V_n'D)^2 Z_i /
sum_{i<n}(D_i-v(X_i)'(V_n'V_n)^(-1)V_n'D)^2
to E[(D_0-E[D_0|X_0])^2 Z_0] /
E[(D_0-E[D_0|X_0])^2]. There is no causal or treatment-outcome independence
condition on Z, and no finite-n full-rank or nonzero fitted-denominator premise.

The docstring describes a sufficient seven-family regularity reading,
nonsingular population control Gram, positive mean weight, and explicitly
acknowledges totalized finite exceptions.

Junk-value audit: intercept moments supply integrability of D, Z and relevant
products. The linear conditional-mean identity identifies r_0^2 with w_0 a.e.;
the regularity requires r_0^2 and r_0^2 Z_0 integrable and E[r_0^2]>0.
Consequently the population ratio does not use a zero integral or division
fallback. The finite ratio can be 0/0, including n=0 or identical treatments;
its value is then 0. A singular control Gram yields fitted coefficient zero,
not an arbitrary OLS solution; this can change finite-n weights, and is
disclosed. The positive population Gram determinant condition prevents a
singular population projection. K=0 is allowed and leaves one intercept.
No problematic natural subtraction, cast, log, sqrt, rpow, extrema or sequence
limsup/liminf occurs. There are no generated proof declarations in this closure.

## SAP.P015b.T24

Challenge: `SAP/P015b/Challenge/Part1.lean:94-102`.
Definitions: `Defs/WholeW1.lean:16-22,53-99`, together with the shared estimator,
weight and R definitions from `Defs/Part1.lean` and `Defs/Part2.lean`.

This is a conjunction of two independently quantified propositions.

1. For every measurable Omega, probability measure P, natural K, measurable
   real sequences D,Y0,tau and real K-vector X, require mutually independent
   identically distributed tuples (D_i,Y0_i,tau_i,X_i), independence of D_0
   from (Y0_0,tau_0,X_0), and R(D,Y0,tau,X). Conclude that both the treatment
   estimator (W_n'W_n)^(-1)W_n'(Y0+tau D) at coordinate 1 and the fitted
   squared-treatment-residual mean of tau converge in probability to E[tau_0].
   There is no separate linear conditional-mean premise, since random
   assignment is to imply it. R has all the moment, determinant and positive
   mean residual-weight clauses listed above.
2. For every measurable Omega, probability measure P, K, single measurable
   real random variables D,Y0,tau and real K-vector X, assume independence
   of D from (Y0,tau,X), D in L^2(P), tau integrable, and Var_P(D)>0.
   Here variance is literally
   toReal(integral^- ||D-E[D]||_e^2 dP). Conclude all nine assertions:
   E[D|C_X]=E[D] a.e.; w=(D-E[D])^2 a.e.; w independent of tau;
   w integrable; w tau integrable; E[w]=Var(D); E[w]>0;
   E[w tau]=E[w]E[tau]; E[w tau]/E[w]=E[tau].
   Y0 is measurable but need not be integrable in this population-only
   conjunct, since no expectation of Y0 is used.

The docstring describes both population identities and both estimator limits
under random assignment, iid sampling, and eight-family regularity.

Junk-value audit: for population identities, L^2 on a probability space implies
D integrable and finite variance; thus toReal(infinity)=0 cannot be used.
The positive variance hypothesis gives a positive finite weight denominator.
Independence and tau integrability make w tau integrable. The measurable
subalgebra C_X and finite measure ensure genuine conditional expectations.
For convergence, R includes tau,D,Y0 integrability through the intercept
families, finite positive E[w_0], and nonsingular population control Gram.
The finite inverses return zero on singular Gram matrices, and fitted-weight
ratios return 0 when the denominator is zero; n=0 is also allowed. These
finite exceptions are not assumed absent at all sufficiently large
deterministic sample sizes. K=0 is legitimate; the intercept and treatment
coordinates remain. No other junk-value source (truncated subtraction,
log/sqrt/rpow, empty extrema, limsup/liminf, partial function defaults) occurs.
The closure auxiliaries are treatmentEstimate._proof_1, supplying NeZero(K+2),
and RandomizationWholePopulation._proof_1, certifying the natural numeral 2
is at least two. Neither is an extra hypothesis.
