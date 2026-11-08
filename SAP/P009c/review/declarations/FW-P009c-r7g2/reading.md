# Blind reading

This file was saved before opening `claims.json`, `record.json`, `earlier.json`,
or `architect-report.md`. It describes the current declarations, not an intended
paper claim. All five entries of `closure.json` and every declaration listed in
them have been read. The generated `Paired._proof_1` was also printed in Lean:
it proves `(1 + 1).AtLeastTwo`, providing the ordinary fact that the denominator
base 2 is at least two; it imposes no statistical condition.

## Shared fully unfolded mathematical notation

The following notation is used in each section to avoid repeating finite sums.
It replaces SAP definitions entirely with finite sets, real arithmetic, and
ordinary limits. The sections below specify which of these notions they use.

For a natural number n, an assignment is a function z : {0,...,n-1} → {false,true}.
A law consists of real numbers p(z) ≥ 0 whose sum over the entire binary cube
is 1. Write E_p f = Σ_z p(z)f(z) and P_p(A) = Σ_z p(z)1_A(z).
An experiment is such a law and arbitrary real functions y_i(z), defined on
the entire cube, including assignments with p(z)=0. Set

- π_i(b) = P_p(z_i=b),
- y_i(b;z) = y_i(z with coordinate i replaced by b),
- τ_i(z) = y_i(true;z) − y_i(false;z),
- θ = Σ_z p(z)[(Σ_i τ_i(z))/n],
- M_b(z) = (Σ_i 1_{z_i=b} y_i(z)/π_i(b))/n,
- W_b(z) = Σ_i 1_{z_i=b}/π_i(b),
- T(z) = M_true(z) − M_false(z),
- A(z) means W_true(z)≠0 and W_false(z)≠0,
- R(z) = n M_true(z)/W_true(z) − n M_false(z)/W_false(z)
  on A(z); the particular zero extension R_0 equals R there and 0 otherwise.

The indicator-times-outcome notation here agrees with the Lean conditional
numerator, so no unchosen branch contributes a nonzero value. An arbitrary real
extension H_t(z) is constrained to equal R_t(z) on A_t(z), at every t and every
assignment, even null assignments; it is unrestricted elsewhere.

Define J(i,j) by i=j or the existence of assignments z,z' agreeing at every
coordinate other than i with y_j(z)≠y_j(z'). This is a full-cube structural
relation, independent of support. Define D(i,j)=1 if there exists ℓ with both
J(ℓ,i) and J(ℓ,j), and 0 otherwise. Thus every diagonal D(i,i)=1 for n>0.
Write

  d_i = Σ_j D(i,j),   dbar = (Σ_i d_i)/n,
  c_i = Σ_j 1_{J(i,j)},   cbar = (Σ_i c_i)/n.

A study is a sequence indexed by natural t of natural n_t>0, with n_t tending
to infinity, and an experiment (p_t,y_t) at each t. All divisions by n_t below
use its real cast. Uniform regularity with fixed real k,q,s means, for every t,

  k>0, q≥2, s≥1;
  for all i, 1/k ≤ π_ti(true) ≤ 1−1/k;
  for all i, Σ_z p_t(z)|y_ti(z)|^q ≤ k^q;
  for all i and b, Σ_z p_t(z)|y_ti(b;z)|^s ≤ k^s.

The powers in this paragraph are Mathlib `Real.rpow`. The same k,q,s work for
every t, i and b. No independence or restriction on null-assignment outcomes is
part of regularity. Here q,s are finite real numbers.

Restricted interference means dbar_t/n_t → 0. Write B_t=√dbar_t/√n_t.
For a sequence X_t on the possibly changing binary cubes, consistency at zero
means: for every real ε>0, P_pt(ε<|X_t|)→0. Its negation means there exists ε>0
for which that probability sequence does not tend to 0. For a specified real
rate a_t, the stochastic-order assertion means exactly

  ∀ ε∈ℝ, ε>0 → ∃ K∈ℝ, K>0 ∧
    ∃ t0∈ℕ, ∀ t≥t0, P_pt(K a_t ≤ |X_t|) ≤ ε.

In particular the tail event is weak at the scaled cutoff; the consistency
tail event is strict. Little-o of f relative to g means f_t/g_t→0, with Lean's
total real division. Big-O means ∃ C>0 and t0, ∀ t≥t0,
|f_t|≤C|g_t|.

Bernoulli randomization means each π_i(true) is strictly between 0 and 1 and,
for every z, p(z)=Π_i [π_i(true) if z_i=true, otherwise 1−π_i(true)]. This is
independence of all assignment bits, with potentially unequal marginals.

A complete-randomization study means there exists a single fixed real p∈(0,1)
such that at every t, with m_t=⌊p n_t⌋ in the natural numbers, 0<m_t<n_t and

  p_t(z) = 1 / binomial(n_t,m_t) if Σ_i 1_{z_i=true}=m_t, else 0.

For paired randomization, a pairing is a permutation ρ of {0,...,n−1} with
ρ(ρ(i))=i and ρ(i)≠i for every i. The law requires even n and

  p(z) = 1/2^(n/2) if ∀ i, z_i≠z_{ρ(i)}, else 0,

where the exponent is natural-number division. Define

  Eρ(i,j) = 1 if D(i,j)=0 and there exists ℓ with J(ℓ,i) and J(ρ(ℓ),j),
             otherwise 0;
  ebar = (Σ_i Σ_j Eρ(i,j))/n;
  rsum = Σ_i 1_{J(ρ(i),i)}.

The partner is part of each pairing's data; it may vary with t.

## SAP.P009c.T40

Source: `Challenge/Part1.lean:31–42`; statement `Defs/WholeW1.lean:43–57`.

Quantifiers and hypotheses, in order: for every study S as above, then every
real k, assume k>0, the bounds 1/k≤π_ti(true)≤1−1/k for every t,i, and failure
of dbar_t/n_t→0. There is no moment assumption on the original outcomes.

Conclusion: there exists a complete family of replacement real outcome
functions y'_ti(z), for every t,i,z. Keep the same n_t and the same p_t exactly.
Using y' to recompute J,D,dbar,θ,T and the ratio domain, the following hold
jointly, in this order:

1. There exist real K,q,s giving the uniform regularity inequalities above for
   the replacement outcomes (K>0, q≥2, s≥1, including both observed and
   coordinate-replaced moments).
2. There exists a real L>0 such that both a_t=dbar_t/n_t and
   a'_t=dbar'_t/n_t have the following finite limsup L: for every real ε>0,
   there exists t0 such that a_t<L+ε for all t≥t0, and for every ε>0 and every
   natural t0 there exists t≥t0 with L−ε<a_t. The same two conditions hold for
   a'. This preserves the scalar limsup, not necessarily any individual edge,
   finite-stage graph, or every finite-stage dbar.
3. T'_t−θ'_t fails the consistency-at-zero condition above under p_t.
4. If there exists t0 such that for every t≥t0 and every z with p_t(z)>0,
   both original W_t,true(z),W_t,false(z) are nonzero, then for every real
   family H_t(z) agreeing everywhere on the replacement nonzero-denominator
   domain with n_t M'_true/W'_true−n_t M'_false/W'_false, H_t−θ'_t fails
   consistency at zero. The y' witness precedes this implication and the
   universal H, so a single y' works for all these extensions. W depends on
   the design alone, so original and replacement domains agree.

The docstring asserts precisely an HT construction and a conditional Hájek
construction, explicitly calls the latter restricted, and specifies no claim
of Hájek inconsistency for designs failing the eventual support guard.

Closure coverage: Assignment; Law and its constructor/mass/nonneg/total;
Experiment and constructor/design/outcome; mean, prob, marginal, potential,
effect, ateAt, eate, muHat, nHat, ht, ArmsNonempty; Interferes, Dependent, d,
degree, dAvg; Study and constructor/N/positive/grows/experiment; size, Regular,
RegularSequence, Restricted, InProbability; HasLimsup; HajekExtension,
EventuallySupportedArms; T40WholeStatement; the generated auxiliary fact about 2.
All are expanded above.

Junk-value audit: real division and inverse give 0 at denominator 0; positive
n_t and k and the uniform marginal inequalities prevent this in θ,T,M,W and
regularity. Both marginal probabilities are positive, since their sum is 1.
An empty observed arm makes W=0; the Hájek assertion deliberately needs the
eventual support guard, and H's other values are genuinely unconstrained.
No zero-extension value is used in this statement. Natural-to-real casts are
exact. The possible `Fin 0` empty sums in the general definitions are excluded
by the study's positive field. Real powers use nonnegative absolute-value
bases and positive k with positive exponents; neither negative-base `rpow`
nor 0^0 is used. No Bochner integral, infinity conversion, partial function,
natural truncated subtraction, square root, log, sInf or sSup occurs in the
actual expanded statement. The limsup predicate uses explicit bounds, not a
conditionally complete lattice's junk limsup: in any case 1/n_t≤a_t≤1, and
likewise for a', so there is no unboundedness convention involved. The
structure update retains positive/grows proof fields and does not reset sizes.

## SAP.P009c.T41

Source: `Challenge/Part1.lean:44–50`; statement `Defs/WholeW1.lean:65–69`.

For every study S, then every real k,q,s, assume the full uniform regularity
inequalities above, Bernoulli factorization at every t, and dbar_t/n_t→0.
Then for every real family H_t(z), if H agrees with the printed contrast on
every nonzero-denominator assignment at every t, all four conclusions hold:

1. For every ε>0, P_pt(ε<|T_t−θ_t|)→0.
2. For every ε>0, there exist K>0,t0 with
   P_pt(K B_t≤|T_t−θ_t|)≤ε for all t≥t0.
3. For every ε>0, P_pt(ε<|H_t−θ_t|)→0.
4. For every ε>0, there exist K>0,t0 with
   P_pt(K B_t≤|H_t−θ_t|)≤ε for all t≥t0.

The constants in the two stochastic-order conclusions may differ and depend
on the entire study and H. The result is not uniform over H. The docstring
states consistency and this rate for HT and every extension, including arbitrary
values on empty-arm assignments.

Closure coverage: all the shared experiment, law, study, regularity,
interference, expectation, marginal and HT definitions listed for T40 except
HasLimsup and EventuallySupportedArms; additionally Bernoulli, Op,
bernoulliRate, HTClaims, WholeEstimatorClaims, and T41WholeStatement. Every
definition in this closure is given by the formulas above; the shared generated
auxiliary proof about 2 has no substantive content.

Junk-value audit: n_t>0, k>0, interior marginals and absolute moments remove
the same division/power issues as in T40. Bernoulli sampling can put positive
mass on all-treated or all-control assignments, so the raw ratios really are
undefined there as ordinary fractions. The theorem explicitly quantifies over
extensions, rather than using division by zero as their meaning. Values on
these assignments can be arbitrarily large at each t. Their probabilities go
to zero under the stated uniform interiority and growth. The rate B_t is
strictly positive: the mandatory diagonal gives 1≤dbar_t≤n_t and n_t>0.
Thus `Real.sqrt` is applied only to positive arguments, and its denominator is
nonzero; the weak tail cutoff in Op is not evaluated at an identically zero
rate. No empty population, infinite expectation, log, negative-base rpow,
sInf/sSup, limsup/liminf, toReal, truncated subtraction or default-valued
partial function is present. All sums are over finite sets with real entries.

## SAP.P009c.T42

Source: `Challenge/Part1.lean:52–55`; statement `Defs/Part3.lean:63–68`.

For every study S, then every real k,q,s, assume full uniform regularity, a
complete-randomization study with a single fixed p∈(0,1) and treatment counts
⌊p n_t⌋ strictly between 0 and n_t at every t, dbar_t/n_t→0, and
cbar_t/√n_t→0. The existential fixed p is inside the complete-design hypothesis.
The conclusion is the following four assertions, in this order:

1. T_t−θ_t is consistent at zero in the strict-tail sense above.
2. R_0,t−θ_t is consistent at zero in the same sense.
3. T_t−θ_t has the weak-cutoff stochastic order above at rate
   a_t=√dbar_t/√n_t+cbar_t/√n_t.
4. R_0,t−θ_t has that same stochastic order.

Here cbar_t is the average number of outcomes structurally affected by one
assignment coordinate, including the mandatory diagonal. The regularity
parameters are uniform and finite real q,s. The docstring calls the extra
cbar little-o hypothesis the C1 condition and describes the same two
estimators, consistency, and rate.

Closure coverage: the shared finite laws, assignment, experiment, moment,
study, interference, eate and HT definitions; also I=1_J, outgoing=c_i,
C1=cbar, Complete, CompleteSequence, LittleO, InProbability, Op, hajek=R_0,
EstimatorClaims, bernoulliRate, and T42Statement. Constructors, fields, and the
shared generated proof about 2 are included in this reading.

Junk-value audit: m_t is a natural floor, whose default value for negative
inputs would be zero, but p>0 and n_t>0 ensure the input is positive, and
Complete requires 0<m_t<n_t. The binomial coefficient is a positive natural
number in this range, so its cast cannot make the design law divide by zero.
The complete support has a nonempty treated and control arm; interior
marginals make both weighted sums nonzero there. Consequently the zero
extension R_0 is irrelevant on support. Off support it is specified to be 0;
all such contributions to the finite probabilities are zero. n_t>0 and
dbar_t,cbar_t≥1 make all square roots, real divisions, and the stochastic rate
ordinary, with a_t>0. LittleO divides by the positive √n_t. No integer floor,
truncated subtraction, log, out-of-domain rpow, integral, infinity conversion,
empty extremum, or limsup/liminf occurs. Empty population domains are excluded.

## SAP.P009c.T43

Source: `Challenge/Part1.lean:57–62`; statement `Defs/WholeW1.lean:76–82`.

For every study S and then every real k,q,s, assume full uniform regularity,
either Bernoulli factorization for every t or the complete-randomization study
condition with a fixed p∈(0,1), and the existence of C>0,t0 such that
|dbar_t|≤C for every t≥t0. The disjunction is between two whole-sequence
conditions, rather than an independently chosen design class at each t.
For every real extension H agreeing with the ratio contrast on its domain,
the four conclusions are: consistency of T_t−θ_t, stochastic order of T_t−θ_t
at a_t=1/√n_t, consistency of H_t−θ_t, and stochastic order of H_t−θ_t at the
same a_t, with the quantifiers in the shared definitions. Restricted
interference is not a separately written hypothesis; bounded dbar and growing
n imply it. Likewise no separate cbar hypothesis is written.

The docstring states HT and every real extension of Hájek are consistent and
root-population-size bounded in probability under these hypotheses.

Closure coverage: the shared finite laws, experiment, assignment, study,
regularity, expectation, eate, HT, interference and arbitrary extension
definitions; Bernoulli, Complete, CompleteSequence, BigO, InProbability, Op,
HTClaims, WholeEstimatorClaims, and T43WholeStatement. The constructors,
fields, and generated auxiliary proof about 2 have been included.

Junk-value audit: the complete-design floor/binomial conventions and all
regularity/division/rpow conventions are as analyzed for T42. In the Bernoulli
branch, empty arms can have positive mass but H has deliberately arbitrary
real values there, as in T41. In the complete branch they are null. The
denominator √n_t is strictly positive; BigO's right side is |1|=1, and a_t>0,
so neither definition depends on zero-scale behavior. dbar uses positive n_t,
and its diagonal precludes an accidentally zero dependence measure. There are
no extrema, limsup/liminf, logs, negative square roots, Bochner integrals,
infinite values, truncated subtraction or partial-function defaults. Natural
counts and binomial coefficients are cast exactly to real numbers.

## SAP.P009c.T44

Source: `Challenge/Part1.lean:64–67`; statement `Defs/Part3.lean:78–86`.

For every study S, then every family of pairings ρ_t on its respective
population, then every real k,q,s, assume full uniform regularity, the paired
law above for every t with that ρ_t, dbar_t/n_t→0, ebar_t/n_t→0, and
rsum_t/n_t→0. The conclusion is consistency of both T_t−θ_t and R_0,t−θ_t,
followed by their two stochastic-order bounds at

  a_t = √dbar_t/√n_t + √ebar_t/√n_t + rsum_t/n_t.

All consistency thresholds and stochastic-bound constants have exactly the
quantifiers in the shared definitions. The ebar term counts only pairs without
a common affecting assignment coordinate but with affecting paired coordinates;
rsum counts each outcome's direct dependence on its own unit's partner. The
docstring describes regular paired randomization and three additional
assumptions, and asserts all three displayed rate terms.

Closure coverage: Pairing with constructor/partner/involution/no_fixed, Paired,
e, eAvg, rSum, I, and all the finite-law, experiment, assignment, study,
regularity, expectation, EATE, HT, zero-extended Hájek, and dependence
definitions; LittleO, Restricted, InProbability, Op, EstimatorClaims,
bernoulliRate, and T44Statement. The generated fact `(1+1).AtLeastTwo` was
checked directly. These are all entries of this target's closure.

Junk-value audit: positive n_t and a fixed-point-free involution force at
least two units; paired randomization also explicitly requires even n_t.
The natural division n_t/2 in 2^(n_t/2) is exact because n_t is even; 2 to any
natural power is positive, so the law has no zero denominator. Pairing.partner
is a total equivalence, not a partial lookup with defaults. On support exactly
one member of each pair is treated, so both arms are nonempty and R_0's zero
branch is irrelevant. ebar and rsum are finite sums of 0/1 quantities, hence
nonnegative. √ebar is possibly 0 but never outside the square-root domain;
the first rate term is strictly positive, so a_t>0 even if the other two terms
vanish. All little-o ratios divide by n_t>0. The absolute moments have positive
exponents and positive bound constants. There are no logs, empty extrema,
infinite expectations, infinity conversions, limsup/liminf defaults, or natural
truncated subtraction. All general definitions' empty-population cases are
excluded by the study structure.
