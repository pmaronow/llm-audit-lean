# Blind statement reading

Written before opening either `claims.json` or `record.json`. Sources read: all
entries of all three closures in `closure.json`, their complete source
declarations in `Defs/Part1.lean`, `Defs/Part2.lean`, `Defs/Part3.lean`, and
`Defs/Part5.lean`, and the three Challenge docstrings/statements. The generated
`NEDConditions._proof_1` was inspected with Lean: it is just the `AtLeastTwo`
instance for the numeral 4, not a mathematical premise.

## SAP.P004c.T41

### Objects, definitions, and quantifiers

Universally quantify a family of types `X_N` (in any one universe), each with a
Mathlib metric and an independently specified measurable space. Universally
quantify a population for every natural number N, and real numbers p,d. A
population consists exactly of nonempty subsets A_Ni of X_N for i in `Fin N`, a
measure zeta_N, an arbitrary real-valued function Y_N(x,z), and a function B_N
from real numbers to sets of real numbers. Here an assignment z is a function
`Fin N -> Bool`, and a circle table is a function `(Fin N) -> (Fin N -> Bool) ->
R`. There is no dimensional, Euclidean, distinct-node, or compatibility
assumption on these objects built into the structure.

Write

* delta_Ni(x) = `Metric.infDist x A_Ni`, the infimum point-to-set distance;
* D_Nij = inf {dist(x,y) : x in A_Ni, y in A_Nj};
* E_Ni(t) = {x : delta_Ni(x) belongs to B_N(t)};
* R_Ni(t,z) = (integral over E_Ni(t) of Y_N(x,z) with respect to zeta_N) /
  `(zeta_N(E_Ni(t))).toReal`.

These are unrestricted distance bands, not necessarily exact circles, annuli,
or bands fixed across populations. Integrals are Mathlib Bochner set integrals.
The population constructor and the `node`, `zeta`, `outcome`, `bands`
projections in the closure have exactly these meanings.

For a Bool a put b(a)=1 for true and 0 for false, and c(p,a)=p for true and
1-p for false. The design weight is q_N(z)=product over i of c(p,z_i).
For any real assignment function U, expectation is the finite sum
E_N U = sum_z q_N(z) U(z), probability of an event A is
sum_z q_N(z) 1_A(z), covariance is E_N(UV)-(E_N U)(E_N V), and variance is
E_N(U^2)-(E_N U)^2. All the probabilities in this declaration use the same
scalar p at every node and every N. The underlying definitions also accept a
vector of real coin parameters, without built-in positivity requirements.

For the fixed d write R_i(z)=R_Ni(d,z). The arm marginal is
m_ia=E_N[1_{z_i=a} R_i(z)]/c(p,a); node effect is m_i,true-m_i,false; AME is
tau_N=(sum_i (m_i,true-m_i,false))/N. The HT estimator is
T_N(z)=(sum_i [b(z_i)R_i(z)/p-(1-b(z_i))R_i(z)/(1-p)])/N.

For any circle table at any radius t, say that source j affects row i if i=j,
or if there exist assignments z,z' agreeing at all k different from j for
which row i has different values. Rows i,j share a source if some l affects
both. `LocalAt` says that h < D_Nij implies they do not share a source.
The closed node ball of i with radius r is the finite set {j : D_Nij <= r}.

The hypotheses, after p,d and the population have been universally quantified,
are:

1. 0<p<1 and 0<=d.
2. There exists b>0 and an eventual threshold such that for every N above it,
   every x and every assignment z satisfy |Y_N(x,z)|<b.
3. There exists a function h:R->R nonnegative at every nonnegative argument,
   such that for every t>=0 there is an eventual N threshold (allowed to depend
   on t) above which rows of R_N(t) at node separation greater than h(t) never
   share a source.
4. There exists a function c:R->R such that for every r>=0 there is an eventual
   N threshold (allowed to depend on r) above which every i's closed node ball
   of radius r has cardinality at most c(r). No positivity of c is separately
   asserted.
5. Eventually in N, for every i, E_Ni(d) is measurable, its measure is strictly
   positive and strictly less than infinity, and for every z the restriction
   of Y_N(.,z) to this set is integrable.

The conclusion is a conjunction. First V_N=Var_N(T_N) is `IsBigO atTop` of
1/N: some real constant C eventually bounds |V_N| by C |1/N|. Second, IF there
exists v>0 such that eventually v<=N V_N, THEN for every real x,

    sum_z q_N(z) 1_{(T_N(z)-tau_N)/sqrt(V_N) <= x} -> Phi(x),

as N tends to infinity. Phi(x) is
`(ProbabilityTheory.gaussianReal 0 1 (Set.Iic x)).toReal`, the standard Gaussian
CDF. This is actual CDF convergence, not a renamed assumption or an estimate
with an arbitrary comparison distribution. The lower bound belongs only to
the second conjunct; the variance order assertion has no nondegeneracy
hypothesis. Every eventual quantifier uses Mathlib `Filter.atTop` on natural
numbers (equivalently, all N above some threshold).

### Totalization and junk-value audit

* Division is real field division, so division by zero is zero. The p and 1-p
  denominators in marginal and HT are strictly positive under the hypotheses.
  Division by N is zero at N=0. All conclusions are asymptotic, so this isolated
  size has no effect. `Fin 0` has no nodes and has one assignment (the empty
  function); node sums are 0 and the design's empty product is 1.
* A nonintegrable Bochner integral is totalized to 0; `ENNReal.toReal` sends
  infinity to 0; a zero spatial measure gives a zero real denominator.
  Hypothesis 5 excludes all of these at the radius under study eventually.
  At earlier sizes and other radii these values are possible. Locality is
  imposed on the resulting totalized circle table for every radius; the
  theorem's conclusions use only its eventual genuine values at d.
* The sets defining D_Nij are nonempty (both nodes are nonempty) and bounded
  below by 0. Thus real `sInf` is a genuine finite infimum, although it need
  not be attained. The point-to-node infimum is also genuine because nodes
  are nonempty. No empty/unbounded infimum convention is used. Distinct sets
  may have separation zero, and D need not obey a triangle inequality here.
* `Real.sqrt` is zero on nonpositive inputs. For valid coins V_N is a genuine
  nonnegative variance. In the CDF conclusion the extra lower bound makes
  N positive and V_N strictly positive eventually. The standardized
  denominator can vanish only at discarded initial sizes. No upper or lower
  limit is defined through a totalized `limsup`/`liminf`.
* Phi's `toReal` is safe because a Gaussian measure of any set is at most 1.
* Natural numbers N and finite cardinalities are cast exactly into R, without
  truncation or overflow. All subtraction in these formulas is in R. There is
  no natural/integer truncated subtraction, logarithm, real power, supremum,
  partial-function default, or other such convention in this statement's SAP
  closure.

The docstring describes C1-C4, the variance bound, and the conditional CLT. The
genuine-average hypothesis is explicit in the statement, but not enumerated in
that short docstring.

## SAP.P004c.T42

### Objects, definitions, and quantifiers

Universally quantify metric/measurable types X_N, a population at each natural
size N, and p,d in R. A population supplies nonempty node sets A_Ni, a measure
zeta_N, outcomes Y_N(x,z), and arbitrary real distance-band sets B_N(t).
Assignments are all functions `Fin N -> Bool`. Set
delta_Ni(x)=`Metric.infDist x A_Ni`,
D_Nij=inf {dist(x,y):x in A_Ni,y in A_Nj},
E_Ni(t)={x:delta_Ni(x) in B_N(t)}, and
R_Ni(t,z)=integral_{E_Ni(t)}Y_N(x,z) dzeta_N /
`(zeta_N(E_Ni(t))).toReal`. These are precisely the fields, constructor,
projections, and spatial-average definitions appearing in this closure; in
particular the spatial spaces and distance bands have no Euclidean or circle
shape restriction.

Write b(true)=1,b(false)=0 and c(p,true)=p,c(p,false)=1-p. The independent
Bernoulli design has finite mass q_N(z)=product_i c(p,z_i). E_N U means
sum_z q_N(z)U(z), Pr_N(A) means sum_z q_N(z)1_A(z), and
Var_N(U)=E_N(U^2)-(E_N U)^2 (the covariance definition specialized to U,U).
At the fixed d, with R_i(z)=R_Ni(d,z), define
m_ia=E_N[1_{z_i=a}R_i(z)]/c(p,a),
mu_a=(sum_i m_ia)/N, and
tau_N=(sum_i (m_i,true-m_i,false))/N.

For each assignment let n_a(z)=sum_i 1_{z_i=a}. Its arm mean is
M_a(z)=(sum_i 1_{z_i=a}R_i(z))/n_a(z), and the Hajek estimator is
H_N(z)=M_true(z)-M_false(z). The corrected linearization is

    L_N(z) = (1/N) sum_i [mu_true-mu_false
                + b(z_i)(R_i(z)-mu_true)/p
                - (1-b(z_i))(R_i(z)-mu_false)/(1-p)].

This is the `augmented` definition with arm fits g_i(a)=mu_a; in the general
`augmented` definition g_i(a) is any real function of a node and a Bool.
The `barMu`, `nodeEffect`, `ame`, `armCount`, `armMean`, `hajek`, and
`linearHajek` definitions are exactly the formulas just given.

A source j affects row i if i=j or if two assignments differing only possibly
at j give different values of that row. Rows share a source when some source
affects both. The closed ball at node i is {j:D_Nij<=r}. `LocalAt` excludes
shared sources for pairs with h<D_Nij.

The hypotheses are, in order:

1. 0<p<1; 0<=d.
2. There exists b>0 such that eventually in N all x,z have |Y_N(x,z)|<b.
3. There exists h:R->R with h(t)>=0 for t>=0; for each t>=0, eventually in N
   the rows of R_N(t) separated by more than h(t) share no source. The eventual
   threshold is inside the quantifier on t.
4. There exists c:R->R such that for each r>=0, eventually in N, all closed
   balls of radius r have cardinality at most c(r). Its threshold may depend
   on r; c has no separate sign premise.
5. Eventually for every i the chosen region E_Ni(d) is measurable, its measure
   is in (0,infinity), and its outcomes are integrable for every assignment.
6. There exists v>0 such that eventually v<=N Var_N(L_N).

Under these hypotheses, for every real x,

    Pr_N((H_N-tau_N)/sqrt(Var_N(L_N)) <= x) -> Phi(x).

Here the probability is the explicit finite Bernoulli sum, convergence is
Mathlib `Tendsto` from natural `atTop` to the real neighborhood filter, and
Phi(x) is the measure of `Iic x` under `gaussianReal 0 1`, converted to R.
Nondegeneracy concerns the corrected linearization's actual variance, not the
variance of H_N and not a second-moment bound. There is no additional C5 or
homophily premise and no separate variance-order conclusion in this theorem.

### Totalization and junk-value audit

* The real divisions by p and 1-p are safe under 0<p<1. Division by N gives
  zero at N=0; node sums and mu_a are then zero. `Fin 0` is empty but the
  assignment space has one empty assignment, with weight 1. Asymptotic claims
  are unaffected by this finite initial case.
* Even when N>0 both all-treated and all-control assignments have positive
  probability. An empty arm has numerator and count zero, and its mean is
  explicitly the real totalization 0/0=0. Consequently H_N is defined on the
  whole assignment space. This convention affects finite-sample values, but
  the probability of either empty arm is p^N+(1-p)^N and tends to zero. The
  Challenge docstring explicitly discloses this convention.
* Set integrals can totalize to zero if nonintegrable, `toReal infinity=0`,
  and zero-measure regions give a zero denominator. The eventual
  genuine-average hypothesis excludes these at d in every sufficiently large
  population. The locality hypothesis at other radii still concerns the
  totalized table if those radii fail to have genuine averages.
* Node nonemptiness and nonnegative metric distances ensure both spatial
  infima are genuine finite infima; they need not be attained. There is no
  positivity or metric premise on separations of distinct node sets here.
* For valid coins the variance under the square root is nonnegative, and
  hypothesis 6 makes it strictly positive eventually. Early zero denominators
  give zero standardized values but do not change convergence. Gaussian set
  masses are finite, so Phi's `toReal` does not collapse infinity.
* Casts from N and finite cardinality to R are exact. Subtractions are real,
  with no truncation. No logarithm, real power, empty/unbounded supremum,
  `limsup`/`liminf`, or partial-function default is used in this SAP closure.

The docstring's corrected-linearization standardization and empty-arm convention
agree with the displayed formulas. It abbreviates the explicit eventual
genuine-average premise.

## SAP.P004c.T44

### Objects, definitions, and quantifiers

Universally quantify metric/measurable types X_N, populations P_N for every
natural size N, and real p,d. A population has nonempty node sets A_Ni, a measure
zeta_N, real outcomes Y_N(x,z), and real distance-band sets B_N(t). Assignments
are all Bool functions on `Fin N`. Its structure constructor and projections
do not impose a dimension or a relation between the metric and measurable
space. Define

    delta_Ni(x) = Metric.infDist x A_Ni,
    D_Nij = inf {dist(x,y):x in A_Ni,y in A_Nj},
    E_Ni(t) = {x:delta_Ni(x) in B_N(t)},
    R_Ni(t,z) = integral_{E_Ni(t)} Y_N(x,z) dzeta_N
                 / (zeta_N(E_Ni(t))).toReal.

These are genuine point/set and set/set infima for nonempty nodes, and the
integral is the Bochner integral. Write R_i(z)=R_Ni(d,z).

Put b(true)=1,b(false)=0 and c(p,true)=p,c(p,false)=1-p. The assignment mass is
q_N(z)=product_i c(p,z_i), and E_N U=sum_z q_N(z)U(z),
Pr_N(A)=sum_z q_N(z)1_A(z),
Cov_N(U,V)=E_N(UV)-(E_N U)(E_N V), Var_N(U)=Cov_N(U,U).
All uses set every node's parameter to the same p. Define
m_ia=E_N[1_{z_i=a}R_i(z)]/c(p,a),
mu_a=(sum_i m_ia)/N, node effect m_i,true-m_i,false, and
tau_N=(sum_i(m_i,true-m_i,false))/N. The HT estimator is
T_N=(sum_i[b(z_i)R_i/p-(1-b(z_i))R_i/(1-p)])/N.
The arm count n_a=sum_i 1_{z_i=a}, arm mean
M_a=(sum_i 1_{z_i=a}R_i)/n_a, and Hajek estimator H_N=M_true-M_false.
The corrected linearization is the `augmented` estimator using the constant
arm fits mu_a:

    L_N = (1/N) sum_i [mu_true-mu_false
             + b(z_i)(R_i-mu_true)/p
             - (1-b(z_i))(R_i-mu_false)/(1-p)].

The closed node ball J_Ni(s) is the finite set {j:D_Nij<=s}. For a finite set
J of nodes, the conditional expectation on their assignments is explicitly

    C_J U(z) = sum_z' q_N(z') 1_{forall j in J, z'_j=z_j} U(z')
                  / product_{j in J} c(p,z_j).

The L2 norm of U is sqrt(sum_z q_N(z) U(z)^2). Thus neither conditional
expectation nor L2 near-epoch dependence is a placeholder.

The hypotheses, after universal quantification of P,p,d, are:

1. 0<p<1 and 0<=d.
2. There exists b>0 such that eventually in N, for all x,z,
   |Y_N(x,z)|<b (`BoundedOutcomes`).
3. Eventually in N, every E_Ni(d) is measurable, has measure strictly between
   0 and infinity, and every Y_N(.,z) is integrable on it (`WellDefined`).
4. There exist functions psi:R->R and g_Ni:R and a real G, simultaneously
   satisfying all of the following (`NEDConditions`):
   psi is nonnegative and antitone on [0,infinity), and tends to zero at
   infinity; there exist a real exponent alpha>4 and reals C,S with S>0 such
   that for every s>=S, psi(s)<=C s^(-alpha); for EVERY N,i,
   0<g_Ni<=G; and for EVERY N,i,s>=0,
   sqrt(E_N[(R_i-C_{J_Ni(s)}R_i)^2]) <= g_Ni psi(s).
   No sign condition is explicitly imposed on C or G; the inequalities
   impose their needed signs on nonempty indices. Real exponentiation is
   Mathlib `Real.rpow`; its numeral-4 helper is only a typeclass proof.
5. For EVERY N the separation D_N is a metric on the nodes: nonnegative,
   D_Nij=0 iff i=j, symmetric, and satisfying D_Nik<=D_Nij+D_Njk.
6. There exists Cb>0 such that eventually in N, for EVERY i and EVERY real
   s>=0, |J_Ni(s)|<=Cb(1+s^2). The single eventual threshold precedes both
   quantifiers i,s. This is stronger in its threshold order than a separately
   eventual estimate for each fixed radius; the additive 1 also changes the
   behavior at small radii.

There is no finite-range/shared-source assumption here. The conclusion is the
following fourfold conjunction under hypotheses 1-6:

1. For every natural N, if N>0 and this particular population has genuine
   averages at d, E_N T_N=tau_N. The outer asymptotic hypotheses remain in
   scope, even though this finite identity does not need all of them.
2. Var_N(T_N)=O(1/N): some real constant eventually bounds its absolute value
   by that constant times |1/N| (`Asymptotics.IsBigO atTop`).
3. For every epsilon>0,
   Pr_N(epsilon<|sqrt(N)(L_N-H_N)|) -> 0 (`InProb`). The displayed
   difference is linearization minus Hajek, and the sign disappears in the
   absolute value.
4. IF there exists v>0 with eventually v<=N Var_N(L_N), THEN for every real x,
   Pr_N((H_N-tau_N)/sqrt(Var_N(L_N))<=x) -> Phi(x), where Phi(x) is
   `(gaussianReal 0 1 (Iic x)).toReal`. This lower bound is needed only for
   this fourth conclusion, not for the other three.

Every convergence above is Mathlib `Tendsto` with natural `atTop` as source and
the real neighborhood filter as target. The docstring explicitly describes a
restriction to the spacing bound Cb(1+s^2) with one eventual threshold for all
radii, states the positive-size/genuine-average conditions for finite
unbiasedness, mentions the metric premise, and claims all four conclusions.

### Totalization and junk-value audit

* Divisions by p,1-p are safe under hypothesis 1. Conditional-expectation
  denominators are finite products of strictly positive factors, also safe;
  when J is empty its product is 1 and conditioning gives E_N U.
* Empty Hajek arms occur with positive finite-sample probability and are
  assigned mean zero via 0/0=0. Their combined probability at positive N is
  p^N+(1-p)^N, tending to zero. This convention is in the source definition,
  although not repeated in T44's docstring.
* `Fin 0` is empty; the assignment space still has one point and design mass
  1. Node sums/N and arm means are zero there. The finite identity explicitly
  requires N>0, and the remaining conclusions ignore finitely many sizes.
* Nonintegrable integrals totalize to 0; infinite measure converts by
  `toReal` to 0; zero measure also gives a zero denominator. Hypothesis 3
  excludes all these at d eventually, and conclusion 1 imposes the same
  condition at each N where it asserts finite unbiasedness. NED is imposed
  on the totalized circle table at every N, including the finitely many
  earlier populations where averages might not be genuine.
* Nonempty node sets and nonnegative distances ensure all node-distance
  infima are nonempty and bounded below, so no junk real `sInf` or empty
  `infDist` value is involved. The metric premise is substantive: general
  set-to-set infima need not separate nodes or satisfy a triangle inequality.
* The L2 square root is applied to a nonnegative finite sum because the design
  is a probability law. The normalization square root is applied to a
  nonnegative variance, and conclusion 4's extra premise makes it strictly
  positive eventually. `sqrt(N)` has a nonnegative argument, including the
  well-defined zero value at N=0.
* The real power s^(-alpha) is tested only for s>=S>0, so no totalized zero or
  negative-base power affects NED. The ordinary square s^2 in spacing uses a
  natural exponent. Values of psi at negative arguments do not enter its
  bound, monotonicity requirement, or approximation inequalities.
* Phi's Gaussian masses are finite before `toReal`. Casts of N and finite
  cardinalities into R are exact. All subtractions are in R. There is no
  logarithm, truncated subtraction, `sSup`, `limsup`/`liminf`, or
  partial-function default in this SAP statement closure.

At this blind stage none of these statements appears to exploit a junk value
for an asymptotic conclusion. Whether their premises and their general spatial
notions match the intended paper claims remains for the next stage.
