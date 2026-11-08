# Blind mathematical reading

Saved before opening `claims.json` or `record.json`. Sources: all twelve
`SAP/P061a/Defs/Part*.lean` files, their aggregator, and
`SAP/P061a/Challenge/Part1.lean` and its aggregator. The Challenge contains ten
theorems, each asserting the corresponding `T*Statement` without additional
binders. This reading describes those propositions, independently of their
docstrings.

## Shared objects and conventions

* An `AtomicDesign Ω` is a function p:Ω→R with p(z)≥0 for every z,
  unconditionally summable, and Σ_z p(z)=1. Ω need not be finite or countable,
  but its positive-mass support is countable. Every event is an arbitrary
  predicate, with P(A)=Σ_z 1_A(z)p(z). Support means p(z)>0.
* Units are i∈Fin N, i.e. integers 0,…,N−1. Exposures g_i(z) and responses
  y_i(z) are arbitrary real functions. Write E f=Σ_z p(z)f(z).
  `HasMean D f` means Σ_z p(z)|f(z)| is summable, hence E f is an ordinary
  finite expectation. `targetMoment D g y e` requires this for each
  1_{g_i=e}y_i.
* Write π_i(e)=P(g_i=e), μ_i(e)=E[1_{g_i=e}y_i]/π_i(e), and
  C_i(e)=Σ_z 1_{g_i=e}(p(z)/π_i(e))y_i(z). Write μ(e)=N⁻¹Σ_i μ_i(e),
  τ_i(d,d')=μ_i(d)−μ_i(d'), and τ(d,d')=μ(d)−μ(d'). The HT estimator is
  h_e(z)=N⁻¹Σ_i 1_{g_i(z)=e}y_i(z)/π_i(e), and h_{d,d'}=h_d−h_{d'}.
  `positiveExposure e` means there exists a real c>0 with π_i(e)≥c for
  every i. This is a lower bound for the particular design and N, not a
  bound uniform over a sequence of designs.
* Support stability says that for every i and any two positive-mass
  assignments with equal g_i, their y_i values agree. Global stability
  requires the same equality for all assignments in Ω, including zero-mass
  ones. Variance is E[(X−EX)²]; covariance is E[(X−EX)(Y−EY)].
* Independence of X and Y means P(E(X)∧F(Y))=P(E(X))P(F(Y)) for all predicates
  E,F on their codomains. Mutual independence of N real exposures means
  P(∀i,E_i(g_i))=Π_iP(E_i(g_i)) for every family of predicates E_i.
* For a real vector v, v_{−i} is its restriction to all j≠i and (e,v_{−i})
  is coordinate insertion. On a feasible set S⊆R^N, coordinate exposure is
  z_i. The hybrid response b_i(e,z) equals y_i(e,z_{−i}) if the inserted
  vector belongs to S, and equals zero otherwise. The defined direct
  contrast is a(d,d')=N⁻¹Σ_i E[b_i(d,Z)−b_i(d',Z)]. Thus infeasibility has a
  zero default in the definition; the relevant theorems must supply
  feasibility on positive-mass assignments before interpreting it as ADE.
* Probability convergence means that for every ε>0,
  P_N(|X_N−a|>ε)→0. Weak convergence to L means
  E_N f(X_N)→∫f dL for every bounded continuous real f. A translated law is
  the pushforward of L by x↦x+c. In T5 L is explicitly a probability measure.
* Mathlib's `Summable` and `tsum` use the unconditional net of all finite
  subsets (`Topology/Algebra/InfiniteSum/Defs.lean`, lines 89–147); on R this
  is absolute summability. A nonsummable `tsum` is totalized to zero.
  Division and inverse at zero are also totalized. No such value is an
  ordinary mean without the stated moment/positivity conditions.
  `Function.extend` (`Logic/Function/Basic.lean`, lines 822–866) agrees with
  the specified function along an injection and with its supplied default
  elsewhere. The natural-to-real injection used here makes all the integer
  extensions unambiguous. `finProdFinEquiv` identifies (k,b) with 2k+b,
  inverse (i div 2,i mod 2). `Real.sqrt` is the nonnegative square root on
  nonnegative reals and zero on negative reals. `ℝ →ᵇ ℝ` is exactly a bounded
  continuous function. Bochner integrals in `weakLimit` are genuine finite
  integrals when L is a probability measure because the test functions are
  bounded. Finite response ranges below use real supremum minus infimum;
  the finite nonempty index sets make these genuine extrema.

## SAP.P061a.T1

There exists a family D_N, for every natural N (including zero), on the full
space {0,1,2}^N, whose mass at every vector is 3^(−N). Define g_i(z)=0 when
z_i=0 and 1 otherwise, y_i(z)=z_i, and c(z)_i=0 when z_i=0 and 1 otherwise.
For every N>0 the following all hold:

1. The g_i are mutually independent. Every y_i lies in [0,2], and y_i(z)
   depends only on z_i. Both target exposures 1 and 0 satisfy
   `positiveExposure`.
2. For every i, P(z_i=1,g_i=1)/π_i(1)=1/2 and
   P(z_i=2,g_i=1)/π_i(1)=1/2; π_i(1)=2/3, π_i(0)=1/3,
   μ_i(1)=3/2, μ_i(0)=0, and τ_i(1,0)=3/2.
3. τ(1,0)=3/2. For every i,z, both
   y_i(z with coordinate i set to 1)−y_i(z with i set to 0)=1 and
   y_i(c(z) with i set to 1)−y_i(c(z) with i set to 0)=1.
   Each of the two corresponding averaged expected contrasts equals 1
   (one equality occurs twice in the conjunction). The gap τ(1,0)−1 is 1/2.
4. For every z, h_{1,0}(z)=[3/(2N)]Σ_i z_i;
   E h_{1,0}=3/2; Var(h_{1,0})=3/(2N). For every real ε>0,
   P(|h_{1,0}−3/2|≥ε)≤3/(2Nε²).

For N=2 there is no function H:R²→R such that
y_0(z)=H((g_i(z))_i) for every z∈{0,1,2}². Explicitly the exposure vectors
of (1,0) and (2,0) agree coordinate by coordinate, but their unit-0 outcomes
are 1 and 2. Finally, as n→∞ the gap at N=n+1 tends to 1/2 and does not tend
to zero. All these assertions are conclusions of the existential statement;
there are no external hypotheses.

## SAP.P061a.T2

There exists a uniform design on the four binary pairs z=(z_0,z_1). Define
own bit x_i=z_i, partner bit x_j=z_{1−i}, g_i=x_i+2x_j, and y_i=x_i.
Its conclusions are:

* For each i and each e∈{0,1,2,3}, π_i(e)=1/4. For each i,
  μ_i(1)=1, μ_i(0)=0; τ(1,0)=1. Responses are globally and support stable,
  and exposures 1 and 0 both have a positive uniform lower bound.
* The exposure-vector image is exactly {(0,0),(2,1),(1,2),(3,3)}, with the
  four corresponding raw assignments (0,0),(0,1),(1,0),(1,1), respectively.
* For every raw z, the two vectors (1,g_1(z)), (0,g_1(z)) cannot both be in
  that image; likewise (g_0(z),1), (g_0(z),0) cannot both be in that image.
* The probability that both first-coordinate hybrids are binary raw
  vectors is 1/2; likewise for second-coordinate hybrids. Pointwise, each
  first-coordinate hybrid is binary iff z_0=0, and each second-coordinate
  hybrid is binary iff z_1=0.

Also, for every natural K>0 there exists a design on K binary pairs whose
mass is Π_{k<K}1/4 (independent uniform pairs). There are 2K units indexed by
(pair,bit); g_i is own bit plus twice partner bit, and y_i is own bit. All
four exposure probabilities are 1/4 at each unit, μ_i(1)=1, μ_i(0)=0,
τ(1,0)=1, and global stability holds. For every i,z, inserting 1 and 0 in
coordinate i of the full exposure vector cannot yield two vectors both in
the full exposure image. For every i the probability that both inserted
vectors lie in the binary raw domain is (1/2)(1/4)^(K−1). Here K−1 is natural
subtraction, protected by K>0. The paired clause does not separately repeat
the single-pair positivity and support-stability predicates.

## SAP.P061a.T3

This is the conjunction of two universally quantified implications.

First: for every natural N, feasible set S⊆R^N, atomic D on S, response
schedule y on S, and real d,d', assume in this order:

1. N>0;
2. π_i(d)>0 and π_i(d')>0 for every i, using g_i(z)=z_i;
3. all targeted first absolute moments at d, and then at d', are finite;
4. for every i, Z_i is independent of the entire vector Z_{−i}.

Then for every i, e∈{d,d'}, and every other-coordinate vector w with
P(Z_{−i}=w)>0, there exists a supported z∈S equal to (e,w). For every i and
such e, b_i(e,·) has a finite absolute mean and μ_i(e)=E b_i(e,Z).
Finally τ(d,d')=a(d,d'). There is no separate hybrid feasibility hypothesis:
the first conclusion supplies it at supported other-coordinate values.

Second: for every type Ω, natural N, atomic D on Ω, real exposure and
response schedules g,y, total real-vector response schedule H_i:R^N→R, and
real d,d', assume N>0, all π_i(d),π_i(d')>0, targeted absolute moments at d
and at d', independence of each g_i(Z) from g_{−i}(Z), and, for every
supported z with g_i(z)∈{d,d'}, y_i(z)=H_i(g(z)). Then for every i and
e∈{d,d'}, H_i(e,g_{−i}(Z)) has a finite absolute mean and its expectation
is μ_i(e). Also τ(d,d')=N⁻¹Σ_i E[H_i(d,g_{−i}(Z))−H_i(d',g_{−i}(Z))].
The consistency assumption is only on support and the two target cells;
independence is with the joint vector of all other exposures.

## SAP.P061a.T4

There exists a family D_m for every natural m, on K=m^8 binary pairs with
N=2m^8 units. Put r_m=1/m for m≥2 and r_m=0 otherwise. Each assignment has
mass Π_{k<K}q_m(z_k), where q_m(00)=q_m(11)=(1+r_m)/4 and
q_m(01)=q_m(10)=(1−r_m)/4. The exposure is own bit X_i and response is
y_i=1+r_m X_partner. The direct contrast A_m averages expected differences
after replacing only the own raw bit by 1 versus 0. Let T_m=τ(1,0), H_m be
the HT contrast, V_m=8+16/m+14/m²+2/m³−4/m⁴, and
s_m=sqrt(Var(H_m)). For every m≥2:

* All assignments have positive mass; each own-bit margin is 1/2 at both
  0 and 1; 1≤y_i(z)≤3/2 for every i,z. Each own bit is independent of the
  entire vector of pairs outside its pair. The covariance of the two
  bits in every pair is 1/(4m).
* A_m=0; μ_i(1)=1+(1/m)(1+1/m)/2 and
  μ_i(0)=1+(1/m)(1−1/m)/2 for every i. T_m=E H_m=1/m².
* Var(H_m)=V_m/(4m^8), 8≤V_m<20, and s_m>0.
  [(1/m²)/s_m]²=4m⁴/V_m and m⁴/5≤[(1/m²)/s_m]².
* P(|H_m−1/m²|≤5s_m)≥24/25. If m≥5, then
  P(|H_m|≤5s_m)≤4Var(H_m)/(1/m²)²=V_m/m⁴≤20/m⁴.

Along m=n+2 as n→∞, T_m−A_m→0, N Var(H_m)→4,
[(T_m−A_m)/s_m]²→+∞, and P(|H_m−A_m|≤5s_m)→0. The formula for D_m
imposes pair independence; no graph-degree predicate or unsquared divergence
predicate is in the proposition. Values m=0,1 have a well-defined mass
formula but none of the displayed finite inference conclusions is required
there.

## SAP.P061a.T5

Four conjuncts are asserted.

1. **Transfer.** Universally choose feasible sets S_N⊆R^N, atomic D_N on
   S_N, responses y_N, fixed real targets d,d', estimators t_N and estimated
   scales ŝ_N:S_N→R, deterministic scales s_N, and a real Borel probability
   measure L. Assume, in order: every s_N>0; every ŝ_N(z)>0 for every z,
   including unsupported ones; every unit's two target probabilities are
   positive; the two targeted absolute moments are finite for every N;
   both coordinate hybrids are feasible for every supported z and every
   unit; each separate hybrid response has a finite absolute mean;
   (t_N−T_N)/s_N converges weakly to L; ŝ_N/s_N converges in probability to
   1; and (T_N−A_N)/s_N→0, with T_N=τ_N(d,d') and A_N the defined feasible
   direct contrast. Conclude (t_N−A_N)/ŝ_N converges weakly to L. For every
   q>0 with L({q})=L({−q})=0, also
   P_N(|t_N−A_N|≤qŝ_N)→L([−q,q]), represented by the finite ENNReal
   measure value's `toReal`. No distinct-target hypothesis and no N>0
   hypothesis is used; N=0 is only an initial sequence index.
2. **Neighborhood bound.** Universally choose a finite nonempty common
   alphabet A, natural N, injective real label ℓ:A→R, atomic D on the full
   space A^N, responses y, neighborhoods H_i⊆Fin N, functions
   f_i:A→A^{H_i}→R, and d,d'∈A. Assume N>0, i∉H_i for every i, positive
   own-coordinate probabilities for both labels at every i, and
   y_i(z with i set to e)=f_i(e,z|H_i) for every i,z and e∈{d,d'}.
   Let Q_i^e(x)=P(Z_i=e,Z|H_i=x)/P(Z_i=e), P_i(x)=P(Z|H_i=x),
   R_i(e)=max_x f_i(e,x)−min_x f_i(e,x), and
   TV(Q,P)=(1/2)Σ_x|Q(x)−P(x)|. Then the absolute difference between τ and
   N⁻¹Σ_i E[y_i(d,Z_{−i})−y_i(d',Z_{−i})] is at most
   N⁻¹Σ_i[R_i(d)TV(Q_i^d,P_i)+R_i(d')TV(Q_i^{d'},P_i)].
   Even when H_i is empty, A^{H_i} has one element; no empty extrema are
   used.
3. **Rate implication.** For every four real sequences T,A,B,s, assume
   all s_N>0, |T_N−A_N|≤B_N for every N, and B_N/s_N→0. Then
   (T_N−A_N)/s_N→0. Here B is the sequence named `L` in this conjunct.
4. **Nonzero drift.** Universally choose spaces Ω_N, atomic D_N, t_N,ŝ_N,
   real sequences T,A,s, a Borel probability measure L, and c∈R. Assume
   c≠0, all s_N>0 and all ŝ_N(z)>0, (t_N−T_N)/s_N converges weakly to L,
   ŝ_N/s_N converges in probability to 1, and (T_N−A_N)/s_N→c. Then
   (t_N−A_N)/ŝ_N converges weakly to the law of X+c for X with law L.

## SAP.P061a.T6

First, for every finite type Ω, natural N, atomic D, schedules g,y and real
d,d', assume N>0, π_i(d)>0 for every i, then π_i(d')>0 for every i.
Conclude μ_i(d)=C_i(d) and μ_i(d')=C_i(d') for every i;
τ(d,d')=N⁻¹Σ_i[C_i(d)−C_i(d')];
τ(d,d')=μ(d)−μ(d'); and τ(d,d')=N⁻¹Σ_iτ_i(d,d').
The third equality is definitional. Finite Ω supplies all moments.

Second, for every natural N, atomic D on {0,1}^N and arbitrary responses,
assume N>0, all own-bit probabilities at 1 positive and all at 0 positive.
Then τ(1,0)=N⁻¹Σ_i[C_i(1)−C_i(0)] for own-bit exposure.

## SAP.P061a.T7

There exists an atomic D on the full real line with mass at each natural
integer k equal to 2^{−(k+1)}, and zero mass elsewhere. Its positive support
is exactly the nonnegative integers. There is one unit. On integer k the
exposure is 0 at k=0 and 1 otherwise; response is 0 at k=0 and
(−1)^{k+1}2^{k+1} at k≥1. Both exposure and response are zero at noninteger
reals. All of these are fixed definitions, not existentially chosen
responses. Conclusions:

* Both exposures 1 and 0 satisfy positivity; their probabilities are 1/2.
  μ_0(0)=0 and the target-0 response has a finite absolute mean.
* The full real-indexed weighted target-1 response is not summable.
  The target-1 HT estimate does not have a finite absolute mean.
* Put a_k=p(k+1)y_0(k+1). For every k≥0, a_k=(−1)^k.
  For every m≥0, the sums over k<2m of max(a_k,0), max(−a_k,0), |a_k|,
  and a_k are respectively m,m,2m,0; the sum over k<2m+1 of a_k is 1.
  Neither sequence max(a_k,0) nor max(−a_k,0) is summable.
* For every real z, h_1(z)=2y_0(z)1_{g_0(z)=1}. Its positive-index weighted
  terms p(k+1)h_1(k+1)=2(−1)^k. Neither their positive nor their negative
  parts is summable.

There is no explicit limit-nonexistence predicate for ordered partial sums,
no explicit nonexistence assertion named AEPO/EED/AEED, and no extended-real
infinite-sum identities. The proposition never uses the totalized value of
the divergent target-1 mean as an ordinary expectation.

## SAP.P061a.T8

First, universally choose Ω,N,D,g,y,d and assume N>0, every π_i(d)>0, and
every target-d absolute moment finite. Then:

* For every i the signed weighted target response is summable,
  μ_i(d)=C_i(d), the unit HT term u_i=1_{g_i=d}y_i/π_i(d) has a finite
  absolute mean, E|u_i|=E|1_{g_i=d}y_i|/π_i(d), and E u_i=μ_i(d).
* h_d has a finite absolute mean and E h_d=μ(d).
* For every additional real d', if all π_i(d')>0 and all its targeted
  absolute moments are finite, then h_{d,d'} has a finite absolute mean,
  E h_{d,d'}=τ(d,d'), and τ(d,d')=N⁻¹Σ_iτ_i(d,d').
* For every i, the conditional exposure mean of the absolute response is
  C_i^{|y|}(d)=E|1_{g_i=d}y_i|/π_i(d), and μ(d)=N⁻¹Σ_i C_i(d).

Second, universally choose Ω,N,D,g,y,d and assume N>0 and every π_i(d)>0.
Both of the following implications hold: finite positive-mass support of D
implies all target-d absolute moments are finite; and if for every i the
response is constant over its supported target-d cell, then all those
moments are finite and, for every i, there exists a real a_i such that
y_i(z)=a_i on that supported cell and
E|1_{g_i=d}y_i|=|a_i|π_i(d). This constancy hypothesis is limited to the one
targeted cell and does not require global stability.

## SAP.P061a.T9

There exist D,D' on the same full space {0,1,2}^4. Write S_n for the set of
vectors having exactly one coordinate equal to 2 and exactly n nonzero
coordinates. D has mass 1/12 on S_2 and zero elsewhere; D' has mass 1/12 on
S_3 and zero elsewhere, with these supports asserted exactly. Exposure is
g_i(z)=z_i. The common response schedule is
y_i(z)=(number of nonzero coordinates of z)·1_{z_i=2}. Then:

* At every i, under D the probabilities of exposures 2 and 1 are 1/4 and
  1/4; under D' they are 1/4 and 1/2. All four positivity inequalities are
  separately asserted.
* Support stability holds for D and for D'. For every i, under D the
  exposure means at 2 and 1 are 2 and 0; under D' they are 3 and 0.
* The two population contrasts for targets (2,1) are 2 and 3, respectively.
  The common schedule is not globally stable on the full assignment space.

## SAP.P061a.T11

The following universal proposition is false: for every type Ω, natural N,
atomic D on Ω, schedules g,y and real d,d', if N>0 and both target exposures
have strictly positive uniform lower bounds over the units, then both
targeted absolute moments are finite, μ_i(e)=C_i(e) for every i and
e∈{d,d'}, and τ(d,d')=N⁻¹Σ_iτ_i(d,d'). Thus T11 negates a universal
contract containing existence as well as equalities; it does not assert
that every positive design fails, nor that an algebraic identity between
totalized values fails. Its quantifier order permits an existential
counterexample to at least one conclusion with all antecedents satisfied.
