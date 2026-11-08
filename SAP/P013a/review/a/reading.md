# Blind reading of the Challenge statements

This file was written from `SAP/P013a/Defs.lean`, all six `Defs/Part*.lean`
files, and both `Challenge/Part*.lean` files, before opening `claims.json` or
`record.json`. Each Challenge theorem is a closed assertion of the corresponding
`TnStatement` below. A source docstring is not an additional hypothesis.

## Conventions and fully expanded shared definitions

All populations and randomization spaces in these statements are finite.
`Fin N` means the integers from 0 through N-1. A design P on a finite type
Omega assigns a strictly positive real weight p(z) to EVERY z, with sum 1.
Thus a design cannot exist on an empty sample space. Write E_P X = sum_z
p(z)X(z), Cov_P(X,Y) = E_P(XY)-E_P X E_P Y, Var_P X = Cov_P(X,X), and
P(A) = sum_{z satisfying A} p(z). No integral or integrability convention is
involved in these definitions.

A population F consists of an arbitrary exposure map D: Omega x Fin N -> Fin K
and a fixed real table y(i,d). There is no additional exposure-model hypothesis.
Write I_i^d(z)=1 if D(z,i)=d and 0 otherwise,
pi_i^d=E I_i^d, pi_ij^{de}=E(I_i^d I_j^e), and Y_i(z)=y(i,D(z,i)).
`Positivity F d` means, for EVERY i, 0<pi_i^d<1; it is not merely nonnegativity.
T_d=sum_i y(i,d), mu_d=T_d/N, tau_de=mu_d-mu_e,
H_d(z)=sum_i I_i^d(z)y(i,d)/pi_i^d,
M_d(z)=H_d(z)/N, and H_de(z)=(H_d(z)-H_e(z))/N.
All sums over i != j below are ORDERED sums.

For later variance estimates set

* B_ij^{de}(z)=I_i^d I_j^e [(pi_ij^{de}-pi_i^d pi_j^e)/pi_ij^{de}]
  [y(i,d)/pi_i^d][y(j,e)/pi_j^e].
* Q_d(z)=sum_i I_i^d(1-pi_i^d)[y(i,d)/pi_i^d]^2
  + sum_{i!=j} B_ij^{dd}(z).
* A2_d(z)=sum_{i!=j: pi_ij^{dd}=0}
  [I_i^d y(i,d)^2/(2pi_i^d)+I_j^d y(j,d)^2/(2pi_j^d)].
* A_d=sum_{i!=j: pi_ij^{dd}=0} y(i,d)y(j,d).
* C_de(z)=sum_{i!=j: pi_ij^{de}>0} B_ij^{de}(z)
  -sum_{i,j: pi_ij^{de}=0}
  [I_i^d y(i,d)^2/(2pi_i^d)+I_j^e y(j,e)^2/(2pi_j^e)].
  The second sum INCLUDES i=j.
* Vhat_de(z)=[Q_d(z)+A2_d(z)+Q_e(z)+A2_e(z)-2C_de(z)]/N^2.

Real division in Lean is total, with a/0=0. In particular B is syntactically
defined as zero at zero joint probability. A proper finite positive-weight
design also makes the corresponding product of indicators zero at EVERY
sample point, so this convention is the zero-joint omission rather than a
new observable contribution. Positive marginal hypotheses are stated where
these quantities are used. `Real.sqrt` is the nonnegative square root and is
zero on nonpositive inputs; additional signs or coverage guards matter.

For finite subsets A,B of the units, vector independence means that for EVERY
two full label assignments a,b: Fin N -> Fin K,
P(D_A=a_A and D_B=b_B)=P(D_A=a_A)P(D_B=b_B).
The printed no-edge predicate for a Boolean matrix h means there exist NO i,j
with h_ij=true and at least one of
(i in A,j not in B), (j in A,i not in B), (i not in A,j in B),
(j not in A,i in B). The corrected no-edge predicate prohibits an edge in
either direction BETWEEN A and B; its four written alternatives repeat the
same two cases. Printed/genuine dependency means that for EVERY disjoint A,B,
the respective no-edge predicate implies vector independence. RowBound(h,m)
means EVERY row has at most m true entries. Pair independence of units i,j
means pi_ij^{de}=pi_i^d pi_j^e for EVERY d,e. Write
g_h(i,j)=1_{i=j or h_ij or h_ji}.

P x Q is the design on pairs with product weights. P^R is the design on all
maps Fin R -> Omega with product weights; its R draws are independent.
For these simulated assignments z_1,...,z_R, let
C_i=sum_r I_i^d(z_r), ptilde_i=(C_i+1)/(R+1), and
Htilde_d(z,z_1,...,z_R)=sum_i I_i^d(z)Y_i(z)/ptilde_i. The actual draw z is
independent of the R simulated draws. All arithmetic here is real arithmetic,
including the cast of R+1. A minimum marginal p0 means it is attained by SOME
unit and is at most EVERY unit's marginal. kappa_d=(sum_i |y(i,d)|)/|T_d|.

For varying finite spaces, X_n ->p a means: for EVERY real epsilon>0,
P_n(|X_n-a|>epsilon) tends to 0. `TendsNormal P X m v` means: for EVERY real
x, P_n(X_n<=x) tends to the CDF at x of the Gaussian with mean m and VARIANCE
v (v is a nonnegative real). `TendsDistribution P X nu` asks this only at
continuity points of the CDF of nu. Its use below explicitly requires nu to
be a probability measure. These are ordinary CDF formulations, not convergence
of expectations. Phi is the N(0,1) CDF. q_alpha is the real infimum of
{x: Phi(x)>=1-alpha/2}; all its substantive uses have 0<alpha<1, where this
is the usual positive normal quantile. Limits are along natural n -> infinity;
an eventual assertion means for all sufficiently large n. Real liminf is
Mathlib's conditional-order liminf, used here only for probabilities in [0,1].

An ExperimentSequence S supplies a finite experiment with N=n+1 units for
EVERY natural n, two distinct labels d_n,e_n, and positivity for both labels
at EVERY size. Abbreviate its estimate, target, true variance and variance
estimate by H_n=H_{d_ne_n}, tau_n=tau_{d_ne_n}, V_n=Var H_n, Vhat_n=Vhat_{d_ne_n}.
NestedPopulationSetup means there EXIST injective maps of each size's exposure
labels into the naturals, distinct fixed natural labels d,e, and ONE table
y: Nat x Nat -> Real, such that d_n,e_n map to d,e and EVERY outcome at EVERY
size equals y(i,label). This fixes existing units' outcomes under matching
labels across sizes; it does not constrain the changing design.

The sequence predicates expand as follows:

* StandingPositivity: 0<pi_i^a<1 for EVERY n,i,a, including other labels.
* ComparisonBounded: there EXIST constants c1>=0,c2>0 such that for EVERY n,i,
  both comparison outcomes have absolute value <=c1 and both reciprocal
  comparison marginals have absolute value <=c2.
* C3: there EXIST c1>=0,c2>0 bounding |y(i,a)| and |1/pi_i^a| in this way for
  EVERY n,i,a. C3 alone does not exclude zero marginals, because 1/0=0;
  the relevant uses separately supply positivity.
* C4: there EXISTS a Boolean matrix g_n at EVERY n, such that for EVERY n,i,j,
  g_n(i,j)=false implies pair independence for ALL labels, and
  N^{-2}sum_ij 1_{g_n(i,j)} tends to 0.
* Printed C5: there EXIST ONE natural m and matrices h_n such that for EVERY n
  the printed dependency predicate and RowBound(h_n,m) hold.
* Genuine C5: the same existential uniform m and h_n, with EVERY h_n symmetric,
  genuine dependency, and RowBound(h_n,m). Directed corrected C5 drops symmetry.
* C6: there EXISTS c>0 with N V_n -> c.
* LowerTail: for EVERY delta>0, P_n(N Vhat_n < N V_n-delta) ->0.
* ScaledVarianceConcentration: N(Vhat_n-E Vhat_n) ->p 0.
* ScaledVarianceVanishes: Var(N Vhat_n) ->0.
* Coverage_n(alpha)=P_n(Vhat_n>=0 and |H_n-tau_n|<=q_alpha sqrt(Vhat_n)).
* JointLowerBound(S,b): for EVERY n and distinct i,j, each of pi_ij^{dd},
  pi_ij^{ee}, pi_ij^{de} is zero or at least b.
* PositiveJointDomain(S,n): SOME distinct i,j has a positive joint among these
  three types. IsMinimumPositiveJoint(S,n,b) means b>0, it equals SOME one of
  these joints for distinct units, and it is at most EVERY positive such joint.
  A hypothesis conditional on PositiveJointDomain leaves b unconstrained at
  sizes with an empty positive-joint domain.

Mathlib definitions checked directly: `Probability/CDF.lean` (cdf is measure
of (-infinity,x] for a probability measure),
`Probability/Distributions/Gaussian/Real.lean` (gaussianReal's second parameter
is variance; zero variance is a point mass), `Order/Filter/Defs.lean`
(Tendsto is filter convergence), and `Data/Finset/Powerset.lean`
(powersetCard consists exactly of subsets of the given cardinality).
Finite sums/products, finset erase/filter/cardinality, Boolean decide, natural
quotient/remainder, natural binomial coefficients, and the usual real
absolute value, powers, log, infimum, and topology supply the remaining
operations. Natural subtraction is truncated; its uses are spelled out below.

## SAP.P013a.T1

For EVERY natural r>=2 set N=2r and epsilon=1/N^2, t=1-2epsilon. Independently
for each of r pairs draw an atom a in {0,1,2,3} with weights
(epsilon,1/2-epsilon,1/2-epsilon,epsilon). Its two exposure labels are respectively
(0,0),(0,1),(1,0),(1,1). Units 2a and 2a+1 form a pair. Both potential outcomes
of the first unit equal 1 and both of the second equal -1. Define
s(atom)=4(first label-second label), with the subtraction in the integers,
and u(atom)=2/epsilon for equal labels, otherwise 16-4/t.

The theorem unconditionally asserts ALL the following, not implications from
these finite identities:

* For EVERY unit and label, pi=1/2 and |y|=1. For EVERY distinct i,j and EVERY
  d,e, the joint is epsilon for same-pair equal labels, 1/2-epsilon for
  same-pair different labels, and 1/4 for different pairs.
* The matrix h_ij=1_{same pair} satisfies both genuine and printed dependency
  and has EVERY row sum <=2. These assertions are repeated in the second
  top-level conjunct.
* tau_10=0. For EVERY assignment z, H_10=sum_a s(z_a)/N,
  N^2 Vhat_10=sum_a u(z_a), and Vhat_10>0.
* V=8t/N, E Vhat_10=V. If A is the event that EVERY pair has different
  exposures, P(A)=t^r, P(A^c)<=1/N, and for EVERY z in A,
  N Vhat_10=8-2/t.
* Var(N Vhat_10)=4(N-2)^4(N+2)^4/[N^5(N^2-2)].
* The one-pair expectation E u=16t.

Then, for the sequence r=n+2, N=2(n+2), it asserts NV->8,
N Vhat->p 6, Vhat/V->p 3/4,
Var(N Vhat)/(4N)->1, Var(N Vhat)->+infinity, and
sqrt(N)H_10 tends in CDF to N(0,8).
For EVERY real alpha with 0<alpha<1, the probability of
|H_10-tau_10|<=q_alpha sqrt(Vhat_10) tends to
2Phi(q_alpha sqrt(3/4))-1, and this number is STRICTLY less than 1-alpha.
There is no numerical decimal claim.

## SAP.P013a.T2

This is the conjunction of FIVE separately universally quantified implications:

1. For EVERY S, assume NestedPopulationSetup, ComparisonBounded, genuine C5,
   C6, and LowerTail, in that order. Then for EVERY alpha with 0<alpha<1,
   liminf_n Coverage_n(alpha)>=1-alpha.
2. For EVERY S, ScaledVarianceConcentration implies LowerTail.
3. For EVERY S, ScaledVarianceVanishes implies LowerTail.
4. For EVERY S, assume NestedPopulationSetup, ComparisonBounded, and genuine
   C5. For EVERY real b>0 satisfying JointLowerBound(S,b), there EXISTS C>=0
   such that EVENTUALLY Var(N Vhat_n)<=C/N, and LowerTail holds.
5. For EVERY S, assume the same three setup predicates. For EVERY real sequence
   b_n such that for EVERY n with PositiveJointDomain(S,n), b_n is its attained
   minimum positive joint, there EXISTS C>=0 with EVENTUALLY
   Var(N Vhat_n)<=C/(N b_n). Also, if N b_n->+infinity, then LowerTail holds.

Neither rate clause asserts centered concentration as a separate conjunct.
There is no existential counterexample clause here. All implicit treated/control
positivity and distinctness come from S; other-label positivity is not required.

## SAP.P013a.T3

This is an unconditional calculation for a SPECIFIED two-unit, two-label
experiment. Its four exposure pairs (0,0),(0,1),(1,0),(1,1) have weights
(2/9,4/9,1/9,2/9). At exposure 0 both outcomes are 0; at exposure 1 they
are (a,-1). One actual and one simulated assignment are independent and
Htilde uses denominator (I_i^1(simulation)+1)/2.

For a=2 the theorem states positivity for EVERY i,d, pi_0^1=1/3,
pi_1^1=2/3, T_1=1, E Htilde=2/9 and |(E Htilde-1)/1|=7/9.
It also asserts 4/9<7/9, 1/2<7/9, (1-1/3)^2<=1/2<(1-1/3)^1,
1>=log(1/2)/log(1-1/3)-1, and relative bias >1/2.
For a=1 it states T_1=0, E Htilde=-1/3, and
|E Htilde-T_1|>|T_1|(1-1/3)^2. There is no division by T_1 in this last part.

## SAP.P013a.T4

For EVERY finite Omega, EVERY N,K and design P, EVERY population F,
assume N>0. For EVERY label d satisfying positivity, EVERY natural R>=1,
and EVERY attained minimum marginal p0, define E=E_{P x P^R} Htilde_d,
T=T_d, kappa=sum_i|y(i,d)|/|T|. Then:

* E=sum_i y(i,d)[1-(1-pi_i^d)^(R+1)]
  =T-sum_i y(i,d)(1-pi_i^d)^(R+1).
* |E-T|<=(1-p0)^(R+1)sum_i|y(i,d)|.
* IF T!=0, then kappa>=1 and |(E-T)/T|<=kappa(1-p0)^(R+1).
  Under this same nonzero-total hypothesis, IF all outcomes at d are
  nonnegative OR all are nonpositive, then kappa=1 and the relative bias is
  <=(1-p0)^(R+1). For EVERY b>0, if
  R>=log(b)/log(1-p0)-1, this relative bias is <=b.
  Also, without the common-sign hypothesis, for EVERY b>0, if
  R>=log(b/kappa)/log(1-p0)-1, the relative bias is <=b.

Independently the theorem asserts the exact RATIONAL inequalities
(1999/2000)^10594<=1/200<(1999/2000)^10593.
No conclusion involving kappa is asserted at a zero total. Positivity and
attainment imply 0<p0<1, so the log denominator is nonzero.

## SAP.P013a.T5

Six conjuncts assert the following:

1. For EVERY N and disjoint finite A,B of its units, printed no-edge for
   h_ij=1_{i=j} is equivalent to A=B=empty.
2. For EVERY finite design, EVERY N,K and exposure map, this identity h
   satisfies printed dependency and RowBound(h,1).
3. For EVERY natural q, on 3q units let h_ij=1_{i!=j and floor(i/3)=floor(j/3)}.
   It is symmetric with false diagonal; for EVERY disjoint A,B its printed
   no-edge condition is equivalent to both being empty; EVERY row has
   EXACTLY 2 true entries. For EVERY finite design and exposure map on these
   units it satisfies printed dependency.
4. For EVERY N, let one fair Bernoulli z be the exposure of EVERY unit and
   let ALL outcomes be zero. The identity h satisfies printed dependency
   and RowBound(h,1). EVERY marginal is 1/2; for EVERY i,j,
   pi_ij^{11}=1/2 and i,j are NOT pair independent (also when i=j).
5. For EVERY N and Boolean matrix g, if EVERY false g_ij implies pair
   independence for that shared-Bernoulli population, its total true count
   is N^2.
6. There EXISTS an ExperimentSequence satisfying StandingPositivity, C3,
   printed C5, and NOT C4.

Zero-sized universal instances do not supply the existential counterexample;
the latter has n+1 units at every size.

## SAP.P013a.T6

Three conjuncts:

1. For EVERY N,h,A,B (disjointness is NOT required), corrected no-edge is
   equivalent to EVERY i in A,j in B having h_ij=h_ji=false. IF h is
   symmetric it is equivalent to EVERY such h_ij=false.
2. For EVERY finite design and population F and EVERY h, assume genuine
   dependency. Then for EVERY i,j, g_h(i,j)=0 implies pair independence.
   For EVERY natural m, IF RowBound(h,m), then sum_ij g_h(i,j)<=N(2m+1).
   IF additionally h is symmetric, this sum is <=N(m+1).
3. For EVERY ExperimentSequence S, directed corrected C5 implies C4.

There is no positivity or nested-outcome hypothesis in this result.

## SAP.P013a.T7

Define endpoints L_0=0 and L_r=2^(2^r) for r>=1. For positive integer i,
k(i) is the LEAST r>=1 with i<=L_r. Odd blocks have y_i(0)=y_i(1)=1.
Even blocks alternate (y_i(1),y_i(0))=(2,0),(0,2), beginning at
i=L_{k-1}+1. This is one fixed infinite outcome table. For each N take its
first N units and assign exposures independently and fairly in {0,1}.
B_N is the set of units in even blocks, b_N its cardinality;
sigma_i=1 or -1 according as i-L_{k(i)-1}-1 is even or odd.
R_i(z)=2z_i-1. The natural subtractions in this definition have nonnegative
intended operands for the positive unit indices used here.

For EVERY N>=1, the theorem asserts EVERY marginal is 1/2, EVERY |y_i(d)|<=2,
and EVERY distinct-unit joint for EVERY label pair is 1/4. The identity h
is a genuine dependency matrix with row bound 1. It also asserts:

* |tau_10|<=2/N; for EVERY z, H_10-tau_10=(2/N)sum_i R_i(z).
* V=4/N; for EVERY z, Vhat_10=4 sum_i Y_i(z)^2/N^2 and Vhat_10>0.
* For EVERY z, N Vhat_10=4+4b_N/N+(8/N)sum_{i in B_N}sigma_i R_i(z).
* E(N Vhat_10)=4+4b_N/N and Var(N Vhat_10)=64b_N/N^2<=64/N.

For EVERY r>=1, at N=L_r: if r is odd, 0<=b_N/N<=L_{r-1}/L_r;
if r is even, 0<=1-b_N/N<=L_{r-1}/L_r. If r>=2, that endpoint ratio
equals 1/2^(2^(r-1)).

For the full sequence N=n+1, let W_n=N Vhat_n and
T_n=(H_10-tau_10)/sqrt(Vhat_n). The theorem asserts NV=4<=E W_n,
Var(W_n)->0, and (H_10-tau_10)/sqrt(V)->N(0,1) in CDF.
There is NO real s with W_n->p s, NO real s with sqrt(V/Vhat_n)->p s,
and NO probability measure nu on R to which T_n converges in distribution
(in the continuity-point CDF sense).
Along the odd endpoints L_{2n+1}, W->p4, sqrt(V/Vhat)->p1, and
T->N(0,1); along the even endpoints L_{2n+2}, these limits are respectively
8, 1/sqrt(2), and N(0,1/2), where 1/2 is VARIANCE.

## SAP.P013a.T8

For EVERY family of finite spaces L_n and designs P_n, EVERY two real
random-variable families estimate_n,Vhat_n, and EVERY real sequences
target_n,V_n, assume for EVERY n that V_n=Var(estimate_n)>0.
For EVERY c>0, assume in order:
N V_n->c; (estimate_n-target_n)/sqrt(V_n)->N(0,1) in CDF;
for EVERY n, N V_n<=E(N Vhat_n); and Var(N Vhat_n)->0, with N=n+1.
Let W_n=N Vhat_n and v_n=N V_n. Then ALL of the following hold:

* W_n-E W_n->p0.
* For EVERY 0<epsilon<1 and EVERY n,
  P(W_n<(1-epsilon)v_n)<=Var(W_n)/(epsilon^2 v_n^2);
  these probabilities tend to zero.
* For EVERY 0<alpha<1, and for EVERY 0<epsilon<1,
  liminf coverage >=2Phi(q_alpha sqrt(1-epsilon))-1;
  also liminf coverage >=1-alpha. Here coverage explicitly means
  Vhat_n>=0 AND |estimate_n-target_n|<=q_alpha sqrt(Vhat_n).
* For EVERY real s>=c, IF E W_n->s AND for EVERY n,z, Vhat_n(z)>0,
  then W_n->p s, sqrt(V_n/Vhat_n)->p sqrt(c/s),
  0<sqrt(c/s)<=1, and (estimate_n-target_n)/sqrt(Vhat_n)
  tends in CDF to N(0,c/s).

Strict positivity of Vhat is an extra antecedent ONLY of the last implication.
The preceding parts allow negative estimates and count them as noncoverage.

## SAP.P013a.T9

Two independent implications:

1. For EVERY ExperimentSequence S, assume NestedPopulationSetup,
   StandingPositivity, C3, and C4. Then M_{d_n}-mu_{d_n}->p0.
   It does not explicitly state contrast consistency or a coverage bound.
2. For EVERY real estimate,target,V,Vhat with V>0 and Vhat>0,
   (estimate-target)/sqrt(Vhat)
   =[(estimate-target)/sqrt(V)]sqrt(V/Vhat).

## SAP.P013a.T10

Displays3(x,p) means p-0.0005<=x<=p+0.0005, including both endpoints.
For EVERY real e,s,z, (e-zs)+(e+zs)=2e.
For EVERY real e,L,U, it is impossible simultaneously to have e,L,U in
these closed rounding bins and L+U=2e, for EACH of the two displayed triples
(0.295,0.050,0.536) and (0.306,0.212,0.404).
Finally, for EVERY real e,s,z, neither triple can be the three displays of
e,e-zs,e+zs. No distribution, positive-scale, or confidence-level assumptions
are needed for this arithmetic incompatibility.

## SAP.P013a.T11

For EVERY finite U,neighbors subsets of the naturals and EVERY natural i,n,
assume i in U, neighbors subset U, i not in neighbors, |neighbors|=39,
1<=n<=|U|-39. Draw an n-element subset S of U uniformly.
Let p=P(i in S and S disjoint neighbors),
q=P(i not in S and S disjoint neighbors), and M=|U|. Then
p=choose(M-40,n-1)/choose(M,n),
q=choose(M-40,n)/choose(M,n), and q=(M-39-n)p/n.
IF M<=10n+5, then q<=9p; IF ALSO p<=27/40000 then
q<=243/40000 AND q<1/100; and IF INSTEAD q>=1/100 then
p>=1/900 AND p>27/40000.
The assumptions force M>=40 and 1<=n<=M, so the binomial denominator is
positive and the subtractions M-40,n-1 are ordinary nonnegative differences.
The boundary n=M-39 is included and gives q=0.

## SAP.P013a.T12

Conjunction of the NEGATIONS of two universal assertions. Each universal
ranges over EVERY finite type Omega (in universe Type), N,K, design P,
population F with N>0, label d satisfying positivity, natural R, and
attained minimum p0, assuming T_d!=0. The first assertion would bound
|[E_{P x P^R}Htilde_d-T_d]/T_d| by (1-p0)^(R+1).
The second additionally ranges over EVERY b>0 and assumes
R>=log(b)/log(1-p0)-1, and would bound that relative bias by b.
The theorem says EACH universal assertion is false, so witnesses to their
failures need not be the same. Unlike T4, R=0 is in these quantified assertions;
the explicit R=1 example in T3 can refute both without using this boundary.

## SAP.P013a.T13

1. For EVERY finite design and population with N>0, and EVERY positive label d,
   E H_d=T_d and
   Var H_d=sum_i pi_i^d(1-pi_i^d)[y(i,d)/pi_i^d]^2
   +sum_{i!=j}(pi_ij^{dd}-pi_i^d pi_j^d)
   [y(i,d)/pi_i^d][y(j,d)/pi_j^d].
2. Separately, for EVERY finite design and population with N>0, EVERY distinct
   positive labels d,e, E H_de=tau_de,
   Var H_de=[Var H_d+Var H_e-2Cov(H_d,H_e)]/N^2, and
   Cov(H_d,H_e)=sum_{i!=j}(pi_ij^{de}-pi_i^d pi_j^e)
   [y(i,d)/pi_i^d][y(j,e)/pi_j^e]-sum_i y(i,d)y(i,e).

No positivity of joint probabilities is assumed in either part.

## SAP.P013a.T14

For EVERY finite design and population with N>0 and EVERY positive label d:
IF EVERY joint pi_ij^{dd}>0 (including i=j), then E Q_d=Var H_d.
Unconditionally under the marginal assumptions,
E Q_d=Var H_d+A_d and Var H_d<=E(Q_d+A2_d).
The theorem does not assert that Q_d or the corrected estimate is nonnegative
at every realization. Joint-zero terms in Q_d use the zero-division convention
described above; A_d and A2_d explicitly range over their zero-joint domain.
