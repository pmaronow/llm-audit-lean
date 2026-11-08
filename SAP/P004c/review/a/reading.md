# Blind mathematical reading

Written from `SAP/P004c/Defs*.lean`, `SAP/P004c/Defs/Part*.lean`, and
`SAP/P004c/Challenge*.lean` before reading `claims.json` or `record.json`.
The Challenge contains nine theorems. Each merely asserts the proposition
defined by the correspondingly numbered `T…Statement`; the definitions below
are part of the asserted statements, not assumptions about an outside paper.

## Common finite objects and probability

For a natural number N, the nodes are I_N = {0,…,N−1} and an assignment is a
function z : I_N → {false,true}. Write z_i numerically as 0 or 1. A circle
table R is any real function R_i(z). No spatial origin of R is required in
the finite-table assertions.

For any vector p of real numbers define c_i(1)=p_i, c_i(0)=1−p_i,
w_p(z)=∏_i c_i(z_i), E_p X=∑_z w_p(z)X(z), and
P_p(A)=E_p 1_A. The definitions alone do not restrict p, but every asserted
use that needs a probability law has 0<p_i<1 (in the theorems, p_i=p with
0<p<1). These finite sums are then ordinary independent Bernoulli
expectations and probabilities. Define Cov_p(X,Y)=E_p(XY)−E_p X E_p Y and
Var_p X=Cov_p(X,X).

Let m_i(a)=E_p[1_{z_i=a}R_i(z)]/c_i(a). This is the arm-conditional
mean. Let Δ_i=m_i(1)−m_i(0), τ=N⁻¹∑_i Δ_i (the definition `ame`),
and m̄(a)=N⁻¹∑_i m_i(a). For i≠j let
m_{ij}^{ab}(X)=E_p[1_{z_i=a,z_j=b}X(z)]/[c_i(a)c_j(b)]. The
definition `pairMarginal` also exists at i=j, but all occurrences in the
asserted expansions exclude i=j, so this really is a pair-conditional
expectation wherever used.

The HT statistic is H(z)=N⁻¹∑_i[z_iR_i(z)/p_i−(1−z_i)R_i(z)/(1−p_i)].
Let n_a(z)=∑_i1_{z_i=a}. The observed arm mean is
M_a(z)=(∑_i1_{z_i=a}R_i(z))/n_a(z). Because division in ℝ is totalized,
M_a=0 if the arm is empty. The Hajek statistic is T=M_1−M_0.

For a fixed real table g_i(a), define
A_g(z)=N⁻¹∑_i[g_i(1)−g_i(0)+z_i(R_i(z)−g_i(1))/p_i
−(1−z_i)(R_i(z)−g_i(0))/(1−p_i)]. Its random residual contrast at node i
is q_i(z)=z_i(R_i(z)−g_i(1))/p_i−(1−z_i)(R_i(z)−g_i(0))/(1−p_i),
and its mean residual effect is δ_i=Δ_i−g_i(1)+g_i(0).
The linearized Hajek statistic L is A_g with g_i(a)=m̄(a). Thus its
control denominator is 1−p_i. The averages m̄(a), hence g, are computed
under the full design law and are fixed with respect to the observed z.

Say i depends on j (`interferes R i j`) if i=j, or if two assignments
that agree everywhere except possibly at j give different values of
R_i. Say i,j share a source if some l is a dependency of both. This
relation is symmetric and reflexive. Given real distances D_ij, the
closed ball B_D(i,r) contains exactly the j with D_ij≤r. A neighborhood
system B_i is otherwise any finite subset of I_N; its maximum degree
d_B is max_i |B_i| (zero if N=0). `LocalAt R D h` means that whenever
D_ij>h, i and j do not share a source. No properties of D are implicit.

Here are the exact variance expressions used below. Put s(1)=1,
s(0)=−1. The expression V_g(B), called `varianceExpansion`, is N⁻²
times the sum of

* ∑_i {E_p[(R_i−g_i(1))² | z_i=1]/p_i
  +E_p[(R_i−g_i(0))² | z_i=0]/(1−p_i)−δ_i²};
* ∑_i∑_{j∈B_i,j≠i}∑_{a,b∈{0,1}} s(a)s(b)
  {m_{ij}^{ab}((R_i−g_i(a))(R_j−g_j(b)))
  −(m_i(a)−g_i(a))(m_j(b)−g_j(b))}.

The expression S_g(B), called `secondMomentBound`, removes both kinds
of subtracted mean product from this formula: it keeps the two
conditional squared terms and the four signed conditional pair products.
`homophilyQ` is N⁻¹∑_i∑_{j∈B_i}δ_iδ_j.
The effect homophily used in T33 is
C(B)=N⁻¹∑_i(Δ_i−τ)∑_{j∈B_i}(Δ_j−τ).
All pair sums are over ordered pairs, with no factor 1/2.

With common p define
D_H=N⁻²∑_i{E[R_i²|z_i=1]/p+E[R_i²|z_i=0]/(1−p)−Δ_i²}
(`htDiagonal`) and
C_H^{ab}=N⁻²∑_i∑_{j∈B_i,j≠i}
{m_{ij}^{ab}(R_iR_j)−m_i(a)m_j(b)} (`htPairCov`).
`htVarianceUpper` U_H is the same expression as V_0(B), except that
only the diagonal subtraction −∑_iΔ_i²/N² is removed; the pair
mean products remain subtracted.

All subtraction above is real subtraction, not truncated natural
subtraction. A displayed N in a real expression is the real coercion of
the natural number. All potentially relevant denominators are protected
by N>0 or 0<p<1, apart from the explicitly defined empty-arm convention
and finite initial terms in asymptotic sequences.

## Spatial objects

A population P consists of a metric space X with an independently
specified measurable-space structure, nonempty sets A_i⊆X, a measure
ζ on X, a real outcome Y(x,z), and an arbitrary family of subsets
bands(d)⊆ℝ indexed by real d. There is no further implicit compatibility,
regularity, geometric shape, or disjointness assumption.

The point-to-node distance is inf_{y∈A_i}dist(x,y), implemented as
`Metric.infDist`. The node separation D_ij is the infimum of
{dist(x,y):x∈A_i,y∈A_j}. Node nonemptiness and the lower bound zero
make these genuine finite infima. The region C_i(d) consists of x whose
point-to-node distance belongs to bands(d). The circle table is
R_i(z)=∫_{C_i(d)}Y(x,z)dζ / ζ(C_i(d)).toReal.

`WellDefined P d` requires, for every i, that C_i(d) is measurable,
0<ζ(C_i(d))<∞, and Y(·,z) is integrable on C_i(d) for every z.
Integrability is Mathlib's almost everywhere strong measurability plus
finite integral of the norm under the restricted measure. Thus wherever
this premise holds the spatial expression is a genuine normalized
integral with a positive finite real denominator.

A population sequence P gives such a population with N nodes for every
natural N, with spaces X_N allowed to vary. Define the following
sequence conditions:

* `SpatialLocalConditions P`: (i) there is b>0 and a sample-size threshold
  after which |Y_N(x,z)|<b for all x,z; (ii) there is a real function h(d)
  with h(d)≥0 for d≥0 such that, for each fixed d≥0, eventually in N the
  table at d satisfies LocalAt with D_N and radius h(d); (iii) there is a
  real function c(r) such that, for each fixed r≥0, eventually in N every
  node's closed D_N-ball of radius r has cardinality at most c(r).
  In (ii) and (iii) the sample-size threshold can depend on the radius.
* `BoundedOutcomes` is exactly (i) alone.
* `MetricNodeDistances P`: for every N, D_N is nonnegative, D_ij=0 iff
  i=j, D_ij=D_ji, and D_ik≤D_ij+D_jk. These conditions are additional
  because separation between nonempty sets need not be a metric.
* `QuadraticSpacing P`: there is C_b>0 and one eventual threshold in N
  such that, for every N past it, every node i and every real s≥0,
  |B_{D_N}(i,s)|≤C_b(1+s²). The threshold is uniform over s and i.

For a finite set J of nodes, `conditionOn p J U z` is
E_p[1_{z'_j=z_j for all j∈J}U(z')]/∏_{j∈J}c_j(z_j).
With interior p this is the conditional expectation given those
coordinates. `l2Norm p U` is √E_p U².

`NEDConditions P p d` says there exist a real function ψ(s), positive
numbers g_{Ni}, and a common real upper bound G such that:
(i) ψ≥0 on [0,∞), is nonincreasing there, and ψ(s)→0 as s→∞;
(ii) there exist a real exponent α>4 and real C,S with S>0 such that
ψ(s)≤C s^(−α) for every s≥S;
(iii) 0<g_{Ni}≤G for every N,i;
(iv) for every N,i and every s≥0, the L² norm, under independent
common-p assignments, of
R_{Ni}−E[R_{Ni}|z_j:j∈B_{D_N}(i,s)] is at most g_{Ni}ψ(s).
In (ii) exponentiation is Mathlib real exponentiation; the base is
positive because s≥S>0. C has no separate positivity premise.

## Limits and normalization

Every eventual statement uses the natural-number filter atTop, i.e.
all sufficiently large N. `IsBigO atTop f (N↦N⁻¹)` means that there
exist a real constant C and an eventual threshold such that
|f(N)|≤C|N⁻¹|. For a sequence of assignment laws p_N,
`InProb p U` means: for every ε>0, P_{p_N}(|U_N|>ε)→0.
`BigOp p U r` means: for every ε>0 there exist C>0 and a threshold
such that P_{p_N}(|U_N|>C|r_N|)<ε for every later N.

`normalCDF(x)` is the real value of the measure of (−∞,x] under
Mathlib's Gaussian measure of mean zero and variance one.
`NormalLimit p U` says that for every real x,
P_{p_N}(U_N≤x) converges to this CDF value. This is convergence in
distribution to the actual standard normal measure.
`Nondegenerate V` means there exist v>0 and a threshold such that
N V_N≥v eventually. In particular V_N>0 eventually.
Real.sqrt is the nonnegative square root (zero on negative inputs);
all variance normalizations requiring a limit have eventual positivity.

For arbitrary weights w_i(z), `marginalLawEffect w F i` is
∑_z w_i(z)F(z with coordinate i forced to 1)
−∑_z w_i(z)F(z with coordinate i forced to 0).
It overwrites coordinate i rather than conditioning on its observed
value. `SharpNull Y` means ∀x,z, Y(x,z)=Y(x,all-zero assignment).

## T31 — exact quantified reading

The theorem is a conjunction of these two universally quantified assertions:

1. For every natural N, every type X at the specified arbitrary universe,
   and every Y:X×assignments→ℝ, SharpNull Y if and only if
   ∀x,z, Y(x,z)=Y(x,all-zero assignment). This is an unfolding of its
   definition and does not conclude that any particular Y satisfies it.
2. For every N, real circle table R and assignment z, if both n_1(z)>0
   and n_0(z)>0, all of the following hold:
   * n_1=∑_i z_i, n_0=N−n_1, and n_0=∑_i(1−z_i).
   * For every pair of real numbers μ,t, the residual sum of squares
     at intercept M_0 and slope T is at most that at μ,t. If these sums
     of squares are equal, then μ=M_0 and t=T. Thus this is a unique
     least-squares minimizer for the realized table, not a statement
     about an estimator's limiting law.
   * For every vector e of real residuals, the following matrix
     identities and inequalities hold. Let X be the N×2 matrix with
     row (1,z_i), A=(XᵀX)⁻¹, and S(K)=A Xᵀ[e_i e_j K_ij]X A.
     For every real N×N matrix K,
     S(K)=A[∑_{i,j}X_{ia}X_{jb}e_i e_jK_ij]_{a,b=0,1}A.
     Then, for every real vector of values v and every real N×N matrix
     U satisfying UᵀU=I, set
     K_ij=∑_k v_k U_ik U_jk and
     Q_ij=∑_k max(v_k,0)U_ik U_jk. The difference Q−K equals
     [∑_k max(−v_k,0)U_ik U_jk]; Q, Q−K,
     [e_i e_jQ_ij], [e_i e_j(Q−K)_ij], S(Q), and S(Q)−S(K)
     are all positive semidefinite. Finally max(S(K)_{11},0)≤S(Q)_{11}.

For real matrices, Mathlib `PosSemidef` means symmetric and having
nonnegative quadratic form on every real vector (the underlying
definition uses finitely supported vectors, equivalent here).
Matrix inversion is adjugate times inverse determinant, returning zero
when singular; the two positive arm counts here ensure XᵀX is
nonsingular. The helper `kernelVariance` defines a scalar weighted sum
using λ_i=z_i/n_1−(1−z_i)/n_0, but T31 does not assert its equality to a
sandwich entry and does not use that helper.

## T32 — exact quantified reading

This is a conjunction of five separately quantified assertions:

1. For every N,p,R,B, if N>0, 0<p<1, i∈B_i for every i, and
   j∉B_i implies that i,j share no source for every i,j, then
   Var H=V_0(B), and Var H≤U_H. Symmetry of B is not required here.
2. For every N,p,b,R,B, if N>0, 0<p<1, |R_i(z)|<b for every i,z,
   every B_i contains i, j∈B_i iff i∈B_j for every i,j, and every
   omitted pair shares no source, then all of these hold:
   0≤D_H≤b²/(Np)+b²/[N(1−p)]; for every a,c∈{0,1},
   |C_H^{ac}|≤2b²(d_B−1)/N; and
   Var H≤b²/(Np)+b²/[N(1−p)]+8b²(d_B−1)/N.
   The degree subtraction here is real subtraction.
3. For every common p, real b, and sequence of tables R_N, if 0<p<1
   and eventually |R_{Ni}(z)|<b for all i,z, then D_H(N)=O(N⁻¹).
4. For every p,b,R_N,B_N and natural D, if 0<p<1 and eventually all
   table entries have absolute value <b, every B_{Ni} contains i, and
   d_{B_N}≤D, then for every a,c, C_H^{ac}(N)=O(N⁻¹). No locality or
   symmetry premise occurs in this fourth assertion.
5. For every family of metric measurable spaces X_N, sequence P and
   real p,d, if 0<p<1, d≥0, SpatialLocalConditions P, and eventually
   WellDefined(P_N,d), the HT variance computed from the spatial table
   at d is O(N⁻¹).

## T33 — exact quantified reading

This is a conjunction of two assertions:

1. For every N,p,R,B, if N>0, 0<p<1, i∈B_i for all i and every
   omitted pair shares no source, put p_i=p and g_i(a)=m̄(a).
   Then Var L=V_g(B), S_g(B)−Var L=C(B)/N,
   [Var L≤S_g(B) iff C(B)≥0], and
   [C(B)≥0 implies Var L≤S_g(B)]. No separate symmetry premise and
   no assumption that C(B)≥0 are imposed on the identity or equivalence.
2. For every N,p,R, if N>0, 0<p<1 and Var H>0, define
   U_i(z)={z_iR_i(z)/p−(1−z_i)R_i(z)/(1−p)−Δ_i}/[N√Var H].
   Then for every z, ∑_i U_i(z)=(H(z)−τ)/√Var H; for every i,
   E U_i=0; and Var(∑_i U_i)=1.

## T34 — exact quantified reading

This is a conjunction of four assertions:

1. For every natural N, assignment z and reals p,S, if N>0,
   n_1(z)>0 and 0<p<1, then
   |N{NS/n_1²−NS/(N²p²)}|=|N²/n_1²−1/p²| |S|, and
   |N²/n_1²−1/p²|
   =|{(n_1/N−p)(n_1/N+p)}/{p²(n_1/N)²}|.
2. For every N,z,e,D,K,b,Kmax, where e_i and D_ij are real and
   K:ℝ→ℝ, if N>0, b>0, |K(t)|≤Kmax for every t≥0,
   K(t)=0 for every t>1, and D_ij≥0 for every i,j, then
   |N⁻¹∑_i∑_{j≠i}z_i z_j e_i e_j K(D_ij/b)|
   ≤Kmax (sup_i|e_i|)² max_i|B_D(i,b)|.
   No metric, symmetry, integrability or probabilistic premise is
   required. The real supremum is over a finite nonempty range because
   N>0, so it is an ordinary maximum.
3. For every real p with 0<p<1, under independent common-p assignments,
   the error E_N(z), defined as |N²/n_1(z)²−1/p²| when n_1>0
   and as zero when n_1=0, is O_p(N⁻¹/²), in the precise BigOp sense
   specified above. The rate expression is (√N)⁻¹.
4. The three fixed real numerical facts
   |8²/5²−1/(1/2)²| |−1/4|=9/25,
   (8²/5²−1/(1/2)²)|−1/4|=−9/25,
   and not (9/25≤−9/25) hold.

There is no quantified bandwidth sequence, rate for a product with
bandwidth, or construction of an eight-node assignment/kernel/residual
table in this statement. S is arbitrary in part 1; the fixed number
−1/4 in part 4 is not asserted to arise from part 2.

## T39 — exact quantified reading

For every natural N, real p and arbitrary real circle table R, if
N>0 and 0<p<1, then
E_p H=N⁻¹∑_i{E_p[R_i(z with i forced to 1)]
−E_p[R_i(z with i forced to 0)]}.
Expectations on the right integrate the full Bernoulli vector and then
overwrite the ith coordinate, hence marginalize only the other
coordinates in effect. No locality or outcome boundedness is assumed.

## T40 — exact quantified reading

For every N, metric measurable space A, spatial population P, real d,
weights w_i(z), functions g_i:A→ℝ and f:A→ℝ, if N>0,
∑_z w_i(z)=1 for every i, w_i(z)≥0 for every i,z,
Y(x,z)=∑_j z_j g_j(x)+f(x) for every x,z, and WellDefined(P,d),
then the following three conclusions hold together:

1. For every i,x, marginalLawEffect(w,Y(x,·),i)=g_i(x).
2. For every i, the forced-coordinate marginal effect of R_i is
   ∫_{C_i(d)}g_i(x)dζ / ζ(C_i(d)).toReal.
3. The mean over nodes of these marginal circle effects equals
   N⁻¹∑_i∫_{C_i(d)}g_i(x)dζ / ζ(C_i(d)).toReal.

The law w can differ by i and need not be a Bernoulli law or the
marginals of a single common joint law. Separate integrability of g_i
and f is not a hypothesis; it follows on each region from integrability
of all the additive potential outcomes by taking differences with the
all-zero and single-treatment assignments. No restriction d≥0 appears.

## T41 — exact quantified reading

For every family of metric measurable spaces X_N, population sequence
P and real p,d, if 0<p<1, d≥0, SpatialLocalConditions(P), and
eventually WellDefined(P_N,d), then Var H_N=O(N⁻¹), and, if
additionally there exist v>0 and an eventual threshold with
N Var H_N≥v, the CDF of (H_N−τ_N)/√Var H_N converges at every real
x to the standard normal CDF. There is no claim of normal convergence
without this last nondegeneracy premise and no premise about C5.

## T42 — exact quantified reading

For every family of metric measurable spaces X_N, population sequence
P and real p,d, if 0<p<1, d≥0, SpatialLocalConditions(P), eventually
WellDefined(P_N,d), and there exist v>0 and a threshold with
N Var L_N≥v eventually, then (T_N−τ_N)/√Var L_N has CDF converging
at every real x to the standard normal CDF. Here T_N assigns zero
means to empty arms, L_N uses the fixed design arm means as described
above, and the denominator is Var L_N, not Var T_N.

## T44 — exact quantified reading

For every family of metric measurable spaces X_N, population sequence
P and real p,d, if 0<p<1, d≥0, BoundedOutcomes(P), eventually
WellDefined(P_N,d), NEDConditions(P,p,d), MetricNodeDistances(P),
and QuadraticSpacing(P), then all the following hold:

1. For every natural N, if N>0 and WellDefined(P_N,d), E H_N=τ_N.
   This finite conclusion has its own local well-definedness premise.
2. Var H_N=O(N⁻¹).
3. √N(L_N−T_N) converges to zero in probability.
4. If additionally N Var L_N≥v>0 eventually for some fixed v,
   then (T_N−τ_N)/√Var L_N converges in CDF to standard normal.

The NED premise controls the actual spatial circle table's conditional
approximations under the same assignment law used in the conclusions.
The global spacing threshold is simultaneous in every radius, rather
than a separate eventual statement for each radius. There is no finite
interference-radius premise in T44.

## Mathlib definitions checked

The relevant source definitions were read directly, including:

* `Topology/MetricSpace/HausdorffDistance.lean:463` (`Metric.infDist`),
  together with its nonempty-set greatest-lower-bound characterization;
* `MeasureTheory/Integral/IntegrableOn.lean:92` (`IntegrableOn`);
* `Probability/Distributions/Gaussian/Real.lean:222` (`gaussianReal` and
  its probability-measure instance; the second parameter is variance);
* `Analysis/Asymptotics/Defs.lean:73,85` (`IsBigOWith`, `IsBigO`);
* `LinearAlgebra/Matrix/PosDef.lean:60` (`PosSemidef`);
* `LinearAlgebra/Matrix/NonsingularInverse.lean:169–179` (matrix inverse).

All sums and products are Mathlib finite sums/products over the full
finite assignment or node type, with the stated filtered/erased
neighborhoods. ENNReal.toReal would map infinity to zero, but
WellDefined rules this out at every spatial-average use relevant to
the conclusions or eventually relevant to an asymptotic conclusion.
