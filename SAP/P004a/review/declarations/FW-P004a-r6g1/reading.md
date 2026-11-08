# Blind reading

Saved before consulting `claims.json`, `record.json`, `earlier.json`, or
`architect-report.md`. This reads the current statements, not their proofs.
All entries in `closure.json` have been inspected. Source declarations were read
in Defs/Part1, Part2, Part3 and WholeW1; the 95 distinct auxiliary `_proof_`
declarations were also printed in `scratch/ClosureProofs.lean`. They supply
numeral typeclass instances, nonempty-node/Borel/finite-dimensional instances,
or the bound on the block index; none supplies a statistical hypothesis.
The generated structure constructor and projections have exactly the fields
listed below. The Challenge theorems have no hypotheses beyond their displayed
parameters and the hypotheses inside the proposition definitions.

## Common notation, fully expanded

An assignment on N nodes is a function z : Fin N → Bool. Write z_i=1 or 0 for
`bit (z i)`. A circle table R is any function (i,z) ↦ R_i(z) in the reals.
For any real vector p define

* w_p(z)=∏_i [p_i if z_i=1, otherwise 1−p_i];
* E_p X=∑_{z : Fin N → Bool} w_p(z) X(z), and P_p(A)=E_p 1_A;
* m_i(a)=E_p[1_{z_i=a}R_i(z)]/[p_i if a=1, otherwise 1−p_i];
* τ_i=m_i(1)−m_i(0), AME=N⁻¹∑_i τ_i;
* Cov_p(X,Y)=E_p(XY)−E_p X E_p Y and Var_p X=Cov_p(X,X).

When 0<p_i<1 these are precisely independent Bernoulli assignment, its
expectation/probability, and the conditional marginal means. These definitions
contain finite sums, not unspecified laws of dependent assignments.

For O_i in R^k, dot products are ∑_{j : Fin k} O_ij θ_j,
ℓ(t)=exp(t)/(1+exp(t)), and p_i(θ)=ℓ(O_i·θ). Put

I=N⁻¹∑_i p_i(1−p_i) O_i O_iᵀ,
β_a=I⁻¹[N⁻¹∑_i m_i(a)p_i(1−p_i)O_i],
g^P_i(a)=O_i·β_a,
γ=I⁻¹[N⁻¹∑_i ((1−p_i)m_i(1)+p_i m_i(0))O_i].

For any deterministic g_i(a), define δ_i=τ_i−g_i(1)+g_i(0),
Q(p,R,B,g)=N⁻¹∑_i∑_{j∈B_i}δ_iδ_j, and

* D_i(g,z)=z_i(R_i(z)−g_i(1))/p_i−(1−z_i)(R_i(z)−g_i(0))/(1−p_i);
* HT(p,R,z)=N⁻¹∑_i[z_i R_i(z)/p_i−(1−z_i)R_i(z)/(1−p_i)];
* A(p,R,g,z)=N⁻¹∑_i[g_i(1)−g_i(0)+D_i(g,z)];
* H(p,R,B,g,z)=N⁻²∑_i∑_{j∈B_i}D_i(g,z)D_j(g,z);
* S(p,R,B,g,z)=N⁻²∑_i |B_i|[z_i(R_i(z)−g_i(1))²/p_i²
  +(1−z_i)(R_i(z)−g_i(0))²/(1−p_i)²].

The score fits g^S use Δ_i=g^P_i(1)−g^P_i(0), L_i=O_i·γ:
g^S_i(1)=p_i Δ_i+p_i(1−p_i)L_i and
g^S_i(0)=−(1−p_i)Δ_i+p_i(1−p_i)L_i.
The fitted IPW statistic is HT(p(θhat(z)),R,z).
For sample fitted coefficients replace I by I(phat,O) and use

βhat_a=I(phat,O)⁻¹[N⁻¹∑_i 1_{z_i=a}R_i(z) coin(phat_i,1−a)O_i],
γhat=I(phat,O)⁻¹[N⁻¹∑_i
 (z_i R_i(z)(1−phat_i)/phat_i+(1−z_i)R_i(z)phat_i/(1−phat_i))O_i].
`fittedScoreFits` uses these βhat, γhat in the same g^S formulas.

The `secondMomentBound` M(p,R,B,g) is N⁻² times the sum of
∑_i [E((R_i−g_i(1))²|z_i=1)/p_i+
E((R_i−g_i(0))²|z_i=0)/(1−p_i)] and
∑_i∑_{j∈B_i,j≠i}∑_{a,b∈{0,1}} s_a s_b
E[(R_i−g_i(a))(R_j−g_j(b))|z_i=a,z_j=b], where s_1=1,s_0=−1.
The latter conditional expectation is exactly the finite indicator-weighted sum
divided by coin(p_i,a)coin(p_j,b). Its use here always has i≠j.

`LogisticConditions O θ0 Θ θhat` means, in this order: Θ is compact;
θ0 belongs to Θ; there exists one real U bounding |O_Nij| for every N,i,j;
there exists c>0 such that eventually in N, for every v in R^k,
c∑_j v_j² ≤ N⁻¹∑_i(O_Ni·v)²; and for every N,z, θhat_N(z) belongs
to Θ and maximizes ∑_i[z_i O_Ni·θ−log(1+exp(O_Ni·θ))] over Θ.
It does not itself assert interior membership, which is separately stated when used.

A spatial population consists of nonempty subsets S_i of a metric measurable
space X, a measure ζ on X, an outcome Y(x,z) in R, and arbitrary distance-band
sets D(d)⊆R. Its node distance is infDist(x,S_i), region
C_i(d)={x:infDist(x,S_i)∈D(d)}, and table
R_i(d,z)=[∫_{C_i(d)}Y(x,z)dζ]/ζ(C_i(d)).toReal.
Node separation ρ_ij is inf{dist(x,y):x∈S_i,y∈S_j};
B_i(r)={j:ρ_ij≤r}. An assignment j interferes with table component i if
i=j or two assignments differing only at j give different R_i values.
i and j share a source if some l interferes with both. `LocalAt R ρ h`
means ∀i,j, ρ_ij>h implies they share no source.
`WellDefined P d` means each C_i(d) is measurable, has strictly positive
finite ζ mass, and Y(·,z) is integrable on it for every z.
`SpatialLocalConditions P` is the conjunction of: one b>0 eventually bounds
|Y_N(x,z)| strictly for every x,z; there exists h(d)≥0 for every d≥0
such that eventually LocalAt holds for that d and h(d); and there exists a
real function c(r) such that for every r≥0, eventually |B_i(r)|≤c(r) for
every node i. These eventual thresholds may depend on d or r.

`Overlap` supplies ε∈(0,1/2) with ε<p_Ni<1−ε for all N,i.
`Nondegenerate V` supplies v>0 with eventually NV_N≥v.
`InProb U` means ∀ε>0, P(|U_N|>ε)→0.
`LittleOp(U,r)` means InProb(U_N/r_N).
`BigOp(U,r)` means ∀ε>0 ∃C>0, eventually P(|U_N|>C|r_N|)<ε.
The W1 variants replace the population size N by an arbitrary n(k), with
k→∞. `NormalLimit U` means the distribution functions converge at every
real x to Φ(x)=(gaussianReal 0 1)(−∞,x].toReal.
q(a)=inf{x:a≤Φ(x)} is `normalQuantile`.
`Conservative coverage α` means ∀ε>0, eventually coverage_N≥1−α−ε,
not a possibly ill-defined real-valued liminf operation.

## SAP.P004a.T1

This is a closed conjunction followed by an existential choice of a full
sequence of actual constrained maximum likelihood estimators.
For every N put node i at (10i,0) in the Euclidean plane, take ζ to be the
sum of unit Dirac masses at these centers, take D(d)=[0,d], and let
Y(x,z)=∑_i 1_{x=(10i,0)}r_i, independently of z, where
r_i=21/20 when i mod 3=1, and r_i=1 otherwise.
O_i=(1,(i mod 3)−1), θ0=(0,log 2), Θ=[−2,2]^2.
All spatial, expectation, fit and limit symbols below mean the formulas above.
The theorem asserts all of the following.

1. These populations satisfy SpatialLocalConditions; θ0 is in the interior
   of Θ; 0<log 2<1; |Y|<2 for all N,x,z; |O_ij|≤1;
   1/10<p_i<9/10 for all N,i; every d≥0 is WellDefined;
   R(0)=r; LocalAt at every d≥0 holds with h=0;
   B_i(0)={i}; and for all N,i,r≥0, |B_i(r)|≤r/5+1.
2. For every integer K>0, with N=3K and R=R(0):
   N⁻¹∑ O_iO_iᵀ=diag(1,2/3), I=diag(25/108,4/27),
   β_0=β_1=(509/500,0), the vector defining Iγ is (61/60,0),
   γ=(549/125,0), every τ_i=0, AME=0 and Q(p,R,{i},g^P)=0.
   It also explicitly sets the printed asymmetric expression
   N⁻¹∑_i∑_{j∈{i}}(τ_i−O_i·(β_1−β_0))
   (τ_j−O_i·(β_1−β_0)) to zero.
3. Define A_t=−24/125 if t=1 and 27/250 otherwise,
   B_t=16/125 if t=1 and −81/1000 otherwise, D_t=A_t−B_t,
   and L_c(z)=N⁻¹∑_i c_{i mod 3}(z_i−p_i).
   For every K>0 and every z, A(p,R,g^P,z)=L_B(z), and
   HT−N⁻¹∑_i(z_i−p_i)O_i·γ=L_A(z).
   N Var(L_A)=3/625; N Var(L_B)=1753/750000;
   N Var(L_A−L_B)=10369/750000.
4. Block j is V_j(z)=∑_{t=0}^2 D_t(z_{3j+t}−p_t).
   For every K≥0 and every real function F on R^K, E[F(V)] is exactly
   ∑_{b : Fin K → Assignment 3} ∏_j w_p(b_j)
   F((∑_t D_t(b_jt−p_t))_j). Thus the joint law is the product of
   the identical one-block laws. A single block has mean zero, second
   moment 3·10369/750000 and fourth moment 915255049/250000000000.
5. For every K>0 put U_K=(∑_j V_j)/sqrt(3K).
   For every z, sqrt(3K)(L_A−L_B)=U_K;
   E U_K²=10369/750000;
   E U_K⁴=(915255049/250000000000)/(9K)
   +3(K−1)(10369/750000)²/K ≤2205448981/2250000000000;
   P(U_K²>(10369/750000)/2)≥107516161/2205448981.
6. There exists θhat for every N,z satisfying LogisticConditions with
   the O,θ0,Θ above. With T_N=HT(p(θhat_N(z)),R,z), along N=3K:
   T_N−L_A=O_p(N⁻¹);
   sqrt(N)(T_N−L_B)−U_K→p0;
   sqrt(N)(T_N−L_B) does not tend to zero in probability;
   sqrt(N)T_N/sqrt(3/625) converges to standard normal; and
   [T_N/sqrt(Var L_B)]/sqrt(3600/1753) does too.
   For every Vhat_K(z)≥0 on every draw, if NVhat→p1753/750000,
   then for every α∈(0,1),
   P(|T_N−AME|≤q(1−α/2)sqrt(Vhat)) tends to
   2Φ(q(1−α/2)sqrt(1753/3600))−1, strictly less than 1−α.

Junk conventions: real division/inversion at zero is zero, so N=0 values
of normalized quantities and U_0 use totalized arithmetic. The substantive
finite assertions use K>0; limit assertions are unaffected by K=0. The
K=0 block-law assertion is the valid one-element empty-assignment/product
identity. Singular matrix inverses are totalized (zero for singular real
matrices), but the displayed positive diagonal information for K>0 excludes
this and LogisticConditions excludes singularity eventually. Small other
N are permitted to be rank deficient. All log arguments used here are positive.
Square roots are only of nonnegative/positive quantities as used in the
substantive assertions. The normal quantile has a nonempty bounded-below
defining set because its arguments are strictly between zero and one.
Gaussian probabilities have finite mass, so toReal does not erase infinity.
The spatial integrals use finite counting measure and WellDefined regions;
zero/infinite-mass means or nonintegrable Bochner integrals do not support
the witness. Nonempty nodes and nonnegative distances make the distance
infima nonempty and bounded below. There is no natural truncated subtraction:
the residue is cast to R before subtracting 1, and K−1 in the moment formula
is real subtraction. No rpow, limsup/liminf or unspecified partial values occur.

## SAP.P004a.T2

For every family of types X_N with metric and measurable structures, this is
the conjunction of one universal asymptotic assertion and one universal finite
assertion. Metric and measurable structures are not explicitly required to be
compatible in the Lean binders.

First, for every k≥0, spatial sequence P on X_N, covariate sequence O_N,
θ0, Θ, estimator sequence θhat, and real d,h, assume in order: d≥0;
h≥0; SpatialLocalConditions P; eventually WellDefined P_N d; eventually
LocalAt R_N ρ_N h; LogisticConditions O θ0 Θ θhat; θ0∈interior Θ;
and Overlap p, where p_N=p(O_N,θ0), R_N is the actual spatial normalized
integral table at d, and B_Ni={j:ρ_Nij≤h}. Define
V_N=Var_p A(p,R,g^S). The conclusion is:

* fittedIPW−[HT−N⁻¹∑_i(z_i−p_i)O_i·γ]=O_p(N⁻¹);
* A(p,R,g^S)−fittedIPW=o_p(N⁻¹/²);
* if Nondegenerate V, the centered fittedIPW divided by sqrt(V_N) has a
  standard normal limit, and for every α∈(0,1) the intervals using raw S
  at phat=p(θhat(z)) with fittedScoreFits have asymptotic coverage ≥1−α;
* within that last assertion, if Q(p_N,R_N,B_N,g^P_N)≥0 for every N,
  the analogous intervals using sqrt(max(H(phat,R,B,fittedScoreFits,z),0))
  also have asymptotic coverage ≥1−α.

The fittedScoreFits use the actual sample βhat and γhat defined above, so
their assignment dependence is specified, not quantified arbitrarily.

Second, for every N,k,p,R,O,B, assume N>0, 0<p_i<1,
det I is a unit (over R this means det I≠0), every i belongs to B_i,
membership is symmetric, and j∉B_i implies R_i,R_j share no source.
Then simultaneously:

* for every i, g^S_i(1)−g^S_i(0)=g^P_i(1)−g^P_i(0), and
  g^S_i(1)/p_i+g^S_i(0)/(1−p_i)=O_i·γ;
* for every z, A(p,R,g^S,z)=HT−N⁻¹∑(z_i−p_i)O_i·γ;
* for every i, E D_i(g^S)=τ_i−g^P_i(1)+g^P_i(0);
* E A(p,R,g^S)=AME;
* Var A=M(p,R,B,g^S)−Q(p,R,B,g^S)/N;
* E H(p,R,B,g^S)=Var A+Q(p,R,B,g^P)/N;
* Var A≤E S(p,R,B,g^S).

Junk conventions: N=0 and rates 1/N or 1/sqrt(N) use zero division, but
only finitely early indices are affected in the asymptotic assertion, and
N>0 is explicit in the finite assertion. k=0 is allowed: covariate sums
are empty and the 0×0 information has determinant one; this gives the
ordinary unadjusted estimator and is meaningful. True and fitted logistic
probabilities are strictly between zero and one; Overlap and compact bounded
covariates supply uniform separation for the asymptotic assertion. Matrix
inverses at finitely early deficient designs have total values; eventual
coercivity and finite nonsingularity exclude them where needed. Pairwise
conditional means occur only for distinct nodes. All actual spatial averages
are eventually positive finite integrable means by WellDefined. Negative raw
S cannot occur with valid probabilities; H is explicitly clipped at zero.
Nondegenerate V excludes zero variance eventually in the normal
standardization. α∈(0,1) puts q inside its legitimate domain. Normal CDF
toReal is finite. Logistic log arguments 1+exp(t)>0. Nonempty nodes avoid
empty infDist; pair-distance infima are nonempty and bounded below.
There is no rpow or real liminf junk value: Conservative is the explicit
eventual lower-bound formula above. The probabilistic definitions would not
be probabilities for arbitrary p, but every applicable quantified p is valid.
The docstring expressly assumes the usual measure-theoretic conditions.

## SAP.P004a.T3

This is a closed conjunction about the following entire sequence. Nodes are
the singleton centers (10i,0), ζ is counting measure on those centers,
D(d)=[0,d]. A node is high-group when i mod 8<2, with O_i=(1,0);
otherwise O_i=(0,1). θ0=(0,−log 9), Θ=[−log 19,log 19]^2,
so p_i=1/2 on the high group and 1/10 otherwise. Let s_i=1 when
i mod 8=0, −1 when i mod 8=1, and zero otherwise. The spatial field is
Y(x,z)=∑_i 1_{dist(x,(10i,0))≤1}s_i z_i, including off-support points.
The center table is R_i(z)=s_i z_i.

Write n_H,n_L for the real-valued group cardinalities,
S=∑s_i z_i, K=∑_{i∈H}z_i, J=∑_{i∈L}z_i,
c(q)=max(1/20,min(19/20,q)), phat_H=c(K/n_H),
phat_L=c(J/n_L). θhat has coordinate log(phat_H/(1−phat_H))
unless n_H=0, in which case it is zero; its second coordinate is
log(phat_L/(1−phat_L)) unless n_L=0, in which case it is −log 9.
Define Rsum=∑_{i∈H} z_i(s_i−S/(n_H phat_H))² and n_1=∑z_i.
The printed residual is
e_i=(n_1/N)z_i(R_i−ghat_i(1))/phat_i+
((N−n_1)/N)(1−z_i)(R_i−ghat_i(0))/(1−phat_i),
where ghat_i(a)=O_i·βhat_a. The printed variance is
Vprint=N⁻²∑_i |B_i|[z_i e_i²/phat_i²+(1−z_i)e_i²/(1−phat_i)²],
and here B_i={i}. T is fittedIPW with the explicit θhat.

The statement asserts:

1. LogisticConditions for this actual θhat, θ0∈interior Θ,
   SpatialLocalConditions for this disk field, |Y|<2 everywhere,
   Y=s_i z_i on each entire unit disk and Y=0 outside all disks;
   WellDefined at every d≥0; the disk field's averages equal those of
   the center-only field for every d (including negative d);
   R(0)=the table above; LocalAt for every d≥0 with h=2(d+1);
   B_i(0)={i}; |B_i(r)|≤r/5+1 for all r≥0;
   1/25<p_i<24/25, and |O_ij|≤1 for every N,i,j.
2. For every integer r>0, N=8r: n_H=N/4,n_L=3N/4;
   N⁻¹∑O_iO_iᵀ=diag(1/4,3/4); the p_i values above;
   β_0=β_1=0, AME=0, Q(p,R,{i},g^P)=1/4;
   T=S/(N phat_H), A(p,R,g^P)=2S/N;
   E S=0, Var S=N/16, Var(2S/N)=1/(4N);
   βhat_1=(S/(n_H phat_H),0), βhat_0=0;
   1/20≤phat_H≤19/20 and every fitted information determinant is a unit;
   for every z, Vprint=(n_1/N)² Rsum/(N² phat_H⁴);
   and Var T>0.
3. Var T at N=32 is 18239/1505280; E Vprint at 32 is
   412940740700292467/161486810505216000000.
   At 64 the two quantities are 1710440723/354248294400 and
   17415062510218476553980121318471/12002159705791979639097262080000000.
   |E Vprint_64−14510/10000000|<1/20000000;
   |E Vprint_32/Var T_32−2110/10000|<1/20000 and
   |E Vprint_64/Var T_64−3005/10000|<1/20000;
   each expectation is strictly below the corresponding variance.
4. Along N=8r, T−2S/N=O_p(N⁻¹), sqrt(N)T/(1/2)→d N(0,1),
   N Var T→1/4, n_1/N→p1/5, Rsum/N→p1/8,
   NVprint→p2/25, Vprint/Var T→p8/25,
   and P(Vprint≤0)→0.
5. For every α∈(0,1/2), both P(|T|≤q(1−α/2)sqrt(Vprint))
   and P(Vprint>0 and |T/sqrt(Vprint)|≤q(1−α/2)) tend to
   2Φ(q(1−α/2)sqrt(8/25))−1<1−α.

Junk conventions: all assignment-dependent quantities are total even for
empty treatment arms. The clipping avoids zero or one fitted probabilities
even when a group has no treated or no control nodes. A group absent at small
N has the specified constant parameter fallback; group proportions use
division by zero before clipping, but for N=8r,r>0 both groups exist.
Those fallback and N=0 values do not control any asymptotic conclusion.
Fitted information is explicitly nonsingular for the finite substantive
claims. Empty sums/assignments for N=0 are harmless. Vprint can be zero for
some positive-probability assignments; the first coverage event is a
well-defined zero-radius interval, and the standardized event requires
Vprint>0. All variance ratios use explicitly positive actual variance at
N=8r,r>0. The logs of 9 and 19 and clipped odds are positive-argument logs;
sqrt and quantile domains are legitimate. The counting measure is finite,
and all spatial means at d≥0 are certified positive and integrable. At d<0,
both fields have empty regions and hence totalized zero averages in the
equality of their averages; that ancillary equality asserts no substantive
positive-mass average. Node infima are legitimate as for T1. No truncated
subtraction, rpow or unguarded liminf/limsup is used.

## SAP.P004a.T4

This is a closed conjunction of two universal finite assertions and a
closed list of additional consequences for the same explicit active design.
All definitions of D,S,Vprint,βhat,phat_H,Rsum,T are those above.

First, for every N,phat,R,B,g,z, assume N>0, both treatment counts
n_1,n_0>0 and 0<phat_i<1 for all i. Then S equals
∑_i z_i|B_i| e_i²/n_1²+∑_i(1−z_i)|B_i|e_i²/n_0²,
where e is the printed weighted residual above. Also Vprint equals
N⁻²∑_i |B_i|[(n_1/N)²z_i(R_i−g_i(1))²/phat_i⁴+
(n_0/N)²(1−z_i)(R_i−g_i(0))²/(1−phat_i)⁴].

Second, for every N,p,R,B,g, assume N>0, 0<p_i<1, i∈B_i,
j∈B_i iff i∈B_j, and for all i,j with j∉B_i,
Cov_p(D_i(g),D_j(g))=0. Then
Var_p(N⁻¹∑_iD_i(g))≤L(p,R,B,g)=E_p S(p,R,B,g), where
L=N⁻²∑_i |B_i|[E((R_i−g_i(1))²|z_i=1)/p_i+
E((R_i−g_i(0))²|z_i=0)/(1−p_i)].
Here g is a deterministic node-and-arm function; arbitrary sample fitted
g is not substituted inside the probability inequality.

Third, for the explicit active MLE design of T3, using its fitted βhat
and singleton neighborhoods, for every r>0,N=8r,z,
Vraw=S(phat,R,{i},ghat,z)=Rsum/(N² phat_H²).
Along that sequence NVraw→p1/2 while N Var T→1/4, and 1/4≤1/2.
At N=32 E Vraw=493725989/38038425600 and
Var T=18239/1505280<E Vraw.

Junk conventions: both arm-count denominators in the first identity are
strictly positive; so are N and the propensity denominators. The second
assertion has no arm-count divisions and remains meaningful on empty-arm
assignments. Both expectations are genuine finite-product expectations.
The active witness uses clipped positive propensities, with positive group
sizes at the asserted finite indices. Its possible zero residual variances
are not divided by. Other small-N inverses and group fallback choices are
as in T3 and do not determine the limits. No quantile, sqrt, rpow or
liminf is used in T4 itself. Its closure contains log/total inverses only
through the active MLE, with the same legitimate/finitely early domains
already described. The docstring's reference to general IPW intervals
points to T2; T4's universal bound itself is for deterministic g.

## SAP.P004a.T5

This is a closed conjunction about three explicitly given binary outcome
fields and a refinement of one of them. There are two nodes: the closed
radius-one disks centered at c_0=(0,0),c_1=(100,0). ζ is planar Lebesgue
measure. Distance is distance to the entire node disk, not to its center.
For label d=0 take D(d)={0}; for d=6 take [0,5]; otherwise take (d−1,d].
Consequently the six bins at j=0,…,5 are the center disk of radius one
and the annuli j<dist(x,c_i)≤j+1 for j≥1; the union is the disk of radius six.

Let a_i(x) be the complex argument of (x−c_i), adjusted from (−π,π]
to [0,2π), divided by 2π. For an array q_j(a), the field is
Y_q(x,z)=∑_{i=0}^1∑_{j=0}^5
1_{x in bin(i,j)}1_{a_i(x)<q_j(z_i)}.
The three q arrays have control value 1/10 everywhere and treatment values:
Case A: 283/3000 everywhere; Case B: 1/50 at j=0 and 273/2500
elsewhere; Case C: (90,91,94,95,97,99)/1000.
Treatment probabilities for AMEs are independent 1/2 coins.
The observed assignment is z*=(true,false).
For any table, armMean_a is ∑_{i:z_i=a}R_i(z)/n_a, and
Hajek=armMean_1−armMean_0.

The statement asserts n_1(z*)=n_0(z*)=1; all q∈[0,1]; and for each
case: Y is binary everywhere and measurable for every assignment; on every
bin it is the indicated angular threshold; outside the two radius-six disks
it vanishes; all six bins and the union are WellDefined; regions are exactly
the stated bins; for each node they are pairwise disjoint and their union
is the d=6 region; bin j has area π(2j+1) and union area 36π.
For every assignment z,node i,bin j, its normalized average is q_j(z_i),
and the union average is ∑_j (2j+1)q_j(z_i)/36.
For every case and bin, the Hajek at z* and the AME each equal q_j(1)−1/10.
For every case, both six-bin sums equal −17/500, while both the union
Hajek at z* and the union AME equal respectively −17/3000,121/18000,
−7/1800 in Cases A,B,C. The sum differs from the union effect in each
case; the Case B union effect is positive, and in Case C −17/500 is
strictly below every individual bin effect.

For each j=0,…,10 change only the band of the same Case A population to
{0} at j=0, and ((j−1)/2,j/2] at j≥1. Every refined bin is WellDefined;
for each node the eleven regions are disjoint and their union is the same
radius-six disk. For all assignments their averages equal the Case A q
value for that node's treatment. Every refined Hajek at z* and every AME
is −17/3000; their sums are −187/3000; the unchanged union AME is −17/3000.
This mathematically refutes an identity of unweighted sums with normalized
union effects. The docstring expressly describes this as a refuted reading,
and expressly asserts no corrected numerical effect for the empirical application.

Junk conventions: node distance zero here describes a whole positive-area
disk, so neither the j=0 original bin nor the j=0 refined bin is a
zero-area singleton circle. All average denominators are certified positive
finite and all integrals exist. The angular argument at the center is
Mathlib's total arg(0)=0; its chosen value changes the field on a zero-area
set only and does not change any asserted average. The branch cut is
measurable; 2π>0. q can be arbitrary in the auxiliary geometry predicate,
but all instances asserted here have q∈[0,1]. Hajek would totalize a mean
over an empty treatment arm to zero, but only z* with both counts one is
used for Hajek conclusions. Marginal means use p=1/2 and have nonzero
conditional denominators. ENNReal.ofReal clips negative arguments, but all
asserted bin/union areas have positive arguments. No zero or infinite
mass is hidden by toReal. j−1 in refined bands is real subtraction after
casting. Finite index types have 2,3,6 or 11 elements, so no empty-index
ambiguity occurs. There is no quantile, sqrt, rpow, liminf/limsup, singular
matrix inverse or unbounded/empty extremum in this declaration's substance.
