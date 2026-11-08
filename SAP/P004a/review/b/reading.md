# Blind reading of the Challenge

This file was written from `SAP/P004a/Defs.lean`, all four Defs parts, and
`SAP/P004a/Challenge.lean` and its Part1, before opening either `claims.json` or
`record.json`. The theorem docstrings are part of the Challenge, but the readings
below describe the propositions themselves. Every theorem is a stub with `sorry`.

## Mathematical dictionary and conventions

An index in `Fin N` is an integer from 0 to N−1. An assignment is a function
z:{0,…,N−1}→{false,true}; write z_i as its 0/1 indicator. All assignment and node
sums and products are finite. Natural-number denominators in real formulas are
coerced to real numbers. There is no implicit assumption N>0. Real division is
totalized (x/0=0), and the inverse of a singular real square matrix is the zero
matrix. The explicit positivity/nonsingularity assumptions below matter.

A spatial population P of size N comprises an arbitrary metric space X with an
arbitrary measurable-space structure (no Borel compatibility instance is required),
nonempty node sets A_i⊆X, a measure ζ, an outcome Y(x,z)∈R, and an arbitrary
band selector D:R→sets of real numbers. Its point-to-node distance is
ρ_i(x)=inf_{y∈A_i} dist(x,y), and its node separation is
D_ij=inf{dist(x,y):x∈A_i,y∈A_j}. The nonempty node sets ensure the relevant
distance sets are nonempty and bounded below. Regions are
E_i(d)={x:ρ_i(x)∈D(d)}. Write

    R_i(d,z) = (integral over E_i(d) of Y(x,z) dζ) / ζ(E_i(d)).toReal.

`WellDefined P d` means, for every i, E_i(d) is measurable, has strictly positive
finite ζ mass, and Y(·,z) is integrable on it for every assignment z. Set integrals
are Bochner integrals against restricted measures. Mathlib assigns zero to a
nonintegrable Bochner integral; `ENNReal.toReal` assigns zero to infinity.
WellDefined excludes these conventions in the circle averages to which it applies.

For any table R_i(z), node j interferes with i if i=j OR there are assignments
z,z′ identical off j with R_i(z)≠R_i(z′). Nodes i,j share a source if some l
interferes with both. `LocalAt R D h` means, for every i,j, D_ij>h implies that
i,j have no shared source. Write B_i(h)={j:D_ij≤h} and b_i=|B_i|.

For a sequence of populations, `SpatialLocalConditions` is exactly the conjunction:

* There exists b>0 such that, eventually in N, |Y_N(x,z)|<b for every x,z.
* There exists a function h(d), nonnegative for every d≥0, such that for each d≥0,
  eventually in N the corresponding R_N(d) is LocalAt at radius h(d).
* There exists a real function c(r) such that, for every r≥0, eventually in N,
  every i satisfies |B_i(r)|≤c(r).

The eventual thresholds in the second and third clauses may depend on d and r,
respectively. No Euclidean geometry or Lebesgue measure is implicit here.

Given real numbers p_i and an assignment z, put
q_i(a)=p_i if a=true, and 1−p_i otherwise, and
w_p(z)=product_i q_i(z_i). `expect p X` is sum_z w_p(z)X(z), and
`prob p A` is sum_z w_p(z)1_A(z). When 0<p_i<1 these are the expectation and
probability under independent Bernoulli(p_i) assignments. Define

    μ_i(a) = E_p[1{z_i=a} R_i(z)] / q_i(a),
    τ_i = μ_i(true)−μ_i(false),        τ = (sum_i τ_i)/N.

These are `marginal`, `nodeEffect`, and `ame`. For fixed g_i(a), put

    r_i = τ_i−(g_i(true)−g_i(false)),
    Q(p,R,B,g) = (sum_i sum_{j∈B_i} r_i r_j)/N,
    C_i(g,z) = z_i(R_i(z)−g_i(true))/p_i
               −(1−z_i)(R_i(z)−g_i(false))/(1−p_i),
    A_g(z) = (sum_i [g_i(true)−g_i(false)+C_i(g,z)])/N,
    H_p(z) = (sum_i [z_i R_i(z)/p_i−(1−z_i)R_i(z)/(1−p_i)])/N.

These are `residualEffect`, `homophilyQ`, `residualContrast`, `augmented`, and
`ht`. Cov(X,Y)=E[XY]−E[X]E[Y], and Var(X)=Cov(X,X).

For design rows O_i∈R^k, dot is the ordinary coordinate sum, ℓ(t)=exp(t)/(1+exp(t)),
and p_i(θ)=ℓ(O_i·θ). Write

    I = (sum_i p_i(1−p_i) O_i O_iᵀ)/N,
    β_a = I⁻¹ (sum_i μ_i(a)p_i(1−p_i)O_i)/N,
    f_i(a) = O_i·β_a,
    γ = I⁻¹ (sum_i [(1−p_i)μ_i(true)+p_i μ_i(false)]O_i)/N,
    δ_i = f_i(true)−f_i(false),    L_i = O_i·γ,
    s_i(true) = p_i δ_i+p_i(1−p_i)L_i,
    s_i(false) = −(1−p_i)δ_i+p_i(1−p_i)L_i.

These are `information`, `beta`, `printedFits`, `scoreGamma`, and `scoreFits`.
`fittedIPW R O θhat z` is H_{p(θhat(z))}(z), denoted F(z) below.

`LogisticConditions O θ₀ Θ θhat` means: Θ⊆R^k is compact; θ₀∈Θ; there exists
a real U bounding every |O_Nij| for every N,i,j; there exists c>0 such that
eventually in N, for every v∈R^k,

    c sum_j v_j² ≤ (sum_i (O_Ni·v)²)/N;

and for every N and every assignment z, θhat_N(z) belongs to Θ and maximizes
over θ∈Θ the log likelihood

    sum_i [z_i O_Ni·θ−log(1+exp(O_Ni·θ))].

Θ need not be convex, and θ₀ need not be interior unless separately specified.
`Overlap p` means there exists ε with 0<ε<1/2 such that for every N,i,
ε<p_Ni<1−ε. The information matrix is consequently eventually nonsingular
under the Gram lower bound (for positive-dimensional designs).

For sequences of random variables U_N on their finite assignment spaces:

* `InProb p U`: for every ε>0, P_pN(ε<|U_N|)→0 as N→∞.
* `LittleOp p U r`: U_N/r_N tends to zero in that sense.
* `BigOp p U r`: for every ε>0 there is C>0 such that eventually
  P_pN(C|r_N|<|U_N|)<ε.
* `Nondegenerate V`: there exists v>0 such that eventually v≤N V_N.
* `NormalLimit p U`: for every real x, P_pN(U_N≤x)→Φ(x), where Φ is the CDF
  of Mathlib's real Gaussian with mean zero and variance one.
* `LiminfAtLeast u a`: for every ε>0, eventually a−ε≤u_N.
* `Conservative coverage α`: the preceding property with a=1−α.

Here all limits are along the natural numbers' `atTop` filter. There is no bare
real `limsup` or `liminf` default involved. The normal quantile is
q(a)=inf{x:a≤Φ(x)}. Every normal-quantile use below is at a∈(1/2,1), where
this is an ordinary finite, positive quantile. Function vectors `Fin k → R`
carry the sup norm max_j |v_j|, not the Euclidean norm; the spatial
`EuclideanSpace R (Fin 2)` is R² with its Euclidean norm and Lebesgue area.

For observed propensities p̂ and observed z, define

    β̂_a = I(p̂,O)⁻¹ (sum_i 1{z_i=a} R_i(z) q̂_i(!a) O_i)/N,
    γ̂ = I(p̂,O)⁻¹ (sum_i [z_i R_i(z)(1−p̂_i)/p̂_i
                   +(1−z_i)R_i(z)p̂_i/(1−p̂_i)]O_i)/N.

`fittedScoreFits` uses δ̂_i=O_i·(β̂_true−β̂_false), L̂_i=O_i·γ̂ and exactly
the s_i formulas above with p̂ in place of p. Define the following estimators:

    rawSAH(p,R,B,g,z) = (sum_i b_i [z_i(R_i−g_i(true))²/p_i²
                           +(1−z_i)(R_i−g_i(false))²/(1−p_i)²])/N²,
    oracleHAC(p,R,B,g,z) = (sum_i sum_{j∈B_i} C_i(g,z)C_j(g,z))/N².

For distinct i,j, pairMarginal(X,i,j,a,b) is
E[1{z_i=a,z_j=b}X]/(q_i(a)q_j(b)). With sign(true)=1, sign(false)=−1,
`secondMomentBound` is

    M(g) = [sum_i {E[(R_i−g_i(true))² | z_i=true]/p_i
                   +E[(R_i−g_i(false))² | z_i=false]/(1−p_i)}
            +sum_i sum_{j∈B_i\{i}} sum_{a,b} sign(a)sign(b)
               E[(R_i−g_i(a))(R_j−g_j(b)) | z_i=a,z_j=b]]/N².

Write n_a=sum_i 1{z_i=a}, armMean_a=(sum_i 1{z_i=a}R_i(z))/n_a,
and Hajek=armMean_true−armMean_false. Empty-arm means are zero by totalized
division. Define

    ε_i = (n_true/N) z_i(R_i−g_i(true))/p̂_i
          +(n_false/N)(1−z_i)(R_i−g_i(false))/(1−p̂_i),
    printedSAH = (sum_i b_i [z_i ε_i²/p̂_i²
                              +(1−z_i)ε_i²/(1−p̂_i)²])/N²,
    sahLimit(p,R,B,g) = (sum_i b_i {
         E[(R_i−g_i(true))² | z_i=true]/p_i
         +E[(R_i−g_i(false))² | z_i=false]/(1−p_i)})/N².

For kernels K and residual numbers e_i, let λ_i=z_i/n_true−(1−z_i)/n_false and

    V_K(z,e) = sum_ij λ_i λ_j e_i e_j K_ij.

Let X have columns 1 and z; M=Id−X(XᵀX)⁻¹Xᵀ. Put

    A(z,K) = (n_true n_false/N) M [λ_i λ_j K_ij]_ij M,
    μ(z,K) = trace A(z,K),    ν(z,K)=2 trace(A(z,K)²).

The residual e_i used with Hajek is R_i(z)−armMean_{z_i}.
`uniformDistanceKernel D h` is 1{D_ij≤h}. Given N real values v_l and an N×N
real matrix U, `spectralKernel v U false` is sum_l v_l U_il U_jl, and its
`true` version replaces v_l by max(v_l,0). `cappedVariance(V,μ)` is
V/min(μ,1) when μ>0 and V otherwise.

The Student density used here is the explicit real function

    Γ((ν+1)/2)/(sqrt(νπ) Γ(ν/2)) * (1+x²/ν)^(-(ν+1)/2).

Its CDF is the real Bochner integral over (−∞,x], and its quantile t_ν(a) is
inf{x:a≤CDF_ν(x)}. In the statement that uses it ν>0 is expressly guarded;
the density then is the usual integrable Student density. `Real.sqrt` is the
nonnegative square root, with value zero on negative inputs. `Measure.map`
is pushforward, `restrict` is measure restriction, and `withDensity f` is
the measure with nonnegative extended-real density f.

Mathlib sources followed for the potentially material conventions include
Topology/MetricSpace/HausdorffDistance.lean (`infDist`),
LinearAlgebra/Matrix/NonsingularInverse.lean (matrix inverse),
MeasureTheory/Integral/Bochner/Basic.lean (integral and set-integral notation),
Probability/Distributions/Gaussian/Real.lean (`gaussianReal`),
Analysis/Normed/Group/Constructions.lean (Pi norm),
Analysis/SpecialFunctions/Pow/Real.lean (real powers), and
MeasureTheory/Measure/{Map,Restrict}.lean. Scalar real powers on the positive
bases occurring in a Student density agree with exp(exponent·log(base)).

## SAP.P004a.T1

There exists a sequence of estimators θhat_N(z)∈R² with the following properties.
The design row is (1,(i mod 3)−1), the truth is (0,log 2), and the parameter
set is [−2,2]². These objects satisfy LogisticConditions, the truth is in the
interior, and the following spatial realization satisfies SpatialLocalConditions:
node i is the singleton (10i,0), ζ is the sum of Dirac masses at the nodes,
Y(x,z) equals the node value at node locations and zero elsewhere, and
D(d)=[0,d]. The node value is 21/20 for i mod 3=1 and 1 otherwise, independently
of z. True p_i are logistic probabilities for the stated design/truth.
They satisfy Overlap. For every positive N the d=0 averages are WellDefined.
For every N, Q(p,R,{i},f)=0. The sequence Var(A_f) is Nondegenerate.
Nevertheless A_f−F is NOT o_p(N^−1/2). The existential estimator must be the
same estimator in LogisticConditions and this failed expansion.

Separately, for the three entered vectors
w=(2/9,1/4,2/9), a=(27/250,−24/125,27/250),
b=(−81/1000,16/125,−81/1000), it asserts
sum_t w_t a_t²/3=3/625,
sum_t w_t b_t²/3=1753/750000,
sum_t w_t(a_t−b_t)²/3=10369/750000>0.
There is no assertion identifying a or b with any estimator coefficient or
these weighted squares with any design variance.

## SAP.P004a.T2

For every family Space_N equipped separately with metric and measurable
structures, the asymptotic statement below and the finite statement below hold.
They are independent universally quantified conjuncts.

Asymptotic part: for every natural k, every population sequence P, design O,
truth θ₀, set Θ, estimator sequence θhat, and real d,h, assume d,h≥0,
SpatialLocalConditions P, eventual WellDefined at d, eventual LocalAt at the
specified h, LogisticConditions, interior truth, and Overlap of the true
logistic propensities. Set R_N=R_N(d), B_N=B_N(h), and V_N=Var(A_s).
Then, in this order:

1. F−[H_p−sum_i(z_i−p_i)L_i/N] is O_p(N^−1).
2. A_s−F is o_p(N^−1/2).
3. If V is Nondegenerate, (F−τ)/sqrt(V_N) has NormalLimit. For every real
   α with 0<α<1, the interval event
   |F−τ|≤q(1−α/2)sqrt(rawSAH(p̂,R,B,ŝ,z)) has Conservative coverage,
   where p̂=p(θhat(z)) and ŝ is fittedScoreFits. If additionally
   Q(p_N,R_N,B_N,f_N)≥0 for every N (not just eventually), then replacing
   rawSAH in that event by max(oracleHAC(p̂,R,B,ŝ,z),0) also has
   Conservative coverage.

Finite part: for all naturals N,k and all p,R,O,B, assume N>0, every p_i∈(0,1),
det I is a unit (equivalently det I≠0 over R), every i∈B_i, the neighborhoods
are symmetric, and j∉B_i implies i,j share no source of R. It asserts all of:

1. For every i, s_i(true)−s_i(false)=f_i(true)−f_i(false), and
   s_i(true)/p_i+s_i(false)/(1−p_i)=L_i.
2. For every assignment, A_s=H_p−sum_i(z_i−p_i)L_i/N.
3. For every i, E[C_i(s)]=τ_i−(f_i(true)−f_i(false)).
4. E[A_s]=τ.
5. Var(A_s)=M(s)−Q(p,R,B,s)/N.
6. E[oracleHAC(p,R,B,s)]=Var(A_s)+Q(p,R,B,f)/N.
7. Var(A_s)≤E[rawSAH(p,R,B,s)].

## SAP.P004a.T3

There exists one estimator sequence θhat_N(z)∈R² satisfying all the following.
Nodes with i mod 8<2 have row (1,0); other nodes have row (0,1). The truth is
(0,−log 9), Θ=[−log 19,log 19]², and LogisticConditions and interior truth hold.
Thus true propensities are 1/2 on the first group and 1/10 on the other group.
The table is z_i for i mod 8=0, −z_i for i mod 8=1, and zero otherwise. Its
spatial realization is the singleton, counting-measure line construction used
in T1. It satisfies SpatialLocalConditions, Q(p,R,{i},f)≥0 for every N,
Overlap, and WellDefined at d=0 for every positive N. Var(A_f) is Nondegenerate.
Eventually the actual variance Var(F) is strictly positive. Finally

    printedSAH(p̂,R,{i},ĝ,z)/Var(F) − 8/25 → 0 in probability,

where p̂=p(θhat(z)) and ĝ_i(a)=O_i·β̂_a. This ĝ uses fittedBeta, not
fittedScoreFits. The variance in the denominator is of the actual fitted-IPW
statistic using that same θhat, under the true assignment distribution.

## SAP.P004a.T4

First, universally quantify N,p̂,R,B,g,z, assume N>0, both n_true,n_false>0,
and every p̂_i∈(0,1). Then

    rawSAH = sum_i z_i b_i ε_i²/n_true²
             +sum_i(1−z_i)b_i ε_i²/n_false²,

and printedSAH equals

    (sum_i b_i [(n_true/N)² z_i(R_i−g_i(true))²/p̂_i⁴
             +(n_false/N)²(1−z_i)(R_i−g_i(false))²/(1−p̂_i)⁴])/N².

Second, independently quantify N,p,R,B,g, assume N>0, all p_i∈(0,1),
self-inclusive and symmetric B, and, for every i,j outside B_i,
Cov(C_i(g),C_j(g))=0. Then Var(sum_i C_i(g)/N)≤sahLimit(p,R,B,g), and
sahLimit(p,R,B,g)=E[rawSAH(p,R,B,g)]. No fitted-estimator limit is asserted.

## SAP.P004a.T5

This is a concrete conjunction without hypotheses. There are two unit closed-disk
node sets centered at (0,0) and (100,0), with Lebesgue area ζ. Within radius 6
of each center the outcome is the indicator that the angular fraction around
that center is less than 1/10 under control, or less than 1/50 in the inner
unit disk and 273/2500 outside it under treatment. Outside both radius-6
disks it is zero. The angular fraction is the complex argument, adjusted from
(−π,π] to [0,2π), divided by 2π (including Mathlib's value at the center).
The observed assignment is (true,false).

The band selector gives {0} at d=0, [0,5] at d=6, and (d−1,d] otherwise.
Thus the six regions indexed j=0,…,5 are the disk of radius 1 and the five
successive disjoint annuli out to radius 6. For every node i, their disjoint
union is its d=6 region and their areas are π(2j+1). All these regions are
WellDefined, and every outcome everywhere under every assignment is 0 or 1.
Both observed arms have one node.

For every j the entire assignment table equals the following finite average,
not only its value at the observed assignment. There are three mass atoms with
masses (2j+1) times (1/50,2/25,9/10) when j=0, and times
(1/10,23/2500,2227/2500) otherwise. At j=0, treatment is the indicator of atom
0, and control of atoms 0 or 1. At j>0, treatment is the indicator of atoms
0 or 1, and control of atom 0. Node i uses its own assignment z_i.

The sum over all six bins of observed Hajek estimates is −17/500; the sum
of their AMEs under p_i=1/2 is also −17/500. The whole-region AME is
121/18000, which is positive and unequal to −17/500.

## SAP.P004a.T6

For every measurable space A (at the theorem's arbitrary universe), naturals
N,m, measure ζ, sets B_ik⊆A, outcome Y(x,z), and propensities p, assume
N,m>0; every B_ik is measurable; for each i the B_ik are pairwise disjoint;
each has strictly positive finite mass; Y(·,z) is integrable on every B_ik
for every i,k,z; and every p_i∈(0,1). Set a_ik=ζ(B_ik).toReal,
R_ki(z)=integral_{B_ik}Y/a_ik, and W_i(z) equal to the corresponding average
over the union of that node's bins. It asserts:

1. For every i,z, W_i(z)=sum_k a_ik R_ki(z)/sum_k a_ik.
2. For every i and arm a, μ_i^W(a)=sum_k a_ik μ_i^{R_k}(a)/sum_k a_ik.
3. For every i, τ_i^W=sum_k a_ik τ_i^{R_k}/sum_k a_ik.
4. τ^W=(sum_i [sum_k a_ik τ_i^{R_k}/sum_k a_ik])/N.
5. For every i and real lo,hi, if each bin's node-i effect is in [lo,hi],
   then the union's node-i effect is in [lo,hi].
6. For every i,c, if a_ik=c for every k, the union's node-i effect is
   sum_k τ_i^{R_k}/m.

Independently, for every positive real c and all real s,t,
|cs|≥|ct| iff |s|≥|t|. Independently, for every N, arbitrary real assignment
weights w (no normalization/nonnegativity assumption), statistic T, observed
assignment obs, and c>0, the weighted sum of indicators
1{|cT(z)|≥|cT(obs)|} equals the analogous sum without c. This includes exact
randomization p-value invariance whenever w are a probability distribution.

## SAP.P004a.T7

Let a five-node star kernel K have entries 1 on the diagonal and whenever
either index is 0, and 0 otherwise; let v=(2,−1,−1,−1,−1) and Q=K+vvᵀ/8.
For m blocks, K_m,Q_m are their block-diagonal repetitions and the outcome
table is the assignment-independent repetition of (0,1,1,−1,−1).

The finite conjunction specifies the assignment on twenty nodes, in four blocks:
(T,T,F,T,F), (F,T,F,T,F), (T,T,F,T,F), (F,T,F,T,F).
It asserts n_true=n_false=10, both observed arm means are zero,
V_{K_4}=V_{Q_4}=4/25 for the observed residuals,
μ(K_4)=41/50, μ(Q_4)=101/100, and
V_{Q_4}/μ(Q_4)=16/101<8/41=V_{K_4}/μ(K_4).

The spatial sequence places each block's center at (10b,0) and its leaves
at offsets (1,0),(0,1),(−1,0),(0,−1), truncating the final block at arbitrary
N. Nodes are singletons, ζ counts the node points, outcomes are the indicated
constant values at those points and zero elsewhere, and D(d)=[0,d]. It
asserts SpatialLocalConditions, WellDefined at d=0 for every positive N,
Q(p,R,B(6/5),g)=0 for every N under p_i=1/2 and
g_i(a)=barμ(a)=sum_i μ_i(a)/N, and Nondegenerate variance of A_g (called
linearHajek). The 6/5 cutoff distance kernel at N=5m equals K_m for every m;
LocalAt at 6/5 holds for every N. For each m>0,
(5m)Var(linearHajek)=16/5.

Finally set C=2Φ(q(39/40)sqrt(15/16))−1. For every ε>0, eventually in m,
the probability, under independent fair assignments on 5m nodes, of the event

    n_true>0 AND n_false>0 AND μ(z,Q_m)>0 AND ν(z,Q_m)>0 AND
    |Hajek(z)| ≤ t_{2μ²/ν}(39/40) sqrt(V_{Q_m}(z,e)/μ)

is strictly less than C+ε. It also asserts C<19/20. This is an upper bound
on an unconditional probability of a conjunction, not a conditional probability
and not a limiting-coverage equality.

## SAP.P004a.T8

The theorem is the conjunction of the following two universal statements, the
second for every metric/measurable family Space_N.

Finite: for every N, real eigenvalue list and real N×N matrix U with UᵀU=Id,
every assignment z with both arms nonempty, every residual vector e, and every
real critical,c,err with 0≤critical≤c, let K=U diag(values) Uᵀ,
Q=U diag(max(values,0)) Uᵀ, and V=cappedVariance(V_Q,μ(z,Q)). Then
V_Q≤V and max(V_K,0)≤V_Q. Further, if V_K≥0 and
|err|≤critical sqrt(V_K), then |err|≤c sqrt(V).

Asymptotic: for every population sequence P and real p,d,h,α, assume
0<p<1, d,h≥0, 0<α<1, SpatialLocalConditions, eventual WellDefined at d,
eventual LocalAt at h, and Nondegenerate variance of linearHajek under
constant assignment probability p. Also supply, for each N, values_N,U_N
with U_NᵀU_N=Id whose untrimmed spectral kernel is exactly the node-distance
cutoff kernel at h. Assume eventually Q(p,R,B(h),g)≥0 with g_i(a)=barμ(a).
For every critical-value array c_N(z) satisfying q(1−α/2)≤c_N(z) for all N,z,
the probability of

    n_true>0 IMPLIES (n_false>0 IMPLIES
       |Hajek−τ| ≤ c_N(z) sqrt(cappedVariance(V_Q(z,e),μ(z,Q))))

has Conservative coverage. Empty-arm draws satisfy this event. The statement
does not define c as a Student quantile and does not assert conditional coverage.

## SAP.P004a.T9

Use the intercept-only design O_i=1, θ₀=0, Θ=[0,1]. For q_z=n_true/N,
define θhat(z)=0 if q_z≤1/2, 1 if q_z≥ℓ(1) (after the first branch), and
log(q_z/(1−q_z)) otherwise. The conjunction asserts LogisticConditions
for this specific estimator at all N, including N=0. For every N>0,
under fair independent assignments,

    P( sqrt(N) |θhat−4(q_z−1/2)| > 1 ) ≥ 3/32.

It also explicitly asserts θhat−4(q_z−1/2) is not o_p(N^−1/2).

## SAP.P004a.T10

For every natural k, design sequence O, truth θ₀, parameter set Θ, and estimator
sequence θhat, assume LogisticConditions and Overlap for p_i=ℓ(O_i·θ₀).
Then ||θhat−θ₀||→0 in probability and is O_p(N^−1/2). If in addition
θ₀∈interior Θ, then, with score S_Nj=sum_i(z_i−p_i)O_ij/N,

    ||θhat−θ₀−I_N⁻¹ S_N|| = O_p(N^−1)

and the same norm is o_p(N^−1/2). The norm is the finite coordinate sup norm.
The interior hypothesis applies only to the remainder assertions.

## SAP.P004a.T11

For every N,p,R, assume N>0 and each p_i∈(0,1). The corrected H_p satisfies
E[H_p]=τ. For H_print(z)=sum_i[(z_i−(1−z_i))R_i(z)/p_i]/N,

    E[H_print] = sum_i [μ_i(true)−(1−p_i)μ_i(false)/p_i]/N,
    E[H_print]=τ iff sum_i (1−2p_i)μ_i(false)/p_i/N=0.

Independently, for every N>0, the table identically equal to 1 with p_i=1/4
has τ=0, E[H_print]=−2, and E[H_p]=0.

## SAP.P004a.T12

Eight singleton nodes lie at (3(i+1),0), ζ counts those points, the outcome
at node i is 2^i/128 independently of assignment and is zero off the nodes,
and D(d)=[0,d]. This population satisfies the pointwise sharp null
Y(x,z)=Y(x,all-false) for every x,z and is WellDefined at d=0.
Under p_i=1/2, the all-false assignment has H_p=−255/512; the assignment
with nodes 0,…,6 true and node 7 false has H_p=−1/512.

For draws indexed 0,…,100, use the first assignment at index 0 and the second
at all other indices. The product probability of this exact iid draw array
is 256^(−101)>0. The proportion of the 100 resampled absolute statistics
at least the SIGNED observed statistic is 1. The count of absolute resampled
statistics at least the ABSOLUTE observed statistic is 0, so its plus-one
p-value is 1/101.

Independently, for the same population and statistic, sum the probabilities of
all iid 101-draw arrays for which the absolute exceedance count /100≤1/20.
This rejection probability equals

    [sum_{m=0}^{127} sum_{b=0}^{5}
       choose(100,b)(m+1)^b (128−(m+1))^(100−b)] / 128^101,

and that number is strictly greater than 1/20. The subtractions in this
natural-number numerator never truncate to an unintended value on these ranges.

## SAP.P004a.T13

For every N,P, any weights w(z)≥0 with sum_z w(z)=1, any real statistic T,
P>0, and every α∈(0,1), draw P+1 assignments independently with law w.
Let b count indices r≠0 for which |T(draw_r)|≥|T(draw_0)| and
p_plus=(1+b)/(P+1). Then

    P(p_plus≤α) ≤ α,
    P(b/P≤α) ≤ (floor(αP)+1)/(P+1)
               ≤ α+(1−α)/(P+1).

Independently, for every N,P,T and every draw array with P>0,

    p_plus−b/P = (1−b/P)/(P+1),
    0 ≤ p_plus−b/P ≤ 1/(P+1).

The last separate assertion is (floor((1/20)100)+1)/(100+1)>1/20.
All probability assertions are explicitly finite product sums, so iid sampling
is part of the proposition rather than an informal sampling assumption.

## SAP.P004a.T14

Two singleton nodes are at (0,0),(3,0), and ζ counts the three atoms
(0,4),(3,4),(3,−4). The outcome is 1−z_1 at the first atom and 1+z_0
at the other two, and 1 off the atoms. Four populations share these data,
with band selector constant in d and equal to {4}, {5}, [4,5], or [0,5].
All four are WellDefined at input d=0. For every point and assignment the
absolute outcome is strictly less than 3. With independent fair assignments,
the AMEs for bands {4} and {5} are zero, and those for [4,5] and [0,5]
are each 1/6. For every pair of real numbers w4,w5 (without restrictions),
w4 times the {4} AME plus w5 times the {5} AME is unequal to the [4,5] AME.

## SAP.P004a.T15

Three independently universally quantified assertions are conjoined.

General integral assertion: for every N, metric/measurable space A, spatial
population P, p, and real d, assume N>0, all p_i∈(0,1), and WellDefined P d.
Let Δ_i(x)=E[Y(x,z)|z_i=true]−E[Y(x,z)|z_i=false]. For every node i,
τ_i(circleAverage)=integral_{E_i(d)}Δ_i(x)dζ/ζ(E_i(d)).toReal, and the
AME is the node average of these same normalized integrals.

Finite shell assertion: for every finite type A, naturals m,N, mass functions
a_i(x), shell labels s_i(x)∈{0,…,m−1}, and arbitrary real functions Δ_i(x),
assume N>0, a_i(x)≥0 for every i,x, and total mass A_i=sum_x a_i(x)>0 for
every i. Put A_ik=sum_{x:s_i(x)=k} a_i(x). For every node i,

    sum_x a_i(x)Δ_i(x)/A_i
      = sum_{k:A_ik>0} (A_ik/A_i)
          [sum_{x:s_i(x)=k} a_i(x)Δ_i(x)/A_ik].

It also asserts the identity obtained by averaging these two expressions over
i. Further, for every weight vector w_k with every w_k>0, if
A_ik/A_i=w_k for all i,k, this node average equals
sum_k w_k [sum_i (sum_{x:s_i(x)=k}a_i(x)Δ_i(x)/A_ik)/N].
No zero-mass shell enters the first two sums; in the last assertion positivity
of w and the weight equality ensure every shell denominator is positive.

Euclidean radial assertion: for every center c∈R² and real a,b with 0≤a<b,
push forward Lebesgue area restricted to {x:a≤dist(x,c)≤b} under x↦dist(x,c),
then multiply the measure by 1/[π(b²−a²)]. The resulting measure on R is
Lebesgue measure with density 2r/(b²−a²) for a≤r≤b and zero elsewhere.
The Lean density and scalar are embedded by ENNReal.ofReal; their stated
parameter constraints make them the usual nonnegative quantities.
