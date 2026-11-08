# Blind reading of the Lean statements

This file was written using only `SAP/P026b/Defs.lean`, its six parts,
`SAP/P026b/Challenge.lean`, its part, and the relevant Mathlib definitions.
Neither `claims.json` nor `record.json` had been opened when this was saved.
The Challenge proofs are `sorry`; no proof is being treated as evidence.

## Expanded vocabulary and conventions

All sums below are finite sums over the indicated finite type, including all
zero-weight sample points. `Fin n` means the integers 0 through n-1. An
off-diagonal double sum is over **ordered** pairs i != j. Numeric data are
rational unless explicitly stated to be real. Natural numbers in real or
rational denominators are cast to that field.

A `Design Ω I R` is just a weight function q:Ω→R and a binary assignment
T:Ω×I→{0,1}. It has no axioms by itself. `probabilityDesign` asserts q≥0
pointwise and sum(q)=1. Write

* E[h] = sum_w q(w) h(w);
* A_ai(w) = 1{T_i(w)=a}; p_ai=E[A_ai];
* p_abij=E[A_ai A_bj];
* positive marginals: p_1i>0 and p_0i>0 for every i;
* Y_i(w)=x_i if T_i(w)=1, and z_i otherwise;
* Tot(y)=sum_i y_i; Δ_N(x,z)=(Tot(x)-Tot(z))/N;
* H_a(y;w)=sum_i A_ai(w)y_i/p_ai;
* H_N(x,z;w)=(H_1(x;w)-H_0(z;w))/N;
* G_a(y,f;w)=sum_i[A_ai(w)(y_i-f_i(w))/p_ai+f_i(w)];
* G_N(x,z,f;w)=(G_1(x,f;w)-G_0(z,f;w))/N;
* C(h,k)=E[hk]-E[h]E[k], V(h)=C(h,h);
* d_ij=Pr(T_i != T_j)=E[1{T_i != T_j}];
* cross support: p_10ij>0 for every ordered i != j;
* R_N(x,z,f;w)=[sum_i A_1i(Y_i-f_i)/p_1i
  -sum_i A_0i(Y_i-f_i)/p_0i]/N.

These are finite weighted sums, not measure-theoretic expectations or
integrals. No integrability issue arises. Division is Mathlib field division
(in particular a/0=0); any protection against it must come from the particular
statement's hypotheses. Natural subtraction is truncated subtraction.

For later variance formulas define

    B_a(y) = sum_i p_ai(1-p_ai)(y_i/p_ai)^2
           + sum_(i != j) (p_aaij-p_ai p_aj)(y_i/p_ai)(y_j/p_aj),

    S(x,z) = sum_(i,j: p_10ij != 0)
                 (p_10ij-p_1i p_0j)(x_i/p_1i)(z_j/p_0j)
             - sum_(i,j: p_10ij = 0) x_i z_j,

    K(x,z) = sum_(i != j)
                 (p_10ij-p_1i p_0j)(x_i/p_1i)(z_j/p_0j)
             - sum_i x_i z_i.

The sums in S include diagonal pairs; the first sum in K includes every
off-diagonal pair, even when its joint probability is zero.

The particular variance estimator `printedVariance`, denoted W_N(x,z;w), is
defined by epsilon(p)=1 if p=0 and 0 otherwise, and

    Q_abij(w) = A_ai A_bj/(p_abij+epsilon(p_abij))
                * (p_abij-p_ai p_bj) * (Y_i/p_ai) * (Y_j/p_bj),

    N^2 W_N = sum_i [A_1i(Y_i/p_1i)^2+A_0i(Y_i/p_0i)^2]
            + sum_(i != j) [Q_11ij+Q_00ij-2 Q_10ij]
            + sum_(i != j: p_11ij=0)
                [A_1i Y_i^2/(2p_1i)+A_1j Y_j^2/(2p_1j)]
            + sum_(i != j: p_00ij=0)
                [A_0i Y_i^2/(2p_0i)+A_0j Y_j^2/(2p_0j)].

In particular this definition has no analogous correction for a zero directed
cross-arm joint. The regularized pair denominator is 1 when its joint is zero.

A `UnitExperiment I` means a real probability law on the **entire** finite
set Ω={0,1}^I: all q≥0, sum q=1, all treatment and control marginals positive.
Assignments with q=0 are allowed. Its design uses T_i(w)=w_i. In each universal
unit-experiment clause below, the quantifier prefix is: for every finite type
I with decidable equality and at least one member, then every such E, then the
listed real vectors/functions/parameters in the written order. N is |I|,
not an independently supplied population size. Prediction f may depend on
the whole assignment; no independence is implicit.

A `ClusterExperiment U C` supplies finite unit and cluster types, a surjection
c:U→C, and a UnitExperiment on C. Its cluster design has assignment w_c and
its unit design has assignment w_(c(i)), with the same weights. A cluster total
is Tot_c(y)=sum_(i:c(i)=c) y_i. Surjectivity requires each cluster to have a
unit; the structure by itself does not assert either type is nonempty. The
universal cluster clauses actually used below do assert nonempty units (and
either nonempty C explicitly or M>m>0).

`independent(D,F,G)` is the assertion, for every real-valued function u on
the codomain of F and then every real-valued v on the codomain of G,
E[u(F)v(G)]=E[u(F)]E[v(G)]. It is not a joint-independence condition on a
family of inputs.

`designWithIntercept K X` has first column constantly 1 and the K columns
of X after it. `Matrix.mulVec` is the usual row dot product. `olsFitted`
projects the response vector orthogonally onto the column space in the
standard finite-dimensional Euclidean inner product. Mathlib's
`EuclideanSpace.equiv` only changes the representation to/from coordinate
functions; `Submodule.starProjection` is ordinary orthogonal projection.
This specifies unique fitted responses even if coefficients are not unique.
`IsLeastSquaresFitted(V,y,z)` means (there exists β with Vβ=z) and
(for every β, sum_i(y_i-z_i)^2 ≤ sum_i(y_i-(Vβ)_i)^2).

## Fixed finite populations

The three-unit example has Ω=I={0,1,2}, uniform weight 1/3 and T_i(w)=1{w=i}.
Its x_i=1, z_i=0, covariate i, and fitted rows f(w,·) are

    (5/6, 1/3, -1/6), (1/3, 1/3, 1/3), (-1/6, 1/3, 5/6).

The asymmetric two-unit design has three equally likely assignments
(0,0),(0,1),(1,1). Its single-unit version retains only coordinate 0, so
that unit is treated only at sample point 2. The unequal-cluster design has
four units, three equally likely choices of treated cluster, and cluster
labels (0,1,2,2).

The XOR design has four equally likely assignments
(0,0,0),(0,1,1),(1,0,1),(1,1,0). Its fitting set is {1,2}; observed outcomes
there, with x=1,z=0, equal T_1,T_2. The supplied deterministic fitting rule
is g(u,v)=u+v-2uv.

The table population has 16 units and ten cluster labels

    c = (0,0,1,1,2,3,4,4,4,5,5,6,6,7,8,9),
    y = (1,1,1,1,1,0,1,1,0,1,1,1,1,0,0,0),
    X = (4,0,4,1,4,2,4,1,2,5,4,1,4,2,2,3).

Units 0–5 form one stratum and 6–15 the other. The sample space is the 90
equiprobable pairs of subsets choosing two of clusters 0–3 and two of
clusters 4–9, independently. `tableDesign` treats clusters as its ten units;
`tableUnitDesign` lifts the same treatment to the 16 units. Potential
outcomes in the table logit estimator coincide with y.

The fixed, ten-cluster linear residual vector is

    l = (1,7/8,1/4,-1/2,-15/31,19/93,1/3,-76/93,-76/93,-79/93).

For the FE statistic, center X by 5/2 in the first stratum and 14/5 in the
second, center y by 5/6 and 3/5 respectively, and center the realized unit
treatment indicators by their realized stratum means (divisors 6 and 10).
Let these centered vectors be Xc,yc,Tc. Set

    e_i(w)=Tc_i(w)-[sum_j Xc_j Tc_j(w)/sum_j Xc_j^2]Xc_i,
    F(w)=sum_i e_i(w)yc_i / sum_i e_i(w)^2.

All of this FE construction is rational and uses the 16 unit rows.

For logistic fits s(t)=1-1/(1+exp(t)), the ordinary logistic function for
finite real t. L_b(α,β) is the binomial log likelihood
sum[y_i log s(α+βX_i)+(1-y_i)log(1-s(α+βX_i))], over units 6–15 if b=true
and units 0–5 if b=false. Both logarithm arguments lie strictly between 0
and 1 for finite coefficients, so Mathlib's extension log(0)=0 and log of
negative numbers is not used. A maximizer means a **finite real pair** with
L_b(γ)≤L_b(β) for every real pair γ. `logitCoefficients b` selects an
arbitrary maximizer if one exists, otherwise (0,0). Existence and uniqueness
are later conclusions, not assumptions.

Precisely as written, `tableLogitPrediction i` uses coefficients for
b=decide(i<6): **the fit on units 6–15 predicts units 0–5, and the fit on
units 0–5 predicts units 6–15**. Thus the fitting-stratum selector and
prediction-stratum selector are opposite. Denote this prediction by h_i,
its cluster residual totals by r_c=sum_(i:c(i)=c)(y_i-h_i), and let
L(w)=H_16(r,r;w), W(w)=W_16(r,r;w), under the real table design.

For real x, `roundsTo(x,t)` means t-0.0005≤x<t+0.0005. `rounded3` is the
same rational condition. `roundedSD3(v,t)` means
(t-0.0005)^2≤v<(t+0.0005)^2; at the positive centers used here this tests
the rounded nonnegative standard deviation. `Real.sqrt` is the nonnegative
square root (zero on negative inputs); all its variance and mean-square
arguments here are nonnegative for probability designs.

## SAP.P026b.T13

For every nonempty finite I, UnitExperiment E, then y1,y0:I→R, then arbitrary
f:{0,1}^I→I→R, the following conjunction holds:

1. For every a in {0,1}, E[G_a(y_a,f)]=Tot(y_a)-sum_i C(A_ai,f_i/p_ai),
   with y_1=y1,y_0=y0.
2. E[G_N(y1,y0,f)]-Δ_N(y1,y0)
   =[sum_i C(A_0i,f_i/p_0i)-sum_i C(A_1i,f_i/p_1i)]/N.

There are no extra covariance or independence hypotheses.

## SAP.P026b.T14

This is an unconditional conjunction of assertions about the fixed real table
population and its logistic definitions above:

1. There exists exactly one finite maximizer of each L_false and L_true.
2. Each coefficient is within 0.0000005, inclusively, of these centers:
   true intercept -1.1201076, true slope 0.5657586;
   false intercept 1.0843223, false slope 0.2280259.
3. E[L]=0; 0.247090≤sqrt(V(L))≤0.247093;
   0.0605≤V(L)<0.0615; E[W]=V(L);
   0.0125≤sqrt(V(W))<0.0135.
4. For every real a, then every real b, both implications hold:
   (a≥0 → a+4b≥0 → a+2b≤0 → a=b=0) and
   (a+b≥0 → a+4b≥0 → a+2b≤0 → a=b=0).
5. Let Δ=Δ_16(y,y)=0, μ=E[L], v=V(L), e=E[W]. For every j=0,…,9,
   the jth entry of
   (Δ,μ,μ-Δ,sqrt(v),sqrt(E[(L-Δ)^2]),v,e,e-v,
   sqrt(V(W)),sqrt(E[(W-v)^2]))
   rounds to the jth entry of
   (0,0,0,.247,.247,.061,.061,0,.013,.013).
6. For every j in {3,4,5,6,8,9}, the same entry does not round to the jth
   entry of (0,0,0,.170,.170,.029,.029,0,.007,.007).

There are no external numerical hypotheses. The coefficient, likelihood,
support, and moment assertions are all conclusions.

## SAP.P026b.T15

An unconditional conjunction about the rational three-unit example:

1. The design is normalized and nonnegative with positive marginals;
   for every i, p_1i=1/3 and p_0i=2/3.
2. For every w and then i, f(w,i) is the displayed matrix entry.
3. For every w, the displayed fitted vector, cast to reals, is in the column
   space of the real design with rows (1,i), minimizes the real residual
   sum of squares over every coefficient pair, and every other fitted
   vector with those properties equals it.
4. For every w, G_3(1,0,f;w)=(1/4,1,1/4)_w.
5. For every i, C(A_1i,f_i)=(1/6,0,1/6)_i.
6. E[G_3]=1/2, Δ_3(1,0)=1, E[G_3]-Δ_3=-1/2,
   and -(1/3)(3+3/2)(1/6+0+1/6)=-1/2.
7. For every w, H_3(1,0;w)=1, and 1/2 != 1.

## SAP.P026b.T16

The conjunction of these five independently quantified clauses:

1. For every nonempty finite I, E, then fixed real y1,y0,g, for every
   assignment w, G_N(y1,y0,g;w)=R_N(y1,y0,g;w), and
   E[G_N(y1,y0,g)]=Δ_N(y1,y0).
2. For every nonempty finite I, E, then natural K (possibly zero), matrix
   X:I×Fin K→R, then y1,y0, form V=[1 X] and let f(w) be the orthogonal
   OLS projection of Y(w) on its column space. For every assignment w,
   f(w) is a least-squares fitted response and G_N=R_N. Moreover
   E[G_N]-Δ_N=-sum_i[C(A_1i,f_i)(1/p_1i+1/p_0i)]/N.
   No full-column-rank assumption is imposed.
3. For every nonempty finite I, E, y1,y0, then arbitrary f, if for every i
   C(A_1i,f_i)=0, then E[G_N]=Δ_N.
4. For every nonempty finite I, E, then x:I→R and arbitrary deterministic
   G:(I→R)→(I→R), with both potential outcomes equal x and
   f(w)=G(Y(w)), E[G_N(x,x,f)]=Δ_N(x,x)=0.
5. All of T15, including its OLS property and numerical bias example.

## SAP.P026b.T17

The conjunction of:

1. It is **not** true that for every real design on three sample points
   and two units, nonnegative normalized weights, positive marginals,
   and d_ij>0 for every i != j imply that for every real outcome vector x
   and then z, both cross support and V(H_2(x,z))≤E[W_2(x,z)] hold.
   Negation of this conjunction need only falsify one of its two conclusions.
2. The specified asymmetric design (0,0),(0,1),(1,1) is a probability
   design with positive marginals. For every distinct i,j it has d_ij>0,
   p_11ij>0, and p_00ij>0.
3. For this design and constant outcomes x=z=1,
   E[W_2(1,1)] != V(G_2(1,1,0)).

The final comparison is inequality of expectation and variance, not itself
a one-sided nonconservativeness assertion. No universal positive claim is
made about designs outside this example.

## SAP.P026b.T18

An unconditional assertion that the fixed real XOR design is a probability
design with positive marginals, that for every j∈{1,2} the random variables
T_0 and T_j are independent in the all-test-functions sense defined above,
and that C(A_10,g(Y_1,Y_2)) != 0 for x=1,z=0 and g(u,v)=u+v-2uv.
It asserts pairwise independence with the focal assignment, not independence
of that assignment from the vector (T_1,T_2).

## SAP.P026b.T19

An unconditional conjunction about the fixed table:

1. For every one of its 90 assignments, sum_i e_i(w)^2>0.
2. Each of the two real logistic likelihoods has exactly one finite maximizer.
3. The following collection of moment assertions does not all hold:
   uniqueness of those same maximizers; E[F] rounds to -.012;
   V(F) rounds to .036; sqrt(V(F)) rounds to .191;
   sqrt(V(F)+E[F]^2) rounds to .191;
   sqrt(V(H_16(l,l))) rounds to .162;
   V(H_16(l,l)) and E[W_16(l,l)] each round to .026;
   sqrt(V(W_16(l,l))) rounds to .007;
   and, for the logit residual r as actually defined above,
   |sqrt(V(L))-.170|≤.0005, |V(L)-.029|≤.0005,
   |E[W]-.029|≤.0005, |sqrt(V(W))-.007|≤.0005.
   FE and Linear rounding uses the half-open rational predicates;
   Logit uses the displayed closed error bounds.

This only negates the combined collection; it does not formally identify
which individual FE, Linear, or Logit assertion fails.

## SAP.P026b.T20

For every nonempty finite I, E, then real y1,y0:

1. For every a and then every assignment w,
   H_a(y_a;w)=sum_i A_ai(w)Y_i(w)/p_ai.
2. E[H_1(y1)]=Tot(y1), E[H_0(y0)]=Tot(y0), and
   E[H_N(y1,y0)]=Δ_N(y1,y0).

## SAP.P026b.T21

The conjunction of three blocks:

1. For every finite Ω and finite I with decidable equality, every real design
   D, if its weights are nonnegative and normalized, then for every natural
   n, if 0<n<|I|, all unit marginals equal n/|I| for treatment and
   (|I|-n)/|I| for control, and for every w with q(w)>0 exactly n units are
   treated, then for every x and then z:
   for every w with q(w)>0,
   H_|I|(x,z;w)=sum_i A_1iY_i/n-sum_i A_0iY_i/(|I|-n),
   and the expectation of this fixed-denominator contrast equals Δ_|I|.
   There is no assumption that all n-subsets are equally likely.
2. For every nonempty finite U with decidable equality, then naturals M,m
   satisfying 0<m<M, then ClusterExperiment E:U→Fin M, if every cluster
   has marginals m/M and (M-m)/M and every positive-weight assignment
   treats exactly m clusters, then for every x and then z:
   for **every** cluster assignment w, even weight-zero assignments,
   H_|U| under the unit design equals
   (M/|U|)[sum_c A_1c Ytotal_c/m-sum_c A_0c Ytotal_c/(M-m)],
   and its expectation is Δ_|U|(x,z).
   Here Ytotal_c is the observed cluster total (the masked total of x or z).
3. The rational unequal-cluster design (cluster labels 0,1,2,2) is a
   probability design with positive marginals 1/3 and 2/3; for every w both
   realized arm counts are positive. For x=z=(1,1,0,0), the expectation of
   the contrast of observed **unit** arm means is 1/9, the expectation of
   H_4 is 0, Δ_4=0, and 1/9 != 0.

Thus the natural subtractions in the first two blocks are positive, not
truncated to zero. Exact treated count in block 2 is an explicit antecedent.

## SAP.P026b.T22

For every nonempty finite I, E, then real y1,y0 and arbitrary f:

1. If every C(A_1i,f_i)=0, then E[G_1(y1,f)]=Tot(y1),
   E[G_0(y0,f)]=Tot(y0), and E[G_N]=Δ_N.
2. For every deterministic vector g:I→R, every C(A_1i,g_i)=0, and the same
   two total identities and ATE identity hold with f(w)=g.
3. For every assignment w,
   G_N(y1,y0,f;w)=H_N(y1,y0;w)-[H_1(f(w);w)-H_0(f(w);w)]/N.

## SAP.P026b.T23

First, for every nonempty finite I, E, then x,z, arbitrary f, real b0, real
b1, and assignment w, let B(w)=sum_i A_1i/p_1i-sum_i A_0i/p_0i. Then all
three assertions hold:

1. H_N(b0+b1x,b0+b1z;w)=(b0/N)B(w)+b1 H_N(x,z;w).
2. H_N(b0+b1x,b0+b1z;w)=b1 H_N(x,z;w) if and only if
   b0=0 or sum_i A_1i/p_1i=sum_i A_0i/p_0i.
3. G_N(b0+b1x,b0+b1z,b0+b1f;w)=b1 G_N(x,z,f;w).

Second, the fixed single-unit asymmetric design is a probability design with
positive marginals, q(2)>0, H_1(1,1;2)=3, (-1)H_1(0,0;2)=0, and these
last two quantities are unequal. No negative-slope, nonzero-slope, or
positive-weight hypothesis is imposed on the universally quantified block.

## SAP.P026b.T24

The conjunction of two independently quantified blocks:

1. For every nonempty finite I, E, then x,z and arbitrary f, for every
   assignment w, G_N(x,z,f;w)=H_N(x-f(w),z-f(w);w)=R_N(x,z,f;w).
   Also for every fixed real r:I→R,
   V(G_N(x,z,r))=[B_1(x-r)+B_0(z-r)-2S(x-r,z-r)]/N^2.
   The variance formula is for deterministic r, not the arbitrary random f.
2. For every nonempty finite U and nonempty finite C, each with decidable
   equality, then every ClusterExperiment E, if d_cd>0 for every c != d,
   then for every x and then z, with cluster totals X_c=Tot_c(x), Z_c=Tot_c(z):
   for every a, V(H_a(X if a=1 else Z))=B_a(X if a=1 else Z);
   and C(H_1(X),H_0(Z)) equals each of
   sum_(c,d)(p_10cd-p_1c p_0d)(X_c/p_1c)(Z_d/p_0d), S(X,Z), and K(X,Z).

The second block has pairwise positive disagreement as an explicit antecedent;
it does not assume positive directed cross joints. Its off-diagonal K sum
does not omit cross pairs with zero probability.

## Mathlib source tracing

The only analytic constructions beyond finite algebra are ordinary finite
Euclidean orthogonal projection, exponential, logarithm, and real square root.
The relevant Mathlib definitions were checked in
`Analysis/InnerProductSpace/PiL2.lean` (EuclideanSpace and its coordinate
equivalence), `Analysis/InnerProductSpace/Projection/Basic.lean`
(`starProjection`), `Data/Matrix/Mul.lean` (`mulVec`), and
`Analysis/SpecialFunctions/Log/Basic.lean` (`Real.log`). Finite subtype sums,
Boolean tests, finite matrices, field arithmetic, and real casts have their
usual Mathlib meanings described above. No SAP definition hides a limit,
an infinite sum, a measure, a claimed theorem, or a proof hypothesis.
