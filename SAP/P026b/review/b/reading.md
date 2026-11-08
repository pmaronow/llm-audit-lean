# Blind reading of the Lean statements

This file was written after reading only `SAP/P026b/Defs.lean`, all six
`Defs/Part*.lean` files, the Challenge files, and relevant Mathlib definitions.
Neither `claims.json` nor `record.json` had been opened. The Challenge contains
12 theorem stubs, T13 through T24. Their `by sorry` bodies provide no evidence
of truth; this reading concerns their types.

## Common objects and exact conventions

`Design Ω I R` consists of arbitrary functions `weight : Ω → R` and
`treatment : Ω → I → Bool`. Alone it imposes no probability conditions. Here
Ω and I are finite, and R is an ordered field, instantiated as Q or R.
Write w for an allocation, T_i(w) for its Boolean treatment, and
A_ai(w) = 1{T_i(w)=a}. Every expectation below is the finite weighted sum
E h = sum_w weight(w) h(w). `probabilityDesign` means every weight is
nonnegative and their sum is one. `positiveMarginals` means p_1i>0 and
p_0i>0 for every i, where p_ai=E A_ai. The ordered pair probability is
q_abij=E[A_ai A_bj]. `disagreement i j` is P(T_i != T_j), whereas
`crossSupport` requires q_10ij>0 for every ordered pair i != j. These are
different conditions. Cov(h,k)=E(hk)-(Eh)(Ek), and Var(h)=Cov(h,h).

Potential outcomes y1,y0 are fixed functions on I. The observed response is
Y_i(w)=y1_i if T_i(w)=true, and y0_i otherwise. Put total(y)=sum_i y_i,
tau_N=(total(y1)-total(y0))/N,
H_a(y;w)=sum_i A_ai(w)y_i/p_ai, and
H_N(y1,y0;w)=(H_1(y1;w)-H_0(y0;w))/N. The supplied integer N need
not equal |I| in the general definitions; each theorem's use is given below.

For a possibly allocation-dependent prediction f_i(w), define
G_a(y,f;w)=sum_i[A_ai y_i/p_ai-A_ai f_i(w)/p_ai+f_i(w)] and
G_N(y1,y0,f;w)=(G_1(y1,f;w)-G_0(y0,f;w))/N.
`residualContrast` is
[sum_i A_1i(Y_i-f_i)/p_1i - sum_i A_0i(Y_i-f_i)/p_0i]/N.
`observedArmSum a x z` is sum_i A_ai times the observed response from x,z.
`differenceInMeans` divides these two observed sums by their respective
realized numbers of units, and subtracts control from treatment.

All `offSum` sums run over ordered pairs i != j. `zeroSum a b F` is
sum_{i != j, q_abij=0} F_ij. Write eps(q)=1 if q=0 and 0 otherwise. The
allocation-dependent pair term in the printed variance estimator is

P_abij(w) = [A_ai A_bj/(q_abij+eps(q_abij))]
             (q_abij-p_ai p_bj)(Y_i/p_ai)(Y_j/p_bj).

The defined `printedVariance` Vhat_N is 1/N^2 times the sum of:

* sum_i [A_1i(Y_i/p_1i)^2+A_0i(Y_i/p_0i)^2];
* sum_{i != j}(P_11ij+P_00ij-2P_10ij);
* for each a=1,0, sum_{i != j,q_aaij=0}
  [A_ai Y_i^2/(2p_ai)+A_aj Y_j^2/(2p_aj)].

In particular the diagonal coefficients here are 1, and the extra corrections
are only for zero same-arm joints. Zero cross-arm joints receive no separate
correction. The q+eps(q) denominator is 1 at q=0 and q otherwise.

For later formulas put

AV_a(u) = sum_i p_ai(1-p_ai)(u_i/p_ai)^2
          +sum_{i != j}(q_aaij-p_ai p_aj)(u_i/p_ai)(u_j/p_aj),

SC(u,v) = sum_{i,j:q_10ij != 0}(q_10ij-p_1i p_0j)
                                      (u_i/p_1i)(v_j/p_0j)
          -sum_{i,j:q_10ij=0}u_i v_j,

CC(u,v) = sum_{i != j}(q_10ij-p_1i p_0j)(u_i/p_1i)(v_j/p_0j)
          -sum_i u_i v_i.

`independent D f g` is the explicit condition that, for every function
u from the codomain of f to R and every function v from the codomain of g
to R, E[u(f)v(g)]=E[u(f)]E[v(g)]. Thus it is distributional independence
in the finite probability settings used here, not merely zero covariance.
`fittingOutcomes D J y1 y0 w` restricts Y(w) to the subtype of units in J.

`UnitExperiment I` is a nonnegative normalized real weight on the entire
finite set of binary functions I → Bool, with strictly positive treatment
and control marginal for each unit. Weights may be zero. Its `design` uses
that function itself as treatment. `ClusterExperiment U C` is a surjective
map c:U→C together with `UnitExperiment C`; its cluster design randomizes
C and its unit design assigns unit i the label at c(i). Surjectivity says
each cluster has a unit; without the explicit `Nonempty` assumptions it does
not itself exclude U=C=empty. Totals of a unit outcome y are
Y_c=sum_{i:c(i)=c} y_i. `clusterTotal` has this same summation meaning.

For a matrix X with K columns, `designWithIntercept K X` has first column
all ones followed by X's K columns. `olsDesignMap` is ordinary matrix-vector
multiplication into Euclidean space. `olsColumnSpace` is its range.
`olsFitted K V y` is the orthogonal projection of y onto this range,
converted back to its coordinates. `IsLeastSquaresFitted K V y z` says
there exists beta with V beta=z and, for every beta',
sum_i(y_i-z_i)^2 <= sum_i(y_i-(V beta')_i)^2. It does not impose full rank
or a unique coefficient vector. Fitted responses are well defined even at
deficient rank.

Mathlib endpoints checked: `Fintype.univ` enumerates all elements;
`Finset.erase` removes the specified element and `filter` retains exactly
the satisfying elements; finite sums use this enumeration without repeated
indices. `Matrix.mulVec` is a row dot product (Data/Matrix/Mul.lean:698),
and `mulVecLin` is that same multiplication as a linear map
(LinearAlgebra/Matrix/ToLin.lean:292). `EuclideanSpace` is `PiLp 2`
(Analysis/InnerProductSpace/PiL2.lean:114); its inner product is the sum
of coordinate inner products and its `equiv` is the coordinate equivalence
at line 279. `Submodule.starProjection` is the orthogonal projection followed
by inclusion (Analysis/InnerProductSpace/Projection/Basic.lean:132), so this
is Euclidean least squares. `Real.sqrt` is the nonnegative square root,
extended by zero on negative arguments (Analysis/Real/Sqrt.lean:112).
`Real.log` is the real logarithm on positive arguments, extended by log|x|
on negative arguments and by zero at zero
(Analysis/SpecialFunctions/Log/Basic.lean:44). `Real.exp` is the usual real
exponential. The defined sigmoid s(t)=1-1/(1+exp(t)) lies strictly between
zero and one for finite real t; hence the likelihood logs below have
positive arguments. Field division is total, with division by zero equal
to zero. Natural subtraction is truncated; its uses with M-m and |I|-n
are accompanied by m<M and n<|I| respectively.

## Fixed examples and Table definitions

All displayed arrays are zero-indexed.

* `asymmetricTwo` has three equally likely allocations 00,01,11 on two
  units, over Q. `realAsymmetricTwo` is the identical real design.
* `singleAsymmetric` retains only unit 0 of that design.
* `oneOfThree` has three equally likely allocations with exactly unit w
  treated. Its potential outcomes in T15 are y1=1,y0=0. The supplied
  `packageFit(w,i)` is a_w+b_w i with
  a=(5/6,1/3,-1/6), b=(-1/2,0,1/2).
* `unequalClusterDesign` has three equally likely allocations, treating
  respectively the cluster of unit labels c=(0,1,2,2). Its unit population
  has size four and its cluster population has size three.
* `realXorThree` has four equally likely allocations 000,011,101,110.
  The fitting set is {1,2} and its deterministic fit is
  xorFit(v)=v_1+v_2-2v_1v_2.
* `twoOfFour` lists all six allocations with two of four treated.
  `twoOfSix` lists all fifteen allocations with two of six treated.
  `tableDesign` assigns weight 1/90 to each pair of these allocations.
  Its ten cluster labels 0..3 use the first component; labels 4..9 use
  the second. The sixteen units map to clusters as
  c=(0,0,1,1,2,3,4,4,4,5,5,6,6,7,8,9).
  Responses are Y=(1,1,1,1,1,0,1,1,0,1,1,1,1,0,0,0), and covariates
  X=(4,0,4,1,4,2,4,1,2,5,4,1,4,2,2,3).
  `tableUnitDesign` lifts the ten-cluster design through c.
* The fixed `tableLinearResidual` is the ten-vector
  (1,7/8,1/4,-1/2,-15/31,19/93,1/3,-76/93,-76/93,-79/93).
  Its definition alone does not certify that it came from any regression.
* To define `feEstimate`, center X and Y separately in the first six and
  last ten units (means X:5/2,14/5; means Y:5/6,3/5). Center treatment
  separately in these same groups using their realized unit means. If
  Xc,Yc,Tc denote these centered vectors, let
  r=Tc-[sum Xc Tc/sum Xc^2]Xc. The estimate is sum rYc/sum r^2.
* Define L_b(beta)=sum over units i in group b of
  [Y_i log s(beta_0+beta_1 X_i)+(1-Y_i)log(1-s(beta_0+beta_1 X_i))].
  In this definition b=false selects i<6 and b=true selects i>=6.
  `logitMaximizer b beta` means L_b(gamma)<=L_b(beta) for every real
  pair gamma. `logitCoefficients b` chooses a maximizer if one exists,
  and otherwise returns (0,0).
  **The prediction definition selects `logitCoefficients (i<6)`: the first
  six units therefore use the maximizer of the last-ten likelihood, and
  the last ten units use the maximizer of the first-six likelihood.**
  `tableLogitResidual` sums Y_i minus these predictions within each cluster.
* `realTableDesign` casts the table design's weights to the reals.
  The logit estimate H is HT with these residual totals in both arms and
  denominator 16. Its variance estimate Vhat is the printed variance
  formula with those same residual totals and denominator 16.

`rounded3(x,r)` and real `roundsTo(x,r)` mean r-0.0005<=x<r+0.0005.
`roundedSD3(v,r)` means (r-0.0005)^2<=v<(r+0.0005)^2; all centers used
in this statement are positive, so it tests the corresponding standard
deviation interval without a square root.

## SAP.P026b.T13

For every nonempty finite decidable unit type I, every UnitExperiment E on
I, every pair of real potential-outcome vectors y1,y0, and every real
prediction f:(I→Bool)→I→R, in that order, both of the following hold:

1. For every Boolean arm a, with y_a=y1 for true and y0 for false,
   E G_a(y_a,f)=total(y_a)-sum_i Cov(A_ai,f_i/p_ai).
2. With N=|I|,
   E G_N-tau_N=[sum_i Cov(A_0i,f_i/p_0i)
                  -sum_i Cov(A_1i,f_i/p_1i)]/N.

There is no independence or fitted-model hypothesis on f.

## SAP.P026b.T14

This is a closed conjunction about the above fixed Table data and the
specified, cross-selected logistic predictions. It asserts:

1. Each of L_false and L_true has exactly one finite real coefficient
   maximizer. The chosen coefficients satisfy coordinatewise bounds of
   radius 0.0000005 about beta_true=(-1.1201076,0.5657586) and
   beta_false=(1.0843223,0.2280259).
2. E H=0; 0.247090<=sqrt(Var H)<=0.247093;
   0.0605<=Var H<0.0615; E Vhat=Var H; and
   0.0125<=sqrt(Var Vhat)<0.0135.
3. For every Boolean b, the chosen coefficients maximize L_b.
4. For every a,b in R, each of these two implications holds:
   (a>=0 and a+4b>=0 and a+2b<=0) implies a=b=0;
   (a+b>=0 and a+4b>=0 and a+2b<=0) implies a=b=0.
5. Let Delta=tau_16(Y,Y)=0, mu=E H, v=Var H, e=E Vhat. The ten entries
   (Delta,mu,mu-Delta,sqrt v,sqrt E(H-Delta)^2,v,e,e-v,
    sqrt Var Vhat,sqrt E(Vhat-v)^2)
   respectively round to (0,0,0,.247,.247,.061,.061,0,.013,.013).
6. At every index j in {3,4,5,6,8,9}, that same entry does not round to
   the corresponding entry of (0,0,0,.170,.170,.029,.029,0,.007,.007).

These are assertions, not assumptions about fits or numerical moments.

## SAP.P026b.T15

This closed statement concerns `oneOfThree`, x_i=i, y1_i=1,y0_i=0.
It asserts normalization, nonnegative weights, positive marginals and
p_1i=1/3,p_0i=2/3. For each allocation w and unit i, the supplied fitted
vector is the corresponding row of
((5/6,1/3,-1/6),(1/3,1/3,1/3),(-1/6,1/3,5/6)). For every w it is a
least-squares fit of the observed outcomes to an intercept and x, and
every other fitted vector satisfying the specified least-squares
minimization property equals this vector.

The generalized estimates are (1/4,1,1/4). The covariances
Cov(A_1i,packageFit_i) are (1/6,0,1/6). The expectation of the generalized
estimate is 1/2, the true ATE is 1, their difference is -1/2, and
-(1/3)(3+3/2)(1/6+0+1/6)=-1/2. Every allocation's unadjusted HT estimate
is 1. Finally 1/2 != 1. There are no hypotheses.

## SAP.P026b.T16

The statement is a conjunction of five clauses, whose universal variables
are scoped separately:

1. For every nonempty finite decidable I, UnitExperiment E and fixed
   real vectors y1,y0,g, for every allocation w the generalized estimator
   with f(w)=g equals the observed residual contrast, and its expectation
   equals the ATE (N=|I|).
2. For every such I,E, every natural K (including zero), every real
   I-by-K covariate matrix X and y1,y0, let V adjoin an intercept and
   f(w) be the projection fit of Y(w) on V. For every w, f(w) satisfies
   the least-squares minimization property and the generalized estimator
   equals the observed residual contrast. Its bias is exactly
   -sum_i Cov(A_1i,f_i)(1/p_1i+1/p_0i)/N.
3. For every such I,E,y1,y0 and arbitrary random real predictions f,
   if Cov(A_1i,f_i)=0 for every i, then E G_N=tau_N.
4. For every such I,E, real x:I→R and deterministic map
   G:(I→R)→I→R, use y1=y0=x and f(w)=G(Y(w)). Then E G_N=tau_N.
   There is no further information supplied to G as an argument.
5. All of T15's closed assertions hold.

## SAP.P026b.T17

This closed conjunction first negates the following universal implication:
for every real Design D on three allocations and two units, if D is a
probability design, has positive marginals, and has positive disagreement
for each distinct pair, then for all real outcome vectors x,z both
crossSupport(D) and Var(H_2(x,z))<=E Vhat_2(x,z) hold.
Negating this conjunction does not by itself assert an actual strict
variance underestimate: failure of crossSupport is sufficient.

It then asserts that realAsymmetricTwo is a probability design with
positive marginals and, for every distinct i,j, positive disagreement,
positive q_11ij, and positive q_00ij. Finally, with y1=y0=1 and f=0,
E Vhat_2 != Var(G_2). There is no stated direction of this inequality.

## SAP.P026b.T18

The fixed realXorThree design is a probability design with positive
marginals. For every fitting unit j in {1,2}, its treatment label is
independent, in the all-test-functions sense above, of unit 0's treatment
label. Nevertheless, with y1=1,y0=0, the covariance of A_10 with the
deterministic xorFit of the two fitting units' observed outcomes is
nonzero. No joint independence of unit 0 from the pair is asserted.

## SAP.P026b.T19

This is a closed statement about the fixed Table population. For every
one of the 90 allocations, the FE residual sum of squares sum_i r_i^2 is
strictly positive. Each of the two logistic likelihoods has a unique
finite maximizer. It is then asserted that the following conjunction is
false (not that every conjunct is individually false):

* unique finite maximizers for both logistic likelihoods;
* E(FE) rounds to -.012; Var(FE) rounds to .036;
  sqrt Var(FE) rounds to .191; sqrt[Var(FE)+(E FE)^2] rounds to .191;
* for H_L=HT_16(tableLinearResidual,tableLinearResidual), sqrt Var(H_L)
  rounds to .162, Var(H_L) rounds to .026, E Vhat_L rounds to .026,
  and sqrt Var(Vhat_L) rounds to .007;
* for the defined real logistic residual estimator H, the respective
  absolute errors of sqrt Var(H), Var(H), E Vhat, sqrt Var(Vhat) from
  .170,.029,.029,.007 are each at most .0005.

The FE and Linear rounding tests are half-open intervals; the four
Logit error tests use closed intervals. No numerical claims about other
table columns or entries occur in this type.

## SAP.P026b.T20

For every nonempty finite decidable I, UnitExperiment E, and real y1,y0:
for every arm a and every allocation w, H_a(y_a;w) equals
sum_i A_ai(w)Y_i(w)/p_ai. The treated and control HT totals have
expectations total(y1) and total(y0), respectively. The HT ATE estimator
with N=|I| has expectation tau_N. No additional assumptions are imposed.

## SAP.P026b.T21

This is a conjunction of three separately scoped parts.

1. For all finite allocation and unit types Ω,I with decidable equality
   on I, all real Designs D, assuming D is a probability design: for
   every natural n with 0<n<|I|, assume for each i that p_1i=n/|I| and
   p_0i=(|I|-n)/|I|, and assume every allocation of positive weight has
   exactly n treated units. Then for every x,z, on every positive-weight
   allocation HT with denominator |I| equals
   observedArmSum_1/n-observedArmSum_0/(|I|-n), and the expectation of
   that latter contrast equals the ATE.
2. For all nonempty finite decidable U, naturals M,m with 0<m<M and
   ClusterExperiment E:U→Fin M, assume every cluster's marginal
   probabilities are m/M and (M-m)/M, and every positive-weight
   allocation has exactly m treated clusters. Then for all unit outcomes
   x,z and every cluster allocation w (including zero-weight ones),
   unit HT equals (M/|U|) times the treated cluster-total sum divided by
   m minus the control cluster-total sum divided by M-m. Its expectation
   under the unit design equals the unit ATE.
3. The closed unequalClusterDesign example is a probability design with
   positive marginals 1/3 and 2/3; both realized unit arms are nonempty
   on every allocation. For y1=y0=(1,1,0,0), expected unit difference in
   means is 1/9, expected unit HT is zero, true ATE is zero, and 1/9!=0.

## SAP.P026b.T22

For all nonempty finite decidable I, UnitExperiment E, real y1,y0 and
arbitrary random real predictions f, all three following clauses hold:

1. If for every i, Cov(A_1i,f_i)=0, then both generalized arm totals
   have expectations total(y1),total(y0), and generalized ATE has
   expectation tau_N, where N=|I|.
2. For every deterministic real prediction vector g, all those
   covariances with g are zero, both generalized totals are unbiased,
   and the generalized ATE is unbiased.
3. For every allocation w,
   G_N(y1,y0,f;w)=H_N(y1,y0;w)
                   -[H_1(f(w);w)-H_0(f(w);w)]/N.

No independence assumption beyond the explicitly sufficient zero
covariances in the first implication is hidden in this statement.

## SAP.P026b.T23

For every nonempty finite decidable I, UnitExperiment E, real x,z,
arbitrary random real f, real b0,b1, and allocation w, in that order:

1. H_N(b0+b1*x,b0+b1*z;w)
   =(b0/N)[sum_i A_1i/p_1i-sum_i A_0i/p_0i]+b1 H_N(x,z;w).
2. H_N(b0+b1*x,b0+b1*z;w)=b1 H_N(x,z;w) if and only if b0=0 or
   sum_i A_1i/p_1i=sum_i A_0i/p_0i.
3. G_N(b0+b1*x,b0+b1*z,b0+b1*f;w)=b1 G_N(x,z,f;w).

The statement additionally asserts these closed facts: singleAsymmetric
is a probability design with positive marginals, allocation 2 has positive
weight, H_1(1,1;2)=3, (-1)H_1(0,0;2)=0, and those two estimates differ.
Here N=1 really is its number of units. This supplies a supported affine
transformation counterexample with b0=1,b1=-1 and baseline outcomes zero.

## SAP.P026b.T24

The first universally quantified clause ranges over every nonempty finite
decidable I, UnitExperiment E, real x,z and arbitrary random real f.
For every allocation w, generalized ATE is HT of the residual potential
outcomes x-f(w),z-f(w) and is also the observed residual contrast.
Additionally, for every fixed real prediction r:I→R,

Var(G_N(x,z,r))=[AV_1(x-r)+AV_0(z-r)-2 SC(x-r,z-r)]/N^2,

where N=|I|. The variance formula is asserted for fixed r, not arbitrary
random f.

The second clause ranges over every nonempty finite decidable U and C
and every ClusterExperiment E:U→C. Assume positive cluster disagreement
for every distinct c,d. Then for every pair of unit-outcome vectors x,z,
writing X,Z for their cluster totals: for every arm a,
Var(H_a(X if a=true else Z))=AV_a(X if a=true else Z). Moreover the
cross-covariance Cov(H_1(X),H_0(Z)) equals each of:

* sum_{c,d}(q_10cd-p_1c p_0d)(X_c/p_1c)(Z_d/p_0d);
* SC(X,Z);
* CC(X,Z).

There is no assumed directed crossSupport condition; the off-diagonal
formula includes terms at zero cross-arm joint probability.
