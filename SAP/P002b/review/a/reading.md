# Blind mathematical reading

This file was written after reading only `SAP/P002b/Defs.lean`, all six
`SAP/P002b/Defs/Part*.lean` files, the Challenge files, and the relevant
Mathlib definitions. Neither `claims.json` nor `record.json` had been opened.
The readings below describe the propositions, including conditions inside
named definitions, independently of the Challenge docstrings.

## Notation and definitions used in the statements

All populations are finite. For a natural number n, the units are
I = {0,...,n-1}. A population consists of arbitrary real potential outcomes
y_i(0), y_i(1), binary receipts d_i(0), d_i(1), and a natural number n1.
The outcomes depend on receipt alone: exclusion is built into this choice of
objects. Write n0 = n-n1, where this subtraction is in the reals, and
p = n1/n. A valid design means n >= 2 and 0 < n1 < n. An assignment is
any subset S of I of cardinality n1, and S^c is its complement in I.
Expectations, variances, and probabilities are with respect to the uniform
distribution on ALL such subsets. More precisely, expectation is the sum
over the assignment set divided by its cardinality, design variance is
the expectation of the squared deviation from that expectation, and
probability is the number of assignments satisfying the event divided by
the total number. Validity makes this support nonempty.

Monotone receipt means d_i(0)=1 implies d_i(1)=1, for every i.
The complier set C is {i : d_i(0)=0 and d_i(1)=1}. The LATE b_P is
|C|^(-1) sum_{i in C}(y_i(1)-y_i(0)). Unless explicitly required, receipts
need not be monotone and C need not be nonempty.

For a real array q, mean(q) = sum_i q_i/n and
mean_A(q) = sum_{i in A} q_i/|A|. Population variance and covariance use
denominator n-1, with subtraction in the reals:

    V(q) = sum_i (q_i-mean(q))^2/(n-1),
    Cov(q,t) = sum_i (q_i-mean(q))(t_i-mean(t))/(n-1).

Group covariance has the analogous denominator |A|-1 when |A| >= 2,
and is DEFINED TO BE ZERO when |A| < 2. Group variance is group
covariance of an array with itself. All real divisions use Lean's total
division, so a real divided by zero is zero. The fourth norm is
L4(q) = ((sum_i q_i^4)/n)^(1/4), implemented with two real square roots.
Real.sqrt returns zero on negative arguments.

Write W_i(a,b) = y_i(d_i(a))-b*d_i(a), and
v_i(a,b) = W_i(a,b)-mean(W(a,b)). Under assignment S the observed receipt
is d_i(1) on S and d_i(0) on S^c; observed outcome is y_i of that receipt.
W^S(b) is the observed outcome minus b times the observed binary receipt.

For any array q and subset S, the raw contrast and its squared scale are

    t(q,S) = (1/n) sum_i q_i(1_{i in S}-p),
    s2(q,S) = p^2(1-p)^2 [sum_{i in S}(q_i-mean_S q)^2/n1^2
                         + sum_{i in S^c}(q_i-mean_{S^c}q)^2/n0^2].

For real t,s2 the absolute studentized value is an extended nonnegative
real. If s2=0 it is zero when t=0 and +infinity otherwise; if s2 is not
zero it is ENNReal.ofReal(|t|/sqrt(s2)). ENNReal.ofReal truncates a
negative input to zero; all scales used here are sums of squares with
nonnegative weights. Denote the raw studentized statistic by AR(q,S).
For a function h of assignments, its critical value c(h,alpha) is the
smallest attained h-value with uniform probability at least 1-alpha
below or equal to it. If there is no candidate it is +infinity. Valid
designs and 0<alpha<1 make the candidate set nonempty. The unadjusted
acceptance event at b is

    AR(W^S(b),S) <= c(T -> AR(W^S(b),T),alpha).

Thus the reference distribution holds the observed array for S fixed
and reassigns it over T. Coverage is the uniform probability of this
event as S varies.

A covariate population also supplies x_i in R^k. Let z_i=(1,x_i),
x_i^circ=(0,x_i), and ||u||^2=sum_j u_j^2. The Gram G_A is
mean_A(z_i z_i'), the score h_A(q) is mean_A(z_i q_i), and
RSS_A(q,c)=sum_{i in A}(q_i-z_i'c)^2. OLS_A(q) is G_A^{-1}h_A(q)
when det(G_A) != 0. On a singular arm it is a fixed classically chosen
global minimizer of RSS, if one exists, and the zero vector otherwise.
In finite-dimensional real least squares such a minimizer does exist.
The chosen coefficients can be nonunique on singular designs. Mathlib's
square-matrix inverse itself is zero for a singular real matrix; the
OLS singular branch is therefore a separate convention, not that inverse.

Population OLS coefficients are psi_a(b)=OLS_I(W(a,b)), and residuals
are eps_i(a,b)=W_i(a,b)-z_i'psi_a(b). For an observed array q, the fitted
arm coefficients are c1=OLS_S(q) and c0=OLS_{S^c}(q). For arbitrary
coefficient vectors c1,c0 define

    A(q,S;c1,c0) = mean_S(q_i-x_i'c1_slopes)
                  -mean_{S^c}(q_i-x_i'c0_slopes).

The feasible adjusted contrast is Ahat(q,S)=A(q,S;OLS_S(q),OLS_{S^c}(q)).
The oracle contrast is Ao(b,S)=A(W^S(b),S;psi_1(b),psi_0(b)).
The adjusted squared scale is

    sadj2(q,S)=RSS_S(q,OLS_S(q))/n1^2
              +RSS_{S^c}(q,OLS_{S^c}(q))/n0^2.

ARadj uses Ahat and sadj2 with exactly the studentization convention
above. Adjusted acceptance and coverage use ARadj and the same full
randomization critical-value construction, holding W^S(b) fixed.

Theta(P,delta,r,A) is the conjunction of:

1. A valid design, monotone receipt, and a nonempty complier set.
2. r*n <= n1 <= (1-r)*n.
3. Cov_C(W(1,b_P),W(0,b_P)) >=
   -delta*sqrt(V_C(W(1,b_P)))*sqrt(V_C(W(0,b_P))).
4. For each a in {0,1}, L4(v(a,b_P)) <= A*sqrt(V(W(a,b_P))).

There are no additional signs imposed on delta,r,A by this definition.
In particular, the complier condition uses the specified zero convention
when there is just one complier.

Xi(P,delta,e,A,B,r) is the conjunction of:

1. A valid design, monotone receipt, and a nonempty complier set.
2. r*n <= n1 <= (1-r)*n.
3. Cov(eps(1,b_P),eps(0,b_P)) >=
   -delta*sqrt(V(eps(1,b_P)))*sqrt(V(eps(0,b_P))).
4. For each a, L4(eps(a,b_P)) <= B*sqrt(V(eps(a,b_P))).
5. For each coordinate s, sum_i x_is=0 and mean_i x_is^4 <= A.
6. For EVERY b in R^k, e*||b||^2 <= mean_i (x_i'b)^2.

Again parameter signs are supplied by individual statements, not by Xi.
Its covariance is over the whole population of residuals, not just C.

For an array q, Max(q)=max({0} union {q_i:i in I}); zero is always
adjoined. All maxima appearing in the theorem conclusions are of
nonnegative arrays on nonempty unit sets.

## Quadratic curves, data generation, and algorithm predicates

A quadratic AR object Q is six arbitrary real coefficients a,b,c,d,e,f.
Its real curve is R_Q(b)=(a*b^2+b_coefficient*b+c)/(d*b^2+e*b+f).
Regularity means the denominator is STRICTLY POSITIVE at EVERY real b
and the numerator is NONNEGATIVE at EVERY real b.

For real curves g_1,...,g_M, c_MC(g,alpha,b) is the smallest attained
sqrt(g_m(b)) for which at least (1-alpha)*M of the M values are less
than or equal to it. If no candidate exists it is zero. The index set
I_MC(g,alpha,b) contains ALL m attaining that critical value, including
ties. C_MC(f,g,alpha)={b : sqrt(f(b)) <= c_MC(g,alpha,b)}. Here too the
square root is the total real square root.

The data-generation predicate used by T22,T23,T27 says there EXIST
n,k, a covariate population P, a Boolean choice adjusted, an observed
assignment O and M reference assignments T_m such that:

* The population has a valid design, monotone receipt, and nonempty C.
* O and EVERY T_m are in the complete-randomization support. The T_m
  need not be distinct and there is no probability law asserted for
  the list.
* If adjusted=true, k>0, every covariate coordinate sums to zero, and
  BOTH arm Grams are nonsingular for O and for EVERY T_m. If
  adjusted=false, no such covariate or rank conditions are required.
* Put Y_i=y_i(d_i(O_i)) and D_i=d_i(O_i), the SAME observed arrays for
  all curves. For a chosen assignment R the raw coefficients are

      a=t(D,R)^2, b=-2*t(Y,R)*t(D,R), c=t(Y,R)^2,
      d=s2(D,R), e=-2*cross(Y,D,R), f=s2(Y,R),

  where cross is the same within-arm covariance expression as s2,
  with squared deviations replaced by the product of the Y and D
  deviations. In the adjusted branch replace t by Ahat, s2 by sadj2,
  and cross by the sum of products of fitted arm residuals divided by
  the respective squared arm sizes. Qf is the coefficient object for
  R=O; Qg_m is that for R=T_m. This is equality of all six
  coefficients, not just equality of the rational functions.

A crossing at b means that TWO simulated curves are UNEQUAL AS
FUNCTIONS but have the same value at b. Equal functions do not create
crossings. The observed curve f is not used to define crossings.
An intersection list J is a finite strictly increasing list of reals
containing exactly ALL such crossings.

Intervals have extended real endpoints l,u. A closed interval means
{b in R:l<=b<=u}; an open interval uses strict inequalities. Thus
infinite endpoints do not introduce new nonreal elements into a piece.
A recorded piece has l,u and an index m. Its set is
{b:l<=b<=u and f(b)<=g_m(b)}. The returned set is the union of these
sets over the finite list of pieces.

Algorithm1Run requires an intersection list J; the list of piece
endpoints must equal, IN ORDER, the successive gaps cut out by
(-infinity,J,+infinity). On a finite gap the sample is its midpoint;
on a left infinite gap it is the right endpoint minus one; on a right
infinite gap it is the left endpoint plus one; on the whole real line
it is zero. Each selected index must be a quantile index AT THAT
SAMPLE POINT ONLY. No correctness on other points is part of the
predicate.

Algorithm2Run requires a complete sorted intersection list J != [],
and a nonempty FINITE piece list. The first left endpoint is -infinity
and its selected index is critical at head(J)-1. For every piece p,
consider the set of real crossings to the right of its left endpoint
between its selected curve and any unequal simulated curve. If that
set is nonempty its LEAST element must be p.right; otherwise
p.right=+infinity. If there is a next piece, p.right must be finite,
its value is the next left endpoint, and the next index is critical
at the midpoint to the next GLOBAL crossing strictly after p.right,
or at p.right+1 if there is no such global crossing. If there is no
next piece, p.right must equal +infinity. This predicate describes a
completed finite execution, rather than an infinite policy or a
termination assertion about a procedure.

## Each theorem

### SAP.P002b.T16

There are no hypotheses or universally quantified inputs. For the
fixed four by two array with rows (1,0),(-1,0),(0,1),(0,-1): every
coordinate sums to zero; every coordinate's mean fourth power is 1/2;
the mean cross product for coordinates s,t is 1/2 if s=t and zero
otherwise; max_i ||(1,x_i)||^2=2; and
1+sum_s max_i x_is^2=3. All five assertions hold simultaneously.

### SAP.P002b.T17

This is the conjunction of a finite statement and an asymptotic one.

For EVERY n,k, array x in R^(n by k), with n>0, and EVERY A>=0,
if mean_i x_is^4<=A for EVERY coordinate s, then all three hold:

* For every s, max_i |x_is| <= (A*n)^(1/4).
* max_i ||(1,x_i)||^2 <= 1+sum_s max_i x_is^2.
* 1+sum_s max_i x_is^2 <= 1+k*sqrt(A*n).

Separately, for EVERY fixed k and A>=0, and EVERY sequence of arrays
x_j with j+1 rows and k columns satisfying the fourth-moment bound
for EVERY j,s, the sequence max_i||(1,x_{ji})||^2 is O(sqrt(j+1))
as j tends to infinity. Mathlib's meaning is that there EXIST a real
constant C and a natural cutoff N such that for EVERY j>=N the
absolute value of the first sequence is <= C times |sqrt(j+1)|.
Neither centering nor positive k is assumed in either part.

### SAP.P002b.T18

For EVERY n,k,P,b,S, assume valid design, |S|=n1, and nonsingular
Grams in BOTH arms. With c_a fitted to W^S(b), two identities hold:

    Ahat(W^S(b),S)-Ao(b,S)
      = -mean_S[x_i'(c1-psi_1(b))_slopes]
        +mean_{S^c}[x_i'(c0-psi_0(b))_slopes]
      = -mean_S[(x_i^circ)'G_S^{-1}h_S(eps(1,b))]
        +mean_{S^c}[(x_i^circ)'G_{S^c}^{-1}h_{S^c}(eps(0,b))].

There is no centering condition on x, no population Gram condition,
no monotonicity condition, and no nonempty-complier condition. In
particular b is an arbitrary hypothesized effect, not necessarily LATE.

### SAP.P002b.T19

For EVERY n,k,P,b,S and arm a, assume valid design and |S|=n1.
Let A=S for a=1 and A=S^c for a=0; assume ONLY this arm Gram is
nonsingular. With c_a fitted to W^S(b), the conjunction is

    psi_a(b)-c_a = -G_A^{-1}h_A(eps(a,b)),
    -2*mean_A[eps_i(a,b)*z_i'(c_a-psi_a(b))]
      = -2*h_A(eps(a,b))'G_A^{-1}h_A(eps(a,b)).

There are no other model, centering, or rank hypotheses.

### SAP.P002b.T20

There are two independent universally quantified parts.

First, for EVERY n,k,P satisfying valid design, monotone receipt,
nonempty C, centered covariates (sum_i x_is=0 for every s), and
nonsingular POPULATION Gram, and for EVERY assignment S with |S|=n1,
all five conclusions hold at b=b_P:

    psi_1(b)_intercept=mean(W(1,b)),
    psi_0(b)_intercept=mean(W(0,b)),
    mean(W(1,b))-mean(W(0,b))=0,
    psi_1(b)_intercept-psi_0(b)_intercept=0,
    Ao(b,S)=mean_S eps(1,b)-mean_{S^c} eps(0,b).

Arm Gram invertibility is not needed for this finite part.

Second, for EVERY strictly increasing sizes:N->N, EVERY fixed k,
EVERY population sequence P_j of size sizes(j), and EVERY fixed
delta,e,A,B,r satisfying k>0, delta<1, e>0, A>0, B>0, and
0<r<=1/2, assume:

* Xi(P_j,delta,e,A,B,r) for EVERY j;
* Var_design(Ao(b_{P_j},S))>0 for EVERY j;
* EVERY control-arm Gram is nonsingular, for EVERY j and EVERY
  assignment S in that design's support.

Define

    R_j(S)=mean_{S^c}[(x_i^circ)'G_{S^c}^{-1}
                                h_{S^c}(eps(0,b_{P_j}))]
            /sqrt(Var_design(Ao(b_{P_j},S))).

For EVERY real kappa>0, the uniform design probability of
|R_j(S)|>=kappa tends to zero as j tends to infinity. No numerical
lower bound on the positive variance is assumed, and treated-arm
invertibility is not an assumption of this part.

### SAP.P002b.T22

For EVERY M,Qf,Qg,alpha, assume M>0, 0<alpha<1, the complete common
data-generation predicate above, regularity of Qf, and regularity
of EVERY Qg_m. For EVERY complete sorted intersection list J which
is NONEMPTY, set f=R_Qf and g_m=R_Qg_m. Then:

1. There EXISTS a completed finite Algorithm2Run on J.
2. For EVERY finite piece list that is an Algorithm2Run, all of the
   following hold: its length is <= length(J)+1; its successive
   RIGHT endpoints are strictly increasing; every right endpoint
   is either +infinity or a real member of J; every real b lies
   in some closed recorded interval; every recorded index is a
   quantile index at EVERY real point of its closed interval;
   each piece set equals C_MC(f,g,alpha) intersected with that
   interval; and the returned union equals C_MC(f,g,alpha).

There is no assertion for J=[] and no quantification over infinite
executions or over an independently prescribed selection policy.

### SAP.P002b.T23

For EVERY M,Qf,Qg,alpha under exactly the M, level, data-generation,
and regularity assumptions of T22, and for EVERY J and piece list,
assume J != [] and Algorithm1Run(g,alpha,J,pieces). For EVERY piece
p and EVERY real b in its CLOSED interval, the selected index belongs
to I_MC(g,alpha,b) and g_{p.index}(b)=c_MC(g,alpha,b)^2. Also the
piece set equals C_MC(f,g,alpha) intersected with its closed interval.
Nothing is asserted here for an empty intersection list.

### SAP.P002b.T24

For EVERY n,k,P,S,Y,D,b, assume a valid design, |S|=n1, and
nonsingular Grams in BOTH arms. Here Y,D are arbitrary real arrays;
D need not be binary. Then all hold:

* For each arm a, fitted_a(Y-bD)=fitted_a(Y)-b*fitted_a(D), as
  equality of the full vectors including the intercept.
* Ahat(Y-bD,S)=Ahat(Y,S)-b*Ahat(D,S).
* IF Ahat(D,S)!=0, then Ahat(Y-[Ahat(Y,S)/Ahat(D,S)]D,S)=0.

There is no centering or compliance assumption.

### SAP.P002b.T25

For EVERY n,k,P,b, assume a valid design, monotone receipt, nonempty
C, and y_i(1)=y_i(0)+b for EVERY unit i. Then W^S(b) is exactly the
baseline array (i->y_i(0)) for EVERY subset S of I, including subsets
outside the design support; b_P=b; and for EVERY 0<alpha<1, BOTH
unadjusted and adjusted coverage at b are at least 1-alpha. No
conditions on x or on any Gram determinant are imposed; singular-arm
adjusted coverage uses the fixed least-squares selection above.

### SAP.P002b.T26

For EVERY n,k,P,Y,D,S, assume a valid design, |S|=n1, centered
covariates, and nonsingular Grams in BOTH arms. Y,D are arbitrary
real arrays. Then these three parts hold:

1. For EVERY real b, Ahat(Y-bD,S)=Ahat(Y,S)-b*Ahat(D,S).
2. IF Ahat(D,S)!=0, then for EVERY 0<alpha<1, with
   bW=Ahat(Y,S)/Ahat(D,S), the adjusted contrast of Y-bW*D is zero,
   its extended absolute adjusted studentized statistic is zero,
   and that statistic is <= its full-randomization critical value.
3. IF the IV cross matrix and instrument Gram below are BOTH
   nonsingular AND Ahat(D,S)!=0, the coefficient on D in the IV
   vector satisfies Ahat(D,S)*coef_D=Ahat(Y,S), and coef_D=bW.

The regressor row is (D_i,1,1_{i in S}x_i,1_{i notin S}x_i), up to
the fixed Boolean ordering of the two interaction blocks. The
instrument row replaces D_i by 1_{i in S} and leaves all other
columns the same. The IV cross matrix is mean_i instrument_i
times regressor_i', the instrument Gram is mean_i instrument_i
times instrument_i', and the IV coefficient vector is the inverse
cross matrix times mean_i instrument_i*Y_i. Thus the statement
uses the just-identified IV normal equations, with explicit
invertibility conditions. It makes no assertion about the shape
of the whole confidence set.

### SAP.P002b.T27

For EVERY M,Qf,Qg,alpha under the M, level, common data-generation,
and regularity assumptions of T22, and for EVERY extended real
l<u, assume NO crossing of distinct simulated functions occurs
at any real b strictly between l,u. Then all four conclusions hold:

* For EVERY interior x and EVERY interior y, I_MC(g,alpha,x)=
  I_MC(g,alpha,y).
* For EVERY interior x and real a,b with l=a and u=b, the index
  set at x is a subset of each endpoint index set.
* For EVERY interior x and real b with l=-infinity and u=b, the
  index set at x is a subset of the index set at b.
* For EVERY interior x and real a with u=+infinity and l=a, the
  index set at x is a subset of the index set at a.

No intersection list is an input to this theorem, and the observed
curve does not enter these conclusions.

### SAP.P002b.T29

For n,delta,r,A,alpha define the extended nonnegative real

    H_n = inf_{b in R} inf_{P:Population(n),
                            Theta(P,delta,r,A) and b_P=b}
                         ofReal(coverage(P,b,alpha)).

An infimum over an empty population subtype is +infinity. If all
the population classes at size n are empty then H_n=+infinity.
The proposition is the NEGATION of the following universal claim:
for EVERY real delta,r,A,alpha, if delta<1, 0<r<=1/2, A>0, and
0<alpha<1, then H_n tends, along ALL natural sizes n to infinity,
to ofReal(1-alpha). Equivalently in classical mathematics, some
admissible fixed tuple of constants has no such nominal limit.
No nonemptiness hypothesis on these model classes is included.

### SAP.P002b.T30

This is the NEGATION of a universal adjusted coverage limit.
For EVERY natural k and EVERY real delta,e,A,B,r,alpha, the
negated claim says: if k>0, delta<1, e,A,B>0, 0<r<=1/2, and
0<alpha<1, then

    inf_{b in R} inf_{P:CovPopulation(n,k),
                      Xi(P,delta,e,A,B,r) and b_P=b}
                     ofReal(adjustedCoverage(P,b,alpha))

tends as n runs through ALL natural sizes to ofReal(1-alpha).
The proposition asserts that at least one admissible tuple of
constants fails this convergence. Empty inner classes have
infimum +infinity, exactly as in T29; no model-class nonemptiness
assumption is made.

## Mathlib meanings checked

The finite sums are ordinary sums over `Fin n`, `Fin k`, and
`Option (Fin k)`; the latter adds the intercept coordinate.
`dotProduct` and matrix-vector multiplication are finite coordinate
sums (`Mathlib/Data/Matrix/Mul.lean`). The singular-zero matrix
inverse convention is in `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`.
`Finset.powersetCard` means all subsets of exactly the prescribed
cardinality (`Mathlib/Data/Finset/Powerset.lean`); `min'` and `max'`
are actual finite extrema on a nonempty finset (`Mathlib/Data/Finset/Max.lean`).
`ENNReal.ofReal` is real-to-nonnegative-real truncation followed by
inclusion into [0,+infinity] (`Mathlib/Basic/ENNReal/Basic.lean`).
Infima are complete-lattice infima, so an empty infimum in ENNReal
is its top element. `EReal.toReal` maps both infinities to zero
(`Mathlib/Data/EReal/Basic.lean`); the gap-sample branches guard
its intended finite uses. `StrictMono` means strict increase
(`Mathlib/Order/Monotone/Defs.lean`), `IsBigO` means existence of an
eventual constant norm bound (`Mathlib/Analysis/Asymptotics/Defs.lean`),
and `Tendsto ... atTop (nhds L)` is ordinary sequential convergence
to L in the indicated real or extended-real topology
(`Mathlib/Order/Filter/Defs.lean`).
