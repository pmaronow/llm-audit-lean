# Blind reading of the Challenge statements

This file was written and saved before opening `claims.json` or `record.json`.
Sources: all six `SAP/P002b/Defs/Part*.lean` files, their import file, and the
Challenge files. There are thirteen theorem stubs. The names below abbreviate
the explicit definitions in the following dictionary; no hypothesis is inferred
from a theorem name or docstring.

## Mathematical dictionary and conventions

All finite indices are `Fin n = {0,...,n-1}`. A population consists of arbitrary
real numbers y_i(0), y_i(1), arbitrary binary receipt decisions d_i(0), d_i(1),
and a natural treated count n1. Outcomes depend on receipt, not separately on
assignment. A covariate population additionally has arbitrary real vectors
x_i in R^k. Boolean false/true mean 0/1, and `binary` maps them to those reals.
There are no implicit conditions on these structures.

* C = {i : d_i(0)=0 and d_i(1)=1} is the complier set. Monotone receipt means
  for every i, d_i(0)=1 implies d_i(1)=1. L = |C|^{-1} sum_C(y_i(1)-y_i(0))
  is `late`.
* For any array q, bar(q) = sum_i q_i/n. For a subset H, bar_H(q) = sum_H q_i/|H|.
  V(q) = sum_i(q_i-bar(q))^2/(n-1), and
  Cov(q,t) = sum_i(q_i-bar(q))(t_i-bar(t))/(n-1).
  Group covariance is the analogous expression with denominator |H|-1 if
  |H|>=2, and is defined to be zero otherwise; group variance is covariance
  with itself. Thus singleton group variance/covariance is explicitly zero.
* w_i(a,b) = y_i(d_i(a))-b d_i(a); v_i(a,b)=w_i(a,b)-bar(w(a,b)).
  The fourth norm of q is sqrt(sqrt(sum_i q_i^4/n)).
* A valid design means n>=2 and 0<n1<n. Put p=n1/n and n0=n-n1 (the latter
  subtraction takes place in R). Omega is the set of all subsets of Fin n
  with exactly n1 elements. E h = sum_{S in Omega}h(S)/|Omega|;
  Pr(Ev) = |{S in Omega : Ev(S)}|/|Omega|; and
  Var_design h = E[(h-Eh)^2]. Complement is in all of Fin n.
* Given any S (not necessarily in Omega), D_i(S)=d_i(1_{i in S}),
  Y_i(S)=y_i(D_i(S)), W_i(b,S)=Y_i(S)-b D_i(S).
* t(q,S)=sum_i q_i(1_{i in S}-p)/n. Let qbar_1=bar_S(q),
  qbar_0=bar_{S^c}(q). The unadjusted scale is
  h(q,S)=p^2(1-p)^2[sum_S(q_i-qbar_1)^2/n1^2
  +sum_{S^c}(q_i-qbar_0)^2/n0^2].
* Absolute studentization A(t,h) is zero if h=0 and t=0, positive infinity
  if h=0 and t!=0, and otherwise ENNReal.ofReal(|t|/sqrt(h)).
  R(q,S)=A(t(q,S),h(q,S)). For a function G on assignments, q_alpha(G) is
  the smallest value in {G(S):S in Omega} for which Pr(G<=value)>=1-alpha;
  if there is no such value it is positive infinity. Acceptance at b for
  observed S is R(W(b,S),S)<=q_alpha(T -> R(W(b,S),T)). Thus the outcomes
  are held fixed when T is varied inside this quantile. `coverage` is the
  design probability of this acceptance event.

For covariates let z_i=(1,x_i), z_i^circ=(0,x_i), with coordinate set
{intercept} disjoint union Fin k. Define
G_H=bar_H(z_i z_i^T), s_H(q)=bar_H(z_i q_i),
RSS_H(q,c)=sum_H(q_i-z_i^T c)^2. The coefficient O_H(q) is G_H^{-1}s_H(q)
if det G_H!=0; otherwise it is one fixed choice of a global minimizer of
RSS_H(q,.) if a minimizer exists, and is the zero vector if no minimizer
exists. In finite-dimensional real least squares a minimizer exists, but
the definition itself contains the last fallback. Coefficient choices on
different singular problems are not explicitly coupled.

Let c_a(b)=O_all(w(a,b)), and u_i(a,b)=w_i(a,b)-z_i^T c_a(b).
Let bhat_1(q,S)=O_S(q), bhat_0(q,S)=O_{S^c}(q). Write
slope(x,c)=sum_j x_j c_j, omitting the intercept. The adjusted contrast is
T(q,S)=bar_S(q_i-slope(x_i,bhat_1))-bar_{S^c}(q_i-slope(x_i,bhat_0)).
The oracle contrast is
T_or(b,S)=bar_S(W_i(b,S)-slope(x_i,c_1(b)))
-bar_{S^c}(W_i(b,S)-slope(x_i,c_0(b))).
Its design variance always refers to the function S -> T_or(b,S).
The adjusted scale is
H(q,S)=RSS_S(q,bhat_1)/n1^2+RSS_{S^c}(q,bhat_0)/n0^2.
The adjusted AR statistic is R_adj(q,S)=A(T(q,S),H(q,S)); adjusted
acceptance and coverage replace R by R_adj in the preceding definitions.
The adjusted Wald value is T(Y,S)/T(D,S).

The parameter predicates used below expand as follows; the constants have
no sign restrictions except when separately imposed by the theorem.

* Theta(P,delta,r,A) means: valid design; monotone receipt; C nonempty;
  rn<=n1<=(1-r)n; groupCov_C(w(1,L),w(0,L)) >=
  -delta sqrt(groupVar_C(w(1,L))) sqrt(groupVar_C(w(0,L)));
  and, for both a, fourthNorm(v(a,L))<=A sqrt(V(w(a,L))).
* Xi(P,delta,e,A,B,r) means: valid design; monotone receipt; C nonempty;
  rn<=n1<=(1-r)n; Cov(u(1,L),u(0,L)) >=
  -delta sqrt(V(u(1,L))) sqrt(V(u(0,L)));
  fourthNorm(u(a,L))<=B sqrt(V(u(a,L))) for each a;
  sum_i x_ij=0 and bar(x_ij^4)<=A for each coordinate j;
  and for every b in R^k, e sum_j b_j^2<=bar((x_i^T b)^2).

The control remainder used in T20 is
K(P,S)=bar_{S^c}[(z_i^circ)^T G_{S^c}^{-1}s_{S^c}(u(0,L))]
/sqrt(Var_design T_or(L,. )).

For the IV conclusion let I=Fin 2 disjoint union (Bool x Fin k).
The regressor row r_i has first two coordinates D_i,1 and remaining
coordinates 1_{1_{i in S}=a}x_ij. The instrument row zIV_i replaces D_i
by 1_{i in S}. The cross matrix is B=bar(zIV_i r_i^T), the instrument Gram
matrix is JIV=bar(zIV_i zIV_i^T), and the coefficient vector is
B^{-1}bar(zIV_i Y_i). Its `inl 0` coordinate is the coefficient on receipt.

For the algorithm statements a sextuple Q=(a,b,c,d,e,f) defines
F_Q(b0)=(a b0^2+b b0+c)/(d b0^2+e b0+f).
`ARRegular Q` requires the denominator strictly positive for every real
b0 and the numerator nonnegative for every real b0.
For g_m:R->R, m in Fin M, c_alpha(b0) is the smallest attained value among
sqrt(g_m(b0)) having at least (1-alpha)M observations at or below it;
the empty-candidate fallback is zero. I_alpha(b0) is the set of all indices
attaining c_alpha(b0), including ties. C_MC={b0:sqrt(f(b0))<=c_alpha(b0)}.
A crossing is a real b0 at which g_s(b0)=g_t(b0) for two functions g_s,g_t
that are not identical as functions. Identical curves do not count as
crossings. `IntersectionList g J` says that J is strictly increasing and
contains exactly all such real crossings.

`DataGeneratedCoefficients Qf Qg` is an existential hypothesis: there exist
n,k, a covariate population P, an adjusted/unadjusted flag, an observed
assignment O, and M simulated assignments T_m such that the design is
valid, receipt is monotone, C is nonempty, and O and every T_m belong to
Omega. If adjusted, require k>0, centered covariates, and invertible
treated and control augmented Grams for O and every T_m. The sextuples
are all made from the same observed arrays Y(O),D(O), with Qf using
assignment O and Qg_m using assignment T_m. For a chosen assignment R,
the unadjusted sextuple is
(t(D,R)^2, -2t(Y,R)t(D,R), t(Y,R)^2,
h(D,R), -2h_cross(Y,D,R), h(Y,R)),
where h_cross is h with each squared centered term replaced by the product
of the centered Y and D terms. The adjusted sextuple uses T and H in
place of t and h, and replaces h_cross by the sum of products of the
within-arm OLS residuals divided by n1^2 and n0^2. Receipt in these arrays
is coded as the real number 0 or 1. This predicate restricts the numerical
sextuples, not merely the functions they represent.

A recorded piece p consists of extended-real endpoints l_p,u_p and an
index m_p in Fin M. Its closed interval is {b in R:l_p<=b<=u_p}; its
returned set is that interval intersected with {b:f(b)<=g_{m_p}(b)}.
The whole returned set is the union over the finite list of pieces.
An open interval replaces both endpoint inequalities by strict ones.

`Algorithm1Run g alpha J pieces` requires an exact intersection list J,
and the list of piece endpoint pairs to be precisely the consecutive
gaps of (-infinity,J,+infinity), in that order. Each piece's index must
belong to I_alpha at the prescribed sample: midpoint for finite endpoints,
u-1 at a left-infinite gap, l+1 at a right-infinite gap, and zero for the
whole line. It imposes no interval-wide quantile hypothesis.

`Algorithm2Run g alpha J pieces` requires an exact, nonempty intersection
list J and a nonempty finite list of pieces. The first left endpoint is
-infinity and its index is in I_alpha(J.head-1). For every piece p, let
E_p={b in R:l_p<b and there exists m with g_m!=g_{m_p} as functions and
g_m(b)=g_{m_p}(b)}. If E_p is nonempty, u_p must be its least element;
otherwise u_p=+infinity. A final piece must end at +infinity. If a next
piece q exists, u_p must be finite, l_q=u_p, and q's index must belong to
I_alpha at the midpoint between u_p and the next member of J strictly
larger than u_p, or at u_p+1 if no such member exists. Thus a completed
finite execution is part of this predicate; it is not a definition of
termination of every possible infinite policy.

`maximum q` is max({0} union {q_i}). `normSq` is the sum of squared
coordinates, so normSq(augmented x_i)=1+sum_j x_ij^2.

`infCoverageTheta(n,delta,r,A,alpha)` is the infimum in [0,+infinity]
first over b in R and then over populations with Theta and L=b of
ENNReal.ofReal(coverage(P,b,alpha)). The Xi version adds fixed k,e,B and
uses adjusted coverage and Xi. Empty inner model classes contribute
+infinity; if every model class at a size is empty, the outer infimum
is +infinity too. The definitions do not assume model classes are nonempty.

Mathlib endpoints and total operations were followed explicitly:

* `Finset.powersetCard` is the set of subsets of the given cardinality
  (`Data/Finset/Powerset.lean`); `max'`/`min'` are actual finite extrema
  on nonempty finsets (`Data/Finset/Max.lean`). Sums over empty indices
  are zero. Real division by zero is zero. Casts and the displayed real
  subtractions do not use natural truncated subtraction.
* `dotProduct` is sum of coordinate products (`Data/Matrix/Mul.lean`).
  The matrix inverse is det-inverse times the adjugate and is the zero
  matrix on singular real square matrices
  (`LinearAlgebra/Matrix/NonsingularInverse.lean:168-176`).
* `Real.sqrt` is the nonnegative square root of max(x,0)
  (`Analysis/Real/Sqrt.lean:112-142`). `ENNReal.ofReal` embeds max(x,0)
  in [0,+infinity] (`Basic/ENNReal/Basic.lean:231`). `EReal` includes both
  infinities; its `toReal` sends either infinity to zero
  (`Data/EReal/Basic.lean:220`); the valid gap constructions branch around
  these infinities before using their real coordinates.
* The indexed infima are complete-lattice infima, including the empty
  infimum +infinity. `Tendsto ... atTop (nhds c)` means convergence as
  the natural index tends to infinity in the usual topology (the order
  topology for [0,+infinity]); it is not a limsup. `IsBigO atTop f g`
  means there exist real C and a natural cutoff such that
  |f(j)|<=C|g(j)| thereafter (`Analysis/Asymptotics/Defs.lean:73-86`).

## Theorem-by-theorem reading

### SAP.P002b.T16

A closed assertion about the four rows x=(1,0),(-1,0),(0,1),(0,-1):
every coordinate sums to zero; each coordinate's mean fourth power is
1/2; for each pair of coordinates s,t the mean product is 1/2 if s=t and
zero otherwise; max_i(1+||x_i||^2)=2; and
1+sum_s max_i x_is^2=3. There are no hypotheses or free parameters.
The stated second-moment matrix is the two-covariate matrix, not the
three-coordinate augmented Gram matrix (whose intercept entry is one).

### SAP.P002b.T17

The conjunction of two universal assertions:

1. For all natural n,k and x in R^{n x k}, if n>0, then for every real
   A>=0 with bar(x_s^4)<=A for every s,
   max_i |x_is| <= (An)^{1/4} for every s,
   max_i(1+sum_s x_is^2)<=1+sum_s max_i x_is^2,
   and 1+sum_s max_i x_is^2<=1+k sqrt(An).
2. For every fixed natural k and real A>=0, for every triangular array
   x_j in R^{(j+1) x k} satisfying bar((x_j)_s^4)<=A for every j,s,
   max_i(1+sum_s (x_j)_is^2)=O(sqrt(j+1)) as j tends to infinity.

Neither centering nor a positive dimension is assumed.

### SAP.P002b.T18

For all natural n,k, covariate populations P, real b, and subsets S:
if the design is valid, S is an allowed assignment, and both G_S and
G_{S^c} are invertible, then, putting q=W(b,S), the feasible-minus-oracle
contrast has both exact representations

T(q,S)-T_or(b,S)
= -bar_S[slope(x_i,bhat_1(q,S)-c_1(b))]
  +bar_{S^c}[slope(x_i,bhat_0(q,S)-c_0(b))]
= -bar_S[(z_i^circ)^T G_S^{-1}s_S(u(1,b))]
  +bar_{S^c}[(z_i^circ)^T G_{S^c}^{-1}s_{S^c}(u(0,b))].

No centering, monotonicity, nonempty complier set, positive dimension,
or specified relation between b and L is assumed.

### SAP.P002b.T19

For all n,k,P,b,S and arm a in {0,1}, if the design is valid, S is an
allowed assignment, and G_H is invertible for H=S when a=1 and H=S^c
when a=0, then

c_a(b)-bhat_a(W(b,S),S) = -G_H^{-1}s_H(u(a,b)),

and the actual residual cross term is

-2 bar_H[u_i(a,b) z_i^T(bhat_a(W(b,S),S)-c_a(b))]
= -2 s_H(u(a,b))^T G_H^{-1}s_H(u(a,b)).

The other arm need not have an invertible Gram. No additional population
conditions are present.

### SAP.P002b.T20

The conjunction of an exact finite assertion and a sequence limit:

1. For every n,k,P satisfying valid design, monotone receipt, nonempty
   C, centered covariates, and invertible G_all, and then every allowed
   S: the two intercepts c_1(L)_intercept and c_0(L)_intercept equal
   bar(w(1,L)) and bar(w(0,L)) respectively; those means have difference
   zero; the two intercepts have difference zero; and
   T_or(L,S)=bar_S u(1,L)-bar_{S^c}u(0,L).
2. For every strictly increasing natural sequence sizes, then every
   natural k, sequence P_j of size sizes(j) and dimension k, and real
   delta,e,A,B,r: assume k>0, delta<1, e,A,B>0, 0<r<=1/2,
   Xi(P_j,delta,e,A,B,r) for every j, strictly positive design variance
   of T_or(L_j,.) for every j, and invertible G_{S^c} for every j and
   every assignment S in that design's support. Then for every real
   kappa>0, Pr_j(|K(P_j,S)|>=kappa) tends to zero as j tends to infinity.

There is no lower bound on delta. Xi is precisely the predicate expanded
above. The limit does not quantify over zero-variance or singular-control
sequences, and its threshold kappa is fixed before taking the limit.

### SAP.P002b.T22

For every natural M, sextuple Qf, Fin M-indexed sextuples Qg, and real
alpha: if M>0, 0<alpha<1, the coefficients are jointly data-generated,
Qf is ARRegular, and every Qg_m is ARRegular, then for every complete
strictly sorted crossing list J that is nonempty, with f=F_Qf and
g_m=F_Qg_m:

* There exists a finite list pieces satisfying Algorithm2Run.
* For every finite list pieces satisfying Algorithm2Run: its length is
  at most |J|+1; the right endpoints are strictly increasing; every right
  endpoint is +infinity or a real member of J; its closed intervals cover
  all real numbers; on every closed piece its selected index belongs to
  I_alpha at every real point; every returned piece is exactly C_MC
  intersected with its interval; and the union of returned pieces is C_MC.

This does not quantify over an arbitrary prescribed infinite policy,
does not prove that every such policy terminates, and does not handle J=[].
Joint data generation and strict denominator positivity are hypotheses,
not conclusions or automatic features of arbitrary sextuples.

### SAP.P002b.T23

For every M,Qf,Qg,alpha satisfying the same M,level,data-generation and
ARRegular hypotheses as T22, then every list J and every finite piece
list: if J is nonempty and Algorithm1Run holds, then for each piece p
and every real b in its closed interval, m_p is in I_alpha(b) and
g_{m_p}(b)=c_alpha(b)^2. Also the returned piece is exactly C_MC
intersected with that closed interval. Completeness and sortedness of J
and the gap/sample rules occur inside Algorithm1Run. No termination or
existence of an Algorithm1Run is asserted here.

### SAP.P002b.T24

For every n,k,P,S, arbitrary real arrays Y,D, and real b: if the design
is valid, S is an allowed assignment, and both arm Grams are invertible,
then for both arms a,
bhat_a(Y-bD,S)=bhat_a(Y,S)-b bhat_a(D,S),
and T(Y-bD,S)=T(Y,S)-b T(D,S). If additionally T(D,S)!=0, then
T(Y-[T(Y,S)/T(D,S)]D,S)=0.

There is no requirement that Y,D are observed potential-outcome arrays
or that D is binary. The nonzero contrast guards only the last assertion.

### SAP.P002b.T25

For every n,k,P and real b: if the design is valid, receipt is monotone,
C is nonempty, and y_i(1)=y_i(0)+b for every unit i, then for every subset
S, even outside the design support, W_i(b,S)=y_i(0) for every i; also
L=b; and for every real alpha with 0<alpha<1, both unadjusted and
adjusted coverage at b are at least 1-alpha.

No covariate centering, positive dimension, Gram invertibility, or
positive studentization scale is required. Infinite statistics and the
zero-over-zero studentization convention are included as defined above.

### SAP.P002b.T26

For every n,k,P, arbitrary real arrays Y,D, and subset S: if the design
is valid, S is allowed, covariates are centered, and both arm Grams are
invertible, then the following conjunction holds:

1. For every real b, T(Y-bD,S)=T(Y,S)-b T(D,S).
2. If T(D,S)!=0, then for every real alpha with 0<alpha<1, putting
   bW=T(Y,S)/T(D,S), T(Y-bW D,S)=0, R_adj(Y-bW D,S)=0, and
   R_adj(Y-bW D,S)<=q_alpha(T -> R_adj(Y-bW D,T)).
3. If the IV cross matrix B and instrument Gram JIV are invertible and
   T(D,S)!=0, then T(D,S) times the receipt IV coefficient equals
   T(Y,S), and that IV coefficient equals bW.

The nonzero denominator is conditional inside items 2 and 3. Item 1 is
unconditional beyond the shared design and Gram hypotheses. There is
no assertion about the confidence set being a finite union of intervals.

### SAP.P002b.T27

For every M,Qf,Qg,alpha satisfying the same positive M,interior level,
joint data-generation and ARRegular hypotheses as T22, then every pair
of extended-real endpoints l<u: if there is no crossing of g in (l,u),
the following four assertions hold:

1. For every x,y in (l,u), I_alpha(x)=I_alpha(y).
2. For every x in (l,u) and every real a,b with l=a and u=b,
   I_alpha(x) is a subset of each of I_alpha(a) and I_alpha(b).
3. For every x in (l,u) and every real b with l=-infinity,u=b,
   I_alpha(x) is a subset of I_alpha(b).
4. For every x in (l,u) and every real a with l=a,u=+infinity,
   I_alpha(x) is a subset of I_alpha(a).

There is no finite endpoint claim at infinity. Qf does not occur in the
conclusions but is still required in the shared hypotheses.

### SAP.P002b.T29

The negation of the following universal assertion: for all real
delta,r,A,alpha, if delta<1, 0<r<=1/2, A>0, and 0<alpha<1, then
infCoverageTheta(n,delta,r,A,alpha) tends to 1-alpha in [0,+infinity]
as n tends to infinity through all natural numbers.

Equivalently, there exist constants satisfying all those inequalities
for which that convergence fails. The proposition does not demand a
nonempty class for each size, a nondegenerate outcome variance, or an
explicit witness population; it does not say that convergence fails for
all choices of constants. The beta infimum and population infimum are
inside the n-indexed limit, in that order.

### SAP.P002b.T30

The negation of the following universal assertion: for every natural
k and real delta,e,A,B,r,alpha, if k>0, delta<1, e,A,B>0,
0<r<=1/2, and 0<alpha<1, then
infCoverageXi(n,k,delta,e,A,B,r,alpha) tends to 1-alpha in [0,+infinity]
as n tends to infinity through all natural numbers.

Equivalently, there exist such k and constants for which convergence
fails. The common dimension k and all constants are fixed before taking
the limit. No nonemptiness or positive residual-variance hypothesis is
added. This is a refutation of a universal convergence assertion, not
an assertion of nominal adjusted coverage.
