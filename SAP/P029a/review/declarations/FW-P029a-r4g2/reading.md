# Blind reading

This file was written before opening `claims.json` or `record.json`. I read all
entries of `closure.json`, the five Challenge docstrings and statements, and the
source definitions in their closures. I also compiled `scratch/ClosurePrint.lean`
and read `scratch/ClosurePrint.out`: all 60 distinct line-zero auxiliary
declarations are numeral `AtLeastTwo` instances, one `NeZero 3` instance, or the
standard real continuous-scalar-multiplication instance. They add no statistical
assumptions. No Solution source was read.

The following notation in this reading is ordinary mathematics, with these exact
expansions (not additional premises). For a finite type L and real arrays p,v,
E_p(v) = sum over all i in L of p_i v_i; P_p(A) = sum of p_i for A(i);
M_p(v|A) = [sum over A(i) of p_i v_i]/P_p(A).
Cov_p(u,v) = E_p(uv)-E_p(u)E_p(v), and Var_p(v)=Cov_p(v,v).
A finite probability law means p_i >= 0 for every i and sum p_i=1.
For a measure mu, P_mu(A)=(mu(A)).toReal,
M_mu(v|A)=(integral over A of v dmu)/P_mu(A), and
Cov_mu(u,v)=integral uv dmu-(integral u dmu)(integral v dmu).
An indicator of a Boolean is the real number 1 for true and 0 for false.

A potential response is a tuple (x,d0,d1,y0,y1) with x in its indicated covariate
type, Boolean d0,d1, and real y0,y1. Its treatment effect is y1-y0; receipt under
Boolean assignment z is dz; observed outcome is y1 if dz is true and y0 otherwise.
A defier means d0=true and d1=false. For finite data with assignment Z, weights w,
and outcomes Y and receipts D just defined, write

    A_z(v) = M_p(wv | Z=z) / M_p(w | Z=z),
    W(p,U,Z,w) = [A_true(Y)-A_false(Y)]/[A_true(1_D)-A_false(1_D)].

Thus every occurrence of W below means exactly this normalized ratio of finite
sums, including its divisions, rather than an unstated regression operation.

## SAP.P029a.T6

Challenge Part1 lines 46–50 asserts a conjunction, with no external hypotheses.
Its clauses, in order, are the following.

1. For every real y, (y+5)-y=5. For every natural n>0 and every real vector
   Y0 indexed by Fin n, sum_i[(Y0_i+5)-Y0_i]/n=5.
2. For every measurable space Omega, probability measure mu on it, arbitrary
   real function Y0, and set C which is measurable and has P_mu(C)>0,
   integral[(Y0+5)-Y0] dmu=5 and M_mu((Y0+5)-Y0 | C)=5.
   There is no measurability premise on Y0: the displayed integrand is pointwise
   the constant 5, so no measurability of Y0 is needed for these particular integrals.
3. For every natural R>0 and t:Fin R -> R, the root mean squared error with
   constant benchmark 5 is sqrt(sum_r(t_r-5)^2/R). Here root mean squared error
   with any benchmark vector b is defined as sqrt(sum_r(t_r-b_r)^2/R).
   This clause is a definitional equality for the proposed statistic.
4. Let nu be Lebesgue measure conditioned on the open interval (-1,1)
   (Mathlib `ProbabilityTheory.cond volume (Ioo (-1) 1)`). Then
   integral u dnu=0 and integral u^2 dnu=1/3.
5. For every measurable space Omega, probability measure mu, natural n>0,
   and array X:Fin n -> Fin 3 -> Omega -> R, assume all coordinates measurable,
   all 3n coordinates jointly independent (`iIndepFun`), and each pushforward
   law equals nu. Define B(omega)=sum_i 5(1+X_i0+X_i1+X_i2)/n.
   Then integral B dmu=5 and integral B^2 dmu-(integral B dmu)^2=25/n.
6. For all real t,B,
   (t-B)^2-(t-5)^2=(B-5)^2-2(t-5)(B-5).
7. For every natural R, real vectors t,B on Fin R, and proof R>0,
   sum(t-B)^2/R-sum(t-5)^2/R = sum(B-5)^2/R-(2/R)sum(t-5)(B-5).
8. For every finite type L and p,t,B:L -> R, if p is a finite probability law
   and E_p(B)=5, then E_p((t-B)^2)-E_p((t-5)^2)=Var_p(B)-2Cov_p(t,B).
9. For every measurable space Omega, probability measure mu, and real functions
   t,B with `MemLp t 2 mu`, `MemLp B 2 mu`, and integral B dmu=5,
   integral(t-B)^2 dmu-integral(t-5)^2 dmu=Cov_mu(B,B)-2Cov_mu(t,B).
   `MemLp` means almost-everywhere strong measurability and finite L2 seminorm.
10. The concrete scoring clauses use I=Fin 50 x Fin 5 x Bool (500 records).
    The five covariate vectors x_k are (0,0,0), (1/2,0,0), (0,1/2,0),
    (0,0,1/2), and (-1/2,-1/2,-1/2). Row i=(r,k,z) of the real design matrix
    X is (1,1_z,x_k0,x_k1,x_k2). Its transpose product is

        G = [[500,250,0,0,0], [250,250,0,0,0],
             [0,0,50,25,25], [0,0,25,50,25], [0,0,25,25,50]].

    For every Boolean opposite and every record i, take
    y0=5+(if opposite then 1_z else 0), y1=y0+5, d0=false, d1=true,
    and x=x_k. The effect is 5, receipt under z is z, and the observed outcome
    is 5+(if opposite then 6 else 5)*1_z.
    Separately, the benchmark sum_i 5(1+x_i0+x_i1+x_i2)/500 for the constant
    profile (1/5,0,0) is 6. G inverse applied to G(5,5,0,0,0) is
    (5,5,0,0,0), and similarly for (5,6,0,0,0).
    The four scalar errors are (5-6)^2=1, (5-5)^2=0,
    (6-6)^2=0, (6-5)^2=1.
11. The admissibility clause says -1<1/5<1; every coordinate of every x_k is
    strictly between -1 and 1; and for every Boolean z, the latent index rule
    at indices (2,-2) gives always-or-complier 1, always-taker 0, complier 1,
    and receipt 1_z. Expanded, those rules are
    H(a)=1 if a>0 and 0 otherwise,
    AC=H(a), A=H(b)H(a), C=H(a)-H(b)H(a), receipt=C*1_z+A.
    There are exactly 250 true assignments in I.

Junk conventions: real division by zero is 0, so the generic benchmark and RMSE
definitions would give 0 at n=0 or R=0; their relevant clauses require positive
counts. `Real.sqrt` is 0 on negative arguments, but here the positive-count
mean of squares is nonnegative. Finite conditional means are 0 at zero event
mass, but C has positive finite mass in the population effect clause. Probability
measures rule out `toReal infinity=0`. Bochner integrals are totalized to 0 when
nonintegrable; the effect integrands are constants, the uniform coordinates have
their specified bounded laws, and L2 assumptions give the error integrability.
The inverse of a singular matrix is totalized by Mathlib, but the displayed G is
an actual nonsingular numerical matrix (the inverse identities are asserted).
Fin n and finite probability laws can be empty syntactically; positive n and total
mass 1 exclude the problematic instances. All numeric casts are exact natural
or integer casts into R. No rpow, limsup, extrema of sets, or partial-function
default is used. The constant-profile benchmark calculation and the noise
design are separate clauses, not a statement identifying their covariates.

## SAP.P029a.T7

Challenge Part1 lines 52–64 states `T7WholeStatement`, which includes the older
`T7Statement` and genuine fitting certificates. It has no external hypotheses.
The following are its exact mathematical ingredients.

For a finite index type I, likelihood vector L and weight vector w, define
Q_in(L,w)=-sum_i log(L_i w_i), Q_out(L,w)=-sum_i w_i log L_i.
A global minimum of a real objective Q at theta means Q(theta)<=Q(t) for every t.
The log is Mathlib's real logarithm. Define extended negative log to be +infinity
at zero and the finite real value -log x otherwise; the extended inside objective
is the finite sum of these terms in EReal.

1. For every finite I and real L,w with all L_i>0 and w_i>0,
   Q_in(L,w)=Q_in(L,1)-sum log w_i.
   For all types I,Theta with I finite, all L:Theta -> I -> R with every entry
   positive, all positive w, and every theta, theta minimizes Q_in(L(.),w)
   iff it minimizes Q_out(L(.),1).
2. For every real L, L*0=0 and its extended negative log is +infinity.
   For every finite I, L_i in (0,1], weight vector w, and index i with w_i=0
   and w_j>0 for every j different from i, the extended inside objective is
   +infinity. This latter clause explicitly treats exactly one zero weight.
3. The one-sided finite law is uniform on Bool x Bool x Fin 4 (16 atoms).
   Write an atom as (x,z,k). Then d0=false, d1=(k<3 if x=true, k<1 otherwise),
   y0=0, y1=1+1_x, and assignment is z. Thus receipt is z AND d1.
   Let w=9 for received treatment and 1 otherwise. The specified score vectors,
   ordered by x=false,true, are s=(1/4,3/4) and s_w=(3/4,27/28).
   The identities 9/(9+3)=3/4 and 27/(27+1)=27/28 hold, and
   W(p,U,Z,w/s)=3/2, W(p,U,Z,w/s_w)=17/10, with 3/2 != 17/10.
4. The two-sided data have cells (x,z):Bool x Bool and four records k:Fin 4
   per cell. Success counts m_(false,false)=1, m_(true,false)=1,
   m_(false,true)=2, m_(true,true)=3, with receipt k<m_(x,z).
   The raw package rates q0 are 1/4 in each control cell, 1/2 at (false,true),
   and 3/4 at (true,true). The corrected rates qw are 3/4 in each control cell,
   9/10 at (false,true), and 27/28 at (true,true).
   Both arrays satisfy 0<q(x,false)<q(x,true)<1 for each x.
   For H(q)=product_(x,z) q(x,z)^m_(x,z) * (1-q(x,z))^(4-m_(x,z)),
   H(qw)/H(q0)=729/1500625<1. Corrected score differences are
   qw(false,true)-qw(false,false)=3/20 and
   qw(true,true)-qw(true,false)=3/14.
5. For every real t>0, set w_t=t at the sole atom (false,true,1), otherwise 1.
   The specified scores are s_t(false)=1/(3+t), s_t(true)=3/4. Then
   W(p,U,Z,w_t/s)=3/2 and W(p,U,Z,w_t/s_t)=(t+11)/(t+7).
   The rational function (t+11)/(t+7) has derivative -1/16 at t=1;
   the constant function 3/2 has derivative 0 there.

The additional Whole definitions make the fitting assertions precise:

* Phi is the Mathlib CDF of `gaussianReal 0 1`, i.e. the standard normal law.
  For beta=(b0,b1):R x R, f_beta(x)=Phi(b0+b1*1_x).
  For beta=(beta_AC,beta_A), the nested receipt rate is
  r_beta(x,z)=a(x)(1-b(x))*1_z+a(x)b(x), with a=f_beta_AC and b=f_beta_A.
  Its clipped rate is max(1/100000,min(1-1/100000,r_beta(x,z))).
* For any finite records, cell map c, Boolean receipts D, and weights w,
  the Bernoulli contribution is q_c^1_D (1-q_c)^1_notD, with natural exponents.
  The corrected cell objective is Q_out of these contributions; the package
  two-sided objective is Q_in of them. The one-sided package objective on the
  eight treated-arm records (x,k) is the corrected objective with all weights 1;
  its supplied weight argument is discarded by definition.
* A realized minimum for a parameter-to-rate map f, proposed rate qhat, and
  objective Q means (exists a finite parameter theta with f(theta)=qhat) AND
  (for every theta, Q(qhat)<=Q(f(theta)) AND
  [Q(qhat)=Q(f(theta)) iff f(theta)=qhat]). No optimality is assumed as a premise.
* For every q:Bool -> R with 0<q(x)<1 for every x, some finite b0,b1 realize q.
  For every q:Bool x Bool -> R with 0<q(x,false)<q(x,true)<1 for each x,
  some four finite real coefficients realize the raw, unclipped q.
* For every positive weight vector on the eight treated records, s is a realized
  minimum of the one-sided package objective. Also s_w is a realized minimum of
  the corrected objective with weights 9 for success and 1 for failure.
* For every positive weight vector on the sixteen two-sided records, q0 is a
  realized minimum of the package objective over the clipped nested model.
  Likewise qw is a realized minimum of the corrected objective over that model,
  using weights 9 for successes and 1 for failures.
* For every t>0, s_t is a realized minimum of the corrected binary probit objective
  on the treated records with w_t. The actual W expressions with w_t/s_t and
  w_t/s respectively have derivatives -1/16 and 0 at 1.
* The two unweighted differences q0(false,true)-q0(false,false)=1/4 and
  q0(true,true)-q0(true,false)=1/2 are also stated.

Junk conventions: real log is total (log 0=0 and log of negative x=log |x|), but
the invariance clauses require positive entries and weights. Finite Gaussian
probit coefficients give strictly interior probabilities; clipping stays in
[1/100000,99999/100000]. The extended definition explicitly uses +infinity at
zero instead of real-log's zero value. EReal sums here contain finite values
and +infinity, never -infinity. W and conditional means divide by zero as 0 in
general; the witnesses have both assignment arms, positive weights and scores,
and positive weighted receipt differences. The perturbation derivatives are
local at t=1, away from the totalized singularities at -3 and -7.
The natural powers in Bernoulli contributions use 0^0=1 in principle; all fitted
probabilities here are interior. The subtraction 4-m is natural truncated
subtraction, but every m is 1,2,3, so no truncation changes it. Finite empty I
gives zero objectives and vacuous positive-entry premises, a harmless extension;
the explicit samples are nonempty. No unbounded extremum or implicit optimizer
selection is used: coefficients are existential and minimization is universal.
No raw dataset, numerical optimizer, or floating-point computation is asserted.

## SAP.P029a.T8

Challenge Part1 lines 66–74 asserts a conjunction without external hypotheses.
Use the finite-sum objectives, Bernoulli contributions, finite-law W, and concrete
one-sided and two-sided arrays expanded in the preceding section. These symbols
have the same expansions here; there is no probit map or coefficient space in T8.

1. For every finite I and likelihood L_i in (0,1], each 0*log L_i=0, and
   Q_out(L,1)=Q_in(L,1).
2. For every finite I, positive L_i, and natural weights w_i,
   exp(-Q_out(L,w cast into R))=product_i L_i^w_i.
3. For every pair of positive real totals S,F, the function
   ell(q)=S log q+F log(1-q) is strictly concave on the open convex interval
   (0,1). Its proposed maximum qhat=S/(S+F) is in (0,1); for every q in (0,1),
   ell(q)<=ell(qhat) with equality iff q=qhat.
4. For all finite types I,C, cell:I -> C, D:I -> Bool and nonnegative weights
   w:I -> R, assume for every c both totals
   S_c=sum_{cell(i)=c,D_i=true} w_i and
   F_c=sum_{cell(i)=c,D_i=false} w_i are strictly positive.
   Then qhat_c=S_c/(S_c+F_c) is interior in every cell. For every array
   q:C -> R interior in every cell, the corrected Bernoulli objective at qhat
   is <= its value at q, with equality iff q=qhat as functions.
5. The same interior and unique-minimum assertions hold concretely for:
   (a) eight treated-arm records (x,k), success iff k<(3 if x else 1), weights
   9 on success and 1 on failure, proposed qhat=(3/4,27/28);
   (b) the same records with weight t at (false,1), otherwise 1, for every
   real t>0, proposed qhat=(1/(3+t),3/4);
   (c) four two-sided cells (x,z), four records each, success counts (1,1)
   in the two control cells and (2,3) in the two treated cells, weights
   9 on success and 1 on failure, proposed rates (3/4,3/4) in control and
   (9/10,27/28) in treatment. These fit predicates assert optimality as their
   conclusion, never as assumptions.
6. For any finite I, arbitrary parameter type Theta, positive likelihood family
   L(theta,i), positive real k, and theta, theta globally minimizes
   Q_in(L(.),constant k) iff it minimizes Q_out(L(.),constant k).
7. The concrete score-Wald assertions are exactly those in T7 item 3:
   the two weight-total ratios, W(w/s)=3/2, W(w/s_w)=17/10, and their inequality.
8. The concrete two-sided assertions are exactly T7 item 4: interior strict
   receipt ordering for both arrays, likelihood ratio 729/1500625<1, and
   corrected differences 3/20 and 3/14.
9. For every t>0 the specified perturbed scores equal (1/(3+t),3/4), and the
   two W values are 3/2 and (t+11)/(t+7). There is no derivative assertion in T8.

Junk conventions: no cell-fit result is claimed at S=0 or F=0, so division by
S+F and both log arguments stay in their ordinary domains. Zero weights multiply
finite logs; integer zero replication uses L^0=1. Although real-log totalization
would permit nonsensical boundary fits in an unrestricted objective, every
comparison q in the fitting clauses is explicitly interior. The natural count
subtractions, W denominators, positive t, and exact casts have the same protections
as in T7. An unused cell would contradict S_c>0,F_c>0. Empty C forces empty I
if a cell map exists; that case is a harmless empty-function optimization and
does not affect the nonempty concrete fits. Empty Theta makes assertions about
an input theta uninstantiable, but arbitrary nonempty parameter types are allowed.
There are no integrals, infinities, square roots, rpow, or partial defaults.
The docstring explicitly confines fitting to free interior Bernoulli cell
probabilities and confines numerical W assertions to specified score arrays.

## SAP.P029a.T9

Challenge Part1 lines 76–84 has no external hypotheses. Here is the explicit
population used by every clause. Records are the dependent disjoint union of
Fin count_k for k:Fin 9, with counts

    (602,768,2514,160,155,461,1789,5247,7237).

Race label is some true for k<3, some false for 3<=k<6, and none for k>=6.
Assignment Z is (k mod 3<2); contact C is (k mod 3=0).
The completion A is true iff k<3; completion B is true iff k<3 or k>=6.
Every record has real mass 1/18933.

1. For every outcome vector Y:records -> R, the population has 18933 records,
   these masses are nonnegative and sum to 1, and each completion agrees with
   every recorded Boolean race label. For each record, take potential responses
   (unit covariate,d0=false,d1=C_i,y0=Y_i,y1=Y_i). Under the fixed assignment Z,
   receipt is exactly C, observed outcome exactly Y, and no record is a defier.
2. P(C)=2551/18933; P(A)=3884/18933; P(B)=18157/18933;
   P(A and C)=602/18933; P(B and C)=2391/18933.
   The integer identities are
   18933*602-2551*3884=1489582 and
   18933*2391-2551*18157=-1049704.
   The contact mean differences are
   M(1_C|A)-M(1_C|not A)=744791/29225158>0 and
   M(1_C|B)-M(1_C|not B)=-131213/1761229<0.
3. For every raw-code function R:records -> Option String, assume for all i,code
   that R_i=some code implies the recorded race is some(code="W"). Here
   (code="W") is evaluated to a Boolean, so every other nonmissing string is
   treated as false. A completed raw record is defined simply as the pair
   (R_i,completion_i). Both completions' first components equal R_i; and every
   supplied nonmissing code has both completion values equal to (code="W").
   The hypothesis in particular forces R_i=none on all nine-cell records whose
   recorded Boolean race is none. It does not accept arbitrary nonmissing raw
   codes on those records.
4. For every real e with 0<e<1, product over all records of
   (e if Z_i=true else 1-e) is strictly positive. This is an assignment-support
   certificate for this particular fixed assignment vector, not an empirical
   independence identity for the fixed empirical record measure.
5. The reverse conditional mean comparisons also hold:
   M(1_A|C)>M(1_A|not C) and M(1_B|C)<M(1_B|not C).

Junk conventions: Fin count and the sigma type use exact positive natural counts,
and all real casts and displayed integer subtractions are exact (not truncated).
Race labels are total Option values with explicitly chosen missingness, not
defaulted partial functions. All contact/race conditioning events and their
complements have positive finite mass by the displayed counts. Thus no
zero-denominator convention affects the strict signs. Every product factor in
the support certificate is positive; the actual index type is nonempty. No
integrals, real logs, roots, rpow, extrema or limits occur. The first-component
raw-code equalities are definitional because the completed record is a pair;
the substantive Boolean compatibility depends on the stated R hypothesis.
The docstring disclaims validation of a raw data file and lists dropped data
summaries; the encoded counts are a stipulated nine-cell construction.

## SAP.P029a.T10

Challenge Part1 lines 86–98 has no external hypotheses and has these five clauses.

1. For every natural n and Boolean arrays C,W on Fin(n+1), assume
   0<count(W)<n+1 and 0<count(C)<n+1. A count is the cardinality of the finite
   set of indices at which that Boolean is true. Write N=n+1, nW=count(W),
   nC=count(C), n11=count(C AND W), all cast into R, and give each index mass
   1/N. Then

       Cov(1_C,1_W)=(N*n11-nC*nW)/N^2,
       M(1_C|W)-M(1_C|not W)=(N*n11-nC*nW)/(nW*(N-nW)),
       M(1_W|C)-M(1_W|not C)=(N*n11-nC*nW)/(nC*(N-nC)).

   Also M(1_C|W)>M(1_C|not W) iff nC*nW<N*n11, and
   M(1_W|C)>M(1_W|not C) iff the same inequality. Here every covariance,
   expectation and conditional mean expands to the finite sums at the start
   of this reading. These are empirical binary counts, not a model fit.
2. The rational identities
   602/1370-160/315=-2957/43155 and
   602/1370-155/308=-13467/210980 hold in R, and both differences are negative.
   This clause contains no dataset variable or provenance condition.
3. The entire nine-cell completion assertion from T9 items 1–2 is repeated:
   the records, uniform probability law, two explicit Boolean completions,
   agreement with recorded Boolean labels, arbitrary observed outcomes,
   no defiers, pooled marginal and joint counts, integer numerators, and the
   two opposite contact-given-race differences with their exact values.
   T10 does not repeat the raw-string preservation or reverse conditional
   comparisons as separate clauses. The general binary identity in item 1
   supplies the latter direction after an identification of finite records.
4. For every 0<e<1, the product Bernoulli probability of the displayed fixed
   assignment vector is positive, exactly as in T9 item 4.
5. For every natural n, finite group type G, real arrays s,A on Fin(n+1),
   and group map g:Fin(n+1)->G, use masses p_i=1/(n+1). For each h in G set
   m_s(h)=sum_{g_i=h}p_i s_i/sum_{g_i=h}p_i and similarly m_A(h).
   Then

       E(sA)-E(s)E(A)
       = E[(s-m_s(g))(A-m_A(g))]
         + E[(m_s(g)-E(s))(m_A(g)-E(A))].

   Moreover, for every distinguished h with P(g=h)>0, assume
   for every i with g_i!=h and every j with g_j=g_i that A_j=A_i
   (A is constant within every group other than h). Then

       E[(s-m_s(g))(A-m_A(g))]
       = [#{i:g_i=h}/(n+1)]
         * M((s-m_s(h))(A-m_A(h)) | g=h).

   Thus the grouped identity is for a finite uniform empirical distribution,
   with arbitrary real s and A; A is not required to be Boolean in this lemma.
   The positivity of the distinguished group is an explicit additional premise.

Junk conventions: n+1 is always positive; the strict binary count premises
force both Boolean values to occur and make all displayed binary denominators
positive. The N-nW and N-nC subtractions in formulas are real subtraction, not
natural truncation. All four rational comparisons have positive numerical
denominators. In the grouped formula unused groups have conditional mean 0 by
division-by-zero convention, but m_s and m_A are evaluated only at realized
groups in the unconditional sums. The distinguished conditional expression
is protected by positive group probability. Finite G can be empty syntactically,
but no map from Fin(n+1) into an empty type exists. The nine-cell counts and
Option conventions are exactly as expanded for T9. There are no analytic
integrals, logarithms, infinities, roots, rpow, extrema, limits or partial defaults.

The docstring says the empirical identification of the Raleigh unknown records,
raw-string codes and the listed empirical covariate conclusions are omitted.
It describes the remaining rational calculations and finite covariance algebra.
