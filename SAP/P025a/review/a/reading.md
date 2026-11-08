# Blind mathematical reading

Saved before opening `claims.json` or `record.json`. Sources read: all seven
`SAP/P025a/Defs/Part*.lean` files, their aggregator, and both Challenge files.
Every Challenge theorem has no external arguments: its type is the corresponding
closed proposition `TjStatement`. The quantifiers below are inside those propositions.

## Fully expanded common notation

All outcomes, masses, bounds, objectives, and weights are real. A vector on `Fin n`
has coordinates indexed by the integers 0 through n-1, in their usual order.
All sums are finite sums over that whole index set unless a restriction is written.
`Monotone y` means i <= j implies y_i <= y_j; `StrictMono y` means i < j implies
y_i < y_j. An empty finite sum is zero. Natural-number subtraction is truncated.
Real division is totalized with division by zero equal to zero; this is the literal
meaning of the definitions even where the theorem hypotheses rule that case out.

For vectors y, a, w on a finite index set, write

    R(y,a,w) = (sum_i a_i w_i y_i)/(sum_i a_i w_i).
    mean(y) = (sum_i y_i)/n, for y on Fin n.
    B(alpha,beta) = {w : every i satisfies 1/beta <= w_i <= 1/alpha}.
    Bn(gamma) = {w : every i satisfies 1 <= w_i <= gamma}.
    A(y,a,alpha,beta) = {R(y,a,w) : w in B(alpha,beta)}.
    An(y,a,gamma) = {R(y,a,w) : w in Bn(gamma)}.
    lo(y,a,alpha,beta) = inf A(y,a,alpha,beta).
    hi(y,a,alpha,beta) = sup A(y,a,alpha,beta).

The last two definitions use the conditionally complete order on the real numbers,
not extended real endpoints. An infimum/supremum has its usual characterization
when the set is nonempty and bounded on the relevant side. The real empty or
unbounded fallback is zero; no boundedness or nonemptiness is built into these
definitions themselves.

For any natural cut k (including k = n), define

    l_i(gamma,k) = gamma if i < k, and 1 otherwise.
    h_i(gamma,k) = 1 if i < k, and gamma otherwise.
    L(y,a,gamma,k) = R(y,a,l(gamma,k)).
    H(y,a,gamma,k) = R(y,a,h(gamma,k)).

A lower cut CL(y,a,gamma,k) says k is the LEAST j in {0,...,n-1}
with L(y,a,gamma,j) <= y_j. An upper cut CH says k is the least j with
H(y,a,gamma,j) <= y_j. A printed lower cut CP says k is the least j with
y_j <= L(y,a,gamma,j). Each least-element assertion includes membership as
well as comparison with every other member. It does not merely say the value is
an infimum. Likewise a least/greatest attainable value below includes actual
attainment and comparison with ALL feasible vectors.

Separation means, for EVERY k in {0,...,n-1}, both y_k != H(y,a,gamma,k)
and y_k != L(y,a,gamma,k).

For classes define

    N_k = gamma sum_{i<k} a_i y_i + sum_{k<=i} a_i y_i.
    D_k = gamma sum_{i<k} a_i + sum_{k<=i} a_i.
    P(y,a,gamma,k) = Some((gamma sum_{i<k} a_i y_i
                           + sum_{k-2<=i} a_i y_i)
                          /(gamma sum_{i<k} a_i + sum_{k-2<=i} a_i))
                       when 2 <= k <= n;
                     None otherwise.

Here `Some`/`None` is an optional real, so `None` is not a numerical value.
The definition explicitly excludes k = 0,1, and k > n. Its k-2 is natural
subtraction, only evaluated in the valid branch for purposes of these statements.

For a finite set of sample states Omega, sample s(omega) a finite set of units,
and assigned real probabilities p(omega), the inclusion number is
pi_i = sum_omega p(omega) 1_{i in s(omega)}. A class total is
sum_{i: class(i)=j} pi_i. Probability normalization is not in these definitions.

The fixed two-unit data are b=(0,1), pi=(1/2,1). The two-state design has
Omega={0,1}, probability 1/2 at each state, s(0)={1}, s(1)={0,1}.
The four-class data are f=(0,1,2,3). The six-unit outcomes are d=(0,0,1,1,2,3),
with class labels (0,0,1,1,2,3). The four-state design has
Omega={0,1} x {0,1}, probability 1/4 at each (r,t), and sample
{r,t+2,4,5}.

For real p and gamma write

    bl(p,gamma) = p/(gamma(1-p)+p).
    bh(p,gamma) = gamma p/((1-p)+gamma p).
    I(p,gamma) = [bl(p,gamma),bh(p,gamma)].
    Q(p,pi1,pi0) = (p/pi1)/(p/pi1+(1-p)/pi0).
    O(pG,pE) = pG(1-pE)/((1-pG)pE).

Closed interval [a,b] means the set of real x with a <= x <= b; nonempty
intersection means there exists such a real in both intervals. Square root is
Mathlib's nonnegative real square root, zero on negative inputs.

For natural N,s, D(N,s) is the finite set of ALL s-element subsets of
{0,...,N-1}; m(N,s,i) is the number of those subsets containing i divided by
the real number of all those subsets. These are separate uniform subset laws.
The application list is
[(48,44),(16,4),(864,291),(288,288),(12,4),(1156,291),(289,288)].
Finally

    F(x,z) = (c1 + x p u + z q v)/(c2 + x p + z q),

with c1,c2,p,q,u,v treated as fixed parameters when this notation is used.

Mathlib source checks: `Order/Bounds/Defs.lean` (IsLeast, its order-dual
IsGreatest, lower/upper bounds), `Order/Monotone/Defs.lean` (Monotone,
StrictMono), `Order/Interval/Set/Defs.lean` (Icc),
`Data/Finset/Powerset.lean` (powersetCard and its membership/cardinality),
`Order/ConditionallyCompleteLattice/Defs.lean` and
`Algebra/Order/Archimedean/Real/Basic.lean` (real infima/suprema),
`Basic/Real/Basic.lean` (real field), `Analysis/Real/Sqrt.lean` (square root).
SAP definitions add no further predicates beyond those expanded above.

## SAP.P025a.T1

A conjunction with no global hypotheses:

1. 0 < 1/2 <= 1; b is nondecreasing; CP(b,1,2,0);
   L(b,1,2,0)=1/2; L(b,1,2,1)=1/3; CH(b,1,2,1);
   H(b,1,2,1)=2/3; 1/2-1/3=1/6. For every real u, then v,
   if 1<=u<=2 and 1<=v<=2, then 1/3<=v/(u+v)<=2/3.
2. A(b,1,1/2,1)=[1/3,2/3], and 1/3 is not in [1/2,2/3].
3. In the fixed two-state design all state probabilities are nonnegative,
   their sum is 1, every inclusion number equals the corresponding pi_i,
   and the sum of state probabilities for which s(omega)={0,1} is 1/2.
4. For every natural n, then a proof n>0, then y on Fin n, if y is
   nondecreasing, then for every real gamma>=1: CP(y,1,gamma,0),
   L(y,1,gamma,0)=mean(y); moreover, if gamma>1 and there exists an i with
   y_0<y_i, then L(y,1,gamma,1)<L(y,1,gamma,0), and
   L(y,1,gamma,0) is not a least element of An(y,1,gamma).

The vectors denoted 1 are constant one vectors of the appropriate dimension.

## SAP.P025a.T2

A closed conjunction: every coordinate of pi lies in [1/2,1]; b is strictly
increasing; mean(b)=1/2; CP(b,pi,2,0); L(b,pi,2,0)=2/3;
L(b,pi,2,1)=1/2; H(b,pi,2,1)=4/5; separation holds for (b,pi,2);
1/2<2/3; and for every real u, then v, if 1<=u<=2 and 1<=v<=2,
then 1/2<=v/(u/2+v)<=4/5. No sampling design is quantified here.

## SAP.P025a.T3

For every natural n, proof n>0, and y on Fin n, if y is nondecreasing,
then for every real alpha, then beta, if 0<alpha, alpha<=beta, beta<=1,
put gamma=beta/alpha. Both H(y,1,gamma,n-1)<=y_{n-1} and
L(y,1,gamma,n-1)<=y_{n-1}. There exist cuts kL,kH in {0,...,n-1}
(chosen after n,y,alpha,beta, before all further universal choices) with ALL
of the following properties:

* CL(y,1,gamma,kL) and CH(y,1,gamma,kH).
* The vectors wL=(1/beta)l(gamma,kL) and wH=(1/beta)h(gamma,kH)
  both belong to B(alpha,beta). Their ratios are respectively
  L(y,1,gamma,kL) and H(y,1,gamma,kH).
* Those two values are respectively the least and greatest members of
  A(y,1,alpha,beta), equal respectively to lo and hi, and
  A(y,1,alpha,beta) is the entire closed interval between them.
* For EVERY real z in that interval there EXISTS a real t in [0,1] such
  that w=(1/beta)((1-t)l(gamma,kL)+t h(gamma,kH)) belongs to B(alpha,beta)
  and R(y,1,w)=z. This is an existence assertion, with no formula for t
  and no separate continuity assertion.
* For EVERY k in {0,...,n-1}, including its last member,

      L(k+1)-L(k) = (gamma-1)(y_k-L(k))/(sum_i l_i(gamma,k+1)),
      H(k+1)-H(k) = (1-gamma)(y_k-H(k))/(sum_i h_i(gamma,k+1)),

  with the same y, unit masses, and gamma in L and H.
* Put m=L(y,1,gamma,kL). For every i<kL, y_i<m; for every i>=kL,
  m<=y_i. For EVERY vector u, if 1<=u_i<=gamma for every i, then

      R(y,1,u)-m = sum_i (u_i-l_i(gamma,kL))(y_i-m)/(sum_i u_i),

  every numerator summand is nonnegative, and R(y,1,u)-m>=0.

## SAP.P025a.T4

For every natural J, proof J>0, vectors y,mass on Fin J, proof y is
strictly increasing, proof every mass_j>0, then real alpha,beta, with
0<alpha<=beta<=1, there EXIST kL,kH in {0,...,J-1} such that, for
gamma=beta/alpha: CL(y,mass,gamma,kL) and CH(y,mass,gamma,kH);
L(y,mass,gamma,kL) is the least member of A(y,mass,alpha,beta);
H(y,mass,gamma,kH) is its greatest member; and those values equal lo and hi
respectively. Attainment quantifies some feasible weight vector through set
membership, without explicitly identifying that vector.

## SAP.P025a.T5

A closed conjunction of the following numerical and finite-law assertions.

* 48/(48+16)=3/4, 864/(864+288)=3/4, 48/(48+12)=4/5,
  1156/(1156+289)=4/5; as natural-number counts, 44+4=48 and 291+288=579.
  The numbers 11/12,97/288,291/1156,288/289 each lie in [1/4,1];
  also 1/4<=1/3 (no separate upper bound on 1/3 is asserted).
* Q(44/48,11/12,1/4)=3/4;
  Q(291/579,97/288,1)=3/4;
  Q(44/48,11/12,1/3)=4/5;
  Q(291/579,291/1156,288/289)=4/5.
* (11/12)/(1/4)=11/3>3; 1/(97/288)=288/97<3;
  (11/12)/(1/3)=11/4<3; (288/289)/(291/1156)=384/97>3;
  (11/3)(288/97)=1056/97=(11/4)(384/97).
  Also bl(44/48,4)<=3/4<4/5<=bh(291/579,4).
* Each of 249/917,503/1491,332/917,503/1988 lies in [1/4,1].
  The following FORWARD selected prevalences have the exact listed values:

      ((3/4)*1)/((3/4)*1+(1-3/4)*(249/917)) = 917/1000,
      ((3/4)*(503/1491))/((3/4)*(503/1491)+(1-3/4)*1) = 503/1000,
      ((4/5)*1)/((4/5)*1+(1-4/5)*(332/917)) = 917/1000,
      ((4/5)*(503/1988))/((4/5)*(503/1988)+(1-4/5)*1) = 503/1000.

  Also 1491/503<3 and 917/332<3.
* Each D(N,s) for the seven listed pairs is nonempty. For EVERY unit i
  in its respective stratum the marginal m(N,s,i), in list order, is
  11/12, 1/4, 97/288, 1, 1/3, 291/1156, 288/289.
* For EVERY natural N, then s, IF (N,s) belongs to the application list,
  D(N,s) is nonempty, sum_{t in D(N,s)} 1/|D(N,s)|=1, and EVERY
  t in D(N,s) has cardinality s. There is no joint product law in the statement.
* 91.7-0.05<=100(44/48)<91.7+0.05 and
  50.3-0.05<=100(291/579)<50.3+0.05.
* Both 3/4 and 4/5 belong to EACH of I(44/48,4) and I(291/579,4).

## SAP.P025a.T6

A conjunction of seven universally quantified or numerical parts:

1. For every real pG, then pE, then gamma, if 0<pE<pG<1 and gamma>=1,
   (I(pG,gamma) intersect I(pE,gamma) is nonempty) iff
   bl(pG,gamma)<=bh(pE,gamma); that inequality iff O(pG,pE)<=gamma^2;
   and nonempty intersection iff sqrt(O(pG,pE))<=gamma.
2. O(917/1000,503/1000)=455749/41749, strictly between 3.30^2 and
   3.31^2; O(44/48,291/579)=1056/97, strictly between 3.29^2 and
   3.30^2. Each rational odds ratio is strictly between 9 and 16.
   Also (11/3)(288/97)=1056/97 and 288/97<3;
   (11/4)(384/97)=1056/97 and 11/4<3.
3. For every real gamma>=1 the two numerical interval intersections are
   nonempty iff respectively sqrt(455749/41749)<=gamma and
   sqrt(1056/97)<=gamma.
4. Each of those two pairs of intervals has empty intersection at gamma=3
   and nonempty intersection at gamma=4.
5. For every real p, then pi1, then pi0, if 0<p<1, pi1>0, pi0>0,
   put q=Q(p,pi1,pi0). Then q=p*pi0/(p*pi0+(1-p)*pi1), and
   q/(1-q)=(p/(1-p))*(pi0/pi1).
6. For every real pG,pE,g1,g0,e1,e0 in that order, if
   0<pE<pG<1 and g1,g0,e1,e0>0, then
   Q(pG,g1,g0)=Q(pE,e1,e0) iff (g1/g0)(e0/e1)=O(pG,pE).
7. For every real pG,pE,g1,g0,e1,e0,gamma in that order, if
   0<pE<pG<1, all four selection numbers are positive,
   Q(pG,g1,g0)=Q(pE,e1,e0), g1/g0<=gamma, e0/e1<=gamma,
   then O(pG,pE)<=gamma^2. There is no explicit gamma>=1 hypothesis
   or upper bound of 1 on the four selection numbers in parts 5-7.

Finally 3.30399<sqrt(455749/41749)<3.30400 and
3.29948<sqrt(1056/97)<3.29949.

## SAP.P025a.T7

The conjunction of the negation of a universal printed statement and a valid
universal upper statement. The NEGATED universal statement is:

For every natural n>0, y on Fin n with y nondecreasing, then real
0<alpha<=beta<=1, there exist kL,kH in {0,...,n-1} such that, with
gamma=beta/alpha, CP(y,1,gamma,kL), CH(y,1,gamma,kH),
L(y,1,gamma,kL) is least in A(y,1,alpha,beta), H(y,1,gamma,kH)
is greatest in that set, and the set equals the closed interval between them.

Thus the first conjunct says at least one admissible instance of that entire
existence statement fails; it does not assert failure for every instance.
The second conjunct says: for EVERY n>0 and nondecreasing y, then every
0<alpha<=beta<=1, there EXISTS kH in {0,...,n-1} with CH(y,1,beta/alpha,kH)
and H(y,1,beta/alpha,kH) a greatest member of A(y,1,alpha,beta).
No counterexample witness is explicitly returned in this theorem.

## SAP.P025a.T8

The conjunction of the negation of the following universal class statement
and an independent universal upper statement. The NEGATED statement is:

For every natural J>0, y and mass on Fin J, y strictly increasing and all
mass_j>0, then every real 0<alpha<=beta<=1, there exist kL,kH in
{0,...,J-1}, with gamma=beta/alpha, such that CP(y,mass,gamma,kL),
CH(y,mass,gamma,kH); L(y,mass,gamma,kL) is least in A(y,mass,alpha,beta);
H(y,mass,gamma,kH) is greatest in that set;
P(y,mass,gamma,kL)=Some(lo(y,mass,alpha,beta)); and
hi(y,mass,alpha,beta)=H(y,mass,gamma,kH).

The second conjunct is: for EVERY J>0, strictly increasing y, strictly
positive mass vector, then 0<alpha<=beta<=1, there EXISTS kH with
CH(y,mass,beta/alpha,kH), H(y,mass,beta/alpha,kH) a greatest member of
A(y,mass,alpha,beta), and hi equal to that same H value.
The negation alone does not isolate which conjunct of the printed claim fails.

## SAP.P025a.T9

For every natural J>0, vectors y,mass on Fin J, if y is strictly increasing
and every mass_j>0, then for every real alpha, then beta with
0<alpha<=beta<=1, put gamma=beta/alpha. ALL of these hold:

* For EVERY natural k<=J, R(y,mass,w)=N_k/D_k for the vector
  w_i=1/alpha if i<k and 1/beta otherwise.
* For EVERY k in {0,...,J-1}, IF CL(y,mass,gamma,k), then
  lo(y,mass,alpha,beta)=N_k/D_k.
* For EVERY natural k with 2<=k<=J, put u=k-2, v=k-1 (valid class
  indices), N=N_k, D=D_k. Then

      P(y,mass,gamma,k)=Some((N+mass_u*y_u+mass_v*y_v)/(D+mass_u+mass_v)),
      (N+mass_u*y_u+mass_v*y_v)/(D+mass_u+mass_v)-N/D
        = (mass_u*(y_u-N/D)+mass_v*(y_v-N/D))/(D+mass_u+mass_v).

* P(y,mass,gamma,0)=None and P(y,mass,gamma,1)=None.

The corrected-cut conditional does not itself assert existence of a corrected cut.

## SAP.P025a.T10

A closed conjunction about f=(0,1,2,3), unit class masses, gamma=2, and
the fixed six-unit/four-state design:

* f is strictly increasing; CL(f,1,2,2); L(f,1,2,2)=7/6;
  P(f,1,2,2)=Some(1); CP(f,1,2,0); P(f,1,2,0)=None; 1!=7/6;
  and for EVERY real vector w on Fin 4, if 1<=w_i<=2 for every i,
  then 7/6<=R(f,1,w).
* All four state probabilities are nonnegative and sum to 1. For EVERY unit
  the inclusion number is its entry of (1/2,1/2,1/2,1/2,1,1).
  For EVERY class its inclusion total is 1 and its cardinality is its entry
  of (2,2,1,1). The six-unit mean is 7/6.
* L(f,1,2,0)=3/2 and L(f,1,2,1)=6/5.
* For EVERY class j, its real cardinality divided by its inclusion total
  equals l_j(2,2), i.e. (2,2,1,1).

## SAP.P025a.T11

A conjunction of three universally quantified parts, independently quantified:

1. For EVERY natural n>0, y on Fin n, if y is nondecreasing, then for
   EVERY real gamma>=1:

   * For EVERY k in {0,...,n-1},
     H(k+1)-H(k)=(1-gamma)(y_k-H(k))/(sum_i h_i(gamma,k+1)),
     with unit masses throughout.
   * IF gamma=1, then for EVERY natural k (no upper bound),
     H(k)=mean(y), L(k)=mean(y), and for EVERY vector w,
     membership in Bn(gamma) is equivalent to w being the constant one vector.
   * IF gamma>1, the set of k with H(k)>=H(k+1) equals the set of k
     with H(k)<=y_k; both sets range only over {0,...,n-1}.
   * For EVERY k in that range, IF H(k)<=y_k, then H(k+1)<=y_k.
   * IF gamma>1, then for EVERY such k,
     H(k+1)-H(k)<=0 iff H(k)<=y_k.

2. For EVERY real c1,c2,p,q,u,v,a,b in that order, if
   c2>=0, p>0, q>0, a>0, a<=b, u<v, put

       A = c2*u-c1+a*q*(u-v),
       B = c1-c2*v+b*p*(u-v).

   Then

       (c2+a*p+a*q)(c2+b*p+a*q)(F(a,a)-F(b,a))=(a-b)*p*A,
       (c2+b*p+b*q)(c2+b*p+a*q)(F(b,b)-F(b,a))=(a-b)*q*B,
       A+B=(c2+b*p+a*q)(u-v),
       A+B<0.

3. For EVERY real c1,c2,p,q,u,v,a,b, under exactly those SAME hypotheses,
   IF a<b, then F(a,a)>F(b,a) iff A<0, F(b,b)>F(b,a) iff B<0,
   and F(a,a)>F(b,a) OR F(b,b)>F(b,a).
   IF a=b, then F(a,a)=F(b,a) and F(b,b)=F(b,a).

There is no restriction on c1, and c2 may be zero. The statement contains
no population calibration, original-scale probability bounds, endpoint formula,
or existence/identification of a first stationary index.
