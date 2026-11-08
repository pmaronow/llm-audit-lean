# Blind reading of the Lean statements

This file was written from `SAP/P025b/Defs.lean`, all seven `Defs/Part*.lean`
files, and the two Challenge files, before opening either `claims.json` or
`record.json`. The descriptions below report the propositions themselves;
the Challenge docstrings are not treated as additional hypotheses or conclusions.

## Shared notation, fully expanded

`Fin n` is the ordered set of integers 0,...,n-1. All displayed divisions below
are real divisions, with integer and natural-number arguments cast to the reals.
Lean real division is total, and division by zero gives zero. Natural subtraction
is truncated; this occurs below only in `1000-k`, under k <= 750.

For a finite index set I and real vectors y,a,w, put

    R(y,a,w) = (sum_i a_i w_i y_i)/(sum_i a_i w_i).

For n observations, `populationMean y` is (sum_i y_i)/n. Define

    B(alpha,beta) = {w : for every i, 1/beta <= w_i <= 1/alpha},
    Bnorm(gamma) = {w : for every i, 1 <= w_i <= gamma},
    A(y,a;alpha,beta) = {R(y,a,w) : w in B(alpha,beta)},
    Anorm(y,a;gamma) = {R(y,a,w) : w in Bnorm(gamma)},
    L(y,a;alpha,beta) = sInf A(y,a;alpha,beta),
    H(y,a;alpha,beta) = sSup A(y,a;alpha,beta).

Here sInf and sSup are Mathlib's real, conditionally complete lattice operations.
For nonempty bounded sets they are the usual infimum and supremum. On an empty
set each is zero; inappropriate unbounded sets also invoke totalized conventions.
They do not, by themselves, assert nonemptiness, boundedness, or attainment.
For the positive boxes and positive total masses used here, R has a positive
denominator and A is a nonempty bounded set. For an empty pooled sample R is 0
for every feasible w, so A = {0} and its two endpoints are 0.

For any natural prefix length k (including k = n), define the normalized vectors

    l(gamma,k)_i = gamma if i < k, and 1 otherwise;
    u(gamma,k)_i = 1 if i < k, and gamma otherwise;
    lval(y,a;gamma,k) = R(y,a,l(gamma,k));
    uval(y,a;gamma,k) = R(y,a,u(gamma,k)).

`lowerCut y a gamma k` says k in {0,...,n-1} is the least j with
lval(y,a;gamma,j) <= y_j. Thus this inequality holds at k and every j satisfying
it has k <= j. `upperCut` has the identical definition with uval. The comparison
is non-strict in both definitions. `separation y a gamma` says, for EVERY
k = 0,...,n-1, both y_k != uval(y,a;gamma,k) and
y_k != lval(y,a;gamma,k). It says nothing about k = n or a sentinel outcome.

`Monotone y` means i <= j implies y_i <= y_j; `StrictMono y` means i < j implies
y_i < y_j. `IsLeast S x` means x belongs to S and x <= every element of S;
`IsGreatest` reverses this order. `IsGLB S x` says x is a lower bound and every
lower bound is <= x; `IsLUB` is the upper-bound counterpart. Unlike IsLeast and
IsGreatest, these latter predicates do not assert that x belongs to S.
`Set.Icc a b` is the closed interval {x : a <= x and x <= b}.

The binary formulas, defined for real p,gamma, are

    bL(p,gamma) = p/[gamma(1-p)+p],
    bH(p,gamma) = gamma p/[(1-p)+gamma p].

`binaryTwo` is the vector (0,1).

A `FiniteDesign I K` consists of a finite-outcome sample map s:K -> finite subsets
of I and real probabilities p_omega >= 0 with sum p_omega = 1. Its expectation
is the finite sum E_d X = sum_omega p_omega X(omega). Its inclusion probability
is pi_i = sum_omega p_omega 1_{i in s(omega)}. For a class map c:I -> Fin J,

    Pi_j = classTotal d c j = sum_{i:c(i)=j} pi_i,
    C_j(omega) = classCount d c j omega
                 = sum_i 1_{c(i)=j and i in s(omega)}.

The PMF has mass ENNReal.ofReal(p_omega), hence precisely p_omega because the
probabilities are nonnegative. `jointLaw d` is the countable product of this PMF's
probability measure on K^N. Thus the replicate labels omega_0,omega_1,... are
independent with this common finite law. The statements using almost-sure
convergence require a measurable space on K and measurable singletons; on a
finite K this makes every subset measurable. The measure is a genuine probability
measure, not a zero-measure fallback.

For h >= 0, a path omega:N -> K is pooled by the index set Fin h x I. The outcome
of (r,i) is y_{c(i)} and its coefficient a_{r,i} is 1_{i in s(omega_r)}.
`pooledLower` and `pooledUpper` are L and H of these vectors with the same bounds
alpha,beta. Each selected occurrence has its own independently selectable box
weight; nonselected occurrences have coefficient zero. `pooledNonempty d h omega`
means there exists r < h for which s(omega_r) is nonempty.

Write PC(d,c,y,alpha,beta) for the following expanded `PooledConvergence`:
outside a jointLaw(d)-null set of paths omega, there exists h0 (depending on omega)
such that every h >= h0 has a nonempty pooled sample, and, on that same path,

    lim_{h -> infinity} pooledLower(d,c,y,alpha,beta,h,omega)
      = L(y,Pi;alpha,beta),
    lim_{h -> infinity} pooledUpper(d,c,y,alpha,beta,h,omega)
      = H(y,Pi;alpha,beta).

Limits are ordinary real limits: for every epsilon > 0, eventually the absolute
error is < epsilon. The definitions involve no limsup or integral.

For class sizes m:Fin J -> N define

    AC(alpha,beta,mass,m) iff for every j,
      m_j > 0 and alpha m_j <= mass_j <= beta m_j;
    SC(alpha,beta,q,m) iff there exists T > 0 with
      AC(alpha,beta,Tq,m);
    M(y,m) = (sum_j m_j y_j)/(sum_j m_j);
    CM(y,q;alpha,beta) = {M(y,m) : m in N^J, SC(alpha,beta,q,m)};
    ACM(y,mass;alpha,beta) = {M(y,m) : m in N^J, AC(alpha,beta,mass,m)};
    KCM(y,mass;alpha,beta,N)
      = {M(y,m) : m in N^J, AC(alpha,beta,mass,m), sum_j m_j = N}.

The proportional region PR(q,gamma) consists of r:Fin J -> R satisfying

    every r_j >= 0, sum_j r_j = 1,
    and for every ORDERED pair j,k, r_j q_k <= gamma r_k q_j.

The class proportions of m are r_j = m_j/(sum_k m_k). Weight proportions for q,W
are r_j = W_j q_j/(sum_k W_k q_k). `rationalVector r` says every r_j is the real
image of some rational number (the rational witness may depend on j).

Mathlib definitions inspected: `Order/Bounds/Defs.lean` (bounds, least/greatest and
GLB/LUB), `Order/Monotone/Defs.lean`, `Order/Interval/Set/Defs.lean`,
`Algebra/Order/Archimedean/Real/Basic.lean` (real sInf/sSup),
`Probability/ProbabilityMassFunction/Constructions.lean` (`ofFintype`),
`Probability/ProbabilityMassFunction/Basic.lean` (`toMeasure`),
`Probability/ProductMeasure.lean` (`Measure.infinitePi` and finite-cylinder laws),
`MeasureTheory/MeasurableSpace/Defs.lean`, `MeasureTheory/OuterMeasure/AE.lean`,
`Order/Filter/AtTopBot/Defs.lean`, and `Order/Filter/Defs.lean` (`Eventually`,
`Tendsto`). All SAP definitions used by the ten statements are expanded here or
in their concrete instances below.

## SAP.P025b.T12

This is a closed conjunction with no hypotheses and no outer parameters. The
design is the census on I = Fin 2, K = Fin 1: its only outcome has probability 1
and sample {0,1}. It asserts:

1. For every i in Fin 2, pi_i = 1, and (0,1) is nondecreasing.
2. For every natural k, u(1,k) is the constant-one vector.
3. 1/1 = 1 and uval((0,1),1;1,k) = 1/2 for each k = 0,1,2.
4. uval at k=1 minus uval at k=0 is <= 0, but uval at k=0 is NOT <= y_0 = 0.
5. The least k in Fin 2 satisfying uval(k) >= uval(k+1) is 0.
6. The upperCut for y=(0,1), a=1, gamma=1 is 1. Thus the least index satisfying
   uval(k) <= y_k is 1.
7. The two literal real arithmetic expressions
   0*0-0+1*1*(0-1) and 0-0*1+1*1*(0-1) each equal -1.
8. R((0,1),1,(1,1)) is not strictly greater than itself.

There is no assertion here about the entire feasible weight box or the sInf/sSup
endpoints, despite their computability in this example.

## SAP.P025b.T13

Quantifiers and hypotheses, in order: for every N,J in N, if N > 0 and J > 0,
then for every type K with a finite enumeration, measurable space and measurable
singletons, every finite design d on Fin N with outcomes K, and every class map
c:Fin N -> Fin J, if c is surjective, then for every strictly increasing real
vector y on Fin J and all real alpha,beta with 0 < alpha <= beta <= 1, if every
population unit has alpha <= pi_i <= beta, the conclusion is

    PC(d,c,y,alpha,beta)
    AND [separation(y,Pi,beta/alpha) implies PC(d,c,y,alpha,beta)].

PC and separation have exactly the meanings and quantifiers expanded above.
In particular PC holds without separation; the second conjunct repeats its
consequence under an extra condition. The theorem does not presume endpoint
convergence as an input or assume eventual pooled nonemptiness as an input.

## SAP.P025b.T14

A closed conjunction with no hypotheses. There are six units (j,b) in
Fin 3 x Fin 2, three classes c(j,b)=j, and class outcomes y=(0,2,3). The eight
design outcomes are triples (b0,b1,b2), each of probability 1/8; the selected
sample is {(0,b0),(1,b1),(2,b2)}. It asserts:

1. Every unit's inclusion probability is 1/2. Every class total Pi_j is 1.
   For every one of the eight design outcomes and every class j, C_j = 1.
2. uval(y,1;2,1) = uval(y,1;2,2) = 2.
3. 5/4 is an attained minimum of A(y,1;1/4,1/2), and 2 is an attained maximum.
4. For EVERY path omega:N -> (Fin 2)^3 and EVERY natural h > 0, its pooled sample
   is nonempty.
5. Every unit satisfies the bounds 1/4 <= pi_i <= 1/2, but
   separation(y,Pi,2) fails.
6. L(y,Pi;1/4,1/2) = 5/4 and H(y,Pi;1/4,1/2) = 2.
7. For EVERY path and EVERY h > 0, the pooled lower and upper endpoints equal
   5/4 and 2 respectively.
8. For EVERY path, the two sequences indexed by all h >= 0 tend to 5/4 and 2.

These last limits are pathwise, not merely almost sure. No optimizer vectors,
polynomial certificates or pooled class-weight-image identity are asserted.

## SAP.P025b.T15

Quantifiers/hypotheses, in order: every J > 0; every y,q:Fin J -> R with y strictly
increasing, all q_j > 0 and sum_j q_j = 1; every real alpha,beta with
0 < alpha <= beta <= 1; and the existence of at least one positive integer class
vector m with SC(alpha,beta,q,m). UNDER ALL these hypotheses, the following
conjuncts hold simultaneously (put gamma = beta/alpha):

1. For every m in N^J and mass in R^J, if each mass_j > 0 and
   AC(alpha,beta,mass,m), then the vector W_j=m_j/mass_j belongs to
   B(alpha,beta) and R(y,mass,W)=M(y,m).
2. For every m in N^J satisfying SC(alpha,beta,q,m),
   L(y,q;alpha,beta) <= M(y,m) <= H(y,q;alpha,beta).
3. L(y,q;alpha,beta) is the greatest lower bound of CM(y,q;alpha,beta), and
   H(y,q;alpha,beta) is its least upper bound. Attainment by an integer population
   is not asserted in this conjunct.
4. The set of weight proportions obtained from every W in B(alpha,beta) equals
   PR(q,gamma), as sets of real J-vectors.
5. Over the real vectors r in PR(q,gamma), the linear functional
   sum_j r_j y_j has an attained minimum L(y,q;alpha,beta) and attained maximum
   H(y,q;alpha,beta).
6. For every real vector r, there exists an m in N^J with
   SC(alpha,beta,q,m) and classProportions(m)=r IF AND ONLY IF
   r belongs to PR(q,gamma) and every coordinate of r is rational.
7. L(y,q;alpha,beta) belongs to CM IF AND ONLY IF there exists a rational-coordinate
   r in PR with sum_j r_j y_j = L(y,q;alpha,beta). The analogous equivalence holds
   for H and its maximizing level.
8. For every real mass vector and every natural m vector,
   AC(alpha,beta,mass,m) IF AND ONLY IF every j satisfies
   m_j>0 and mass_j/beta <= m_j <= mass_j/alpha.
9. For every mass with all mass_j>0, and every m satisfying AC,
   L(y,mass;alpha,beta) <= M(y,m) <= H(y,mass;alpha,beta).
10. For every mass, natural N and real v, v belongs to KCM(y,mass;alpha,beta,N)
    IF AND ONLY IF there exists m in N^J such that every
    m_j>0 and mass_j/beta <= m_j <= mass_j/alpha, sum_j m_j=N, and M(y,m)=v.
11. For every mass and m, AC(alpha,beta,mass,m) IF AND ONLY IF all m_j>0 and,
    for every j, there exists a vector pi:Fin(m_j) -> R whose entries lie in
    [alpha,beta] and whose sum is mass_j.

In item 11 the probability-vector witness may depend on j. This item concerns
per-unit marginal numbers, and does not explicitly construct a joint sampling
law. Items 8-11 are also under the initial q-compatibility existence hypothesis.
The statement has no existential example of failure of sharpness when mass or N
is fixed, and no automatic existence theorem for compatible populations.

## SAP.P025b.T16

A closed conjunction with no hypotheses, comprising the following two examples
and continuous-box certificates.

First example: I=K=Fin 3, each outcome omega has probability 1/3 and sample
Fin 3 minus {omega}. Unit outcomes are (0,1,1), class map is (0,1,1), class
outcomes are (0,1), bounds are alpha=1/2,beta=3/4, and mass=(2/3,4/3).
The assertions are:

1. Every inclusion probability is 2/3; the two class totals are 2/3 and 4/3;
   the actual three-unit population mean is 2/3.
2. For every m in N^2, AC(1/2,3/4,mass,m) iff m=(1,2).
   M((0,1),(1,2))=2/3.
3. lval((0,1),mass;3/2,1)=4/7 and uval((0,1),mass;3/2,1)=3/4.
   The differences (2/3)-(4/7)=2/21 and (3/4)-(2/3)=1/12;
   4/7 < 2/3 < 3/4; separation((0,1),mass,3/2) holds.
4. ACM((0,1),mass;1/2,3/4)={2/3}. The number 4/7 is not its GLB and 3/4 is not
   its LUB.

Second example: class outcomes (0,1), mass=(50,100), alpha=1/10,beta=1/5,
and total population size N=1000. The assertions are:

5. For every m in N^2,
   [AC(1/10,1/5,mass,m) and m_0+m_1=1000] iff
   [m_0+m_1=1000 and 500 <= m_1 <= 750].
6. For every natural k, if 500 <= k <= 750, then
   AC(1/10,1/5,mass,(1000-k,k)).
7. M((0,1),(250,750))=3/4; lval((0,1),mass;2,1)=1/2;
   uval((0,1),mass;2,1)=4/5; (4/5)-(3/4)=1/20 and 3/4 < 4/5.
8. KCM((0,1),mass;1/10,1/5,1000)
   = {k/1000 : k natural, 500 <= k <= 750}.
   Its attained minimum is 1/2 and its attained maximum is 3/4.
   H((0,1),mass;1/10,1/5)-(3/4)=1/20.

Finally, 4/7 and 3/4 are respectively an attained minimum and maximum of
A((0,1),(2/3,4/3);1/2,3/4), and 1/2 and 4/5 are respectively an attained
minimum and maximum of A((0,1),(50,100);1/10,1/5).

There is no explicit six-hundred-or-more-unit sampling design in the second
example; its class-count compatibility and exact mean set are asserted.

## SAP.P025b.T17

A closed conjunction with no hypotheses. Define F(p,gamma,false)=100 bL(p,gamma)
and F(p,gamma,true)=100 bH(p,gamma). Define rounding Q(x,t), for natural t, by

    t/10 - 1/20 <= x < t/10 + 1/20.

Thus t represents a percentage to one decimal place, with the lower tie included
and the upper tie excluded. The assertions are:

1. For EVERY integer k, |100k/48 - 917/10| <= 1/20 iff k=44;
   |100k/160 - 675/10| <= 1/20 iff k=108; and
   |100k/579 - 503/10| <= 1/20 iff k=291. These inference windows use <= on
   both sides, unlike the half-open Q predicate.
2. Six exact percentage identities hold:

       100 bL(44/48,2)       = 1100/13,
       100 bL(44/48,4)       = 220/3,
       100 bH(291/579,5/4)   = 48500/869,
       100 bL(291/579,3/2)   = 9700/241,
       100 bH(291/579,3/2)   = 9700/161,
       100 bH(291/579,5/2)   = 48500/677.

3. For every row of the literal list below, in gamma order
   1, 5/4, 3/2, 2, 5/2, 3, 4, both low and high Q assertions hold. Each cell
   pair (t_input,t_exact) means
   Q(F(p_exact,gamma,side),t_exact) AND
   Q(F(p_input,gamma,side),t_input):

| p_exact | p_input | side | seven (t_input,t_exact) pairs |
| --- | --- | --- | --- |
| 44/48 | 917/1000 | low | (917,917), (898,898), (880,880), (847,846), (815,815), (786,786), (734,733) |
| 44/48 | 917/1000 | high | (917,917), (932,932), (943,943), (957,957), (965,965), (971,971), (978,978) |
| 108/160 | 675/1000 | low | (675,675), (624,624), (581,581), (509,509), (454,454), (409,409), (342,342) |
| 108/160 | 675/1000 | high | (675,675), (722,722), (757,757), (806,806), (839,839), (862,862), (893,893) |
| 291/579 | 503/1000 | low | (503,503), (447,447), (403,402), (336,336), (288,288), (252,252), (202,202) |
| 291/579 | 503/1000 | high | (503,503), (559,558), (603,602), (669,669), (717,716), (752,752), (802,802) |

4. The list has length 42, exactly six entries have t_input != t_exact, and in
   every entry either t_input=t_exact or t_input=t_exact+1.
5. bL(44/48,3)=11/14, bH(291/579,3)=291/387, and the former is strictly larger.
   bL(44/48,4)=11/15, bH(291/579,4)=97/121, and the former is strictly smaller.
6. For every real gamma in the finite set {1,5/4,3/2,2,5/2,3},
   bH(291/579,gamma) < bL(44/48,gamma), AND
   bH(503/1000,gamma) < bL(917/1000,gamma).
7. At gamma=4, the number 4/5 lies in BOTH closed binary intervals using
   p=44/48 and p=291/579. It also lies in BOTH intervals using
   p=917/1000 and p=503/1000.

## SAP.P025b.T18

For every natural n>0, every real vector y on Fin n, and every four reals
alpha,beta,alpha',beta', assume in order 0<alpha<=beta<=1,
0<alpha'<=beta'<=1, and beta/alpha=beta'/alpha'. With a identically one,
the conclusions, all simultaneous, are:

1. A(y,1;alpha,beta)=A(y,1;alpha',beta').
2. A(y,1;alpha,beta)=Anorm(y,1;beta/alpha).
3. The two L endpoints agree, and the two H endpoints agree, between the two
   pairs of probability bounds.
4. IF beta/alpha=1, then for EVERY real weight vector w,
   [w in B(alpha,beta)] iff [w is identically 1/alpha], and
   L(y,1;alpha,beta)=H(y,1;alpha,beta)=(sum_i y_i)/n.

The statement covers arbitrary real outcomes and imposes no sorting requirement.

## SAP.P025b.T19

For every natural n>0, every nondecreasing y:Fin n -> R, and every real
alpha,beta with 0<alpha<=beta<=1, for EVERY kL,kH in Fin n, IF
lowerCut(y,1,beta/alpha,kL) and upperCut(y,1,beta/alpha,kH), THEN for EVERY
i,j in Fin n with y_i=y_j, BOTH equalities hold:

    (1/beta) l(beta/alpha,kL)_i = (1/beta) l(beta/alpha,kL)_j,
    (1/beta) u(beta/alpha,kH)_i = (1/beta) u(beta/alpha,kH)_j.

The prefix inequalities defining these weights are strict i<kL or i<kH; the
inequalities defining the first valid cuts are non-strict lval<=y_k and
uval<=y_k. The theorem is conditional on supplied valid cuts and does not itself
assert existence of either cut, a no-cut-through-ties characterization, or any
recurrence identity.

## SAP.P025b.T20

For every natural n>0, every y:Fin n -> R such that for EVERY i, y_i=0 OR y_i=1,
and every real alpha,beta with 0<alpha<=beta<=1, put
p=(sum_i y_i)/n and gamma=beta/alpha. The simultaneous conclusions are:

1. A(y,1;alpha,beta) is EXACTLY the closed interval [bL(p,gamma),bH(p,gamma)].
2. L(y,1;alpha,beta)=bL(p,gamma) and H(y,1;alpha,beta)=bH(p,gamma).
3. If p=0 then both binary formulas are 0; if p=1 then both are 1.
4. If gamma=1 then both binary formulas are p.

There is no sorting hypothesis. The binary formulas have positive denominators
since 0<=p<=1 and gamma>=1.

## SAP.P025b.T21

The universal variables and hypotheses occur in the same order as T13:
N,J in N positive; finite K with a measurable space and measurable singletons;
design d on Fin N with outcomes K; surjective c:Fin N -> Fin J; strictly
increasing real y; real 0<alpha<=beta<=1; every unit's pi_i in [alpha,beta].
There is THEN one further hypothesis:

    for every k in Fin J,
    y_k != uval(y,Pi;beta/alpha,k) AND
    y_k != lval(y,Pi;beta/alpha,k).

Under these hypotheses the conclusion is PC(d,c,y,alpha,beta), including
almost-sure eventual pooled nonemptiness and both endpoint limits. In particular
the separation requirement is only on k=0,...,J-1 and both limit endpoints use
the actual class totals Pi, not their normalized shares.
