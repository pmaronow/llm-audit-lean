# Blind reading

This file was saved before opening either `claims.json` or `record.json`.
The sources read were the five docstrings and declarations in
`SAP/P003b/Challenge/Part1.lean`, every source definition named by their
closures, and the generated declarations printed by `scratch/BlindPrint.lean`.
No assessment against an external claim is made here.

## SAP.P003b.T26

There are no free parameters or hypotheses. This is a conjunction certifying
one finite example, rather than a universal coverage theorem.

The four natural-number coordinates of a `Counts` value are ordered
`(11,10,01,00)`. For a potential-outcome population v=(a,b,c,d), write
N=a+b+c+d, e=b-c (subtraction in the integers), and tau(v)=e/N, first
calculated in the rationals and then embedded in the reals. For observed
counts o=(A,B,C,D), T(o)=A/(A+B)-C/(C+D), again rational then real.

The following finite definitions are used in the statement:

* `randomStates v m` lists q=(i,j,k,l) with 0<=i<=a, 0<=j<=b,
  0<=k<=c, 0<=l<=d, i+j+k+l=m. In the actual implementation i ranges to
  min(a,m), j to min(b,m-i), k to min(c,m-i-j), and l=m-i-j-k is
  retained if l<=d. Each tuple occurs once.
* Its multiplicity is w(v,q)=choose(a,i)choose(b,j)choose(c,k)choose(d,l),
  using `Nat.fast_choose`. The observed tuple is
  O(v,q)=(i+j,k+l,a-i+c-k,b-j+d-l).
* For any o, put m=A+B and
  E(v,o,m)=N*((N-m)*A-m*C)-m*(N-m)*(b-c), with all arithmetic in Z.
  The tail count is the sum of w(v,q) over the above q for which
  |E(v,O(v,q),m)|>=|E(v,o,m)|. `pValue v o` is that natural-number
  sum, cast to Q, divided by choose(N,m). Integer absolute values are
  implemented with `Int.natAbs`.
* `possibleTables o` enumerates, for independent integers
  0<=i<=A, 0<=j<=B, 0<=k<=C, 0<=l<=D, the population tuples
  (i+k,A-i+l,C-k+j,B+D-j-l). It can list a tuple repeatedly.
* K(alpha,o)=`accepted alpha o` is the finite set of real numbers tau(v)
  for those enumerated tuples v with alpha<=pValue(v,o). List duplicates
  and duplicate effects are removed by finite-set conversion and image.
  L(alpha,o)=inf K(alpha,o) and U(alpha,o)=sup K(alpha,o) are real
  conditional infimum and supremum.
* A mask r=(rA,rB,rC,rD) in `missingMasks o` is any natural tuple with
  rA<=A, rB<=B, rC<=C, rD<=D. The two completed observations are
  oMinus=(A-rA,B+rA,C+rD,D-rD) and
  oPlus=(A+rB,B-rB,C-rC,D+rC).
* `missingInterval alpha o r` is the closed real interval whose lower
  endpoint is min(L(alpha,oMinus),T(oMinus)) when K(alpha,oMinus) is
  nonempty, and T(oMinus) otherwise; its upper endpoint is
  max(U(alpha,oPlus),T(oPlus)) when K(alpha,oPlus) is nonempty, and
  T(oPlus) otherwise. An interval with lower endpoint exceeding its upper
  endpoint is empty.
* `designProb v m event` is the real sum of multiplicities of states
  satisfying event divided by choose(N,m). This is a finite weighted
  count, not a measure-space primitive.

The fixed population is v=(11,0,3,6). Its mask is r(q)=(0,0,1,0) if
q=(0,0,3,0), and (0,0,0,0) for every other q. The conjunction states:

1. N=20, 0<3<N, 0<109/500<1, and tau(v)=-3/20.
2. For every q in `randomStates v 3`, r(q) is a permitted mask for
   O(v,q), and both K(109/500,oMinus) and K(109/500,oPlus) are nonempty.
3. The weighted proportion of these q for which tau(v) belongs to the
   just-defined missing interval is exactly 297/380.
4. 297/380 < 1-109/500.

The docstring calls this a legal deterministic missingness counterexample to
the printed claim. The statement itself contains no independence requirement
on masks and no fixed-mask requirement.

Junk-value audit: Q and R division by zero returns zero. Here N=20 and
choose(20,3)>0; all observations and their valid completions have treatment
size 3 and control size 17. Every possible population has total 20, so all
effect, estimate, and p-value divisions are proper. Natural subtraction is
truncated, but all subtractions in the state enumeration, observed counts,
possible-table enumeration and valid completions are protected by the
enumerated coordinate bounds. Real infimum and supremum return zero for
the empty set (and also for sets unbounded in the relevant direction);
all accepted sets actually used as endpoints here are explicitly nonempty
and finite. The `missingInterval` fallback on empty accepted sets is an
additional explicit convention, but is inactive in this example. There are
no integrals, extended reals, logs, square roots, powers with real exponent,
limits, empty label types, or partial-function defaults. Casts N->Z->Q->R
are exact. Generated `_proof_1` through `_proof_4` merely certify that the
numerals 109,500,297,380 have at least two elements in Lean's numeral
elaboration; record constructors, recursors, and the derived decision of
coordinate equality add no mathematical condition.

## SAP.P003b.T27

This is the negation of the following universal statement, with quantifiers
in this order: for every k1,k2,r in Z and f:Z->Bool, if
0<k1<k2, k1-1<=r<=k2, and, for every integer x with k1<=x<=k2,
(f(x)=false iff x<=r), then there exist natural numbers steps and
evaluations such that the execution described below returns exactly
`some (r,evaluations)` and

    evaluations <= floor(log(k2-k1+1)/log(2)+2).

The left side of the inequality is cast to R, as is the integer floor on
the right. Thus the theorem asserts failure of universal simultaneous
correctness and the evaluation bound, without naming a witness in its
type. The predicate values outside [k1,k2] are unrestricted.

`searchStep f a b` puts c=(a+b)/2 using Euclidean integer division,
and returns (a,c) when f(c)=true, or (c,b) when f(c)=false.
`printedExecution fuel k1 k2 f a b` is a fuel-bounded recursion:

* fuel=0 returns `none`.
* With positive fuel, first do `searchStep`, yielding (a',b'). If
  b'=a'+1, return (a',1) when a'>k1 and b'<k2. Otherwise, if a'=k1,
  return (k1-1,2) when f(k1)=true and (k1,2) otherwise. Otherwise, if
  b'=k2, return (k2-1,2) when f(k2)=true and (k2,2) otherwise.
  If none of these conditions holds, return `none`.
* If b' is not a'+1, recurse with one less fuel and endpoints (a',b').
  A successful returned pair has its evaluation count increased by one;
  `none` stays `none`.

The universal proposition initializes a=k1,b=k2. `steps` is fuel, not a
separately charged evaluation count. The returned count charges the midpoint
and, on a boundary branch, a further endpoint evaluation, even if repeated.
The order of the two boundary branches is part of the assertion.

Junk-value audit: `logTwo x` is `Real.log x / Real.log 2`. Mathlib's log
has totalized values (log 0=0 and log(-x)=log x), but k2-k1+1>=2,
and log 2 is positive. Neither bad log arguments nor zero denominators
can occur here. Integer division by 2 is floor division, including for
negative arguments; the positive initialized domain keeps the actual
midpoints positive. The floor is a real-to-integer floor, not natural
truncation. Fuel zero and failure are represented honestly by `Option.none`,
not replaced by an arbitrary returned value; existence of sufficient fuel
is part of the universal proposition being negated. No other junk-value
operations occur. The printed recursive auxiliary and match declaration
were inspected; they are the same fuel recursion. `logTwo._proof_1` and
the closure's `T24Statement._proof_1` only elaborate the numeral 2.

## SAP.P003b.T30

This is a conjunction of two universally quantified assertions. The
potential-count and observed-count tuples have natural coordinates ordered
(11,10,01,00). For v=(a,b,c,d), total is a+b+c+d and effect is the integer
b-c; tau(v) is (b-c)/total in Q, cast to R. For o=(A,B,C,D),
T(o)=A/(A+B)-C/(C+D) in Q, cast to R.

Here the finite exact p-value p(v,o) means precisely: set m=A+B,N=v.total;
enumerate tuples q=(i,j,k,l) with 0<=q<=v coordinatewise and sum q=m;
give them weight choose(a,i)choose(b,j)choose(c,k)choose(d,l); form
O(v,q)=(i+j,k+l,a-i+c-k,b-j+d-l); sum the weights with

    |N*((N-m)*O(v,q).a-m*O(v,q).c)-m*(N-m)*(b-c)|
      >= |N*((N-m)*A-m*C)-m*(N-m)*(b-c)|;

divide the sum in Q by choose(N,m). All expressions inside absolute values
are integers. Possible(o,v) means membership in the list of tuples
(i+k,A-i+l,C-k+j,B+D-j-l), indexed independently by
0<=i<=A,0<=j<=B,0<=k<=C,0<=l<=D. K(alpha,o) is the finite set of
tau(v) for possible v with alpha<=p(v,o). I(alpha,o) is the set of real
t for which there exist l,u in K(alpha,o) with l<=t<=u. L=inf K and
U=sup K in R.

First, for every o:Counts and alpha:R, assuming
0<A+B and A+B=C+D, and 0<alpha<1, define
v*=(0,A+D,B+C,0). The conclusion is all of:

* v* is possible, tau(v*)=T(o), and p(v*,o)=1;
* T(o) belongs to K(alpha,o) and I(alpha,o);
* K(alpha,o) is nonempty, and L(alpha,o)<=T(o)<=U(alpha,o).

Second, for every m:N, Y:Fin(2*m)->Bool, treated-set assignment
z:{s:Finset(Fin(2*m)) // s.card=m}, and alpha:R, assuming m>0 and
0<alpha<1, define o by counting the four conditions
z and Y=true; z and Y=false; outside z and Y=true; outside z and Y=false.
Define w:Fin(2*m)->Bool x Bool by w(i)=(Y(i),not Y(i)) on z and
w(i)=(not Y(i),Y(i)) off z. `wholeAgrees w Y z` means, for every label,
the first coordinate on z and the second off z equals Y(i).
`tableCounts w` counts the four Bool pairs (true,true), (true,false),
(false,true), (false,false). Let bit(true)=1,bit(false)=0 in R;
`tableTau w` is sum_i(bit(w(i).1)-bit(w(i).2))/(2*m), and
`tableEstimator w s` is sum_{i in s}bit(w(i).1)/s.card minus
sum_{i outside s}bit(w(i).2)/(2*m-s.card).

The second conclusion states, in order: o.total=2*m, its two arm sizes
are m, w agrees with Y on z, tableCounts(w)=v*, tableTau(w)=tau(v*)
and T(o), tableEstimator(w,z)=T(o), and the uniform probability over all
m-element treated sets s that
|tableEstimator(w,s)-tableTau(w)|>=|T(o)-tableTau(w)| is 1. It also
states p(tableCounts(w),o)=1 and repeats all the K, I, nonemptiness and
endpoint assertions. `uniformProb E` is exactly the cardinality of the
filtered finite universe satisfying E divided in R by the cardinality of
that universe. No random original Y or z is postulated; both are universally
fixed before the uniform rerandomization s.

Junk-value audit: potential effects, observed estimates, table effects,
table estimators, p-values and uniform probabilities all use division that
would return zero at denominator zero. The hypotheses ensure positive m,
2*m, both arm sizes, and choose(2*m,m); m-element subsets exist, so the
uniform universe is nonempty. The first half similarly has positive arms
and possible totals equal to o.total. Natural subtraction in enumerations,
observations, and the control-arm denominator is protected by the range or
finite-subset bounds; negative effects use Z or R subtraction. Empty real
infimum/supremum would be zero, but the conclusion supplies a member of K,
so endpoints are genuine finite extrema. I is explicitly the finite convex
hull and is empty when K is empty, independently of the endpoint convention.
No logs, square roots, integrals, extended reals, limits or default partial
values occur. All casts are the usual exact embeddings. Generated record
recursors and equality decisions merely implement natural-coordinate tuples.

## SAP.P003b.T31

For every o=(A,B,C,D):N^4 and alpha:R, in that order, assume
0<A+B, 0<C+D, 0<alpha<1, and K(alpha,o) is nonempty. Put
n=A+B+C+D,m=A+B,h=C+D. The conclusion is

    U(alpha,o)-L(alpha,o)
      <= sqrt((4/alpha) * n/(n-1) * (n/(m*h))).

The term n-1 is subtraction in N before casting to R; m*h is likewise a
natural-number product before casting. All other divisions and the final
square root are in R. Balance is not assumed.

For completeness, K(alpha,o) means the following finite set with no
additional predicates. Enumerate all v=(i+k,A-i+l,C-k+j,B+D-j-l)
for 0<=i<=A,0<=j<=B,0<=k<=C,0<=l<=D. For such a v with total N
and integer effect e=v.b-v.c, tau(v)=e/N in Q, cast to R. Enumerate
q=(qa,qb,qc,qd) with 0<=q<=v, sum q=m, weight
w=choose(v.a,qa)choose(v.b,qb)choose(v.c,qc)choose(v.d,qd), and
observation O=(qa+qb,qc+qd,v.a-qa+v.c-qc,v.b-qb+v.d-qd).
The rational p-value is the sum of w for which
|N*((N-m)*O.a-m*O.c)-m*(N-m)*e|
>=|N*((N-m)*A-m*C)-m*(N-m)*e|, divided by choose(N,m).
K contains tau(v) precisely for these enumerated v with p-value>=alpha,
with duplicate effects removed. L and U are the real infimum and supremum
of this finite set. No coverage probability or algorithmic bound is stated.

Junk-value audit: n>=2,m>=1,h>=1, alpha>0. Consequently n-1 is ordinary
positive subtraction, all displayed denominators are positive and the
square-root argument is positive. Mathlib's `Real.sqrt` is zero on negative
arguments, but that convention is inactive. Enumerated possible totals are
n, with 0<m<n, so p-value and effect denominators are positive. All
enumeration and observation natural subtractions are guarded by their
coordinate bounds. K is finite and explicitly nonempty, hence neither
empty nor unbounded infimum/supremum conventions apply. No estimates,
integrals, extended reals, logs, real powers, limits, empty index types or
partial functions occur. Casts preserve the natural and integer values.
The generated `_proof_1` is only elaboration of the numeral 4; the tuple
recursors and derived equality are structural.

## SAP.P003b.T33

For every o=(A,B,C,D):N^4 and v=(a,b,c,d):N^4, in that order, assume
0<A+B, A+B=C+D, a+b+c+d=A+B+C+D,
1<=min(b,c), and 2<=max(b,c). Thus both discordant counts are positive
and at least one is at least 2. The conclusion is

    p((a+1,b-1,c-1,d+1),o) >= p((a,b,c,d),o).

There is no assumption that v, or its updated vector, is possible for o.
There is no alpha parameter, coverage assertion, strict inequality, or
claim about the special case b=c=1.

Here p(v,o) has the following complete finite meaning. Set N=a+b+c+d,
m=A+B,e=b-c in Z. List every q=(i,j,k,l) with i<=a,j<=b,k<=c,l<=d,
i+j+k+l=m, via successive ranges bounded by the remaining treatment
size. Put O=(i+j,k+l,a-i+c-k,b-j+d-l), assign q weight
choose(a,i)choose(b,j)choose(c,k)choose(d,l), and sum these weights
for which

    |N*((N-m)*O.a-m*O.c)-m*(N-m)*e|
      >= |N*((N-m)*A-m*C)-m*(N-m)*e|.

Divide the result in Q by `Nat.fast_choose N m`. The updated p-value uses
exactly the same definition with its updated potential-count vector and
the same o. The absolute values are `Int.natAbs`; the comparisons are on
natural numbers, equivalent to comparison of integer absolute magnitudes.

Junk-value audit: subtraction b-1 and c-1 is in N, but min(b,c)>=1
prevents truncation and preserves N and e. The state enumeration and O
use only coordinate-bounded natural subtractions. The positive balance and
total equality give N=2*m>0 and choose(N,m)>0 for both vectors, so rational
division by zero is impossible. The p-value remains a well-defined tail
probability even for a v incompatible with o, since o supplies only a
numeric threshold. The theorem uses no accepted set, endpoints, sInf,
sSup, estimates with possibly empty arms, integrals, extended reals,
logs, square roots, real powers, limits, or partial functions. All natural
to integer casts and rational divisions preserve their intended values.

## Closure coverage

The named source definitions above include every SAP definition in each
of the five supplied closures. In addition to reading their source, the
generated entries were printed in `scratch/BlindPrint.lean`: `Counts.mk`,
`Counts.rec`, `Counts.casesOn`, `instDecidableEqCounts`, its `decEq`,
`decEq.match_1`, and all five `decEq._proof_*` declarations; the four
`T26Statement._proof_*` declarations; `T31Statement._proof_1`;
`T24Statement._proof_1`; `logTwo._proof_1`; and
`printedExecution._f` and `printedExecution.match_1`. The Counts projections
are the four natural fields of the structure. The generated equality
proofs implement coordinatewise decidable equality; the numeral proofs
implement positive decimal numerals; none adds an axiom or a substantive
hypothesis to a reviewed statement.
