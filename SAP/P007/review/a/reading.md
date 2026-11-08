# Blind reading of the Challenge

This file was written after reading only `SAP/P007/Defs.lean`, all four
`Defs/Part*.lean` files, the Challenge files, and relevant Mathlib definitions.
Neither `claims.json` nor `record.json` had been opened when this reading was
saved. The mathematical statements below describe the Lean propositions,
including conjunctions and domains; the Challenge docstrings are not substituted
for the propositions.

## Shared definitions, expanded

All dimensions are natural numbers. Write `[h]={0,...,h-1}` for `Fin h`.
A row is a function `[h] -> {false,true}`, and an array is a function from
`[n]` to rows. **True means missing**, false means observed. A `Law` on any
finite type is a weight function into the real numbers, with every weight
nonnegative and the sum of all weights exactly one. Its probability of an
event is the sum of its weights on that event; its expectation of a real
function is the finite sum of weight times function. There are no measures,
conditional-expectation operators, or integrability side conditions involved.

For such an array law L, put

- O(i,j) = the event that every coordinate t<h with t<j in row i is observed.
  This definition is meaningful for every natural j, including 0 and j>h;
  O(i,0) is the certain event, and O(i,j)=O(i,h) when j>=h.
- s(i,j) = Pr_L(O(i,j)).
- D_i(x) = 0 when O(i,h) holds at x, and 1 otherwise.
- F(x) = (sum over i<n of D_i(x))/n, as a real quotient.
- A(L) = Pr_L(for every i<n, O(i,h) fails). This is the probability that
  **every row is deleted**, as distinct from the expected deleted fraction.
- I(L) means: for every assignment of a predicate E_i on complete row
  vectors, Pr_L(for all i, E_i(x_i)) = product over i of Pr_L(E_i(x_i)).
  These are arbitrary predicates, so this is mutual independence of row
  vectors, without independence within rows or equality of row distributions.
- B(L,q) means 0<=q<1 and, for every i<n, (if h>0 then s(i,1)<=q), and,
  for every natural j with 1<=j<h and s(i,j)>0,
  s(i,j+1)/s(i,j)<=q. The ratio restriction is imposed only on positive
  conditioning probabilities. No restriction at a zero prefix is asserted.
- c(i,j) = s(i,j+1)/s(i,j) if s(i,j)>0, and 0 otherwise. This is a defined
  coefficient at a null prefix, not a conditional probability on a null event.
- H(L) means equality of all row laws: for all row indices i,j and every
  row predicate E, Pr_L(E(x_i))=Pr_L(E(x_j)). It does not assert independence.
- b(n,q,k)=(1-q^k)^n, and f(q,k)=1-q^k, using natural powers.
- R(n,q,a)=log(1-a^(1/n))/log(q), where 1/n is the real reciprocal and the
  power with exponent 1/n is Mathlib's real power.
- b_R(n,q,x)=(1-q^x)^n, with a real power inside and a natural power outside.
- `superlog h` means h(n)/log(n) tends to positive infinity as n tends to
  infinity through the naturals. The numerator is cast to a real number.

For independent-cell models, an array x has weight
product over i<n and j<h of (1-a_ij) if x_ij=true, and a_ij otherwise.
Thus a_ij is an **observation** chance. `equalWeights n h q` uses a_ij=q.
`unequalWeights n h` uses a_i0=3/4 and a_ij=1/4 for j>0.
`equalModel n h q P` means there exists an actual nonnegative normalized
finite law L with exactly those equal weights, I(L), B(L,q), and P(L).
`unequalModel n h P` asserts the analogous existence for the unequal weights,
with I(L), B(L,3/4), and P(L). These existence predicates do not assume P as
a hypothesis of a universal theorem.

For a deterministic observed array m, row m_i is a finite subset of [K].
Let U(K,k) be all subsets S of [K] having cardinality k. Define
retainedShare(m,S) = #{i<n : S is a subset of m_i}/n,
M(m,k) = the sum of retainedShare(m,S) over S in U(K,k), divided by
|U(K,k)|, and loss(m,k)=1-M(m,k). These are uniform sampling **without
replacement** and listwise retention. Mathlib `powersetCard` consists exactly
of subsets of the stated cardinality and has size `Nat.choose K k`.

For a Boolean missingness matrix m with n rows and any finite column type J,
N(m) is the natural-number sum of its missing entries, and V(m) is the real
average, over j in J, of #{i<n : m_ij=true}/n. `observedColumns m` gives in
each row the subset of columns whose entry is false. A column type
`Fin K ⊕ Fin d` is a disjoint union of retained K columns (left summand) and
removed d columns (right summand).

Mathlib conventions checked: binomial coefficients are natural numbers,
with choose(r,k)=0 for r<k; the subsequent casts do not introduce truncated
integer subtraction. Natural subtraction in the fixed arithmetic constants
does truncate in principle, but all its displayed minuends exceed the
subtrahends. Real division is totalized with division by zero equal to zero.
The uses of F, M, and V here have positive row/sample/column denominators.
Threshold statements use n>0, 0<q<1, and 0<a<1, so their logarithms and
reciprocals are in the intended domains. Real log has log(0)=0 and log of a
negative number equal to log of its absolute value, but the threshold
statements do not use those extensions. Natural floor and ceiling are the
greatest/least suitable natural numbers (floor is zero for negative inputs);
all thresholds below are positive. In `superlog`, n=0,1 give a zero
denominator; these finitely many terms do not affect the limit. Empty finite
sums/products are 0/1 as usual. The asymptotic laws have a zero-row term,
but all probabilistic hypotheses start at n=1 and the limit ignores n=0.
`Tendsto` and `atTop` are the usual filter definitions of convergence and
eventual lower bounds; `StrictMono` means strict inequality is preserved for
every pair of ordered arguments.

## T1

There are no theorem parameters or hypotheses outside the following
conjunction (`T1Statement`).

1. For every observed array m with 8580 rows and 1205 columns,
   M(m,4) = sum_i choose(|m_i|,4)/(8580*choose(1205,4)). Moreover, if
   sum_i |m_i| = 3482533 (cast to integers in the hypothesis), then
   sum_i choose(|m_i|,4)>=9560288484630,
   M(m,4)>=24513560217/1923069889510>1/100, and
   loss(m,4)<=1898556329293/1923069889510<99/100.
2. For each integer r represented by `Fin 1206`, hence 0<=r<=1205,
   1104475905+(r-405)*10989810 <= choose(r,4), with integer arithmetic.
3. choose(405,4)=1104475905, choose(405,3)=10989810,
   choose(406,4)=1115465715;
   8580*choose(1205,4)=749997256908900;
   947*choose(405,4)+7633*choose(406,4)=9560288484630;
   3482533=8580*405+7633;
   9560288484630/749997256908900=24513560217/1923069889510;
   1/100<24513560217/1923069889510;
   1898556329293/1923069889510<99/100.
4. The affine bound in item 2 is equal to choose(r,4) at both r=405 and
   r=406, and 1-24513560217/1923069889510=1898556329293/1923069889510.

## T2

Again this is a conjunction without outer assumptions.

1. For every natural A, if |A/10501920-0.668390827582004|<=0.000000001,
   then A=7019387.
2. The following fixed arithmetic (`averageArithmetic`) holds:
   8580*1224=10501920; 8580*19=163020;
   7019387-8580*19=6856367; 8580*1205=10338900;
   10338900-6856367=3482533;
   0.6625<=6856367/10338900<0.6635;
   6856367/10338900<0.6675;
   0.6675<=7019387/10501920<0.6685.
3. For every Boolean matrix m of shape 8580 by (1205+19), if all 19
   right-summand columns are missing in every row and
   |V(m)-0.668390827582004|<=0.000000001, put after_ij=m_i(left j).
   Then N(m)=7019387, N(after)=6856367,
   sum_i |observedColumns(after)_i|=3482533,
   V(m)=7019387/10501920, V(after)=6856367/10338900,
   0.6625<=V(after)<0.6635, V(after)<0.6675,
   loss(observedColumns(after),4)<=1898556329293/1923069889510 and
   loss(observedColumns(after),4)<99/100. These are all clauses of
   `correctedMask m`, not an extra assumption.
4. For every observed array m of shape 8580 by 1205 with observed total
   3482533, loss(m,4)<=1898556329293/1923069889510 and loss(m,4)<99/100.
5. The following exact decimal arithmetic (`simulationComparisons`) holds:
   1-0.02820753=0.97179247;
   1-0.01365003=0.98634997;
   1-0.006640252=0.993359748; and
   0.97179247<0.98634997<0.99<0.993359748.
   There is no quantification over other numbers of columns or random runs.

## T3

The conjunction of two existential assertions:

1. There is a law on one row with two columns whose entire mass is on
   the row (true,false), i.e. (missing,observed). It satisfies I(L) and
   B(L,0), s(0,1)=s(0,2)=0, Pr(column 1 observed)=1,
   Pr(column 1 missing)=0, A(L)=1, and (1-0^2)^1=1.
2. There is a law on one row with two columns whose entire mass is on
   (true,true). For every real q with 0<=q<1, this same law satisfies
   I(L), B(L,q), and, for every one of the two columns, its missing
   probability is one. The law is chosen before q is quantified.

## T4

The conjunction of two existential assertions:

1. The point-mass law on the one-row matrix (true,false) exists,
   satisfies I(L), B(L,1/2), and s(0,1)=s(0,2)=0. For every real v,
   if 0<=v<=1, then s(0,2)=v*s(0,1). Also 1/2<1,
   s(0,2)<=(1/2)^2, A(L)=1, and 3/4<=A(L).
2. There is a law on two rows and three columns with the displayed
   product weights: independently for each row, choose (true,false,false)
   or (false,true,false), with probability 1/2 each. It satisfies I(L)
   and B(L,1/2). For every row i,
   s(i,1)=1/2, s(i,2)=s(i,3)=0, s(i,1)>0,
   s(i,2)/s(i,1)=0, and s(i,3)<=1/8. Finally A(L)=1 and 49/64<=A(L).

## T5

For every natural n,h, given n>0 and a proof hh of h>0, for every law L
on n by h arrays and every real q, if B(L,q), then the following all hold.

1. If q=0, each row's column 0 is missing with probability one, A(L)=1,
   and (1-q^h)^n=1.
2. For every row i, s(i,0)=1. For every row i and natural j<h,
   s(i,j+1)<=s(i,j)*q; also s(i,j)=0 implies s(i,j+1)=0.
3. For every row i, c(i,0)=s(i,1),
   s(i,h)=product over t=0,...,h-1 of c(i,t),
   and for every j<h, 0<=c(i,j)<=q. Also s(i,h)<=q^h and
   1-q^h<=1-s(i,h).
4. If in addition I(L), then
   A(L)=product_i(1-s(i,h)) and (1-q^h)^n<=A(L).

Independence is required only for item 4; it is not an outer hypothesis.

## T6

The conjunction of three universal assertions:

1. For every n,h with n>0,h>0, then every real q with 0<=q<1,
   -1<-(q^h), 1-q^h<=1,
   1+n*(-q^h)=1-n*q^h, and 1-n*q^h<=(1-q^h)^n<=1.
2. For every n,h with n>0,h>0, then every law L on n by h arrays and
   real q, if I(L) and B(L,q), then
   1-n*q^h<=(1-q^h)^n<=A(L)<=1,
   0<=1-A(L)<=n*q^h; if q=0 then A(L)=1; and if q>0 then
   n*q^h=exp(log(n)+h*log(q)).
3. For every natural n>0, n<=2*n, 2*n!=n, and
   |Fin n x Fin 2|=2*n. This last assertion counts pairs and does not
   itself construct any grouped missingness model.

## T7

This is the conjunction of six existential model assertions followed by
four rounded threshold equalities. `equalModel`/`unequalModel` carry all the
law, weights, independence, and observation-bound conditions defined above.

1. An equal model with n=1,h=2,q=3/4 exists for which
   b(1,3/4,2)=7/16<1/2<37/64=b(1,3/4,3),
   2<R(1,3/4,1/2)<3, its natural floor is 2 and ceiling is 3,
   for every natural k, b(1,3/4,k)!=1/2,
   A(L)=7/16,
   for every k, b(1,3/4,k)<=1/2 iff k<=2, and
   1/2<=b(1,3/4,k) iff 3<=k;
   b_R(1,3/4,R(1,3/4,1/2))=1/2.
2. An equal model with n=10000,h=33,q=3/4 exists with
   A(L)=b(10000,3/4,33)<1/2<b(10000,3/4,34).
3. An equal model with n=10000,h=952,q=99/100 exists with
   A(L)=b(10000,99/100,952)<1/2<b(10000,99/100,953).
4. An unequal model with n=1,h=2 exists with
   b(1,3/4,2)=7/16<=1/2<A(L)=13/16.
5. An unequal model with n=1,h=16 exists with
   b(1,3/4,16)=4251920575/4294967296<99/100<b(1,3/4,17),
   A(L)=4294967293/4294967296>99/100, and the floor/ceiling of
   R(1,3/4,99/100) equal 16/17 respectively.
6. An unequal model with n=10000,h=33 exists with
   A(L)=(1-3/4^33)^10000, A(L)>=1-30000/4^33, A(L)>99/100,
   and b(10000,3/4,33)<1/2.
7. Floors/ceilings of R(10000,3/4,1/2) are 33/34, and those of
   R(10000,99/100,1/2) are 952/953.

## T8

First, for every natural n>0, then every real q,a with 0<q<1 and
0<a<1, all of the following hold, writing R=R(n,q,a).

1. b(n,q,0)=0; for every natural k, 0<=b(n,q,k)<1; and b(n,q,.) is
   strictly increasing on the naturals.
2. R>0, b_R(n,q,R)=a, and for every real x>=0,
   b_R(n,q,x)=a implies x=R.
3. For every natural k, b(n,q,k)<=a iff k<=R as real numbers;
   a<=b(n,q,k) iff R<=k; and b(n,q,k)=a iff k=R.
4. For every natural k, b(n,q,k)<=a iff k<=floor(R), and
   a<=b(n,q,k) iff ceil(R)<=k. Also b(n,q,floor(R))<=a and
   a<=b(n,q,ceil(R)).
5. ceil(R)=floor(R) iff R is a natural number. If R is not a natural
   number, then ceil(R)=floor(R)+1 and
   b(n,q,floor(R))<a<b(n,q,ceil(R)).
6. For every natural k>0, then every law L on n by k arrays, if I(L)
   and B(L,q), b(n,q,k)<=A(L); if ceil(R)<=k, then both
   a<=b(n,q,k) and a<=A(L).
7. For every natural k>0 with k<R, an equal model n,k,q exists for
   which A(L)=b(n,q,k)<a.
8. For every natural k>0 an equal model n,k,q attaining
   A(L)=b(n,q,k) exists, irrespective of its relation to R.

Conjoined to this universal statement are `workedValues`: the four
floor/ceiling equalities in T7 item 7, and
0.47075<=b(10000,3/4,33)<0.47085,
0.49685<=b(10000,99/100,952)<0.49695.
There are also the four strict inequalities bracketing 1/2 at 33/34 and
952/953, and an unequal model n=1,h=2 with b(1,3/4,2)<=1/2<A(L).

## T9

There exists a law on two rows and two columns, with independent-cell
observation chances (3/4,1/2) in each row, such that all of the following
hold: I(L), B(L,3/4); for every real q, B(L,q) implies 3/4<=q;
for every row i, s(i,1)=3/4, s(i,2)=3/8, s(i,1)>0, and
s(i,2)/s(i,1)=1/2; E(D_i)=5/8 for each row; E(F)=5/8;
f(3/4,2)=7/16<E(F); b(2,3/4,2)=49/256 != f(3/4,2);
and A(L)=25/64. This law's stated weights specify a normalized law by
existence, not an assumed table that might fail to normalize.

## T10

The conjunction of six universal assertions:

1. For every natural n,k with n>0,k>0, then every law L on n by k
   arrays and every real q, if B(L,q), each row i satisfies
   E(D_i)=1-s(i,k)>=f(q,k); also
   E(F)=sum_i(1-s(i,k))/n>=f(q,k). Independence is not required.
2. For every n,k>0 and every real q with 0<=q<1, an equal model n,k,q
   exists with E(F)=f(q,k).
3. For every n,k>0 and every real q with 0<=q<1,
   b(n,q,k)=f(q,k)^n and b(1,q,k)=f(q,k).
4. For every n,k with n>=2,k>0 and real q with 0<q<1,
   0<f(q,k)<1 and b(n,q,k)<f(q,k).
5. For every n,k>0 and real q with 0<q<1,
   b(n,q,k)=f(q,k) iff n=1.
6. For every n,k>0, f(0,k)=1 and b(n,0,k)=1.

## T11

The conjunction of:

1. For every n,k>0 and every law L on n by k arrays, I(L) implies
   A(L)=product_i(1-s(i,k)). No observation bound or identical-law
   assumption appears in this part.
2. There exists a law on two rows and one column with independent-cell
   observation chances 1/4 in row 0 and 1/2 in row 1. It satisfies I(L),
   B(L,1/2), not H(L), s(0,1)=1/4, s(1,1)=1/2,
   A(L)=3/8, and b(2,1/2,1)=1/4<=A(L).

## T12

The conjunction of three assertions:

1. For every natural n,K,d, given n>0 and K>0, for every Boolean
   matrix m with n rows and K+d columns, if all right-summand d columns
   are missing in every row, set A=N(m), after_ij=m_i(left j). Then
   A=N(after)+n*d;
   V(m)=A/(n*(K+d)); V(after)=(A-n*d)/(n*K), with the subtraction in
   this quotient performed in the reals;
   (K+d)*V(m)=d+K*V(after); and
   V(after)=((K+d)*V(m)-d)/K.
2. For every Boolean matrix m of shape 8580 by (1205+19), if the 19
   right-summand columns are wholly missing and
   0.6675<=V(m)<0.6685, then
   V(after)<199811/301250<0.6675 and V(after)<0.6675.
3. For every such matrix with those wholly missing columns and
   N(m)=7019387, V(m)=7019387/10501920,
   V(after)=6856367/10338900,
   0.6625<=V(after)<0.6635,
   V(m)-V(after)=66168127/12654813600, and
   100*(V(m)-V(after))=66168127/126548136.

## T14

For every natural n,k, given n>0,k>0, then every law L on n by k arrays
and every real q, I(L) and B(L,q) imply (1-q^k)^n<=A(L).
There is no equality-of-row-laws assumption or restriction on dependence
between columns of a row. q=0 is included.

## T15

For every natural n,g, given n>0,g>0, then every law L on n by g Boolean
arrays and every real q, I(L) and B(L,q) imply (1-q^g)^n<=A(L).
This is literally T14 with g in place of k. If the coordinates represent
nonempty groups with one common missingness indicator per group, it is a
statement about group indicators. No group sizes, partitions of columns, or
within-group membership functions occur in the formal proposition.

## T16

For every natural-valued sequence k, then every family L with L_n a law
on n by k(n) arrays (including n=0), assume k(n)>0 for every n>0.
For every single real q with 0<=q<1, assume for every n>0 both I(L_n)
and B(L_n,q), and assume k(n)/log(n) tends to positive infinity.
Then A(L_n) tends to 1 as n tends to infinity. In particular q is fixed
for the entire family, rather than chosen separately at each n. The laws
and row distributions otherwise may change arbitrarily with n.

## T17

For every natural-valued sequence g and every family L_n of laws on
n by g(n) arrays, assume g(n)>0 for each n>0. For every single real
0<=q<1, if I(L_n) and B(L_n,q) for every n>0 and
g(n)/log(n) tends to positive infinity, then A(L_n) tends to 1.
This has exactly the quantifier structure and domain conventions of T16,
with group-indicator coordinates in place of variable coordinates.

There is no theorem named T13 in the Challenge files read at this stage.
