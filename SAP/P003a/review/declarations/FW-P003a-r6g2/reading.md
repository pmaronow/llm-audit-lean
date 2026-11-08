# Blind reading

Saved before opening `claims.json`, `record.json`, `earlier.json`, or
`architect-report.md`. I read both Challenge files, all source definitions in
the five closures, and the elaborated `#print` output for all 100 distinct
closure declarations (`scratch/BlindClosure.lean`, `scratch/blind-closure.log`).
Generated constructors, projections, recursors, equality decision procedures,
pattern matchers, and numeral/typeclass proof auxiliaries have their ordinary
Lean meanings; none introduces an additional mathematical assumption.

## SAP.P003a.T5

The theorem asserts the conjunction called `T5WholeStatement`, rather than the
older `T5Statement`. Its four universally quantified parts are as follows.

1. First choose any integers k1 <= k2, then any function
   reply : N x Z -> Bool. Put d = k2-k1+1, a positive integer regarded as a
   natural number. Start at time zero with integer bracket (k1-1,k2+1) and
   fuel d+1. A recursive call with bracket (a,b) stops and returns that bracket
   and an empty remaining trace if fuel is zero or b <= a+1. Otherwise it
   records (a,b), computes c = floor((a+b)/2), and consumes one fuel unit.
   A true reply at (time,c) recurses on (a,c), and a false reply recurses on
   (c,b); time increases by one. The output includes the final bracket (A,B)
   and the chronological list P of brackets immediately preceding queries.
   Q is the list of midpoints of P. The conclusions are:
   - B=A+1 and length(P)<d+1;
   - k1-1<=A and B<=k2+1;
   - each (a,b) in P has k1-1<=a, b<=k2+1, and a<floor((a+b)/2)<b;
   - Q contains no repeated integer and every member lies in [k1,k2];
   - length(Q)<=Nat.log 2 d+1 and, in real arithmetic,
     length(Q)<=floor(log(d)/log(2))+1
     <=floor(log(d)/log(2)+2).
   Here Nat.log is Mathlib's natural-number base logarithm. There is no
   assumption on replies, including monotonicity, accuracy, or time invariance.
2. Choose integers k1,k2,r and f : Z -> Bool. Assume k1<=k2,
   k1-1<=r<=k2, and for every integer x in [k1,k2],
   f(x)=false iff x<=r. Run the preceding recursion with reply(time,c)=f(c).
   The final lower endpoint equals r. The final and every recorded bracket
   satisfy k1-1<=a<=r<b<=k2+1. The final lower endpoint is also in
   [k1-1,r]. A second recursion, `sentinelSearch`, which records c instead
   of (a,b) and returns a instead of the full bracket, returns precisely
   (A,Q) with the same fuel and initial bracket.
3. Choose four natural observed counts o=(a,b,c,d0), and m : N. Assume
   m>0, a+b=m, and c+d0=m. Put n=2m, Delta=(a:Z)-(c:Z).
   The total a+b+c+d0 equals n; -m<=Delta<=m. The observed estimate is
   the real image of the rational a/(a+b)-c/(c+d0), and n times this
   estimate equals 2 Delta. The list of candidate integers is
   [a-c-(a+b)+j : j=0,...,a+b+c+d0]; its underlying finite set is
   the integer interval [Delta-m,Delta+m]. The upper interval
   [2 Delta,Delta+m] has (m-Delta).toNat+1 elements, and the lower interval
   [Delta-m,2 Delta] has (m+Delta).toNat+1 elements. Both cardinalities
   are <=n+1.

   For every pair of reply functions ru,rl : N x Z -> Bool and every pair
   of cost functions cu,cl : Z -> N, assume, at every actually queried
   upper (respectively lower) integer x, that its cost is <=2(n+1) if x=0
   and <=n+1 otherwise. The upper queries are the preceding search on
   [2 Delta,Delta+m]; the lower queries are its search on
   [Delta-m,2 Delta]. Let U,L be the respective list sums of the costs.
   Then each is <=(n+1)(Nat.log 2 (n+1)+2). This last expression, as a
   real number, is <=(n+1)floor(log(n+1)/log(2)+3). If n>=15, U+L is
   <=4n log(n)/log(2). The cost assumptions are implications in the
   statement: the theorem does not construct permutation tests or prove
   their individual costs from another definition.
4. For every natural n>=15,
   2(n+1)floor(log(n+1)/log(2)+3)<=4n log(n)/log(2).

All integer effects and candidate arithmetic use signed integers. Counts are
simply a structure of four natural numbers, with total their sum; they carry
no embedded validity predicate. The query-cost sum is an ordinary finite
list sum. The docstring explicitly concerns the corrected sentinel search.

Junk-value audit: integer division by 2 is Euclidean division, hence the
floor midpoint even at negative brackets, and its divisor is never zero.
`Int.toNat` truncates negative inputs to zero, but the search length d and
m+-Delta here are positive/nonnegative under the hypotheses. The domains
are nonempty. Zero fuel has a default return even before adjacency, but the
conclusion length(P)<d+1 and final adjacency rule out relying on an exhausted
search. Empty query lists and their zero costs have ordinary finite meanings.
Rational division by zero is totalized to zero, but both observed arm sizes
equal m>0. `Real.log 0=0`, and negative inputs to Real.log use the absolute
value convention; neither is used in the asserted logarithmic bounds:
d>=1, n+1>0, and the log(n) bounds have n>=15. log(2)>0. `Nat.log` has
totalized small/base-degenerate cases, but the base is 2 and its arguments
are positive. Floors are real-to-integer floors, without saturation. All
natural/integer-to-rational/real casts here are exact. There are no infinite
sums, integrals, extended-real conversions, extrema, or limit operations.

## SAP.P003a.T11

For n : N, a potential table is a function y : Fin n -> Bool x Bool, with
first coordinate the treatment potential outcome and second the control
outcome. Write b(false)=0 and b(true)=1 as real numbers. An assignment of m
treated units is a finite subset z of Fin n together with the equality
card(z)=m. Its uniform event probability is the number of assignments in the
event divided, in R, by the number of all such assignments. Define

  tau(y) = (sum_i (b(y_i.1)-b(y_i.2)))/n,
  T_y(z) = (sum_{i in z} b(y_i.1))/card(z)
           - (sum_{i notin z} b(y_i.2))/(n-card(z)),
  D_y(z) = |T_y(z)-tau(y)|,
  S = {D_y(z) : z is an assignment of size m},
  q(x) = (# {z : x<=D_y(z)})/(# {z}).

The estimator's second denominator elaborates as subtraction in R, not
natural truncated subtraction. S is a finite image set, without duplicate
values. The theorem is the conjunction of the following.

1. For every n,m,y,alpha, in that order, if 0<m<n and 0<alpha<1, S is
   nonempty and there exists d in S such that alpha<=q(d), every e in S
   with alpha<=q(e) satisfies e<=d, and
   {x in R : q(x)<alpha}=(d,infinity). This rejecting set is nonempty and
   has no least real element. The last assertion is explicitly
   not(exists x, q(x)<alpha and forall u, q(u)<alpha -> x<=u).
2. For the particular table y : Fin 2 -> Bool x Bool constantly
   (false,false), tau(y)=0 and every size-one assignment has T_y(z)=0.
   For every real x, q(x)=1 if x<=0 and q(x)=0 otherwise. At alpha=1/2,
   the rejecting real set is exactly (0,infinity).
3. A separately defined q0(x)=if x<=0 then 1 else 0 has
   q0(x)<1/2 iff x>0, at least one rejecting x, and no least rejecting x.
   This same tail is asserted for the count-based experiment with potential
   type counts v=(0,0,0,2) and m=1.

For the last count experiment, a count vector is four naturals in order
(11,10,01,00); its total N is the sum and its signed effect numerator is
(v.b:Z)-v.c. Its real effect is the real image of the rational
(v.b-v.c)/N. Treated states are enumerated by nested lists
0<=qa<=min(v.a,m), 0<=qb<=min(v.b,m-qa),
0<=qc<=min(v.c,m-qa-qb), qd=m-qa-qb-qc<=v.d.
Each q has weight product_{s=a,b,c,d} choose(v.s,q.s). The observed counts
are (qa+qb,qc+qd,v.a-qa+v.c-qc,v.b-qb+v.d-qd), with the source's
left-associated natural arithmetic. The estimate of observed o is the
real image of o.a/(o.a+o.b)-o.c/(o.c+o.d), in Q. Count-based probability
is the sum of the weights of event states divided by choose(N,m).
Thus the third part also checks a genuine complete-randomization tail,
not just an arbitrary real step function.

Junk-value audit: uniform probability would be zero on an empty assignment
type (0/0 in R); the legal hypotheses 0<m<n give actual assignments and
positive cardinality. They also imply n>0 and positive treated and control
denominators. The fixed example has n=2,m=1. Count-based choose(2,1)=2
is nonzero. The natural subtractions in state enumeration have bounded
indices, and those in observed counts use states bounded by the type
counts, so no truncation changes valid outcomes. Finite image sets can be
empty in an invalid experiment, but nonemptiness is an explicit conclusion
here. There is no sInf or chosen default minimum: the no-least statement
quantifies over real witnesses directly. No integrals, logs, square roots,
infinite sums, extended-real values, or limits occur.

The docstring calls this a refutation of the printed assertion that a
smallest rejecting real threshold exists. At this blind stage, I have not
checked what the canonical assertion actually quantifies over.

## SAP.P003a.T12

The theorem has three conjuncts.

1. For every finite type Omega (in Type 0), functions w,D : Omega -> R,
   a proof that w(i)>0 for every i, and a proof sum_i w(i)=1, then for
   every alpha with 0<alpha<1, put q(x)=sum_i [x<=D(i)]w(i).
   Either every i has alpha<=q(D(i)), or there exists i with
   w(i)>0, q(D(i))<alpha, and for every j,
   q(D(j))<alpha iff D(i)<=D(j). In this second case
   sum_j [q(D(j))<alpha]w(j)=q(D(i)). In both cases
   sum_j [q(D(j))<alpha]w(j)<alpha.
2. For every Borel measure mu on R with the Mathlib probability-measure
   instance, then every finite set s of reals, if mu(s)=1, then every
   alpha in (0,1) satisfies

     mu({d in R : (mu([d,infinity))).toReal<alpha}).toReal<alpha.

   In particular the tail includes its threshold and rejection is strict.
   Zero-mass points in s are allowed; this conjunct does not assume a
   particular atom enumeration or positive weights at all points of s.
3. For every n,m : N, potential table y : Fin n -> Bool x Bool, and
   alpha : R, assuming 0<m<n and 0<alpha<1, the following support and
   inversion assertions hold under the uniform size-m assignment law.
   Define b, tau(y), T_y, D_y, S, and q exactly by the finite sums and
   cardinality quotients in the T11 section. Put R={d in S : q(d)<alpha}.
   Either R is empty and no assignment rejects, or there is x in R with
   x<=d for every d in R, and for every assignment z,
   q(D_y(z))<alpha iff x<=D_y(z). The uniform rejection probability then
   equals q(x)<alpha. In either case the rejection probability is <alpha.

   For each assignment z, record the observed Boolean outcome at label i
   as y_i.1 if i is treated and y_i.2 otherwise. Its observed four-count
   vector o records treated ones, treated zeros, control ones, control
   zeros. The true y is a possible labeled completion, meaning that
   recomputing its observed outcome function at z yields that function.
   Its true type-count vector v is also possible for o. If q(D_y(z))>=alpha,
   then the rational count-based p-value p(v,o), viewed as real, is
   >=alpha, tau(y) belongs to the accepted finite effect set, and tau(y)
   belongs to its closed interval hull. Finally the uniform probability
   of the latter interval-membership event is >=1-alpha.

Here all remaining count-based definitions unfold as follows. Counts are
four natural numbers; total is their sum; signed effect is (b:Z)-c;
tau(v) is the real cast of this effect divided by total in Q. True type
counts count labels with each Boolean pair (11,10,01,00). The possible
tables for o=(a,b,c,d) are the list

  (i+k, a-i+l, c-k+j, b+d-j-l),
  0<=i<=a, 0<=j<=b, 0<=k<=c, 0<=l<=d.

`Possible o v` means membership in that list. For any such v, set N=total(v)
and m=a+b. Enumerate treated type states qa,qb,qc,qd as in the T11
section (bounded by v and summing to m), with weight
M(v,q)=choose(v.a,qa)choose(v.b,qb)choose(v.c,qc)choose(v.d,qd).
The observed state is
O(v,q)=(qa+qb,qc+qd,v.a-qa+v.c-qc,v.b-qb+v.d-qd).
Put, entirely in Z,

  A(v,o,m)=N*((N-m)*o.a-m*o.c)-m*(N-m)*(v.b-v.c).

The tail count is sum_q [|A(v,O(v,q),m)|>=|A(v,o,m)|]M(v,q);
the absolute values here are integer natAbs. The rational p(v,o) divides
this count by choose(N,m); the computational binomial is Nat.fast_choose.
The accepted finite set is {tau(v) : v in the possible-table list,
alpha<=real(p(v,o))}. Duplicates disappear. The exact interval is
{t : exists l,u in that accepted set, l<=t<=u}; it is empty if the set is
empty. `finiteTail` is the finite sum in part 1. `uniformProb`, the table
effect, and the table estimator are exactly the cardinality quotient and
real sums displayed for T11, with card(z)=m.

Junk-value audit: an empty Omega cannot satisfy sum w=1, so the weighted
theorem is not a claim about a normalized empty law. For the measure
conjunct mu is a probability measure, so every measured set has measure
at most 1; `.toReal` never receives infinity. Although ENNReal.toReal of
infinity is zero in general, that convention cannot affect this theorem.
All sets involved are legitimate Borel tail/rejection sets (and the usual
conditions are presupposed). Finite s with mass 1 cannot be empty. The
experiment hypotheses give nonempty assignments, positive population and
arm sizes, and positive binomial denominators for the true and possible
tables. Bounds in the nested loops prevent natural truncated subtraction
from altering their intended values. Effect subtraction and A are signed
integer arithmetic; the estimator's n-card(z) is real subtraction. Finite
filtering and all comparisons include ties as specified. The empty accepted
set has an explicitly empty hull, without an sInf/sSup default; no claimed
membership is obtained from that convention. The least rejected support
point uses an existential witness and has a separate empty case. There
are no infinite sums, Bochner integrals, logs, roots, powers, or limits.

## SAP.P003a.T13

For every natural n, then every Boolean-pair table
w : Fin n -> Bool x Bool, if n>0, let a,b,c,d be the cardinalities of
the subsets on which the pair is respectively (true,true), (true,false),
(false,true), (false,false). Set bit(false)=0, bit(true)=1 in R. The
statement asserts

  a+b+c+d=n,
  sum_i bit(w_i.1)=(a:R)+b,
  sum_i bit(w_i.2)=(a:R)+c,
  (sum_i (bit(w_i.1)-bit(w_i.2)))/(n:R)
    = real( ((b:Z)-c : Q)/(a+b+c+d : Q) ).

It additionally asserts the following four rational equalities, without
hypotheses:

  tauQ(10,0,0,10)=0; (10-0)/20=1/2;
  tauQ(0,20,0,0)=1; (0-0)/20=0.

Thus the general equality identifies the treatment effect as (b-c)/n,
while these numerical values give two discrepancies with (a-c)/n. The
statement itself does not introduce a separate erroneous effect definition.
Counts are just four naturals; their signed effect is (b:Z)-c, total is
their sum, and tauQ is that rational quotient. Table counts are finite
filter cardinalities, so each label contributes to exactly one cell.

Junk-value audit: subtraction in the effect is in Z, subtraction in the
table sum is in R, and the numerical witnesses use Q. None is truncated
natural subtraction. The hypothesis n>0 and the asserted count total
exclude zero population denominators; both numerical denominators are 20.
For n=0 the table is an empty function and sums and totalized quotients
would be zero, but no assertion under the n>0 implication uses that case.
Natural casts into Z, Q, and R preserve these finite counts exactly. No
probability quotients, extrema, infinite sums, integrals, limits, logs,
square roots, or partial-function defaults occur.

## SAP.P003a.T14

For an integer-indexed function h : Z -> R, define the following explicitly.
A pmf means h(j)>=0 for all j, h is summable as a real series indexed by Z,
and its Mathlib tsum is 1. A mass with first moment adds summability of
j -> (j:R)h(j). An SD law means such a mass and an integer c2 with

  sum'_j (j:R)h(j)=(c2:R)/2,
  h(c2-i)=h(i) for all i in Z,
  h(j)<=h(i) for all i,j in Z with c2<=2i and i<=j.

The alternate `PrintedDecrease` is the unrestricted condition
h(j)<=h(i) for every i<j in Z. The zero mass is 1 at 0 and 0 elsewhere.
The fair mass is 1/2 at each of 0 and 1 and 0 elsewhere.

For k : N, the physical lattice L_k is the subtype of real numbers x with
exists j in Z, x=(j:R)/(k:R). Write p_k(j)=j/k, as an element of this
subtype. For f : L_k -> R, a lattice pmf means nonnegative values,
summability over L_k, and total tsum 1. Write

  g(j)=f(p_k(j)),
  image(j)=sum'_{x in L_k} [k*x=j]f(x),
  sourceMean=sum'_{x in L_k} x*f(x),
  sourceMoment=Summable(x -> x*f(x)).

Lattice symmetry at integer parameter c2 is DEFINED as
g(c2-j)=g(j) for all j in Z. Lattice SD is DEFINED as g being the
integer SD law above. In particular the symmetry and SD equivalences
below unfold to definitional restatements, rather than comparisons with
a separately supplied physical-coordinate SD predicate.

The theorem asserts this conjunction:

1. Every integer pmf fails unrestricted PrintedDecrease; the zero mass and
   the fair mass are SD; the zero mass fails PrintedDecrease; and
   sum'_j j*fairMass(j)=1/2.
2. For every k>0, then every f : L_k -> R satisfying the lattice-pmf
   predicate, g is an integer pmf, image(j)=g(j) for every integer j,
   and for all x in L_k and j in Z, k*x=j iff x=p_k(j).
   For every integer c2, lattice symmetry is equivalent to
   f(p_k(c2-j))=f(p_k(j)) for all j. Lattice SD is equivalent to the
   explicitly defined integer SD property of g.

   SourceMoment holds iff j -> j*g(j) is summable on Z. If SourceMoment
   holds, sourceMean=(sum'_j j*g(j))/k. Moreover, for every c2 in Z,
   sourceMean=c2/(2k) iff sum'_j j*g(j)=c2/2. The pmf and image-law
   conclusions do not require SourceMoment.
3. The function f on L_2 which is 1 at physical point 1/2 and 0
   elsewhere is a lattice pmf. Its g is 1 at j=1 and 0 elsewhere.
   For every integer j, p_2(4j) has physical value 2j. The function
   h_print(j)=f(p_2(4j)), i.e. f(2j), is identically zero and is not a
   pmf.

The physical symmetry center corresponding to c2 is c2/(2k). In ordinary
coordinates the displayed reflection is x -> c2/k-x, and the decrease
condition is on the right side of that center. Integer c2 allows both
integer and half-integer centers after multiplying coordinates by k.

Junk-value audit: real division by zero would collapse L_0 to {0} and
destroy the one-to-one indexing j -> j/k. Every universal lattice-law
assertion is guarded by k>0; the concrete example has k=2. Division by 2
or 2k is also nonzero in its uses. All infinite sums are Mathlib tsums,
which are assigned zero for nonsummable real families. Pmf predicates
explicitly require Summable, and mean identities explicitly require
SourceMoment. IsSD itself includes summability of j*h(j). Over R,
summability of an unordered family implies absolute summability, so
this is a finite absolute first-moment condition. The image mass is
summable under the pmf hypothesis (and for k>0 the relevant fiber is a
single point). The separately stated mean of fairMass has finite
support. Symmetry and the base pmf correspondence require no moment,
so no undefined first moment is used to identify them. Empty sums have
their ordinary zero value; pmf normalization prevents an empty law.
Integer subtraction is signed, all casts are exact, and subtype proof
fields have no numerical effect. There are no ENNReal conversions,
integrals, real roots, logarithms, extrema, limsups, or liminfs.
