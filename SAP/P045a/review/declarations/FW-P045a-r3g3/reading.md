# Blind reading

Saved before opening `claims.json` or `record.json`. Sources inspected: the five
Challenge docstrings and statements, every declaration listed in `closure.json`,+and the Mathlib graph-distance definition. `scratch/ClosurePrint.lean` prints all
123 distinct closure declarations; its complete output was inspected, including
the generated constructor, recursor, match, equality-decision and numeral proof
declarations. Those generated proofs supply ordinary finite indices or nonzero
numeral facts, rather than substantive assumptions. This document reads only the
formal statements and their docstrings; it does not decide their canonical scope.

## SAP.P045a.T11

The theorem asserts the proposition defined at `Defs/Part5.lean:141`.
For every natural number n, assuming n > 0, and every undirected simple graph G
on the vertices {0,...,n-1}, all three following assertions hold. No connectivity
or randomness assumption occurs.

Write d(s,v) for Mathlib's extended natural graph distance: the infimum, in
the complete order of natural numbers together with infinity, of lengths of
walks from s to v. It is zero on the diagonal, a shortest-path length when a
path exists, and infinity between disconnected vertices. For a finite set S,
M(S) is the set of all vertices v for which some s in S has d(s,v) <= 2.
A list c is admissible precisely when, for every k with 0 <= k < length(c),
its kth entry does not belong to M(the set of its first k entries).

1. For every finite list c of vertices, if c is admissible, then c has no
   repeated entries, its length is at most n, and every two distinct members
   s,t of its underlying finite set have d(s,t) >= 3. Additionally, if M(c) is
   the whole vertex set, the set is both separated as just described and
   covering: each vertex v outside the set has some centre s in the set with
   d(s,v) <= 2.
2. For every finite set S of vertices, and then every v outside M(S), the
   number of vertices outside M(S union {v}) is strictly less than the number
   outside M(S). S need not itself be an admissible centre set.
3. There exists a finite admissible list c with M(c) equal to the whole vertex
   set. Together with part 1 this gives a completed separated covering set.

This unfolds `greedyRun`, `marked`, `separated`, `covers` and `epsilonNet`:
the last is exactly the conjunction of separation and the outside-centres
covering condition, not an independently assumed conclusion. Admissibility
requires only each chosen vertex to be outside earlier radius-two balls.
No probability of any choice, centre set, cluster, or treatment is asserted.
The docstring explicitly omits uniform-choice four-path probabilities and
software replacement/recomputation.

Junk/domain audit: the generic definitions use truncated natural subtraction
epsilon-1, but the theorem always uses epsilon=3, so this is exactly 2.
Distance infinity for disconnected vertices is the intended extended distance,
and is never converted to a finite natural or real value. The infimum defining
distance over no walks is infinity, the correct disconnected case. Empty centre
sets have no marked vertices; an empty list satisfies admissibility because
its index type is empty. This does not make completion vacuous since n>0.
List access uses `Fin length`, so has no default or out-of-bounds case. There
are no divisions, real powers, logarithms, integrals, limits, or partial-function
defaults in this statement.

## SAP.P045a.T12

The theorem asserts `T12WholeStatement` (`Defs/WholeW2.lean:115`), which
includes `T12Statement` (`Defs/Part5.lean:151`). There are no input hypotheses:
it is a conjunction of concrete finite calculations, with universal indices
where specified below.

The population is I={0,...,9}. Its adjacency A(i,j) means
(i+1) modulo 10 = j or (j+1) modulo 10 = i. The statement checks symmetry,
absence of self-loops, and exactly two neighbours at every vertex.
An assignment is a function I -> {false,true}. The probability space used here
is the finite set E of sorted pairs e=(s,t), s<t, of vertices, each with mass
1/|E|. Assignment z_e treats precisely s and t. The statement gives |E|=45.

For any assignment z, let b_i indicate that some neighbour of i is treated.
The four exposure labels d11,d10,d01,d00 mean respectively (z_i,b_i) equal
to (true,true), (true,false), (false,true), (false,false). There are exactly
four constructors; the equality instance and its auxiliary proofs implement
ordinary equality on them. Potential outcome y_i(d) is 2,1,1,0 in that order,
independently of i; the observed outcome is y_i(D_i(z)).
Define pi_i(d)=(1/45) sum over e in E of 1{D_i(z_e)=d} and
pi_i=(1/45) sum over e in E of 1{z_e(i)=true}.
All population means below are sums divided by 10; every design expectation
is the sum over E divided by 45.

Define

- L(e)=(1/10) sum_i 1{z_e(i)=true} y_i(D_i(z_e))/(1/5).
- R(e)=(1/10) sum_i [1{D_i(z_e)=d11} 2/pi_i(d11)
  + 1{D_i(z_e)=d10} 1/pi_i(d10)].
- H(e)=(1/10) sum_i 1{D_i(z_e)=d11} 2/pi_i(d11).
- mu11=(1/10) sum_i y_i(d11), mu10=(1/10) sum_i y_i(d10).
- mu_all=(1/10) sum_i y_i(D_i(all-treated)).

For every i, pi_i=1/5>0; (pi_i(d11),pi_i(d10),pi_i(d01),pi_i(d00))
=(2/45,7/45,1/3,7/15), all strictly positive, and
pi_i=pi_i(d11)+pi_i(d10). For every pair e in the entire type I x I
(even unsorted or equal pairs), L(e) equals the same own-treatment formula
with pi_i in place of the constant 1/5.

Exactly ten members of E have adjacent endpoints, and exactly 35 have
nonadjacent endpoints. For every e in E, adjacent endpoints give
(L,R,H)=(2,9,9); nonadjacent endpoints give (1,9/7,0).
In particular, for every e in E, L(e) != R(e).
The means satisfy E[L]=11/9, E[R]=3, E[H]=2,
mu_all=mu11=2, mu10=1, E[R]=mu11+mu10 and E[H]=mu_all.
The bias is E[L]-mu11=-7/9 and also
E[L]-mu_all=11/9-2=-7/9
=-(1/10) sum_i (pi_i(d10)/pi_i)(y_i(d11)-y_i(d10)).

The docstring calls this an exact counterexample to the printed second
equality, with the usual measure-theoretic conditions assumed. On its face
the proved inequality concerns these two explicitly defined random quantities.
Assessment of what the printed equality actually claims is deferred.

Junk/domain audit: real division is total with x/0=0 in Lean. The generic
finite-set average and population mean would return zero on empty index sets.
Here E has 45 members, I has 10, pi_i=1/5, and every pi_i(d) is positive,
so every denominator used has its ordinary meaning. The all-treated potential
outcomes are evaluated outside the two-treated support; this is a legitimate
potential-outcome assignment, not an undefined conditional quantity. Boolean
assignments and exposure matches are total. Naturals enter the reals via
ordinary casts; modulo is by the positive integer 10 and does not wrap any
out-of-range array index. All sums are finite. No integral, `toReal`, logarithm,
square root, real power, limit, supremum, or defaulted partial function occurs.

## SAP.P045a.T13

The theorem asserts `T13WholeStatement` (`Defs/WholeW2.lean:155`), including
`T13Statement` (`Defs/Part5.lean:167`). There are several conjuncts whose
quantifiers are independent, as follows.

For every natural n>0, every probability mass p on the finite set of Boolean
assignments z:{0,...,n-1}->{false,true}, every symmetric loopless Boolean
adjacency A, and every real schedule y_i(d) on the four exposures defined in
the T12 section, assume for every i that pi_i=sum_z p(z)1{z_i=true}>0.
A probability mass here includes the structure fields p(z)>=0 for every z
and sum_z p(z)=1. No product-law, independence, or support-size assumption is
made. Correct exposure specification is built into the schedule: observed
outcome at z is y_i(D_i(z)). Define pi_i(d)=sum_z p(z)1{D_i(z)=d},
mu_d=(1/n)sum_i y_i(d), and

N(z)=(1/n)sum_i 1{z_i=true} y_i(D_i(z))/pi_i,

Q(z)=(1/n)sum_i [1{D_i(z)=d11}y_i(d11)/pi_i
                  +1{D_i(z)=d10}y_i(d10)/pi_i].

Also define the exposure-specific total T_d(z)=sum_i
1{D_i(z)=d}y_i(D_i(z))/pi_i(d), and expectation E[X]=sum_z p(z)X(z).
Under the hypotheses just listed, the theorem asserts:

1. For every i, pi_i=pi_i(d11)+pi_i(d10).
2. E[N]=(1/n)sum_i [(pi_i(d11)/pi_i)y_i(d11)
   +(pi_i(d10)/pi_i)y_i(d10)].
3. E[N]-mu11=-(1/n)sum_i (pi_i(d10)/pi_i)(y_i(d11)-y_i(d10)).
4. If for every i, y_i(d10)<=y_i(d11), then E[N]<=mu11 and
   E[N]<mu11 if and only if there exists i with pi_i(d10)>0 and
   y_i(d10)<y_i(d11).
5. If for every i, y_i(d11)<=y_i(d10), then mu11<=E[N].
6. If for every i both pi_i(d11)>0 and pi_i(d10)>0, then
   E[(T_d11+T_d10)/n]=mu11+mu10.

A separately quantified conjunct takes the same data and positivity hypotheses
and asserts N(z)=Q(z) for every Boolean assignment z, including zero-mass ones.
Another separately quantified conjunct, again under those data and hypotheses,
asserts:

- For every z and i, 1{z_i=true}=1{D_i(z)=d11}+1{D_i(z)=d10}.
- For every i the two weights pi_i(d11)/pi_i and pi_i(d10)/pi_i are
  nonnegative and sum to one.
- If both treated-exposure probabilities are positive at every i, then
  E[T_d11/n]=mu11.
- If every vertex has a neighbour, then
  (1/n)sum_i y_i(D_i(all-treated))=mu11.

Finally there is a fixed two-unit witness, independent of the preceding
universal data: A(i,j) is i!=j, and the probability of z is the product over
i of 1/2 when z_i is true and 1-1/2 otherwise. Thus the four assignments are
independently fair and each has mass 1/4. Outcomes are y(d11)=(2,1),
y(d10)=(1,2), and y(d01)=y(d00)=(0,0). At each unit the two treated-exposure
outcomes differ. In assignment order 00,01,10,11, N is 0,2,1,3.
Its mean is 3/2, equal to mu11=3/2. This is a cancellation witness without
constant treated-exposure outcomes. The docstring describes these formulas,
the conditional hypotheses, the witness and the usual measure conditions.

Junk/domain audit: the universal population size and own-treatment probabilities
are explicitly positive. Exposure-specific division occurs in the HT assertions
only under positivity of both treated-exposure probabilities. A zero exposure
probability is allowed in mixture weights and causes a genuine zero numerator,
not division by zero. The two-unit witness has pi_i=1/2 and both treated-exposure
probabilities 1/4. `bernoulli` could have negative masses for arbitrary real
parameters, but this witness uses only 1/2; the general theorem uses the validated
`Design` structure. Empty realised treated sets contribute an empty sum, namely
zero, with the fixed positive probability denominators; N is not a random-arm
ratio. Real subtraction is untruncated. All natural casts are exact. No
nonintegrable function, infinite series, infinity conversion, or partial default
is present.

## SAP.P045a.T14

The theorem is `T14Statement` (`Defs/Part5.lean:203`). It has three
conjuncts, not an outer stochastic hypothesis.

For natural subclass counts a,b and real sums A,B, define the pooled ratio
as the optional real value none if a+b=0 and some((A+B)/(a+b)) otherwise.
The printed sum is none if a=0 or b=0 and some(A/a+B/b) otherwise.
Thus these definitions explicitly model undefined ratios instead of claiming
Lean's zero-denominator arithmetic is a statistical value.

The first conjunct gives pooled(2,1,9/2,2)=13/6 and
printed(2,1,9/2,2)=17/4; pooled(2,1,11/4,5/4)=4/3 and
printed(2,1,11/4,5/4)=21/8, all as `some` values. Their treated-minus-control
differences are respectively 5/6 and 13/8. Then, for every natural a,b,
assuming a>0 and b>0, for every real A,B,

A/a+B/b-(A+B)/(a+b)=b*A/(a*(a+b))+a*B/(b*(a+b)).

The second conjunct concerns groups {0,...,5}, paired by the total map
0<->1, 2<->3, 4<->5. Let F be the finite set of all three-element subsets H
of the six groups; let a(H) count those g in H whose partner is in H.
Then |F|=20, exactly eight H in F have a(H)=0, and every H in F has
a(H)=0 or a(H)=2. For every real B,
printed(0,3,0,B)=none whereas pooled(0,3,0,B)=some(B/3).

The third conjunct uses 6*75=450 individuals indexed by (g,i). Set
H0={0,1,2}, which belongs to F. Its same-regime subclass is {0,1};
its other subclass is {2}. The witness assignment w_g(i) is true exactly
when i<50 for g<3 and i<25 otherwise. For every g it has the stated
number of treated individuals and positive mass under the uniform
fixed-count assignment law on 75 individuals at that count. Explicitly,
fixedAssignments(n,k) is the finite set of all Boolean assignments having
exactly k true entries, and crMass(n,k,z) is its reciprocal cardinality
on that set and zero outside it.

Outcomes are functions of the full assignment w. Let k be the sum of treated
counts in g and its partner. A treated individual has outcome 9/4 when k=100,
2 when k=75, and 3/2 otherwise. A control individual has outcome 11/8 when
k=100, 5/4 when k=75, and 1 otherwise. The observed arm mean is the sum of
these outcomes over individuals with own assignment b, divided by their number.
For every g<3 and each b, the witness arm mean is 9/4 (treated) or 11/8
(control) if g<2, and 2 or 5/4 if g=2. Applied to actual sums of these means
over {0,1} and {2}, the pooled and printed functions give the four numerical
values in the first conjunct. This explicitly ties the scalar discrepancy
to the 450-individual schedule and an admissible allocation.

The docstring discloses omission of the explicit complementary count 12,
strict positivity of the scalar discrepancy for positive numerators,
and equal-subclass-mean doubling.

Junk/domain audit: `none` for empty subclasses is an intentional undefinedness
representation; it does not substitute zero for a printed ratio. All `some`
ratios have positive total or subclass counts. The general discrepancy identity
assumes both counts positive. A generic arm mean returns zero when its realised
arm is empty, but all arm means asserted in this witness have arm sizes 50 and
25, hence nonzero. Generic crMass can have empty support for k>n; the counts
here are 25 and 50 within 75 and the concrete assignment witnesses nonempty
support. The first-stage finite set contains H0, so is nonempty. Population
cardinalities are ordinary natural counts, cast exactly into the reals when
used as denominators. No truncated subtraction, nonfinite expectation,
unbounded extremum, or defaulted partial access enters the statement.

## SAP.P045a.T15

The theorem is `T15WholeStatement` (`Defs/WholeW2.lean:185`), including
`T15Statement` (`Defs/Part6.lean:13`). Its independently quantified portions
are the following.

First, for every natural a,b, every real A,B, assuming a+b>0:
pooled(a,b,A,B)=some((A+B)/(a+b)); if a>0 and b>0 then
(A+B)/(a+b)=[a/(a+b)](A/a)+[b/(a+b)](B/b); and if a=0 and A=0 then
pooled(a,b,A,B)=some(B/b). `pooled` has precisely the optional-value
definition in T14. No numerator/count consistency is required for this
scalar algebra, except A=0 in the displayed empty-subclass implication.

Second, for every finite subset H of the six fixed paired groups and every
real function m on these groups, the cardinality and sum over H partition
into g whose partner belongs to H and g whose partner does not.

Third, define a full two-stage probability law. Its sample type is pairs
(H,w), where H is any subset of six groups and w assigns a Boolean assignment
on 75 individuals to every group. Write k_H(g)=50 if g is in H, and 25
otherwise. The second-stage mass is the product over all six groups of
crMass(75,k_H(g),w_g), with crMass and fixed-count support as described in T14.
The two-stage mass is zero unless H has three elements, and otherwise is
(1/|F|) times this second-stage product, where F consists of all three-element
subsets. Thus conditional on H the group assignments are independent and
uniform within their prescribed counts. The theorem asserts nonnegativity,
total mass one, and, for every (H,w), strict positivity if and only if
H is in F and every w_g has count k_H(g).

Use the full interference outcome schedule from T14 (treated/control levels
9/4,11/8 at combined partner count 100; 2,5/4 at count 75; 3/2,1 otherwise),
and define M_g(b,w) as its observed group arm mean. The direct estimator is
D(H,w)=[sum_{g in H} M_g(true,w)]/|H|
       -[sum_{g in H} M_g(false,w)]/|H|.
For every H in F and every w, if every group has the prescribed count, then
each g in H has both own arms nonempty and M_g equals (9/4,11/8) if its
partner is also in H, and (2,5/4) otherwise. Under these same hypotheses,
D(H,w) is the selected sum of arm differences divided by 3, and also
[a(H)/3](7/8)+[(3-a(H))/3](3/4), with a(H) as in T14.

Next define the all-psi reference law on w as the product of uniform
50-of-75 laws at every group, including partners. For every group g,
individual i and Boolean b, the probability of own assignment b in this
reference law is 2/3 for true and 1/3 for false. The conditional expectation
of that individual's outcome given that assignment is 9/4 for true and
11/8 for false. Conditional expectation here is explicitly the finite
weighted sum restricted to the event divided by its event probability.

The psi-psi target is the average over three tracts of the difference of
the two individual-arm potential-outcome averages within each tract.
The tract coordinates (0,0),(0,1),(1,0),(1,1),(2,0),(2,1) enumerate groups
0,1,2,3,4,5, respectively; each tract average is over two groups times
75 individuals. This target is 7/8. The uniform first-stage expectations
of a(H)/3 and (3-a(H))/3 are 2/5 and 3/5. The full-law expectation
of D is 4/5 and its bias against the psi-psi target is -3/40.

Fourth, for every type G with decidable equality, then every finite subset
H of G, every function partner:G->G and every function m:G->real, define
P={g in H:partner(g) in H}, Q={g in H:partner(g) not in H},
a=|P|, b=|Q|, A=sum_{g in P}m(g), B=sum_{g in Q}m(g).
No finiteness assumption on the ambient type, pairing involution, or stochastic
law is required. The theorem asserts disjointness of P,Q, their union H,
|H|=a+b, and sum_H m=A+B. If a+b>0 then the finite-set average
(sum_H m)/|H| equals (A+B)/(a+b), and pooled(a,b,A,B) is `some` of that
average. If both a and b are positive then the shares a/(a+b) and b/(a+b)
are strictly positive, sum to one, and the average equals their weighted
mixture of A/a and B/b. If a=0 and b>0 then A=0 and the average is B/b.

Finally the theorem gives 9/4-11/8=7/8, 2-5/4=3/4, and
E[D]=(2/5)(7/8)+(3/5)(3/4). Its docstring describes all these portions and
states that the usual measure-theoretic conditions are assumed.

Junk/domain audit: empty finite sets have sum zero; the generic average returns
zero on an empty set because real division by zero is total. Assertions
interpreting that average as a mean require a+b>0 or b>0. Optional pooling
explicitly rejects zero total count. The scalar mixture requires both counts
positive. The empty-first-subclass scalar assertion requires A=0; the general
set assertion proves that zero numerator from the empty set. The expression
3-a(H) is real subtraction, not truncated natural subtraction; on supported
three-group selections, 0<=a(H)<=3. All fixed-count supports use feasible
25- or 50-of-75 counts. Conditional means use probabilities 2/3 and 1/3.
Realised arm means outside the two-stage support may use Lean's empty-arm zero,
and D for H empty likewise evaluates to zero, but these assignments have
exactly zero probability. On every positive-mass assignment all selected arm
sizes and |H|=3 are positive. Consequently those totalizations cannot affect
any asserted expectation. The all-psi law also gives both arms positive at
every supported group. All spaces and sums are finite; no Bochner integral,
`toReal` of infinity, asymptotic limit, unbounded extremum, logarithm, square
root, real power or defaulted partial function is used.
