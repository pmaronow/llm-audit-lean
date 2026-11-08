# Blind reading

Saved before opening `claims.json` or `record.json`. Sources read: all entries of
`closure.json`, the five Challenge docstrings and statements in
`SAP/P003a/Challenge/Part2.lean`, and every source declaration in their closures.
Generated line-zero declarations were also inspected with `#print` in
`scratch/PrintClosure.lean`; they only certify numeral denominators are at least
two or that a finite index size is nonzero. In particular, the apparently
unrelated T14 and search-cost auxiliary proofs in T9/T10 are numeral instances,
not additional mathematical premises.

All sums over finite types or lists below are ordinary finite sums. A sum over
all integers is Mathlib's `tsum`. In a real Banach space, `Summable` entails
absolute summability; a `tsum` without summability uses Mathlib's totalized
convention, which gives zero for a nonsummable real family. No theorem below
uses an unguarded infinite mean: its relevant mass has a summable first moment
or is explicitly finitely supported.

## SAP.P003a.T9

Location: Challenge/Part2.lean:21–29; body is `T9WholeStatement`,
Defs/WholeW2.lean:255–265, including `T9Statement`, Defs/Part9.lean:23–32.
The docstring calls the printed claim false and describes dependent examples.
The Lean statement is a conjunction of the following facts, with no external
hypotheses or existentially unspecified data.

For a real function f on the integers, the mass predicate means:

* f(j) ≥ 0 for every integer j;
* f is summable, its sum is 1, and j ↦ j f(j) is summable.

The SD predicate means this mass predicate and existence of an integer c2 such
that sum_j j f(j) = c2/2, f(c2−j) = f(j) for every integer j, and, for every
integer i,j, c2 ≤ 2i and i ≤ j imply f(j) ≤ f(i). Thus the center may be an
integer or a half-integer, and decrease is weak, on the right of that center.
These are the full unfoldings of `IsMass`, `IsSD`, and `SDShape` here.

First set F(j) = (1/2 if j=0, else 0) + (1/2 if j=1, else 0), and
D(j) = (1/2 if j=0, else 0) + (1/2 if j=2, else 0).
F is SD with mean 1/2. D is a mass with mean 1, D(1)=0, D(2)=1/2,
and D is not SD. For every integer j, summing weight 1/2 over the two Booleans
b with indicator 1_b=j gives F(j), and summing weight 1/2 with
2*1_b=j gives D(j). This specifies the joint construction X=Y=1_b with a
uniform Boolean b; it does not assume or assert independence.

The second construction uses the finite type `Fin 4`, with

| atom | X | Y | weight |
| --- | --- | --- | --- |
| 0 | −1 | 0 | 1/3 |
| 1 | 0 | 0 | 1/6 |
| 2 | 0 | 1 | 1/6 |
| 3 | 1 | 1 | 1/3 |

Every weight is positive and their finite sum is 1. Define
A(j) = (1/3 if j=−1, else 0) + (1/3 if j=0, else 0) +
(1/3 if j=1, else 0) and
B(j) = (1/3 if j=−1, else 0) + (1/6 if j=0, else 0) +
(1/6 if j=1, else 0) + (1/3 if j=2, else 0).
For every integer j, the sums of weights of atoms with X=j, Y=j, and
X+Y=j are respectively A(j), F(j), and B(j). A is SD with mean zero.
B is a mass with mean 1/2, satisfies B(1−j)=B(j) for every integer j,
has B(1)<B(2), and is not SD. This spells out `w2BX`, `w2BY`, `w2BW`,
`w2ThreeMass`, and `w2BSumMass` as well as the first two mass definitions.

Quantifiers: the finitely chosen laws are fixed; all their pointwise assertions
range universally over integers or the four finite atoms. The SD predicates
internally existentially quantify the doubled center after fixing the law.
The negative SD assertions rule out every integer doubled center satisfying
the full predicate.

Junk conventions: 2, 3, and 6 are nonzero real denominators. Every infinite sum
is finite-support and absolutely convergent, or is protected by `IsMass`.
The index types Bool and Fin 4 are inhabited. There is no natural subtraction,
integer division, real logarithm, square root, real power, infinite measure,
partial lookup, extremum, or limit in this statement. Finite vector indexing
is total because its indices have type Fin 4. The integer-to-real casts are
the usual exact embeddings.

## SAP.P003a.T10

Location: Challenge/Part2.lean:31–34; body `T10Statement`,
Defs/Part9.lean:35–44. The docstring describes independent fair smoothing,
center shifts, and parity-lattice masses.

For a real function f on the integers, SD means: f is everywhere nonnegative;
f and j ↦ j f(j) are summable; sum_j f(j)=1; and there exists an integer c
with sum_j j f(j)=c/2, f(c−j)=f(j) for all j, and
f(j)≤f(i) whenever c≤2i and i≤j. The shape predicate alone consists of the
last symmetry and monotonicity conditions and requires no normalization,
summability, sign, or moment condition.

The theorem has three separately universally quantified conjuncts:

1. For every f:Z→R with the above SD predicate, g(j)=(f(j)+f(j−1))/2
   has that SD predicate. This is convolution with an independent uniform
   zero-one variable, expressed directly as a mass formula.
2. For every f:Z→R and integer c, if f(c−j)=f(j) for all j and
   f(j)≤f(i) whenever c≤2i and i≤j, then g has the same shape with
   doubled center c+1. No probability-law premise occurs in this conjunct.
3. For every f:Z→R satisfying SD and then every integer p with p=0 or p=1,
   let h(j)=f((j−p) div 2)/2, where `div` is Mathlib integer Euclidean
   division (floor division for the positive divisor 2). Then h is SD and,
   for every integer k, h(p+2k)=f(k)/2 and h(p+2k+1)=f(k)/2.
   Equivalently this is the law of 2X+p+B for independent fair B in {0,1}
   and integer X of mass f; the unsmoothed support is p+2Z.

These formulas fully unfold `smoothMass` and `paritySmooth`, including the
rounding operation; p is a parity representative, not a real shift parameter.
In each SD conclusion the center is existentially quantified anew. The first
two quantifier blocks are independent of the third.

Junk conventions: division by 2 is always legitimate. Integer floor division
in the parity formula is intentional for odd inputs and negative integers;
the two asserted residue formulas specify both branches. The divisor is
never zero. Infinite sums in SD are summable by its definition; the
shape-only conjunct contains no infinite sum at all. No empty finite index,
natural truncation, partial function, integral, infinity-to-real cast,
logarithm, square root, real power, extremum or asymptotic limit is used.
All relevant integer-to-real casts are exact.

## SAP.P003a.T15

Location: Challenge/Part2.lean:36–46; body `T15WholeStatement`,
Defs/WholeW3.lean:60–89. The docstring asserts SD for every positive balanced
design with a discordant unit, base laws, residual laws, and proof-gap examples.

An input population v=(a,b,c,d) consists of four natural counts of potential
outcome pairs (11,10,01,00); N=a+b+c+d. For a natural m, the list of treated
states contains all q=(qa,qb,qc,qd) obtained in this order:
qa ranges from 0 to min(a,m); qb from 0 to min(b,m−qa);
qc from 0 to min(c,m−qa−qb); qd is m−qa−qb−qc and the state is kept
exactly if qd≤d. Subtractions here are natural truncated subtraction.
The state weight is
choose(a,qa)choose(b,qb)choose(c,qc)choose(d,qd), where the implemented
`Nat.fast_choose` agrees with Mathlib `Nat.choose`.
Its observed cell counts are
o(q)=(qa+qb, qc+qd, a−qa+c−qc, b−qb+d−qd).
Subtractions in this formula are also natural subtraction, evaluated left
associatively as written in Lean; all states used here are coordinatewise
feasible, so no subtraction is truncated incorrectly.
For observed o=(A,B,C,D), define the rational
t(o)=A/(A+B)−C/(C+D).
For any state event E define
P_v,m(E) = sum_over_list_q [1_E(q) weight(q)] / choose(N,m), in R.
Thus the integer-indexed mass at j is P_v,m(m*t(o(q))=j), with the equality
computed in Q. The physical rational mass at x is P_v,m(t(o(q))=x).
These unfold `Counts`, `Counts.total`, `randomStates`, `binomial`,
`multiplicity`, `observed`, `estimateQ`, `designProb`,
`scaledEstimatorMass`, and `wholeEstimatorMass`.

For any integer-indexed f, SD here means: f≥0 pointwise; f and j f(j) are
summable; sum f=1; and there exists c2 in Z with sum j f(j)=c2/2,
f(c2−j)=f(j) for all j, and f(j)≤f(i) for all c2≤2i and i≤j.

The full statement is the conjunction of these seven blocks:

1. For every v and m, if m>0, N=2m, and b+c≥1, then the mass of m*t
   defined above is SD.
2. For every v with N=2 and b+c≥1, v occurs among the following seven
   rows. For every listed row and then every rational x, the physical mass
   at x is (1/2 if x=l, else 0)+(1/2 if x=u, else 0), for these endpoints:

   | v | l | u |
   | --- | --- | --- |
   | (1,1,0,0) | 0 | 1 |
   | (0,1,0,1) | 0 | 1 |
   | (1,0,1,0) | −1 | 0 |
   | (0,0,1,1) | −1 | 0 |
   | (0,2,0,0) | 1 | 1 |
   | (0,0,2,0) | −1 | −1 |
   | (0,1,1,0) | 0 | 0 |

   The two coincident endpoint contributions add to 1; no atom is lost.
3. For every v,m with m>0 and N=2m, if b+c=1 or b+c=2, the integer
   mass of m*t is SD. This repeats a special case of block 1 explicitly.
4. Every removal in either list
   R10=[(1,1,0,0),(0,2,0,0),(0,1,1,0),(0,1,0,1)] or
   R01=[(1,0,1,0),(0,1,1,0),(0,0,2,0),(0,0,1,1)]
   has total count 2 and at most two discordant units.
5. For every v,m with m>0, N=2m, b+c≥3, one has b≥2 or c≥2.
   For every removal r in those lists with each coordinate ≤ the
   corresponding coordinate of v, let u be the coordinatewise natural
   difference v−r. Then u.total=2(m−1), m−1≥1,
   b+c−2≤u.b+u.c, u.b+u.c≥1, and the mass of (m−1)*t under u
   with m−1 treated is SD. The residual quantifier follows the chosen v,m.
6. Define the printed induction-case predicate at v to be
   (b=1 and c=0) or (b=0 and c=1) or c+c=2 or
   [2<c+c and ((b≥2 and c≥1) or (b≥1 and c≥2))].
   Each v in [(0,4,0,0),(1,3,0,0)] has N=4, b+c≥1, min(b,c)=0,
   and fails that predicate. At v=(1,2,1,0), c+c=2 but b+c=3.
   The removal (0,1,1,0) is feasible from (0,4,1,1), its residual is
   (0,3,0,1), and the minimum residual discordant count is zero.
7. For every row in the next table, for every rational x, the complete
   m=2 physical mass is the same two-endpoint formula as in block 2,
   and the mass of 2*t is SD:

   | v | l | u |
   | --- | --- | --- |
   | (0,4,0,0) | 1 | 1 |
   | (1,3,0,0) | 1/2 | 1 |
   | (1,2,1,0) | 0 | 1/2 |
   | (0,3,0,1) | 1/2 | 1 |

The lists and formulas in blocks 2–7 fully unfold `wholeBaseRows`,
`wholeWitnessRows`, `wholeRemovals10`, `wholeRemovals01`, `wholeCountsLE`,
`wholeCountsSub`, `wholePrintedInductionCases`, and `wholeTwoPointMass`.
There is no unmentioned stochastic assumption: complete randomization is the
weighted finite list law itself.

Junk conventions: positive balance gives 0<m<N, choose(N,m)>0, and both
observed arms have size m. The rational and real divisions in the actual
probabilities and estimator therefore have nonzero denominators. The
unrestricted definitions would assign 0 to division by zero, but these uses
exclude it. The residual feasibility premise makes coordinate subtraction
ordinary subtraction; b+c≥3 and N=2m imply m≥2, so m−1 is positive.
List bounds make qd and observed residuals valid. Every SD mass here is
finitely supported, hence every mass sum and first moment exists. Lists
with membership premises are explicit and nonempty. No integral, extended
real, logarithm, square root, real power, extremum, limit, or partial lookup
occurs. Casts N→Q/R and Z→Q/R are exact; integer j may be negative even
though population and assignment counts are natural.

## SAP.P003a.T16

Location: Challenge/Part2.lean:48–58; body `T16WholeStatement`,
Defs/WholeW3.lean:164–195. The docstring describes a uniform partner sampler,
a corrected signed pair decomposition, and both signed and printed pair laws.

A table w is a function Fin n→Bool×Bool. Let bit(false)=0 and
bit(true)=1 in R, and write w(k)=(Yk(1),Yk(0)) in binary numeric form.
An assignment is a finite subset z of Fin n with cardinality m. Its estimator
is sum_{k in z}Yk(1)/|z| − sum_{k not in z}Yk(0)/(n−|z|).
For a finite type Omega, the probability of E is
|{omega in Omega:E(omega)}|/|Omega| as a real quotient.
This unfolds `PotentialTable`, `bit`, `Assignment`, `tableEstimator`, and
`uniformProb`.

For a fixed label i, a partner is a label j≠i. Remaining labels are the
subtype {k in Fin n:k≠i and k≠j}. A residual assignment r is a finite
subset of Fin n of size m−1 excluding i and j. The sampling source is the
finite dependent sum over partners j of Bool × residual assignments for j.
For an element (j,b,r), the resulting assignment is r union {i} if b is
true and r union {j} otherwise. For fixed j and predicates E on Bool and
F on that j's residual assignments, its rectangular event is precisely
{(j,b,r):E(b) and F(r)}. These unfold `WholePartner`, `WholeRemaining`,
`WholeResidualAssignment`, `WholePairSource`, `wholePairSample`, and
`wholePairRectangle`; their laws are asserted rather than put into the types.

Write s(w,z,k)=Yk(1) for k in z and −Yk(0) otherwise.
The signed pair value L(wi,wj,b), an integer, is Yi(1)−Yj(0) for b=true
and Yj(1)−Yi(0) for b=false. The residual contribution is
sum_{k≠i,j} s(w,z,k)/m. Given a bijection e from Fin(n−2) to the remaining
labels, the restricted table has values w(e(k)), and its restricted treated
set is {k:e(k) in z}. These unfold `wholeSignedTerm`, `pairContribution`,
`wholeResidualContribution`, `wholeRestrictedTable`, and
`wholeRestrictedAssignment`.

The statement has four conjuncts, with independent quantifier blocks:

1. For all natural n,m with m>0 and n=2m, then every w and assignment z,
   its estimator equals sum_k s(w,z,k)/m.
2. For all such n,m and then every i in Fin n: the sampling source is
   nonempty; for every partner j both an e as above and a residual
   assignment exist; every sampled assignment has size m; for every
   predicate E on finite subsets of Fin n, its probability under the sampled
   assignment equals its probability under the uniform size-m assignments;
   and for every fixed j and predicates E,F, the rectangular source
   probability is (1/(n−1))*uniform_Bool(E)*uniform_residual(F).
3. For all such n,m, then every w,z,i,j with i in z iff j not in z, the
   estimator equals L(wi,wj,1_{i in z})/m plus the residual contribution.
   If m=1 that residual is zero. For every e as above, its restricted treated
   set has cardinality m−1 and its signed sum divided by m equals that
   residual. If m>1, the residual equals ((m−1)/m) times the restricted
   table's estimator.
4. Twelve complete probability laws hold under uniform Bool. The first six
   concern L. The last six concern the printed expression P, obtained by
   replacing each displayed minus in L with plus. In each row the law is
   (1/2 at the first listed value)+(1/2 at the second listed value), zero
   at every other integer, including the coincident-atom case:

   | wi | wj | values of L | values of P |
   | --- | --- | --- | --- |
   | (1,0) | (1,1) | 0,1 | 2,1 |
   | (1,0) | (1,0) | 1,1 | 1,1 |
   | (1,0) | (0,1) | 0,0 | 2,0 |
   | (1,0) | (0,0) | 1,0 | 1,0 |
   | (1,1) | (1,1) | 0,0 | 2,2 |
   | (1,1) | (0,0) | 1,−1 | 1,1 |

The last block unfolds `WholeFairLaw`, `WholePairLaws`, and
`wholePrintedPair`; these definitions specify literal formulas and complete
finite laws, rather than assuming any estimator identity.

Junk conventions: all n,m in conditional blocks satisfy n=2m≥2 and m≥1.
Thus n−1≥1, m>0, original arm sizes m>0, and all finite source and
assignment types used for probability are nonempty (asserted explicitly for
the sampler, and guaranteed by the size bounds). Uniform probability on an
empty finite type would use 0/0=0, but it is not used here. Natural n−2
and m−1 are legitimate residual sizes, including zeros when m=1. The
restricted estimator is used only when m>1, so its two denominators m−1
are positive. For m=1 the residual has no terms and is correctly zero.
`Fin n` and `Fin(n−2)` are total finite index types; the latter can be empty,
which is harmless for the bijection and empty sum. No infinite sum, integral,
extended-real cast, logarithm, square root, real power, extremum, limit, or
partial function occurs. Pair differences are integers, not truncated
natural subtraction; their casts into R preserve negative values.

## SAP.P003a.T17

Location: Challenge/Part2.lean:60–70; body `T17WholeStatement`,
Defs/WholeW3.lean:232–277. The docstring asserts the variance algebra,
a fixed-C extension, two five-subject examples, and Monte Carlo validity.

Counts are natural quadruples. A potential table w:Fin n→Bool×Bool has
counts v=(a,b,c,d) equal to the cardinalities of the four types
(11,10,01,00); its real mean effect is
sum_k(bit(wk.1)−bit(wk.2))/n. At the counts level the same parameter is
the real cast of the rational ((b:Z)−c)/(a+b+c+d). Here the subtraction
is signed integer subtraction. For a finite set z, unit outcomes choose
wk.1 on z and wk.2 off z; the observed counts record respectively the
number of treated ones, treated zeros, control ones, and control zeros.
For arbitrary observed counts o=(A,B,C,D), its estimate is the real cast
of rational A/(A+B)−C/(C+D). The unit-level estimator uses the identical
two finite sums of binary outcomes divided by |z| and n−|z|.
These unfold `Counts`, its projections/constructor/total/effect,
`PotentialTable`, `bit`, `tableCounts`, `tableTau`, `tauQ`, `tau`,
`estimateQ`, `estimate`, `unitOutcomes`, `unitObserved`, `tableEstimator`.

Define, entirely in R,
Q(a,b)=a*(a/(a+b)−1)^2+b*(a/(a+b))^2,
Vprint(o)=Q(A,B)/(A+B)^2+Q(C,D)/(C+D)^2,
V(o)=A*B/(A+B)^3+C*D/(C+D)^3,
SE(o)=sqrt(V(o)), and
R_C(o,v)=C if SE(o)=0, else (estimate(o)−tau(v))/SE(o).
Rprint_C uses sqrt(Vprint) in that same conditional definition.
This unfolds `wholeBinaryQ`, `wholePrintedVariance`, `varianceEstimate`,
`standardError`, `studentized`, and `wholePrintedStudentized`.

Given K natural and observed count vectors o1,...,oK, the observed-rank
formula is
S_C(o,v;(oi))=[1+sum_{i in Fin K} 1{|R_C(oi,v)|≥|R_C(o,v)|}]/(K+1).
The treated-state rank first sends every sampled state q to observed(v,q),
where observed(v,q)=(qa+qb,qc+qd,a−qa+c−qc,b−qb+d−qd), with natural
subtraction. These unfold `wholeObservedRank`, `rankValue`, and `observed`.

Uniform probability on a finite type is event cardinality divided by the
type's cardinality in R. Assignment(n,m) is the type of finite subsets
of Fin n of cardinality m. The complete-randomization state probability
used in the final examples is the weighted finite list probability: enumerate
qa=0..min(a,m), qb=0..min(b,m−qa), qc=0..min(c,m−qa−qb), put
qd=m−qa−qb−qc and keep qd≤d; weight each state by the product of the four
binomial coefficients choose(vtype,qtype), and divide the total event weight
by choose(a+b+c+d,m). This unfolds `uniformProb`, `Assignment`,
`randomStates`, `binomial` (=Mathlib Nat.choose), `multiplicity`, and
`designProb`.

The theorem is a conjunction of seven blocks:

1. For every observed o with A+B>0 and C+D>0,
   Q(A,B)=AB/(A+B), Q(C,D)=CD/(C+D), Vprint(o)=V(o), V(o)≥0,
   and SE(o)=0 iff A*B=0 and C*D=0 (the last products are in N).
2. For every real C, then o,v with both observed arms positive,
   Rprint_C(o,v)=R_C(o,v); if SE(o)=0 the latter is C; and if
   SE(o)>0 it is the displayed quotient. C is quantified before any data.
3. For every real C, natural K, o,v, and function samples:Fin K→Counts,
   the treated-state rank equals S_C(o,v;observed(v,samples(i))).
   This is an algebraic identity for all inputs, including dependent or
   infeasible samples, and makes no probability assertion about them.
4. There are exactly 10 assignments of two treated out of five. For the
   constant table w(k)=(0,0), its counts are (0,0,0,5), its unit- and
   counts-level effects are zero, every such assignment observes (0,2,0,3)
   and has estimate zero, V=SE=0 at these observations, and R_C=C for
   every real C.
5. For the table w(0)=(0,1) and w(k)=(0,0) for k≠0, its counts are
   (0,0,1,4), and both effect formulas are −1/5. Four of the ten
   assignments include label 0 and six do not. All assignments in the
   first class observe (0,2,0,3), while all in the second observe
   (0,2,1,2). At the first observation SE=0 and estimate−tau=1/5.
   At the second, estimate=−1/3 and V=2/27. The two tables in blocks
   4 and 5 unfold `wholeZeroTable` and `wholeOneControlTable`.
6. For every natural n,m,K, every w, and then every real C,alpha, if
   0<m<n, K>0, and 0≤alpha≤1, take a uniform element of the finite
   function type Fin(K+1)→Assignment(n,m). Its coordinate 0 supplies
   the observed assignment and its coordinates i+1 supply all K samples.
   From each assignment obtain observed counts from the fixed w. Holding
   v=tableCounts(w) and C fixed, the probability that the rank S_C of
   this observation among those K fresh observations is ≤alpha is ≤alpha.
   The uniform law on the whole function type is exactly independent
   uniform coordinates; the statement does not replace it by an arbitrary
   joint law with uniform marginals.
7. For the fixed counts v=(0,0,1,4), m=2, and fixed observed
   o=(0,2,0,3), the complete-randomization probability
   P(|R_C(observed(v,q),v)|≥|R_C(o,v)|) equals 1 for C=0 and equals
   2/5 for C=10^6. These are exact probabilities, not Monte Carlo ranks.

Junk conventions: for the first two algebraic blocks the two arm-size
denominators are positive. Variance is nonnegative by its explicit formula
with natural counts, so `Real.sqrt` is never evaluated on a negative
variance; `Real.sqrt` would otherwise return zero. The zero-SE branch is
an intentional, explicit constant extension and is tested on genuine
positive-arm examples with zero SE, including a nonzero numerator. It is
not an accidental 0/0 convention. The parameter tau on an empty counts
vector, estimates with empty arms, and infeasible treated states in block
3 use Lean's totalized rational/real division and truncated subtraction;
block 3 asserts only the literal identity using the same total functions
on both sides. No validity conclusion there uses those exceptional inputs.
K+1 is always positive, including for the identity with K=0, where the
rank is 1. The probability block assumes K>0 and 0<m<n, making both
arms and the assignment type nonempty. Its product type is nonempty.
The exact examples have choose(5,2)=10 and positive arms. Their state
enumeration enforces feasibility, so natural subtraction gives genuine
residual counts. `n−|z|` is natural subtraction but |z|≤n for all finite
subsets; it is positive in the experiments. No Bochner integral, infinite
sum, infinity-to-real map, logarithm, real power, extremum, limit, or
default value of a partial function appears. Fixed powers 2,3,6 are
natural exponentiation. All numeric casts are exact embeddings.
