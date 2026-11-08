# Blind reading

Saved before opening either `claims.json` or `record.json`. Sources read: all five
Challenge declarations and their docstrings; all named definitions in their
`closure.json` entries; all 83 distinct generated auxiliary declarations, printed
by `scratch/ClosurePrint.lean` (successful compilation, output in
`scratch/closure-print.log`). The auxiliary declarations are numeral-instance
certificates, the cardinality proof for a five-element set, and the positivity
and normalization proofs for the explicit cutoff law. They impose no extra
mathematical hypotheses. References below use actual source line numbers.

Common notation: `[n] = {0,...,n-1}` (Lean `Fin n`); all sums/products over a finite
type run over every element. A finite set is a duplicate-free `Finset`; its
cardinality is a natural number. Fractions in probability formulas are real
fractions, with natural cardinalities embedded in the reals. An indicator is 1
when its predicate holds and 0 otherwise. Subset statements are pointwise
implications. No audited statement uses a Bochner integral or an extended real.

## SAP.P037b.T21

Location: `SAP/P037b/Challenge/Part1.lean:38-42`; statement definition:
`SAP/P037b/Defs/Part2.lean:62-91`.

**Definitions unfolded.** Write S(n,m) for all m-element subsets of [n], namely
the cardinality-m part of the powerset of [n]. For four subsets A,P,R,s of [n],
define L(A,P,R,s) as follows, in this order: 4 if s intersects A; otherwise 1 if
s is disjoint from P; otherwise 2 if s is disjoint from R; otherwise 3. Thus L
never takes value 0. Define q(n,m,A,P,R,0)=1/2 and, for k=1,2,3,4,
q(n,m,A,P,R,k)=#{s in S(n,m): L(A,P,R,s)=k}/(2 choose(n,m)). The five labels are
therefore control, no seeded peer, nonreferent seeded peer only, referent seeded
peer, and direct seed, respectively, in the concrete configurations at issue.

**Full assertion and quantifiers.** This is an unconditional conjunction about
fixed finite data, with universal label indices and one existential sequence:

1. |S(12,6)|=924. For every k in [5], q(12,6,empty,{0,1,2,3,4,5},{0},k)
   is the kth coordinate of (1/2,1/1848,461/1848,1/4,0). For every k in [4],
   the kth coordinate of (1/2,1/1848,461/1848,1/4) is strictly between 0 and 1.
   In particular 0<1/1848<1/100.
2. For every k in [5], q(12,6,{2},{0,1},{0},k) is the kth coordinate of
   (1/2,1/22,3/44,3/22,1/4). Each of its first four coordinates exceeds 1/100.
   Both {2,3,4,5,6,7} and {3,4,5,6,7,8} belong to S(12,6). Their L labels
   for A={2}, P={0,1}, R={0} are respectively 4 and 1.
3. There exists a sequence z:[10000] -> Bool x Finset([12]) such that every
   z(j).second belongs to S(12,6). Set D(j)=L(empty,{0,...,5},{0},z(j).second)
   if z(j).first is true, and D(j)=0 otherwise. For every k in [4],
   #{j:D(j)=k}/10000 is the kth coordinate of
   (1/2,1/2000,499/2000,1/4). There is no independence or sampling law asserted
   for this existential, deterministic sequence.
4. For every k in [5], the raw numbers of local subsets with label k are
   (0,1,461,462,0) in the first configuration and (0,84,126,252,462) in the
   second. The four-coordinate probability vector in item 1 sums to 1; the
   five-coordinate vector in item 2 sums to 1. Every coordinate of the simulated
   four-vector in item 3 is positive, and 1/2000<1/100.

The docstring calls this a restricted result and explicitly omits conditional
probability 1/924 for the two named selections and a fuller membership-change
assertion with outcome, baseline, school, and frequency masks. No such clauses
are hidden in the Lean proposition.

**Junk-value audit.** Real division uses 0 inverse = 0. The general q definition
would consequently assign nonsensical zero conditional masses when m>n and
choose(n,m)=0, while still setting q(0)=1/2. Here only (n,m)=(12,6) occurs, with
choose(12,6)=924>0, and the simulation denominator is 10000>0. All set numerals
lie within [12]; all label numerals lie within [5]. `Fin` numerals are in general
reduced modulo their size, but no reduction changes these values. `castSucc`
embeds labels 0,...,3 in [5] without changing them. Empty self-sets mean an
ineligible focal student and are intentional. There are no truncated
subtractions, square roots, logarithms, real powers, infima/suprema, limit
operators, empty index types, partial-function defaults, or nonintegrable means
in this statement or its definitions. Generated number proofs from other named
statements contribute only arithmetic typeclass evidence, not those statements.

## SAP.P037b.T22

Location: `SAP/P037b/Challenge/Part1.lean:44-66`; principal definition:
`SAP/P037b/Defs/WholeW2.lean:188-248`, including
`SAP/P037b/Defs/Part2.lean:94-117` and the named W2 substatements.

**Definitions unfolded.** A finite design on a finite type O consists of real
masses p(z)>0 for every z in O with sum_z p(z)=1. Its probability of E is
sum_z p(z)1_E(z). In particular O cannot be empty, and its listed points are
exactly its support. For D:O x I -> [5], write
pi(i,k)=sum_z p(z)1_{D(z,i)=k}, k=0,1,2,3, and piD(i)=Pr(D(z,i)=4).
For J>0 and a sequence d:[J]->O, let H(E,d)=#{j:E(d(j))}, f(E,d)=H(E,d)/J,
and phat(i,k)=#{j:D(d(j),i)=k}/J, k=0,...,3. A sequence has product mass
w(d)=product_j p(d(j)); product-law probabilities and expectations are sums of
w(d) times indicators or values over *all* sequences. Independence is therefore
part of the law, not an assumption that arbitrary deterministic sequences have.

For a four-vector field v on I, let P(v)={i: for every k, 0<v(i,k)<1} and
C_c(v)={i: for every k, c<v(i,k)}. For predicates seed,outcome,baseline,screen on
O x I, define
M(z)={i: i in C_(1/100)(v), not seed(z,i), outcome(z,i), baseline(z,i), screen(z,i)}.
For finite I its finite-set version A(z) consists of exactly these elements.
Its prediction average for g:I x [4]->R is sum_{i in A(z)}g(i,k)/|A(z)|.
The printed average uses B={i: every pi(i,k)>0} and denominator |B| instead.
An O-indexed family M is almost surely constant precisely if there exists one
set A subset I for which sum_z p(z)1_{M(z)=A}=1.

The specific cutoff design has O=Bool x ([4] -> S(12,6)), where the subsets are
subtypes carrying a proof of cardinality 6. Every point has mass
1/(2*924^4), strictly positive, and the support has size 2*924^4. Given self A,
peers P, and referents R in block zero, its exposure is 0 for a false school
indicator and otherwise L(A,P,R,s_0), with L defined in the preceding section.
The two-student network N(z,i), i in [2], uses (empty,{0,...,5},{0}) for i=0
and ({2},{0,1},{0}) for i=1. These definitions are explicit uniform legal-block
laws, not arbitrary probability-vector placeholders.

**Full assertion and quantifiers.** The following are conjoined. Universally
bound objects in one item need not equal those in another. The main W2 items
quantify types in universe 0; the included older statement has been specialized
to universe 0 as well. This is not a restriction on finite cardinality.

1. For every finite O, arbitrary type I, finite design p, D, natural J>0,
   sequence d:[J]->O, four arbitrary predicates seed,outcome,baseline,screen,
   and z in O, form pi and phat as above. Then P(pi)=C_0(pi),
   C_(.01)(pi) subset P(pi), C_(.01)(phat) subset C_0(phat),
   C_0(phat) subset P(pi), M(z) subset P(pi), and M(z) subset {i:not seed(z,i)}.
   This item does not require the arbitrary seed predicate to equal D=4.
2. For every finite design p and event E with 0<Pr(E)<1, the product-law
   probability that H(E,d)>=101 in 10000 draws is strictly between 0 and 1.
3. For every finite design p, arbitrary estimated four-vectors and masks, and
   i, Pr(seed(z,i))<=Pr(i not in M(z)). For every natural r<=10000,
   r/10000>.01 iff r>=101; if r>=101, 1/(r/10000)<=10000/101<100.
4. For every finite design p,D,J>0,d,i, and k in [5], pi_full(i,k)=0 implies
   f({z:D(z,i)=k},d)=0. This is pointwise over supported sequences.
5. For every finite design p,D,i, sum over all five label probabilities is 1;
   the sum over labels 0,...,3 plus piD(i) is 1; their four-label sum is <=1.
6. In the specific cutoff design, for its ineligible focal student (indexed by
   Unit), pi puts () in P(pi) but outside C_(.01)(pi). There exists a supported
   10000-sequence whose phat is (1/2,1/2000,499/2000,1/4), hence puts () in
   C_0(phat) but outside C_(.01)(phat).
7. For every finite design p,D,i,k in [4], let E={z:D(z,i)=k} and pE=Pr(E).
   For every natural r (without an r<=10000 hypothesis),
   Pr_product(H(E,d)=r)=choose(10000,r)*pE^r*(1-pE)^(10000-r).
   For every 10000-sequence, 10000*f(E,d)=H(E,d), and f>.01 iff H>=101.
   If i is in P(pi), the scalar event f>.01 has probability strictly between
   0 and 1. For every sequence, if i passes all four empirical .01 cutoffs,
   each reciprocal phat(i,k) is <=10000/101<100.
8. For every finite design p,D and i in P(pi), there exist representatives
   a:[4]->O realizing each indirect label. There exists a 10000-sequence using
   only these representatives, with exactly 2500 occurrences of each label,
   passing all four .01 cutoffs and having positive product mass. Also there
   exists w in O whose constant 10000-sequence has at least three zero indirect
   frequencies, fails the joint cutoff, and has positive product mass. The
   product-law probability of passing the joint four-cutoff screen is >0 and <1.
9. For every finite design p,D, arbitrary real estimated four-vector field,
   masks outcome,baseline,screen, and i, now take seed(z,j) iff D(z,j)=4.
   Write pD=Pr(D(z,i)=4), pM=Pr(i in M(z)). For every z, M(z) contains only
   nondirect students; pD<=Pr(i not in M(z)); and pM<=1-pD. If pD>0 and pM>0,
   then 0<pM<=1-pD<1, pM<1, and M is not almost surely constant. The map M is
   measurable when both O and Set(I) carry the top (discrete) sigma algebra.
   A positive pD alone is not asserted to force nonconstancy.
10. For the explicit two-student cutoff network, Pr(N(z,1)=4)=1/4. There exists
    one 10000-sequence for which all four phat values for *each* of the two
    students equal 1/4. With this fixed sequence, seed iff N=4, outcome available
    iff i=0, and baseline/screen identically true, the finite analysis set is
    {0} for every realized z. With all three availability/screen masks true,
    there exist assignments a,b with N(a,1)=4 and N(b,1)=1, whose analysis sets
    are {0} and {0,1}, respectively.
11. For every finite O and finite I, design p,D,J>0, sequence d, arbitrary
    outcome/baseline predicates, Bool peerConflict, real schoolMean(z,i),
    realized z, prediction table g, and k in [4], define
    screen(z,i) iff peerConflict=false or schoolMean(z,i)>.02; seed iff D=4;
    estimated=phat; A the resulting finite analysis set; and B the fixed
    all-four-positive set. If A is nonempty, its prediction mean is exactly
    sum_{i in A}g(i,k)/|A| with |A|>0, and B is nonempty and its printed mean is
    sum_{i in B}g(i,k)/|B| with |B|>0. No relation between g and a fitted model is
    imposed: g is an arbitrary supplied prediction table.

The docstring describes these as the corrected canonical claim, assumes usual
measure-theoretic conditions (all laws here are finite), and asserts no study or
public-rerun sample size.

**Junk-value audit.** J is positive wherever it occurs as a denominator; the
fixed value 10000 and all cutoff-design denominators are positive. The two mean
definitions return 0 on empty sets by 0/0=0, but every assertion using them is
guarded by A nonempty and also concludes B nonempty. Reciprocals are asserted
only after frequencies exceed .01. In item 7, natural subtraction 10000-r
truncates to zero when r>10000, but choose(10000,r)=0 then; both the probability
and formula are zero, even with the standard 0^0=1 convention at endpoints.
Product laws with pE=0 or 1 use this convention and give the correct degenerate
binomial laws. Empty I makes the relevant set identities vacuous but does not
affect the separate strictness and mask examples; empty O admits no design
because normalization would say 0=1. All numerals in finite types are in range.
Predicates are classically decidable, with no partial-function defaults. The
top-sigma-algebra measurability conclusion is intentionally automatic and is
not a claim of regularity for an unspecified different sigma algebra. No logs,
square roots, real powers, extended-real conversions, order extrema, or limits
occur. The `CutoffBlockW2` cardinality proofs and law normalization are real
certificates, not hypotheses assuming any audited conclusion.

## SAP.P037b.T29

Location: `SAP/P037b/Challenge/Part1.lean:68-85`; principal definition:
`SAP/P037b/Defs/WholeW1.lean:254-287`, with `T29Statement` at
`SAP/P037b/Defs/Part2.lean:243-268` and selection certificates at
`SAP/P037b/Defs/WholeW1.lean:225-236`.

**Definitions unfolded.** Let Q be all 5-element subsets of [10]. Assignments
are pairs (b,s) in Bool x ([4]->Q). The constant real assignment mass is
1/(2*252^4). Exposure D is 0 if b=false; otherwise 1 if both s(0) and s(1)
are disjoint from {0,1,2,3,4}; otherwise 3 if 0 belongs to s(0); otherwise 2.
The subtype proofs enforce exactly five selected seeds in each of four blocks.
The focal student has no direct-seed label in this four-label model.
Define pi(k)=sum_z mass(z)1_{D(z)=k}, k in [4]. For a pair (u,v) in Q x Q,
Avoid(u,v) means both are disjoint from {0,...,4}; the named avoiding pair is
({5,6,7,8,9},{5,6,7,8,9}). Counts, frequencies, product masses, product-law
expectations and probabilities mean exactly the finite sums defined in T22.
The W1 variance of Y is the product expectation of
(Y-product_expectation(Y))^2, centered at its actual mean.

**Full assertion and quantifiers.** This is an unconditional conjunction about
this one fixed design, with the following universal sequences, labels and counts.

1. Its single-assignment masses sum to 1. For every k in [4], pi(k) is the kth
   coordinate of (1/2,1/127008,31751/127008,1/4), and 0<pi(k)<1. For every
   natural r, even r>10000, pi(1)<=|r/10000-pi(1)| and
   pi(1)/2<|r/10000-pi(1)|.
2. For H(d)=#{j:D(d(j))=1}, under the 10000-fold product law,
   E[H]=625/7938, Pr(H=0)=(127007/127008)^10000, and
   E[(H/10000-1/127008)^2]=127007/161310320640000.
   The zero-hit probability is strictly greater than 9/10 and less than 19/20.
3. The same distance inequalities are also stated numerically for every
   natural r, with lower bounds 1/127008 and, strictly, 1/254016.
   10000/127008=625/7938;
   p(1-p)/10000=127007/161310320640000 for p=1/127008;
   this value divided by p^2 equals 127007/10000;
   (1/2)(1-1/2)/10000=1/40000; (1/200)^2=1/40000.
4. choose(10,5)=252 and choose(9,4)=126. |Q|=252 and |Q x Q|=63504.
   For every (u,v) in Q x Q, its assignment-law marginal has mass 1/63504.
   Exactly one such pair avoids all peers, and universally Avoid(u,v) iff
   (u,v) is the named avoiding pair. Exactly 31752 pairs contain 0 in their
   first subset; exactly 31751 have 0 absent there and do not avoid all peers.
5. The four pi coordinates sum to 1. For every assignment its mass is positive
   and equals (1/2)*product_{h in [4]}(1/252). The masses of all 10000-sequences
   sum to 1.
6. Set p=1/127008. Then 0<p<1/20000 and p/2=1/254016. For every
   10000-sequence, let r=H(d). Then r<=10000. If r=0, |r/10000-p|=p. If r>=1,
   1/10000-p<=|r/10000-p| and p<1/10000-p. Always
   p<=|r/10000-p| and p/2<|r/10000-p|. This pointwise assertion is valid
   regardless of any chosen dependence law on the sequences.
7. Under the explicit independent product law, for every natural r<=10000,
   Pr(H=r)=choose(10000,r)*p^r*(1-p)^(10000-r). E[H/10000]=p. For the actual
   variance V of H/10000, V=127007/161310320640000,
   V/p^2=127007/10000, and sqrt(V)/p>7/2. Pr(H/10000=0) is the same stated
   power and exceeds 9/10 (the <19/20 bound remains in item 2).
8. For the control frequency H({D=0},d)/10000, its product-law mean is 1/2,
   its variance is 1/40000, and the real square root of its variance is 1/200.

The docstring calls this a synthetic four-block, forty-eligible school, with no
assertion that it occurred in the study. It distinguishes the pointwise grid
obstruction from the moments under independent draws and explicitly assumes the
usual measure-theoretic conditions.

**Junk-value audit.** Every denominator is a fixed positive integer, except
V/p^2 and sqrt(V)/p, whose denominator is the explicitly positive p. Both
square-root arguments are explicitly positive rational variances. `Real.sqrt`
would return zero on negative arguments, but this is not used. Binomial natural
subtraction occurs only with r<=10000; 0^0 is harmless in endpoint binomial
formulas. Subset/cardinality types are inhabited (for instance the named avoiding
pair and its repeated block selection), and all finite numerals are in range.
Expectation and variance are honest finite product sums with positive normalized
masses. No nonintegrability defaults, extended-real conversions, unbounded or
empty extrema, logarithms, real powers, limits, or partial-function defaults
occur. Numeral proofs with names from W1 cutoff or other statements are only
arithmetic instance declarations; those other statement bodies are not imported
as mathematical premises of this assertion.

## SAP.P037b.T30

Location: `SAP/P037b/Challenge/Part1.lean:87-90`; statement:
`SAP/P037b/Defs/Part3.lean:14-62`.

**Definitions unfolded.** Finite design, probability, counts, and product-law
probabilities mean precisely the finite sums in T22. For natural arrays
n,t,m:[b]->N, define
A(n,t,m)=(1/2)*product_h [choose(n_h-m_h,t_h)/choose(n_h,t_h)], with natural
subtraction before taking the numerator's binomial coefficient. The rare
four-label design and its pi are exactly those fully unfolded in T29.

**Full assertion and quantifiers.** The theorem conjoins the following groups;
variables in different groups are independent universal binders unless stated
existential.

1. For every finite O, strictly positive normalized design p on O, event E,
   natural J>0, let q=Pr(E), H(d)=#{j:E(d(j))}, w(d)=product_j p(d(j)), and
   f(d)=H(d)/J. For every natural r<=J,
   sum_d w(d)1_{H=r}=choose(J,r)*q^r*(1-q)^(J-r).
   E[f]=q; E[(f-q)^2]=q(1-q)/J; Pr(H=0)=(1-q)^J.
   For every real epsilon>0,
   Pr(|f-q|>=epsilon)<=q(1-q)/(J epsilon^2)<=1/(4J epsilon^2).
   For every epsilon>0 and delta>0, J>=1/(4 delta epsilon^2) implies
   Pr(|f-q|>=epsilon)<=delta. If q=0, every sequence has H=0.
   If 0<q<1, then (1-q)^J>0 and q(1-q)/J>0.
2. For every finite design p, natural m,J with J>0, m arbitrary events
   E_k (k in [m]), and real epsilon>0, the product-law probability that there
   exists k with |H(E_k,d)/J-Pr(E_k)|>=epsilon is <=m/(4J epsilon^2).
   No independence between the different E_k is assumed; only independent draws.
3. For every natural b, arrays n,t:[b]->N, actual peer subsets
   P_h subset [n_h], and hypotheses t_h<=n_h for every h, let O be the
   dependent product of all t_h-element subsets of [n_h]. Then
   (1/2)*sum_{z in O} (product_h 1/choose(n_h,t_h))
       *1_{for every h, z_h disjoint from P_h}
   equals A(n,t,(|P_h|)_h). Thus this is the fair-school probability of avoiding
   every actual peer in independent uniform within-block seed selections.
4. For four blocks all with n_h=10,t_h=5, the values of A are respectively
   8/6561 for m=(2,2,2,2); 1/6048 for (5,3,0,0); 0 for (6,2,0,0); and
   1/127008 for (5,5,0,0).
5. For every finite design p,E,J>0 and supported sequence d, with q=Pr(E),
   f=H/J, there exists natural r<=J such that f=r/J. If 0<q<1/(2J), then
   q<=|f-q|. If q=0, f=0. This is pointwise and imposes no distribution on d.
6. For every finite design p,D:O x I->[5], J>0 and sequence d, the students with
   all four indirect empirical frequencies positive belong to
   {i: for every k in [4], 0<Pr(D(z,i)=k)<1}.
7. In the fixed rare design every one of its four exact probabilities is
   strictly between 0 and 1; there exists a supported 10000-sequence for which
   it is false that every one of the four empirical frequencies is positive.

There is no restriction paragraph in the docstring. It describes binomial law,
moments, precision bounds and the blocked school-exposure formula.

**Junk-value audit.** J>0 and epsilon,delta>0 protect every statistical
denominator. In the avoidance identity t_h<=n_h ensures choose(n_h,t_h)>0;
the fact P_h is a subset of [n_h] ensures |P_h|<=n_h, so natural subtraction
n_h-|P_h| is ordinary subtraction. The standalone A definition permits arbitrary
bad arrays, for which zero denominators would return zero or excessive m_h would
truncate; neither regime is used in the general identity or numerical examples.
Binomial (J-r) is used with r<=J. Cases q=0 or 1 have the intended degenerate
binomial meanings, including 0^0=1. Empty event families m=0 make the union empty
and give 0<=0. Empty block families b=0 give an empty product of 1 and a singleton
assignment type; the fair-school avoidance probability is 1/2 on both sides.
Blocks with n=t=0 similarly have one empty selection and choose(0,0)=1. Empty O
cannot have a finite design. No square roots, logs, real powers, extrema, limits,
nonintegrable integrals, extended-real conversions or partial defaults occur.

## SAP.P037b.T31

Location: `SAP/P037b/Challenge/Part1.lean:92-96`; statement:
`SAP/P037b/Defs/Part3.lean:65-88`.

**Definitions unfolded.** For B natural, B(B) consists of all subsets s of
[B] x [4] with exactly two members in each block {b} x [4]. For n,m natural,
U(n,m) is every m-element subset of [n]. The uniform event quantity is
#{s in U(n,m):E(s)}/choose(n,m). No other law or estimator definition is used
in this theorem.

**Full assertion and quantifiers.** First there is an unconditional conjunction
of the following finite identities:

1. |B(14)|=78364164096; |U(56,28)|=7648690600760440;
   |U(8,4)|=70; |B(2)|=36. The subset {0,1,2,3} belongs to U(8,4), whereas
   {(0,0),(0,1),(0,2),(0,3)} does not belong to B(2).
2. Under uniform U(56,28), the probability that 0 and 1 are both selected is
   27/110. Under uniform U(4,2), the corresponding probability is 1/6.
3. Define uncentered second moments
   V_U(y)=(1/70)*sum_{s in U(8,4)}[(sum_{i in [8]}(1 if i in s else -1)y_i)/4]^2
   and
   V_B(y)=(1/36)*sum_{s in B(2)}[(sum_{i in [2]x[4]}(1 if i in s else -1)y_i)/4]^2.
   Then V_U(1,1,1,1,0,0,0,0)=1/7;
   V_B(y_(b,j)=1 if b=0 else 0)=0;
   V_U(2,0,1,1,1,1,1,1)=1/7;
   V_B(y_(b,j)=2 if (b,j)=(0,0), 0 if (b,j)=(0,1), 1 otherwise)=1/6.

Second, universally quantify a finite O, natural n, masses p:O->R, proofs that
p(z)>=0 for every z and sum p=1, school indicators S:O x [n]->Bool, and the
condition for every i that sum_z p(z)1_{S(z,i)=true}=1/2. Then universally
quantify any y:[n]->R, any natural m>0, and set
T(z)=sum_i ((1 if S(z,i) else -1)y_i)/m. The conclusions are
E_p[T]=0 and

E_p[T^2] = (1/m^2) sum_i sum_j y_i*y_j *
  (1 if i=j else 4*sum_z p(z)1_{S(z,i)=true and S(z,j)=true}-1).

The half-marginal condition is an explicit hypothesis in this general identity,
not asserted universally for the specific 56-school laws. Unlike
`ProbabilityDesign`, this last group permits zero masses.

The restriction docstring explicitly describes the eight-school numbers as
uncentered second moments, omits their separate zero-mean/variance
identification, and omits full actual-design variance claims for 56 schools.
It also omits a 56-school support inclusion, block-respecting probability and
ratio, universal marginals/pairs/covariances, a complete eight-school pair family,
and a separate 34-state count. None of these omitted assertions is silently
encoded by the proposition.

**Junk-value audit.** Uniform event division could return 0 for m>n when
choose(n,m)=0, but every use is (56,28) or (4,2) and has a positive denominator.
Second-moment denominators 70,36,4 are positive. The general formula assumes
m>0, so m^2>0. Empty O is inconsistent with normalization; n=0 is allowed and
gives T=0 and the correct empty sum identity, without affecting the concrete
examples. All finite numerals are in range; the two eight-school coordinate
systems represent the displayed outcomes in the natural block ordering.
There is no truncated subtraction in the statement (the minus ones are real),
no square root, log, real power, extrema, limit, extended-real conversion,
nonintegrable integral, or partial-function default. Calling the displayed
numbers second moments is accurate without relying on a default convention for
variance.
