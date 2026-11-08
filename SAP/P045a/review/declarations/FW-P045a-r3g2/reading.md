# Blind reading

This file was saved before opening `claims.json` or `record.json`. Sources read:
the five Challenge docstrings and statements; every declaration listed in their
`closure.json` entries; the enclosing definitions in Part1, Part2, Part4, Part5,
WholeW1 and WholeW2. Generated constructors, projections, exposure recursors,
decidable equality and all `_proof_…` entries were also printed and read in
`scratch/ClosurePrint.out`. The auxiliary proofs establish numeral instances,
exposure constructor equality or bounds for indices; they add no assumptions.

Throughout, a sum over a finite type means Mathlib's `Finset.univ.sum`.
`Fin n` is the type of natural numbers strictly below n. A Boolean assignment is
a function from `Fin n` to `Bool`; write b(z_i)=1 when z_i=true and 0 otherwise.
A finite design is a real function p on a finite type with p(w)>=0 for every w
and sum_w p(w)=1. Write E_p X=sum_w p(w)X(w), P_p(E)=sum_w p(w)1_E(w), and
E_p[X|E]=(sum_w p(w)1_E(w)X(w))/P_p(E). These are literal finite sums and real
division, not unmentioned probability-space constructions. The mean of a
function on a finite type I is (sum_i x_i)/|I|; the average over a finite set S
is (sum_{i in S} x_i)/|S|. All cardinalities in real formulas are cast to R.

## SAP.P045a.T6

The statement is the conjunction of three independently quantified assertions.

1. For every natural n, every Boolean matrix A on `Fin n` that is symmetric and
   has false diagonal, every Boolean assignment z, and every i in `Fin n`, put
   N_i={i} union {j:A(i,j)=true}, m_i=|N_i|, and
   c_i=|{j in N_i:z_j=true}|. All of the following hold simultaneously:
   * sum_j b(z_j)b(if j=i then true else A(j,i))=c_i;
   * sum_j b(if i=j then true else A(i,j))=m_i;
   * c_i<=m_i;
   * c_i=m_i iff every j in N_i is treated;
   * c_i=0 iff every j in N_i is untreated;
   * c_i<m_i iff at least one j in N_i is untreated;
   * c_i=0 implies c_i<m_i;
   * (c_i<m_i and c_i!=0) iff 0<c_i<m_i;
   * [for every assignment v, c_i(v)=0 iff c_i(v)<m_i] iff m_i=1;
   * not (c_i=m_i and c_i=0);
   * c_i=m_i iff not c_i<m_i.
   Here `allTreated`, `allControl`, and `badAllControl` mean respectively the
   three events c_i=m_i, c_i=0 and c_i<m_i. The last event is the complement of
   all-treated, not the event that all vertices are untreated.
2. For every finite type Omega (in Lean, `Type`, not an arbitrary universe),
   every finite design p, every decidable predicate E on Omega and every real
   function Y, if P_p(E)>0, then
   E_p[1_E Y/P_p(E)]=E_p[Y|E]. The type, its Fintype instance, p, E, the
   decidability instance and Y are quantified before the positivity implication.
3. For every n>0, finite design p on all Boolean assignments, symmetric
   loopless A, and real outcome array Y(i,z), suppose, in this order:
   * for every i,z, c_i(z)=m_i implies Y(i,z)=Y(i,all-true);
   * for every i,z, c_i(z)=0 implies Y(i,z)=Y(i,all-false);
   * for every i, P_p(c_i=m_i)>0;
   * for every i, P_p(c_i=0)>0.
   Define the corrected estimator at z to be the mean over i of
   1_{c_i=m_i}Y(i,z)/P_p(c_i=m_i) minus
   1_{c_i=0}Y(i,z)/P_p(c_i=0), with each term implemented by an if/else zero.
   Define the faulty estimator by replacing c_i=0 with c_i<m_i in both its
   indicator and its denominator. Define the target as
   (1/n)sum_i[Y(i,all-true)-Y(i,all-false)]. The conclusions are:
   * the corrected estimator's expectation is the target;
   * the faulty estimator's expectation is
     (1/n)sum_i[Y(i,all-true)-E_p[Y(i,Z)|c_i(Z)<m_i]];
   * if, additionally, for every i,z, c_i(z)<m_i implies
     Y(i,z)=Y(i,all-false), then the faulty estimator is unbiased too.
   This last additional sufficiency is an implication in the conclusion; it is
   not a hypothesis of the preceding two expectation identities.

Junk conventions: real division by zero is zero, including the conditional
mean, finite mean and HT denominators. The theorem explicitly excludes zero in
the event identity and n=0 and both extreme-event probabilities in the contrast
identity. Each N_i contains i, so m_i>=1; all-control is contained in the
complement event, which consequently also has positive probability. No zero
denominator is used in these conclusions. In the first conjunct n=0 is allowed,
but then the quantifier over i is empty. A finite design on an empty Omega
cannot exist since its masses would sum to 0 rather than 1. There are no logs,
roots, powers outside a domain, integrals, extended-real conversions, infima,
suprema or partial-function defaults here. All arithmetic subtraction is real
except comparisons of natural counts, which use no subtraction.

Docstring scope, independently of any canonical claim: it calls this a
restriction, retaining the mathematical characterizations and expectation
formulas and dropping a numerical two-unit example and software execution,
weights, outcome-generation and population-size changes. It describes the
additional sufficiency as threshold sufficiency.

## SAP.P045a.T7

Matrices in several definitions have type N -> N -> R, although the matrix
under discussion has its meaningful entries in 0,...,n-1. Let U_n be the list
of pairs (i,j) with 0<=i<j<n, ordered by increasing column j and then row i.
Let L_n be the list with 0<=j<i<n, also ordered by increasing column then row.
For a matrix M, F_n(M)(i,j)=M(i,j) when j>=i. When j<i, find the first list
index k of (i,j) in L_n, get U_n[k] if present, otherwise use (0,0), and copy
that entry of M. This is `faultyCopy`. The original single-edge matrix A has
value 1 exactly at (0,3) and (3,0), and 0 everywhere else on N x N.

For each of the 64 functions u:`Fin 6` -> Bool, the corresponding symmetric
binary input has zero diagonal. Above the diagonal it uses the Boolean at the
index of (i,j) in U_4, reduced modulo 6; below it uses the index of (j,i), also
modulo 6. This describes `upperInput4` even outside the four-by-four square.
For a matrix M and Boolean assignment z on n vertices, the exposure at i has
first digit b(z_i), and second digit 1 iff sum_j b(z_j)M(j,i)>0. The four
possible values are the distinct constructors d11,d10,d01,d00. This is a
column-based matrix exposure.

The theorem asserts this full conjunction, with no initial hypotheses:

* A is symmetric and has zero diagonal for all natural indices. F_4(A) has
  entries F(0,3)=1,F(3,0)=0,F(2,1)=1,F(1,2)=0.
* U_4=[(0,1),(0,2),(1,2),(0,3),(1,3),(2,3)] and
  L_4=[(1,0),(2,0),(3,0),(2,1),(3,1),(3,2)]. For every n>=4, U_n[2] and L_n[2]
  are respectively `some (1,2)` and `some (3,0)`. For every n<=3 and every
  natural k<length(U_n), L_n[k] equals the coordinate-swap of U_n[k], as an
  optional list element.
* Exactly 32 of the 64 u produce an F_4(input(u)) with some asymmetric pair
  i,j in `Fin 4`.
* With z=(false,false,false,true), exposure of vertex 0 is d01 under A and
  d00 under F_4(A). With z=(false,false,true,false), exposure of vertex 1 is
  d00 under A and d01 under F_4(A).
* For every real q with 0<=q<1, draw a Boolean b with weight q if true and
  1-q if false. The N-indexed matrix that is zero if b=true and F_4(A)
  otherwise equals F_4(A) with probability 1-q.
* The list of swapped U_4 cells is
  [(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)], and the cardinality of u is 64.
* For every i,j in `Fin 4`, F_4(A)(i,j) is exactly 1 at (0,3) and (2,1),
  and 0 at every other entry.
* For every q with 0<=q<1 and then every Boolean `faulty`, consider the output
  O_f(b) on `Fin 4` x `Fin 4`. If f=true, first erase every strictly upper
  entry of A when b=true and then apply F_4. If f=false, use A when b=false
  and zero when b=true. (There is only one upper edge.) Boolean draw weights
  are nonnegative and sum to 1. For every four-by-four real matrix M,
  P(O_f(b)=M)=1_{O_f(false)=M}(1-q)+1_{zero=M}q.
  In particular its masses at O_f(false) and zero are respectively 1-q and q,
  and for every M unequal to both these matrices its mass is zero.

Junk conventions: `List.idxOf` returns the list length for an absent cell;
optional lookup followed by `getD (0,0)` supplies (0,0) when out of range.
These genuinely affect the definition outside 0,...,n-1. In every asserted
in-range matrix calculation the cell exists, so the fallback is unused. The
N-indexed function equality in the older probability conjunct is still safe:
F_4(A) is nonzero at (0,3), and therefore is unequal to the zero function
regardless of its out-of-range entries. The modulo 6 in the input definition
has positive divisor and agrees with the actual index for all in-range pairs.
Optional list positions are compared as `Option`, not silently extracted.
Empty cell lists at n=0 or n=1 make the k-quantifier empty. Finite sums, Boolean
probabilities and matrix exposures have no divisions except by fixed positive
numerals in the probability parameters. No measure integrals or other
analytic junk conventions occur. The constructor-index and decidable-equality
definitions merely distinguish the four exposure cases.

The docstring describes the complete finite counterexample and complete
deletion output law, with the usual measure-theoretic conditions assumed.

## SAP.P045a.T8

The fixed true graph is the symmetric loopless graph on vertices 0,...,9 with
these unordered edges (the entries above the diagonal of `printedAdj`):

    01,02,04,12,13,19,23,24,25,28,34,35,36,45,47,67,68,78,79,89.

For any natural d, let D_d be the finite collection of all d-element subsets
R of these upper-triangle edges. The measured adjacency at (i,j) is the true
adjacency AND [(i,j) not in R and (j,i) not in R]. Let k_R(i) be its neighbor
count. Let a_i=5/2 for i=1 and a_i=1 otherwise. For a vertex t, define
S_R(t)={i:measured adjacency(t,i)=true} and
C_R(t)={0,...,9} minus ({t} union S_R(t)). Put

    H_R(t) = [sum_{i in S_R(t)} (5/4)a_i/k_R(i)]
             / [sum_{i in S_R(t)} 1/k_R(i)]
           - [sum_{i in C_R(t)} a_i(1+(1/4)1_{true adjacency(t,i)})/(9-k_R(i))]
             / [sum_{i in C_R(t)} 1/(9-k_R(i))].

All subtractions inside this formula are real. Define
B_d=(1/|D_d|)sum_{R in D_d}[(1/10)sum_t H_R(t)]-23/80.
This unfolds `deletionHajek` and `deletionBias` completely. The theorem has no
initial hypotheses and asserts:

* There are 20 true edges, (mean_i a_i)/4=23/80, and for every natural d<=2,
  every R in D_d and every i, 1<=k_R(i)<=6.
* B_0=890121037/44498644960; 1/50<B_0<1/49;
  9/1000<B_1<1/100; -1/800<B_2<-1/900;
  |B_2|<|B_1|<|B_0|; and B_0!=0.
* For every d in `Fin 3`, then R in D_d, all degrees lie in [1,6], and
  for every t both S_R(t) and C_R(t) are nonempty.
* For every d in `Fin 3`, then R in D_d, every i has k_R(i)/10>0 and
  (9-k_R(i))/10>0; and for every t each of the two sums of reciprocal
  degrees in the denominators of H_R(t) is strictly positive.
* |D_0|=1, |D_1|=20 and |D_2|=190.

Thus the definitions are explicit arithmetic rather than a general probability
space. Their natural statistical reading is uniform one-treated-vertex
assignment t, uniform d-edge deletion R, and untreated outcomes
a_i(1+1/4 times the indicator of a truly treated neighbor). The comparison is
the indirect d01-versus-d00 Hajek contrast. This reading follows from the
formula; the theorem does not separately define a general outcome function or
state the sampling mechanism in a hypothesis.

Junk conventions: every real division has Mathlib's zero-denominator value 0
in the unrestricted definitions. For the theorem's d=0,1,2, the theorem states
strict positivity of all exposure probabilities, both ratio denominators and
the deletion-set cardinalities, and n=10 is positive. Therefore these junk
values do not influence B_0,B_1,B_2. `deletionMasks d` would be empty for d>20,
and its average would be 0, but no such d is used in the numerical comparisons.
Fin-typed matrix literals index only valid coordinates; the numeral instances
printed from the closure add no convention changing vertex 1 or the rationals.
There is no extended-real conversion, analytic integral, supremum or infinite
sum. The docstring explicitly says this refutes a universal monotonic-bias
reading of guidance, rather than saying that guidance itself is false.

## SAP.P045a.T9

This is the conjunction of five assertions, each with its own quantifiers.

1. For every real matrix M:N x N -> R and every natural i,j, the matrix
   C(M)(i,j)=M(j,i) if j<i and M(i,j) otherwise is symmetric. This is
   `correctedCopy`; it retains the diagonal and upper triangle literally.
2. For every natural n and matrices A,U:N x N -> R, assume, in order, A is
   symmetric at all natural indices, A has zero diagonal at all indices, A is
   binary inside the n-square, U has zero diagonal at all indices, and U is
   binary strictly above the diagonal inside the square. Then all three
   implications hold:
   * If U(i,j)<=A(i,j) whenever i<j<n, then 0<=C(U)(i,j)<=A(i,j) for every
     i,j<n, including the diagonal.
   * If A(i,j)<=U(i,j) whenever i<j<n, then A(i,j)<=C(U)(i,j)<=1 for every
     distinct i,j<n.
   * If U(i,j)=A(i,j) whenever i<j<n, then C(U)(i,j)=A(i,j) for every i,j<n.
   No assumption is made on U below the diagonal.
3. For every n, every symmetric loopless Boolean true graph T and measured
   graph S, assume S(i,j)=true implies T(i,j)=true for every i,j. Then for
   every assignment z and vertex i, defining exposure as (own treatment,
   existence of a treated adjacent vertex): S-exposure d01 implies T-exposure
   d01; d11 implies d11; d00 implies d00 or d01; and d10 implies d10 or d11.
4. For every n>0, finite design p on assignments, graphs T,S as above with
   the same subgraph condition, and real array y(i,d) on the four distinct
   exposures, assume P_p(D_S(i)=d00)>0 for every i and then
   P_p(D_S(i)=d01)>0 for every i. Let Y(i,z)=y(i,D_T(z,i)),

       M_d(z)=(1/n)sum_i [if D_S(z,i)=d then
                   Y(i,z)/P_p(D_S(i)=d) else 0],
       c_i=E_p[1_{D_T(Z,i)=d01} | D_S(Z,i)=d00].

   Then E_p M_d00=mean_i[(1-c_i)y(i,d00)+c_i y(i,d01)],
   E_p M_d01=mean_i y(i,d01), and

       E_p(M_d01-M_d00) - [mean_i y(i,d01)-mean_i y(i,d00)]
         = -mean_i[c_i(y(i,d01)-y(i,d00))].

   Additionally, if y(i,d00)<=y(i,d01) for every i, then the expected contrast
   is at most mean_i y(i,d01)-mean_i y(i,d00). These definitions unfold
   `htObserved`, `exposureProb`, `effect`, `condMean`, `expect`, and `mean`.
5. With precisely the fixed graph, finite deletion sets and H_R(t) arithmetic
   unfolded in the T8 section, B_0!=0 and |B_1|<|B_0|.

Junk conventions: C has no defaults or divisions. On n=0 the finite-square
matrix consequences and vertex quantifiers are empty, but this does not affect
the independent n>0 expectation assertion. The latter excludes zero sample
size and zero d00/d01 denominators. A zero probability for d10 or d11 is
permitted but neither is used as a denominator. Finite conditional
probabilities c_i have positive conditioning probability. The final numerical
instance uses B_0 and B_1 with the positive denominators described for T8, even
though T9 itself does not repeat those positivity conclusions. Means and
averages have zero-as-division-by-zero values outside these domains; none is
used to obtain the claimed result. No Nat subtraction, log, square root,
extended-real conversion, infimum, supremum, integral or infinite series occurs.

The docstring discloses a restriction: it omits a matrix decomposition, a
separate zero-diagonal conclusion, implementation and simulation reporting,
and statements about approximation bias or approximate centering. It retains
the symmetry/bounds/recovery, exposure implications, HT identities/sign and
the two stated Hajek comparisons.

## SAP.P045a.T10

The type of vertices is `Fin 4` with labels 0,...,3. The distance is the
absolute natural difference of the labels cast into N-infinity, i.e. the
four-path graph distance. To unfold the generic definitions used here, for
vertices `Fin n`, a function d:Fin n x Fin n -> N-infinity, epsilon a natural,
and a finite centre set S:

* S is separated iff for every s in S, every t in S with s!=t,
  epsilon<=d(s,t). It covers iff every v not in S has a centre s in S with
  d(s,v)<=epsilon-1, where subtraction here is truncated natural subtraction.
  `epsilonNet` is the conjunction of these two predicates.
* Mark(S)={v:there exists s in S with d(s,v)<=epsilon-1}, a filter of the
  finite universe. Put R=univ minus Mark(S).
* The next-draw weight f_c(S,v), for Boolean coded c, is as follows. If c=true
  and |R|=1, take u to be the head of the list of R, falling back to v if the
  list is empty. Give v weight 1/(u.val+1) if v.val<=u.val and 0 otherwise.
  In every other case give v weight 1/|R| if v in R and 0 otherwise.
* For a finite list cs of vertices, its trace weight W_c(cs) is the product,
  over k in `Fin cs.length`, of f_c(set(cs.take(k)),cs[k]), provided that
  Mark(set(cs.take(k)))!=univ for every such k and Mark(set(cs))=univ.
  Otherwise W_c(cs)=0. This allows repeated vertices in coded traces.
* The terminal mass m_c(S) is the real infinite sum over t in N of
  a_{c,S}(t)=sum_{z:Fin t -> Fin n} [if set(List.ofFn z)=S then
  W_c(List.ofFn z) else 0]. `fourPathLengthMass` is exactly this inner sum
  for n=4, epsilon=3, and path distance, rather than an independent mass.
* The nearest centre h_S(v) is the optional head of S's list after sorting by
  increasing d(s,v), with equal distances ordered by increasing vertex label.
  The partition P(S) is the finite image, over s in S, of the vertex set
  {v:h_S(v)=some s}.
* The Bernoulli mass of a Boolean vector c on all n vertex labels is
  product_i(if c_i=true then p else 1-p). The probability L_p(S,z) of a
  clustered treatment vector z is the finite weighted sum over all c of this
  mass times the indicator that for every vertex v there exists a centre s
  with h_S(v)=some s and z_v=c_s. Thus centre labels get independent
  Bernoulli(p) treatments and unused coordinates of c are summed out.
* The unconditional clustered-treatment mass Q_c,p(z) is
  sum_{S:Finset(Fin n)} m_c(S)L_p(S,z), with epsilon fixed at 3.

There are no initial hypotheses in T10; it asserts the following conjunction
at n=4, epsilon=3, path distance and p=1/2:

* Coded terminal masses are m_true({0,1})=1/12, m_true({0,2})=1/12,
  m_true({0,3})=1/3, m_true({1})=1/4, m_true({2})=1/4;
  sum_S m_true(S)=1; the total mass of non-separated S is 1/6.
* Coded treatment masses are Q(0000)=Q(1111)=3/8,
  Q(1100)=Q(0011)=5/48, Q(1000)=Q(0111)=1/48. For every Boolean z outside
  these six vectors, Q(z)=0.
* Repaired terminal masses are m_false({0,3})=1/2 and
  m_false({1})=m_false({2})=1/4. Repaired treatment masses are
  Q(0000)=Q(1111)=3/8, Q(1100)=Q(0011)=1/8,
  Q(1000)=Q(0111)=0.
* Mark(empty)=empty, Mark({0})={0,1,2}, Mark({1})=Mark({2})=univ,
  Mark({3})={1,2,3}.
* For every v, f_true(empty,v)=f_true({0},v)=1/4, whereas
  f_true({3},v)=1 if v=0 and 0 otherwise.
* For every j!=0 and every natural r, the trace consisting of r+1 zeros
  followed by j has weight (1/4)^(r+2). For each such j that sequence of
  weights is summable, and its infinite sum divided by
  f_true(empty,0) is 1/3.
* For every Boolean c and every finite centre set S, a_{c,S} is summable.
* For every S outside {{0,1},{0,2},{0,3},{1},{2}}, m_true(S)=0. For every S
  outside {{0,3},{1},{2}}, m_false(S)=0. These finite collections unfold
  `fourPathCodedCentreSets` and `fourPathRepairedCentreSets`.
* Under m_true, P(S) equals {{0},{1,2,3}} with probability 1/12,
  {{0,1},{2,3}} with probability 5/12, and {{0,1,2,3}} with probability 1/2.
  Its probability of any other partition is zero.
* For every S, S is a separated covering 3-net iff
  S belongs to {{0,3},{1},{2}}.
* sum_S m_false(S)=1. For every treatment vector outside
  {0000,1111,1100,0011}, Q_false,1/2(z)=0 (this collection unfolds
  `fourPathRepairedVectors`). Finally the two functions Q_true,1/2 and
  Q_false,1/2 on all assignments are unequal.

Junk conventions: `tsum` of a nonsummable real sequence is defined as 0 in
Mathlib. This potentially significant convention is neutralized here by the
explicit summability assertion for every coded flag and every S, as well as
for all displayed retry series. The natural subtraction epsilon-1 truncates
at zero in generic definitions, but epsilon is 3 throughout this theorem.
Path distance uses natural absolute distance, not one-sided subtraction, and
is always finite. There is no conversion of infinity to a real. The draw
rule's `head?.getD v` is guarded by |R|=1, so its fallback is never used.
When R is empty the other draw branch has v not in R and returns 0 without
using a 1/0 weight. Every singleton-branch divisor u.val+1 is positive; the
retry conditional formula divides by 1/4. The general Bernoulli expression
would admit negative weights for p outside [0,1], but p=1/2 here. The nearest
centre of the empty set is `none`, which makes its clustered-assignment event
false on four vertices; its terminal mass is also 0. All positive-mass centre
sets are nonempty. All numeral indices are in range. Empty traces, empty
finite products and empty sets have Mathlib's usual values; a zero-length
trace cannot cover this nonempty path and has zero trace weight. No Bochner
integrals, logs, square roots, infima, suprema or limits other than the
explicitly summable series are involved.

The docstring describes a complete finite law for both the coded and repaired
four-path algorithms, specifies all tie-breaking and treatment independence,
and says that the usual measure-theoretic conditions are assumed.
