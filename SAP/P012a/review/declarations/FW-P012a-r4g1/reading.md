# Blind reading

Saved before opening either `claims.json` or `record.json`. I read all five
closure lists, the source of every listed definition, and the 47 distinct
generated declarations with line number zero. The latter were printed in
`scratch/ClosurePrint.lean`: they are proofs about numerals being at least two
and the two ordinary sum/product pattern-match eliminators. They introduce no
assumptions. Constructors and projections have exactly their displayed
structure or inductive-declaration meanings.

The notation below expands the SAP definitions into finite sets, functions,
real arithmetic, and propositions. A definition given here is part of each
following section that uses it; none is being treated as an uninterpreted
predicate.

## Common objects and fully expanded notation

A vertex is an element of the countable disjoint union
`N ⊕ (N × N)`. Write `s(i)=inl(i)` and `u(i,k)=inr(i,k)`.
Data consist of finite subsets `S,M` of natural numbers, and total functions
`parent,time,degree : N → N`, `trait : N → Bool`. Put `J=S\M`,
`V_S={s(i):i∈S}`, and `E_R={{s(parent(j)),s(j)}:j∈J}`. These are **sets**,
so repeated images do not count repeatedly. Admissibility means, in order:

1. `M⊆S`;
2. `time` is injective on `S`;
3. for every `j∈J`, `parent(j)∈S` and `time(parent(j))<time(j)`;
4. for every `i∈S`, `r_i≤degree(i)`, where
   `r_i=|{e∈E_R:s(i)∈e}|`.

A state is a finite vertex set `V`, a finite set `E` of finite vertex sets,
and a **total** Boolean trait function `Z` on the ambient countable type.
For any state define `d_H(v)=|{e∈E:v∈e}|`. Simplicity means every `e∈E`
has cardinality two and is contained in `V`. An augmented graph is simple
and every edge contains at least one `s(i)` with `i∈S`. Compatibility is the
conjunction of that condition, `V_S⊆V`, `E_R⊆E`, `Z(s(i))=trait(i)` for
every `i∈S`, every vertex in `V\V_S` having an edge to some `s(i)` with
`i∈S`, and `d_H(s(i))=degree(i)` for every `i∈S`. Isolated sampled
vertices are allowed; isolated unsampled vertices are not. The tag of a vertex
alone does not determine sampling: `s(k)` for `k∉S` is also unsampled.

For a state let `m=|E|`, `z_v=1` when `Z(v)=true` and zero otherwise,
and `A_vw=1` when `v≠w` and `{v,w}∈E`, zero otherwise. Define the real numbers

```
N_H = Σ(v∈V) Σ(w∈V) (A_vw-d_H(v)d_H(w)/(2m)) z_v z_w,
D_H = Σ(v∈V) Σ(w∈V) ([v=w]d_H(v)-d_H(v)d_H(w)/(2m)) z_v z_w,
h_H = N_H/D_H.
```

Here and below natural numbers in real formulas are cast to `R`.
`homophily(H)` is `some(h_H)` precisely when `m>0` and `D_H≠0`, and is
`none` otherwise. The raw quotient `h_H` always exists as a Lean real number.
The set of compatible defined homophily values is
`A_D={x∈R: ∃H, H is compatible with D, m_H>0, D_H≠0, h_H=x}`.

For preferential recruitment, a vertex is not yet sampled at the event of
`j` when it is `s(k)` with `k∉S` or `time(j)≤time(k)`, or when it has tag
`inr`. Let `U_ij={v∈V:{s(i),v}∈E and v is not yet sampled at j}` and
`U^=_ij={v∈U_ij:Z(v)=Z(s(i))}`. The raw preferential value is

```
p_D,H = (Σ(j∈J) ([Z(s(j))=Z(s(parent(j)))]
                    - |U^=_(parent(j),j)|/|U_(parent(j),j)|)) / |J|.
```

The Option value is `some(p_D,H)` exactly when `|J|>0` and all the
susceptible sets in that sum are nonempty; otherwise it is `none`.

Let `t_i=degree(i)-r_i` in **natural-number subtraction**, and `T=Σ(i∈S)t_i`.
The recruitment state has vertices `V_S`, edges `E_R`, trait `trait(i)`
at `s(i)`, and false at `inr` vertices. Let `a` count its edges whose
two endpoints both have trait true, `b` those whose endpoints both have
trait false, and `c` those containing both traits. More generally the same
edge filters define these three counts for any state.

The private-leaf completion `H_ε` has vertices
`V_S ∪ {u(i,k):i∈S, k<t_i}`, edges
`E_R ∪ {{s(i),u(i,k)}:i∈S,k<t_i}`, sampled traits `trait(i)`, and
trait `trait(i)` at every `u(i,k)` if `ε=true`, its negation if
`ε=false`. The latter rule also assigns traits to inactive vertices.
Write `H_-=H_false`. Put

```
phi(x,y,z) = 1-z/(2x+z)-z/(2y+z),
ell(D) = phi(a,b,c+T),
Q(D) = (4ab-(c+T)^2)/((2a+c+T)(2b+c+T)).
```

The graph operations below leave every field fixed except those explicitly
mentioned. Removing an edge erases `{v,w}` from `E`; adding an edge inserts
that set. Adding a vertex inserts it into `V` and updates its trait.
Flipping a trait updates just that value to its Boolean negation.
`U(D,H)=V_H\V_S`, and `Pool(D,H,i)={v∈U(D,H):{s(i),v}∉E_H}`.
Cleanup with flag false retains precisely the vertices of nonzero degree;
cleanup with flag true retains those vertices **and** every sampled vertex
already in `V_H`. Both leave edges and the total trait function fixed.

A replacement relative to original state H and pending state L selects either
`v∈Pool(D,H,i)` and returns L, or any `v∉V_L`, any Boolean trait, and
returns L with that vertex inserted and its trait updated. There is no coin
in this general relation. The coin-specific version allows the first case
only for coin=true, and the fresh case only for coin=false or an empty pool.

For completeness the general graph-proposal relation, with cleanup flag ε,
is the union of the following four possibilities:

* Select `i∈S`, `j∈V_H`, `s(i)≠j`, with `{s(i),j}∈E_H\E_R`
  and `j∉V_S`. Remove that edge, make a replacement `v` for i relative
  to original H, returning P. For ε=true add only `{s(i),v}`; for ε=false
  add both `{s(i),v}` and `{j,v}`. Then clean up with flag ε.
* Select distinct `i,j∈S`, with `{s(i),s(j)}∈E_H\E_R`. Remove that
  edge, replace i using original H and this pending state, returning P and v.
  Add `{s(i),v}`, replace j using **original H** and the new pending state,
  returning Q and w, add `{s(j),w}`, then clean up with flag ε.
* Select `i∈S`, `j∈V_H`, `s(i)≠j`, with `{s(i),j}∉E_H`, and
  `v,w∈U(D,H)` satisfying `{s(i),v},{j,w}∈E_H`. Remove these two
  edges, insert `{s(i),j}`, and clean up with flag ε. The relation itself
  does not explicitly require j sampled or v and w distinct.
* Select `i∈S`, `j∈V_H`, `s(i)≠j` for which neither the deletion test
  nor the preceding addition test holds; return cleaned-up H.

A trait proposal flips any one vertex in `U(D,H)`, or, only when ε=true
and `U(D,H)=∅`, returns H. A proposal is either a graph or trait proposal.
The printed graph-run relation fixes i,j and both Boolean coins, uses the
coin-specific replacements in the two deletion cases, and otherwise has
exactly the preceding false-flag graph operations.

## SAP.P012a.T1

This is a closed proposition, with no outer assumptions. Its docstring calls
it a refutation and makes a stronger execution-level description. Its first
four conjuncts are the following concrete assertions.

(a) Data have `S={1,2}`, `M={1}`, constant parent 1, `time(i)=i`,
`degree(1)=2`, every other degree 1, and trait true exactly at 2. H has
vertices `{s(1),s(2),u(3,0)}`, edges `{s(1),s(2)}` and
`{s(1),u(3,0)}`, and trait true exactly at s(2). These data are admissible,
H is compatible, and Pool(D,H,1) is empty. For each Boolean t, the state
obtained by removing `{s(1),u(3,0)}`, inserting fresh u(4,0) with trait t,
adding `{s(1),u(4,0)}` and `{u(3,0),u(4,0)}`, and false-cleaning is a
false-flag proposal but is incompatible. The input's Option functionals
are `some(-1/3)` and `some(-1/2)`.

(b) Data have `S={1,2,3}`, `M={1}`, parent(3)=2 and all other parents 1,
time the identity, degree(2)=3 and all other degrees 1, and trait true
exactly at 2. H has vertices `{s(1),s(2),s(3),u(4,0)}`, edges
`{s(1),s(2)}`, `{s(2),s(3)}`, `{s(2),u(4,0)}`, and trait true exactly
at s(2). These data are admissible, H is compatible, and Pool(D,H,2) is
empty. For both traits t the same edge replacement at s(2), using new
u(5,0) and also adding `{u(4,0),u(5,0)}`, is a proposal with incompatible
output. No functional values for this second example are asserted.

(c) Data have `S={1,2,3}`, `M={1,3}`, constant parent 1, identity time,
degree(3)=0 and all other degrees 1, and trait true exactly at 2. H has
all three sampled vertices, only edge `{s(1),s(2)}`, and trait true exactly
at s(2). These data are admissible, H is compatible, false-cleaning H is
a false-flag proposal and is incompatible, and H's functionals are
`some(-1)` and `some(0)`.

(d) Data have S={1,2}, M={1}, constant parent 1, time(i)=i-1 in N,
all degrees 1, and trait true exactly at 2. The dyad with those two
vertices, their one edge and the observed traits is compatible and the
data admissible. It has no unsampled vertices; **there exists no output
of its false-flag trait relation**. Its functionals are some(-1), some(0).

Further conjuncts, in their quantifier order:

* For all D,H,i,j,coins c1,c2,K, a printed run implies a general
  false-flag graph proposal. No compatibility assumption is imposed here.
* For all c1,c2,K, the printed run on the fixed selected pair (a) is
  equivalent to existence of v outside the input vertex set and then a
  Boolean t, with K exactly the cleaned edge replacement described in (a),
  with v in place of the named fresh vertex. The same statement holds
  independently for (b).
* For every fresh v for input (a), and every t, its pending output P has
  unchanged cleanup, V_P=V_H∪{v}, exactly the erased/inserted edges,
  trait function updated just at v, and no zero-degree active vertex.
  The old endpoint and v are unsampled, their mutual edge is present, and
  the old endpoint has no sampled neighbour. Sampled vertices, recruitment
  edges, observed traits, and all sampled degrees are preserved, but P is
  incompatible. Also there exists a permutation of the entire ambient
  vertex type fixing every sampled vertex, mapping P's active vertices
  and edges to the named output's, and preserving traits on active vertices.
  The identical assertions hold for (b) with its selected vertices.
* For every c1,c2,K the printed run on input (c) and pair (1,s(2)) holds
  exactly when K is its false-cleanup. That cleaned state has vertices
  `{s(1),s(2)}` and the original edge, excludes sampled s(3), fails sampled
  vertex inclusion, and fails the conjunction of active membership and
  correct trait at every sampled vertex.
* For every H compatible with the data (d), H has exactly the dyad's
  vertices and edges, and agrees with its traits at all active vertices.

Junk conventions: total traits outside active vertices are irrelevant except
where equality of the total update function is explicitly asserted. Erasing
an absent edge and inserting an already present edge are well-defined set
operations; the branch hypotheses exclude those cases where loss/restoration
is claimed. Freshness is actual nonmembership, not a default fresh label.
All raw divisions in (a),(c),(d) are protected by the asserted Option values;
there is no reliance on 0/0. Natural subtraction in time(i)=i-1 truncates at
0, but only times 1 and 2 are observed in (d), yielding 0 and 1.
The empty trait pool is a real empty finite set; its relation has no
constructor, not an arbitrary default sample. The independent universal
execution clauses are not claims of random-draw independence or probability.

## SAP.P012a.T2

This is a closed conjunction of universal assertions about the **true-flag**
relations defined above, not a probability-kernel normalization statement.
The main assertion is: for every data D and states H,K, first assume D
admissible, then H compatible, then that K is a true-flag graph or trait
proposal; conclude K compatible.

The additional conjuncts quantify the indicated data and states first,
then their hypotheses, and assert the following full traces:

1. For every D,H,i,j,v,P satisfying admissibility, input compatibility and
   every unsampled-deletion branch condition, let R=H minus `{s(i),j}`
   and A=P plus `{s(i),v}`. The replacement facts are: v is active in P
   and unsampled, P has R's edges, `{s(i),v}` is absent there, and either
   v is in the original pool and P=R, or v was absent from R's vertices
   and P is R with v inserted with some trait. For every k∈S,
   `d_R(s(k))+[k=i]=d_H(s(k))`; for every ambient vertex x,
   `d_P(x)=d_R(x)`; for every k∈S, `d_A(s(k))=d_H(s(k))`.
   Finally j is absent after true-cleanup of A iff every original edge
   containing j was exactly `{s(i),j}`.
2. For every D,H,i,j,v,w,P,Q satisfying the sampled-deletion conditions,
   let R=H minus `{s(i),s(j)}`, A=P plus `{s(i),v}`, B=Q plus
   `{s(j),w}`. The preceding replacement facts hold once for (H,R,i,v,P)
   and once for (H,A,j,w,Q). Every vertex of the **original** pool for j
   is still nonadjacent to s(j) in A. For k∈S,
   `d_R(s(k))+[k=i]+[k=j]=d_H(s(k))` and
   `d_A(s(k))+[k=j]=d_H(s(k))`; inserting replacement vertices changes no
   vertex degree, and B restores every sampled degree. The replacements
   v,w are not assumed distinct.
3. For every D,H,i,j,v,w satisfying the addition conditions, let R be H
   after both removals, A after adding `{s(i),j}`. Then j is sampled;
   the two removed edges are distinct and are not recruitment edges;
   for every ambient x,
   `d_R(x)+[x∈{s(i),v}]+[x∈{j,w}]=d_H(x)`; every sampled degree in A
   is its original value. Each of v,w is removed by true-cleanup iff its
   degree in A is zero. A common v=w is permitted.
4. For all D,H, compatibility alone implies true-cleanup(H)=H.
5. For all D,H,K, a true-flag trait proposal alone implies identical
   vertices and edges, and either the unsampled set is empty and K=H,
   or there exists a chosen unsampled v such that K is its trait flip,
   its new trait is the negation, and every other ambient trait is unchanged.

Junk conventions: this theorem uses only finite set operations, degrees,
natural additions, function updates, and membership. It has no real
division or extrema. Empty pools do not choose default elements: fresh
vertices are explicitly supplied. An empty sampled set may make graph
branch implications vacuous, but the empty trait self-loop exists.
The infinite ambient type guarantees room for a genuinely fresh name.
No substantive branch precondition is encoded as the conclusion.

## SAP.P012a.T3

This closed proposition asserts the following, separately quantified
conjuncts. For **every** admissible D, assume in order |S|=527, |M|=6,
and Σ(i∈S)degree(i)=4487. Then H_- is compatible, T=3445,
a+b+c=521, its edge count is positive and homophily denominator nonzero,
and

```
count_true(H_-)=a, count_false(H_-)=b, count_mixed(H_-)=c+3445,
h_H_- = ell(D) = Q(D),
h_H_- ≤ -1462/1983, h_H_- ≤ -178409/241987,
h_H_- < -7027/10000, h_H_- < -6918/10000, h_H_- < -7179/10000.
```

Under the same assumptions, |E_R|=521, D_H_->0, |V_H_-|=3972>2626.
For every i∈S and k<t_i, u(i,k) is active and unsampled, has degree 1,
every incident edge is exactly `{s(i),u(i,k)}`, and its trait is the
opposite of trait(i). For every i∈S, the sampled degree in H_- is
`r_i+t_i=degree(i)`.
Then, for every q in the real finite set
`{-7027/10000,-6918/10000,-7179/10000}`, and **every** real L,U,
if |L-q|≤1/20000, then h_H_-<L and A_D is not a subset of [L,U].

Independently, for all nonnegative real a,b,c with a+b+c=521, the quotient
`(4ab-(c+3445)^2)/((2a+c+3445)(2b+c+3445))` is at most -1462/1983,
and the exact identity

```
(-1462/1983)((2a+c+3445)(2b+c+3445))-(4ab-(c+3445)^2)
  = 7932c+(3445/1983)(a-b)^2 ≥ 0
```

holds. For all **natural** a,b,c with sum 521 the quotient is at most
-178409/241987. The exact numerical assertions are the strict ordering
`-1462/1983 < -7179/10000 < -7027/10000 < -6918/10000`, the gaps
685459/19830000, 450803/9915000, 384043/19830000 obtained by subtracting
-1462/1983 from the three respective printed decimals, each gap greater
than 1/20000, and
`phi(260,261,3445)=phi(261,260,3445)=-178409/241987`.

Junk conventions: spare-degree subtraction is natural subtraction; input
admissibility prevents truncation. Every cast is from a finite nonnegative
integer to a real and is exact. All completion denominators are explicitly
nonzero (indeed positive); the independent quotient bounds have factors
at least 3445 by their hypotheses. No empty/unbounded infimum is used.
The definition A_D removes undefined homophily values with an Option guard.
Empty sets cannot satisfy the published cardinality assumptions, whose
joint satisfiability still needs a nonvacuity check. The universal number
triples alone assert arithmetic attainability of the integer bound; a
separate data realization is not explicitly existentially asserted.

## SAP.P012a.T4

This is the conjunction of two independent universal implications.

First, for every D, assume admissibility, |S|=527, |M|=6 and sampled
degree sum 4487. For every real L, assume **L is a greatest lower bound
of A_D**: L≤x for every x∈A_D, and every real lower bound l of A_D has
l≤L. Conclude

```
L ≤ -1462/1983, L ≤ -178409/241987,
-7027/10000-L ≥ 685459/19830000,
-6918/10000-L ≥ 450803/9915000,
-7179/10000-L ≥ 384043/19830000.
```

Second, for every D and state H_nom, assume D admissible, |S|=527,
|M|=6, and Σ(i∈S)d_H_nom(s(i))=4487. For every real L, assume L is a
greatest lower bound of A_D, and assume there exists q in the three-value
real finite set above with |L-q|≤1/20000. Conclude the sampled degree
sum **of D** differs from 4487, there exists i∈S with
degree(i)≠d_H_nom(s(i)), and H_nom is not compatible with D. No
simplicity, augmentation or trait assumption is imposed on H_nom.

Junk conventions: IsGLB is its relational Mathlib notion, not a totalized
`sInf`. A greatest real lower bound does not exist for the empty set, or
for an unbounded-below set. Thus this hypothesis cannot select a junk
infimum. All quotients in the homophily-value set are guarded; the
displayed constants have positive denominators. No natural subtraction is
used by this closure. A nonempty defined compatible-value set and a
satisfiable rounded-endpoint antecedent require checking separately.

## SAP.P012a.T5

This is a conjunction of two separately quantified assertions. First, for
every D, assume admissibility and then

```
T>0 or (2a+c>0 and 2b+c>0).
```

Conclude: ell(D) is the **least element** of A_D, meaning ell(D)∈A_D
and ell(D)≤x for every x∈A_D; H_- is compatible;
homophily(H_-)=some(ell(D)); ell(D)=Q(D); and, for every state H,
compatibility and then positive edge count/nonzero homophily denominator
imply ell(D)≤h_H. The last bound is on defined compatible values; it does
not claim every compatible state has defined homophily.

Second, for every D, assume admissibility, |S|=527, |M|=6, and sampled
degree sum 4487. Conclude T=3445, a+b+c=521,
ell(D)≤-1462/1983 and ell(D)≤-178409/241987.
There is no formal assertion here about what edge-type counts an external
paper supplies or whether they can be recovered from that paper. The
docstring explicitly calls that an omitted assertion.

Junk conventions: natural subtraction in t_i is exact on admissible data.
In the first part, T>0 makes both 2a+c+T and 2b+c+T positive; otherwise
their positivity is assumed. H_-'s Option equality ensures its m>0 and
D_H_-≠0. In the second part, the claimed T=3445 likewise keeps the
symbolic formula's denominators positive. The value set excludes every
undefined raw h_H. IsLeast is actual membership plus a lower-bound
property, not a totalized infimum. Empty sampled data cannot satisfy the
first part's regularity condition. No logarithms, square roots, real
powers, integrals, extended-real conversions, limsups, partial-choice
defaults, or other totalization conventions occur in any target closure.
