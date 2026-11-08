# Blind reading

Saved before opening `claims.json` or `record.json`. Source locations are those in
`closure.json`; all entries in both closures were read. The generated declarations
with line 0 were additionally printed in `scratch/Closure.lean`. The `_proof_*`
entries prove that particular natural numerals are at least two (for elaborating
numerals in the formulas); the `match_1` entries are ordinary sum/product case
eliminators. They impose no statistical or graph assumptions.

## SAP.P012a.T11

The theorem has no external parameters: its proposition is the conjunction
called `T11WholeStatement`, described below. Its docstring describes sufficient
conditions for failure of point identification, a private-leaf construction,
degree-preserving swaps, the two displayed difference formulas, positivity of
their common denominator, and a concrete two-subject calculation.

### Objects and definitions, unfolded

The ambient vertex type is the disjoint union `ℕ ⊕ (ℕ × ℕ)`.
Write `s(i)=inl(i)` and `u(i,k)=inr(i,k)`; these labels are distinct across the
two summands, and equality within a summand is equality of the indices.
Membership in the observed sample, rather than the spelling of a label,
determines which vertices are sampled.

Data D consists of finite sets S and R of natural labels (sampled people and
seeds) and total functions parent, time, degree : ℕ → ℕ and trait : ℕ → Bool.
Write N=S\R, O={s(i):i∈S}, and
B={{s(parent(j)),s(j)}:j∈N}. These are finite sets, so repeated edges are
deduplicated. Let r_i be the number of edges in B containing s(i), and let
q_i=degree(i)−r_i, with natural-number truncated subtraction.

Admissibility means precisely:

1. R⊆S.
2. time is injective on S.
3. For every j∈N, parent(j)∈S and time(parent(j))<time(j).
4. For every i∈S, r_i≤degree(i).

A state H consists of a finite vertex set V_H in the ambient type, a finite
set E_H of finite vertex sets, and a total binary function τ_H on the ambient
vertex type. Write d_H(v)=|{e∈E_H:v∈e}|. Compatibility of H with D means all
of the following:

1. Each edge has exactly two elements and lies in V_H.
2. Each edge contains some s(i) with i∈S.
3. O⊆V_H and B⊆E_H.
4. τ_H(s(i))=trait(i) for every i∈S.
5. Every v∈V_H\O is adjacent to some s(i), i∈S.
6. d_H(s(i))=degree(i) for every i∈S.

In particular there are no loops, multiple edges, unobserved–unobserved edges,
or isolated unobserved vertices. Isolated sampled vertices are permitted.

For any state, put m_H=|E_H|, z_H(v)=1 if τ_H(v)=true and 0 otherwise, and
A_H(v,w)=1 if v≠w and {v,w}∈E_H and 0 otherwise. The real-valued functions
used by the theorem are exactly

    Num(H) = Σ(v∈V_H) Σ(w∈V_H)
               [A_H(v,w) − d_H(v)d_H(w)/(2m_H)] z_H(v)z_H(w),
    Den(H) = Σ(v∈V_H) Σ(w∈V_H)
               [1_{v=w} d_H(v) − d_H(v)d_H(w)/(2m_H)] z_H(v)z_H(w),
    h(H) = Num(H)/Den(H),
    Q(H) = Σ(v∈V_H) d_H(v)z_H(v).

All natural counts in these real expressions are cast to ℝ before arithmetic.
The option-valued homophily is `some h(H)` if m_H>0 and Den(H)≠0, and is
`none` otherwise. The set of compatible homophily values is

    {a∈ℝ : there exists a compatible H with m_H>0, Den(H)≠0, h(H)=a}.

Point identification says this set equals {a} for some real a.

For b∈Bool, define L_b(D) to have vertices
O ∪ {u(i,k):i∈S, 0≤k<q_i}, edges
B ∪ {{s(i),u(i,k)}:i∈S, 0≤k<q_i}, and trait function
τ(s(i))=trait(i), τ(u(i,k))=trait(i) if b=true and its Boolean complement
if b=false. The trait formula is total, even at vertices outside this finite
vertex set. Thus every added vertex has a distinct private label.

Deleting an edge means erasing its unordered two-element vertex set from E_H;
adding an edge means inserting it. Neither operation changes V_H or τ_H.
For i,j,x,y define K=swap(H,i,j,x,y) by deleting
{s(i),u(i,x)} and {s(j),u(j,y)}, then inserting
{s(i),u(j,y)} and {s(j),u(i,x)}. Equivalently its edge set is the corresponding
two erasures followed by two insertions. A neighbour set at v means
{w∈V_H:{v,w}∈E_H}.

### Complete conjunction and quantifier order

The first conjunct (`T11Statement`) itself has three conjuncts:

**(1) Existential construction and nonidentification.** For every D, every proof
of its admissibility, and every i,j∈ℕ, if i,j∈S,
r_i<degree(i), r_j<degree(j), and trait(i)≠trait(j), there exist states H,K
such that:

- H and K are compatible, and H=L_true(D), including its total trait function.
- {s(i),u(i,0)} and {s(j),u(j,0)} are edges of H; the two cross edges are absent.
- K=swap(H,i,j,0,0).
- V_H=V_K, |E_H|=|E_K|, τ_H=τ_K, and d_H(v)=d_K(v) for every ambient v.
- Den(H)>0 and Den(H)=Den(K).
- h(H)−h(K)=2/Den(H), and h(H)≠h(K).
- The compatible homophily-value set is not equal to any real singleton.

There is no prescribed time ordering between i and j. Their unequal observed
traits imply they are distinct. The states are existentially chosen after D,i,j.

**(2) Formula for arbitrary other traits, slot zero.** For every admissible D,
every i,j∈S with strict spare-degree inequalities as in (1), trait(i)=false,
trait(j)=true, and every state H, assume V_H and E_H equal those of L_true(D),
τ_H agrees with observed traits on O, τ_H(u(i,0))=false, and
τ_H(u(j,0))=true. Let K=swap(H,i,j,0,0), Q=Q(H), and m=m_H. The conclusion is:

- Both states are compatible; the two old edges are present and cross edges
  absent in H.
- Vertices, total trait function, edge count, and every ambient degree are equal.
- Den(H)=Q−Q²/(2m)=Q(2m−Q)/(2m)=Den(K)>0.
- h(H)−h(K) equals

      [2(1−d_H(s(j))d_H(u(j,0))/(2m))
       −2(0−d_H(s(j))d_H(u(j,0))/(2m))] / Den(H),

  and equals 2/Den(H), and the two h values are unequal.

Apart from the specified sampled and two private traits, all other traits of H
are universally arbitrary; its assumed graph geometry is fixed by the leaf
construction.

**(3) Exact instance.** Take S={1,2}, R={1}, parent constantly 1, time(i)=i,
degree constantly 2, and trait(i) the Boolean test i=2. Let

    V_H={s(1),s(2),u(3,0),u(4,0)},
    E_H={{s(1),s(2)},{s(1),u(3,0)},{s(2),u(4,0)}},
    τ_H(v)=true exactly when v=s(2) or v=u(4,0).

Let K delete the two sampled–private edges and add their crossed versions,
retaining vertices and the total trait function. The statement asserts
admissibility of this D, compatibility of both H,K, m_H=3, Q(H)=3,
Den(H)=Den(K)=3/2, option homophily values `some (1/3)` and `some (-1)`,
and h(H)−h(K)=4/3=2/Den(H). The instance is a closed assertion, not an
assumption made of the universal clauses.

The second top-level conjunct generalizes (2) to **all private slots**. For
every admissible D, then every i,j,x,y∈ℕ, assume i,j∈S, both strict spare-degree
inequalities, trait(i)=false, trait(j)=true, x<q_i and y<q_j. Then for every H
with the same V,E as L_true(D), observed trait agreement, and
τ_H(u(i,x))=false, τ_H(u(j,y))=true, conclude every property in (2) with
slots x,y in place of zero. Additionally, both H and K explicitly satisfy
m>0 and Den≠0, and

    degree(j) ≤ Q(H),             0 < degree(j),
    degree(i) ≤ 2m_H − Q(H),      0 < degree(i).

The degree bounds with Q are real inequalities; the strict degree inequalities
on the right are natural-number inequalities. These are conclusions, not
additional input hypotheses.

The third top-level conjunct is: for every admissible D, every b∈Bool, every
i∈S, and every natural k<q_i, the neighbour set of u(i,k) in L_b(D) is exactly
{s(i)}. There are no additional restrictions on this final universal assertion.

### Totalization and junk-value audit

- Natural subtraction in q_i is truncated, but admissibility supplies
  r_i≤degree(i) at every sampled i, so it is ordinary nonnegative subtraction
  wherever a leaf set or a strict spare condition uses it. Off-sample q_i are
  total but do not contribute to the construction.
- Real division is total with a/0=0. The raw h functions therefore have values
  even at edgeless or zero-denominator states. The option wrapper rejects those
  states. Every h value used in the construction/formulas has positive edge
  count (the two private edges exist) and positive Den, either explicitly or
  forced by the conclusions; the exact instance has m=3 and Den=3/2. Thus no
  asserted difference relies on division by zero.
- Empty finite sums equal zero; empty unions/images are empty. Admissible
  empty data are allowed, but cannot meet the two sampled-vertex/spare/trait
  hypotheses in the main clauses. The final private-neighbour clause is then
  harmlessly vacuous. Nonidentification is substantiated by two defined distinct
  values, rather than by an empty compatible-value set.
- `Finset.erase` silently does nothing on an absent edge and `insert` silently
  deduplicates an existing edge. The theorem explicitly establishes presence
  and absence of the four relevant edges, so the swap does not exploit these
  conventions. A two-label set would collapse to a singleton for equal labels;
  the opposite traits and the disjoint label constructors rule this out here.
- Data parent/time/degree/trait and state traits are total. Values at irrelevant
  labels are not observations. Seed parent values are unused in recruitment
  edges. Compatibility compares traits only at sampled vertices and finite graph
  functionals only at active vertices, although preservation of the entire total
  trait function is asserted for the constructed swap.
- Natural casts into ℝ are injective and preserve finite counts. There is no
  integer subtraction in a natural type except q_i; Q-related subtraction is
  real. There are no integrals, infinite extrema, limits, logarithms, square
  roots, real powers, infinities, partial-function default values, or empty
  index-type choices in this closure.

## SAP.P012a.T12

This is a closed assertion about fixed data and two fixed states, not a
universal identification theorem. Its docstring calls a printed claim false
and says a two-recruit witness has preferential-recruitment difference −5/12,
different from two formula right-hand sides.

### Objects and definitions, unfolded

The ambient labels, Data, State, admissibility, and compatibility have exactly
the types and meanings given in the T11 section: finite observed sets,
time-injective parent-before-child recruitment data, finite undirected simple
graphs containing the recruitment edges, observed traits and degrees fixed,
every unobserved vertex adjacent to a sampled vertex, and every edge touching
the observed sample. In particular the binary traits and all function fields
are total; N=S\R and B is the parent–child edge set, and r_i counts B-edges
incident to s(i).

For data D and an event indexed by j∈ℕ, a vertex v is not-yet-sampled if:

- v=s(k) and either k∉S or time(j)≤time(k); or
- v=u(a,b), in which case it is always not-yet-sampled.

Thus a sampled recruit at its own event is still included. For recruiter i
and event j define

    U(D,H,i,j) = {v∈V_H : {s(i),v}∈E_H and v is not-yet-sampled at j},
    M(D,H,i,j) = {v∈U(D,H,i,j) : τ_H(v)=τ_H(s(i))}.

Write c=|N|. The real functions are

    Psum(D,H) = Σ(j∈N) [1_{τ_H(s(j))=τ_H(s(parent(j)))}
                        − |M(D,H,parent(j),j)|/|U(D,H,parent(j),j)|],
    p(D,H) = Psum(D,H)/c.

All cardinalities in the real fractions are cast to ℝ. Preferential recruitment
is `some p(D,H)` exactly when c>0 and all the above event denominators for
j∈N are positive; otherwise it is `none`.

### The complete fixed proposition

There are no free variables, hypotheses, or existential choices at the outer
level. The data D are:

    S={1,2,3}, R={1}, parent(i)=1 for every i,
    time(i)=i−1 in ℕ,
    degree(1)=3 and degree(i)=1 for i≠1,
    trait(i)=true for every i.

For each Boolean t let H_t have

    V={s(1),s(2),s(3),u(4,0)},
    E={{s(1),s(2)},{s(1),s(3)},{s(1),u(4,0)}},
    τ(s(i))=true for all i and τ(u(a,b))=t for all a,b.

Only u(4,0) is an active unobserved vertex. The two states have the same
vertices and edges and differ at that active vertex's trait. The theorem is
the conjunction of these assertions (the first group is named
`a2_counterexampleClaim`):

1. D is admissible and both H_true,H_false are compatible with D.
2. r_1<degree(1), and parent(2)=1.
3. For every i∈S, {s(i),u(4,0)}∈E_Htrue if and only if i=1.
4. U(D,H_true,1,2)={s(2),s(3),u(4,0)} and
   U(D,H_true,1,3)={s(3),u(4,0)}.
5. The option-valued preferential recruitment is `some 0` for H_true and
   `some (5/12)` for H_false.
6. p(D,H_true)−p(D,H_false)=−5/12, and this difference is unequal to both
   −1/[c |U(D,H_true,1,2)|] and −1/[c |U(D,H_true,1,3)|].
7. The raw real values are also explicitly p(D,H_true)=0,
   p(D,H_false)=5/12, and c=2.
8. The two proposed comparison fractions equal −1/6 and −1/4, respectively.

The universal quantifier in item 3 follows the fixed choices of D and states;
it does not vary the witness. For clarity, the event terms of p(D,H_false)
are 1−2/3 and 1−1/2, giving (1/3+1/2)/2=5/12. The event terms for H_true
are both zero. The formal proposition itself asserts no general formula for
an arbitrary data set or arbitrary number of recruits.

### Totalization and junk-value audit

- The time function i−1 uses truncated natural subtraction. On sampled labels
  1,2,3 it gives exactly 0,1,2; the off-sample value at 0 is irrelevant.
  Thus the observed ordering is strict and parent-before-child is satisfied.
- Real divisions in p and its event terms are total. Here c=2 and the event
  susceptible counts are 3 and 2 in both states. All fractions asserted by the
  theorem therefore have positive denominators; the `some` assertions also
  certify the definedness guards. No undefined average is being used.
- Finite sums and cardinalities can be zero in general, and raw p would use
  zero-divisor conventions in such cases. This theorem does not quantify over
  such cases. There are two nonseed recruits, one real event for each, and one
  active private neighbour. No empty-index convention contributes to the result.
- All degree/count casts to ℝ preserve their natural values. Erasure/insertion,
  extrema, integrals, infinities, logarithms, powers, square roots, and partial
  function default values are absent from this statement's operative definitions.
- The two states' total traits also differ on inactive right-summand labels,
  but compatibility and p inspect only active vertices. This extension has no
  effect on any asserted functional value.
