# Blind reading

Written from the current Challenge, all entries in `closure.json`, and the
corresponding Defs sources, before reading claims.json, record.json, earlier.json,
or architect-report.md. Generated declarations were also inspected with
`scratch/ClosureChecks.lean`, which compiled successfully. The following common
notation is part of each of the five readings, not an additional assumption.

## Common objects, fully expanded

The vertex type is the disjoint union `Nat ⊕ (Nat × Nat)`. Write S_i for the left
injection of i and U_ik for the right injection of (i,k). These injections are
distinct, and U_ik=U_jl exactly when i=j and k=l. A data record D consists of finite
subsets S,M of Nat, and total functions parent,time,degree : Nat → Nat and
trait : Nat → Bool. Write N=S\M, V_S={S_i:i∈S}, and
B={{S_parent(j),S_j}:j∈N}, a finite SET of finite vertex sets, with duplicates
removed. The recruitment degree r_i is the cardinality of {e∈B:S_i∈e}.
Admissibility means, in this order:

1. M⊆S.
2. For all i,j∈S, time(i)=time(j) implies i=j.
3. For every j∈N, parent(j)∈S and time(parent(j))<time(j).
4. For every i∈S, r_i≤degree(i).

Write d_i=degree(i), z_i=trait(i), s_i=d_i-r_i in Nat,
T=Σ_{i∈S}s_i, T_b=Σ_{i∈S,z_i=b}s_i and D_b=Σ_{i∈S,z_i=b}d_i.
These are finite sums. A state H is a finite vertex set V, a finite set E of
finite vertex sets, and a TOTAL Boolean function τ on the ambient vertex type.
Its degree k_v is |{e∈E:v∈e}|. A state is simple if every e∈E has cardinality 2
and e⊆V. It is augmented if it is simple and every e∈E contains S_i for some i∈S.
Compatibility means:

1. H is augmented.
2. V_S⊆V and B⊆E.
3. For every i∈S, τ(S_i)=z_i.
4. Every v∈V\V_S is joined to at least one S_i, i∈S.
5. For every i∈S, k_{S_i}=d_i.

Thus nonsampled vertices cannot be isolated or have nonsampled neighbours;
sampled seeds with degree zero are allowed. The names of nonsampled vertices
need not be right injections: a left injection outside V_S is also nonsampled.
All trait restrictions concern the active vertices; a state nevertheless stores
values at every ambient vertex. `Data.mk`, `State.mk` and their projections are
ordinary structure constructors/projections, with no extra condition.

For a state let A_vw=1 if v≠w and {v,w}∈E, and 0 otherwise;
x_v=1 if τ(v)=true, and 0 otherwise; m=|E|. The two real finite sums are

    num(H)=Σ_{v,w∈V}(A_vw-k_v k_w/(2m)) x_v x_w,
    den(H)=Σ_{v,w∈V}(1_{v=w} k_v-k_v k_w/(2m)) x_v x_w.

`hValue` is num/den. `HomophilyDefined` means m>0 and den≠0;
`homophily` is `some(hValue)` under that condition and `none` otherwise.
Let A(H), Z(H), C(H) count, respectively, edges whose vertices all have trait
true, edges whose vertices all have trait false, and edges containing both
traits. On the recruitment-only state (V_S,B), with τ(S_i)=z_i and all right
injections assigned false, these are a,b,c_R. Define

    Φ(x,y,c)=1-c/(2x+c)-c/(2y+c),
    h_L=Φ(a,b,c_R+T),
    h_U=Φ(a+T_true,b+T_false,c_R).

All arguments are cast to reals before these formulas are evaluated.
Let H_same have vertices V_S∪{U_ik:i∈S,0≤k<s_i} and edges
B∪{{S_i,U_ik}:i∈S,0≤k<s_i}. Its sampled traits equal z_i; its U_ik trait
equals z_i if same=true and the Boolean negation of z_i otherwise. The same rule
assigns traits to inactive ambient labels too. Its added vertices are private
leaves. Let HV={r∈Real:there exists a compatible H with homophily(H)=some r}.
`FullHomophilyRegion(D,L,U)` means that every compatible H is defined, L∈HV
and L≤r for all r∈HV, and U∈HV and r≤U for all r∈HV. It does not assert that
every real number between L and U is attained.

`removeEdge H v w` erases {v,w} from E; `addEdge` inserts it. Neither changes
vertices or traits. `unsampled` is V\V_S. `cleanup D repaired H` retains the
vertices v∈V for which (repaired=true and v∈V_S) or k_v≠0, and keeps E and τ
unchanged. `induced D H` is (V_S,{e∈E:e⊆V_S},τ).
`InducedCompatible` means it is simple, has exactly V_S as vertices, contains B,
and has degree at S_i at most d_i for every i∈S. It adds no trait clause.
`wholeNeighbors H v` is {w∈V:{v,w}∈E}.

## SAP.P012a.T6

The theorem is a closed conjunction, with independent universally quantified
parts, rather than a theorem fixing one D globally.

First, for EVERY D, if D is admissible, D_false>0 and D_true>0, then:

* For EVERY compatible H, den(H) equals
  (2A(H)+C(H))(2Z(H)+C(H))/(2(A(H)+Z(H)+C(H))), is strictly positive, and
  hValue(H)=Φ(A(H),Z(H),C(H)). Furthermore
  a≤A(H)≤a+T_true, b≤Z(H)≤b+T_false,
  c_R≤C(H)≤c_R+T, and h_L≤hValue(H)≤h_U.
* H_false and H_true are compatible, their `homophily` values are respectively
  some h_L and some h_U, and the least/greatest and all-defined assertions
  described by FullHomophilyRegion hold.

Second, for EVERY real x,y,c, if 2x+c≠0 and 2y+c≠0, then
Φ(x,y,c)=(4xy-c²)/((2x+c)(2y+c)). This algebraic part permits negative inputs.

Third, for EVERY admissible D with the same two strict degree-total hypotheses:

* For BOTH same=false and same=true, every i∈S and k<s_i has U_ik nonsampled,
  degree one, with every incident edge equal to {S_i,U_ik}, and trait equal to
  z_i or its negation according to same. Every i∈S has degree r_i+s_i=d_i.
* For EVERY real L,U,
  HV⊆[L,U] if and only if L≤h_L and h_U≤U.
* For EVERY pair of lists vertices,children of Nat, if each list has no repeated
  entries and its associated finite set is respectively S,N, the following
  scan assertions hold. There is no chronological order requirement here.

The scan starts a seven-Nat record q=(d0,d1,ones,zeros,mixed,visits,additions)
at all zeros, traverses vertices once and then children once. A vertex record i
adds d_i to d1 if z_i=true and otherwise to d0. A child record j classifies
(z_parent(j),z_j), adding one to ones, zeros, or mixed. Each transition also adds
one to visits and additions. The two recursive scans consume the head then
recurse on the tail. At the end the theorem asserts:

    d0=D_false, d1=D_true, ones=a, zeros=b, mixed=c_R,
    d1=2ones+mixed+T_true, d0=2zeros+mixed+T_false,
    d1-(2ones+mixed)=T_true, d0-(2zeros+mixed)=T_false,
    visits=additions=|S|+|B|.

In the last line both subtractions are Nat subtractions. The finishing function
sets s1=d1-(2ones+mixed), s0=d0-(2zeros+mixed), c=mixed+s0+s1,
x=ones+s1,y=zeros+s0. It returns the following pair of rationals:

    (1-c/(2ones+c)-c/(2zeros+c),
     1-mixed/(2x+mixed)-mixed/(2y+mixed)).

The theorem asserts that the real casts of these outputs are h_L and h_U.
The docstring additionally describes 26 postprocessing arithmetic operations,
indexed access and unit-cost exact arithmetic. The definition explicitly
implements the arithmetic expression; only the scan counters, rather than a
separate final-operation counter, occur in the logical statement.

Junk conventions: natural s_i subtraction truncates in general but not for
sampled indices under admissibility. The displayed finish-budget equalities
exclude truncation there. Empty-list scans are the identity, empty finite sums
are zero; the two positive degree totals rule out empty S and zero trait-degree
factors in all homophily uses. Real and rational division are total with 1/0=0,
but the compatible states and the endpoint constructions have positive
denominators here. The free algebraic identity explicitly excludes its zero
factors. Nat→Real and Nat→Rat casts are exact and nonnegative. There are no
integrals, extended reals, logarithms, roots, powers on noninteger domains,
infima/suprema, limits, or partial-choice defaults in this closure. Generated
`_proof_*` entries shared from other definitions are proofs of numeric
`AtLeastTwo` instances, not hidden mathematical hypotheses. The generated scan
recursors and Sum/Prod matchers implement exactly the cases described above.

## SAP.P012a.T7

Additional definitions needed in this section: a vertex is not yet sampled at
event j if it is U_ik, or if it is S_k with k∉S or time(j)≤time(k). Define

    Sus(H,i,j)={v∈V:{S_i,v}∈E and v is not yet sampled at j},
    Same(H,i,j)={v∈Sus(H,i,j):τ(v)=τ(S_i)},
    C_j={k∈N:parent(k)=parent(j) and time(j)≤time(k)},
    m_j=|{k∈C_j:z_k=z_parent(j)}|,
    I_j=1 if z_j=z_parent(j), else 0.

`pValue(D,H)` is [Σ_{j∈N}(1_{τ(S_j)=τ(S_parent(j))}
-|Same(H,parent(j),j)|/|Sus(H,parent(j),j)|)]/|N|, in reals.
`PreferentialDefined` requires |N|>0 and all event susceptible-set cardinalities
strictly positive. `preferential` returns some pValue in this case and none
otherwise. Define

    p_L=(Σ_{j∈N}(I_j-(m_j+s_parent(j))/(|C_j|+s_parent(j))))/|N|,
    p_U=(Σ_{j∈N}(I_j-m_j/(|C_j|+s_parent(j))))/|N|,
    PV={r:there exists compatible H with preferential(D,H)=some r}.

`FullPreferentialRegion(D,L,U)` means every compatible H is defined and L and U
are respectively an attained least and greatest element of PV, not that PV
fills the interval.

The theorem states the following conjunction:

1. For EVERY D, admissibility and |M|<|S| imply: for EVERY compatible H and
   EVERY j∈N, {S_k:k∈C_j}⊆Sus(H,parent(j),j), and there EXIST Nat y,q such that
   y≤s_parent(j), q≤y, |Sus|=|C_j|+y, |Same|=m_j+q, and

       m_j/(|C_j|+s_parent(j)) ≤ (m_j+q)/(|C_j|+y)
         ≤ (m_j+s_parent(j))/(|C_j|+s_parent(j)).

   H_true and H_false are compatible and attain some p_L and some p_U,
   respectively, and FullPreferentialRegion(D,p_L,p_U) holds.
2. For EVERY admissible D with |M|<|S| and EVERY j∈N, j∈C_j and |C_j|>0.
3. For EVERY such D and EVERY chronological list order, the exact streaming
   assertions below hold. Chronological means no duplicates, finite set S, and
   time(i)<time(j) for every earlier/later pair in the list.
4. For EVERY admissible D (without requiring |M|<|S|), there EXISTS a
   chronological list. For EVERY Boolean same, i∈S, and k<s_i,
   wholeNeighbors(H_same,U_ik)={S_i}.

The algorithm reads records (label,seed,parent,degree,trait) for the supplied
order. Its state is a TOTAL function cells:Nat→Option Cell, rational low/high,
and Nat count,reads,reciprocals,work. A cell contains Nat remaining, rational
reciprocal and Boolean trait. Initially all cells are none and all numbers zero.
At each record a it first puts at a.label the cell
(a.degree-(0 if a.seed else 1),0,a.trait). If seed, it adds one read and 8 work.
Otherwise it reads c=cells(a.parent), using default (0,0,false) if absent;
sets R=c.reciprocal+1/c.remaining, I=1_{a.trait=c.trait}; updates the parent cell
to (c.remaining-1,R,c.trait); sets low:=low+(1-I)(R-1),
high:=high+I(1-R); increments count,reads,reciprocals by one and work by 32.
The final rational output is (low/count,high/count).

For every admissible, nonempty-event input and every chronological order,
PWholeOnePass asserts that the two real-cast outputs equal p_L,p_U;
count=|N|>0, reads=|S|, reciprocals=|N|, work+4≤32|S|+4. For EVERY split
order=pre++post, reads after running pre equals pre.length; there EXISTS a
finite key set equal to pre.toFinset, of cardinality at most |S|, and cells(r)
is some exactly when r belongs to that key set, for EVERY r. For EVERY split
order=pre++j::post with j∈N there EXISTS c such that the parent cell after pre
is some c, c.trait=z_parent(j), and
c.remaining=|C_j|+s_parent(j)>0.

Junk conventions: all finite sums and casts are as above. Nonempty-event
assumptions and C_j containing j rule out every denominator zero in the
mathematical definitions. Admissibility prevents truncating sampled spare
degrees. In the algorithm, nonseed degrees are at least one; a parent is an
earlier record, and its remaining count is positive at each decrement, as
explicitly asserted for every event. Thus the getD default and division by zero
are unreachable on the stated domain, even though the total program defines
both. An exhausted remaining count can be zero AFTER its last use, harmlessly.
Empty S is allowed in the independent order-existence/private-leaf conjuncts
and makes their universal leaf clauses empty; it is excluded from the endpoint
and one-pass parts. No integrals, noninteger powers, order-completion operations
or infinite limits occur. Derived Inhabited really gives the cell (0,0,false).

## SAP.P012a.T8

This is a closed assertion about fixed finite objects, with no free parameters.
The data have S={1,2,3}, M={1}, parent(3)=2, parent(j)=1 for j≠3,
time(i)=i, d_2=2, d_i=3 for i≠2, and z_i=(i=3).
B={{S_1,S_2},{S_2,S_3}} and the sampled recruitment degrees are (1,2,1).
Let W=U_40. The starting state H has vertices {S_1,S_2,S_3,W}, edges

    {12,23,13,1W,3W},

and τ(v)=true exactly at S_3, on the whole ambient vertex type. Here 12 means
{S_1,S_2}, etc. The output K deletes 1W and 3W, inserts 13 as a finite-set
insertion (13 is already present), then removes isolated nonsampled vertices
while preserving sampled vertices. Traits do not change.

The complete assertion is: D is admissible; H is compatible; 1<3;
3∈N; parent(3)≠1; r_1<d_1 and r_3<d_3; edges 1W,3W,13 are in H;
K is NOT compatible; induced(D,H).edges=induced(D,K).edges;
K.vertices=V_S; K.edges={12,23,13}; sampled degrees in H are (3,2,3)
and in K are (2,2,2). This supplies an allowed compatible starting state for an
operation, but does not itself assert any universal operation relation or the
negation of an existential graph-nonidentification result. The docstring calls
the printed claim false and identifies the failed proof operation.

Junk conventions: erase of an absent edge is identity and insert of an existing
edge is identity; the latter is essential to the counterexample's meaning,
because simple graphs do not carry parallel edges. Cleanup checks degrees in
the pending state and leaves its edges/total trait function unchanged. It deletes
W, whose degree is zero. There are no divisions, real quantities, infinite
operations or default partial functions in this statement. The positive spare
conditions here amount to s_1=s_3=2. Functions on inactive labels are total but
do not affect compatibility or the induced edge comparison.

## SAP.P012a.T9

The same fixed data as T8 are used. Let W=U_40 and X=U_50. The starting H has
vertices {S_1,S_2,S_3,W,X}, edges {12,23,1W,3X,1X,3W}, and
τ(v)=true exactly at S_3 and X. The output K deletes 1W and 3X and inserts
1X and 3W; both inserted edges were already present. It leaves V and the total
trait function fixed, and performs no cleanup.

The statement is a conjunction asserting: D admissible; H compatible;
r_1<d_1 and r_3<d_3; z_1=false,z_3=true; τ(W)=false,τ(X)=true;
all four of 1W,3X,1X,3W are present in H; K is NOT compatible;
K.vertices=H.vertices; K.edges={12,23,1X,3W}; degrees in the order
(S_1,S_2,S_3,W,X) are (3,2,3,2,2) in H and (2,2,2,1,1) in K;
|E_H|=6, |E_K|=4; K.trait=H.trait;
Σ_{v∈V_H}k_v x_v=5 and Σ_{v∈V_K}k_v x_v=3;
den(H)=35/12 and den(K)=15/8; both denominators are positive and unequal.
There is no remaining universal quantifier over a swap or choice of states.
The docstring describes a failed printed proof step and says the printed claim
is false. Whether that is the right target description requires the later claim
comparison.

Junk conventions: insertion is idempotent, intentionally recording the failure
to preserve degrees when proposed new edges already exist. The real finite-sum
denominators use 2|E|, positive here (12 and 8), so their division is ordinary.
The outer homophily quotient and Option guard do not occur. Natural and real
casts are exact; no truncated subtraction, integrals, infinite limits or other
partial operations affect this witness. Numeric `_proof_*` entries are merely
instances for the literal denominators 12,8,etc.

## SAP.P012a.T10

For EVERY D, assume admissibility; then for EVERY i,j∈Nat assume, in order,
i∈S, j∈S, time(i)<time(j), NOT(j∈N and parent(j)=i), r_i<d_i and r_j<d_j.
The conclusion first asserts the geometry below, then, for EVERY total Boolean
function τ extending all sampled z_k, asserts the compatibility/distinction
properties below. In particular the witness graphs are explicit, not supplied
by an assumed existence or conclusion hypothesis.

For v∈Nat let

    L_v={U_vk: k<s_v and (k≠0 or (v≠i and v≠j))},  W=U_i0.

Define H with vertices V_S∪{W}∪⋃_{v∈S}L_v, edges
B∪{{S_i,W},{S_j,W}}∪⋃_{v∈S}{{S_v,w}:w∈L_v}, and trait function τ.
Define K with vertices V_H\{W}, edges
(E_H\{{S_i,W},{S_j,W}})∪{{S_i,S_j}}, and the SAME total trait function τ.

The geometry conclusion means: s_i,s_j>0; {S_i,S_j}∉B; for EVERY v∈S,
|L_v| is s_v-1 when v=i or v=j and otherwise s_v; L_v is disjoint from V_S
and excludes W; for EVERY distinct v,w∈S the sets L_v,L_w are disjoint.
For EVERY τ, whether it extends sampled traits or not, W∈V_H\V_S and
wholeNeighbors(H,W)={S_i,S_j}; for EVERY v∈S,w∈L_v the neighbour set of w
in BOTH H and K is {S_v}; {S_i,S_j} is absent from H and present in K;
the two induced edge sets are exactly B and B∪{{S_i,S_j}}.

For EVERY τ extending the observed traits, the remaining conclusion asserts:
H and K are compatible; K has exactly the erased vertex set and replaced edge
set described above; K.trait=H.trait; the repaired cleanup after the two edge
deletions and one insertion in H equals K as an entire State; both induced
states are InducedCompatible (as expanded above); H≠K and induced(D,H)≠
induced(D,K). Finally there does NOT EXIST a permutation e of the ambient
vertex type such that e fixes every S_k,k∈S, e(V_H)=V_K,
{e(edge):edge∈E_H}=E_K and τ_K(e(v))=τ_H(v) for every v∈V_H. This is the
precise unfolded meaning of the last non-relabeling clause.

Junk conventions: sampled s_v subtraction does not truncate by admissibility;
s_i-1 and s_j-1 do not truncate because both spares are positive. Finite ranges
for other vertices may be empty, legitimately giving zero private leaves.
The time inequality ensures i≠j. The explicit injections, deleted slots, and
absence of the chosen recruitment edge prevent insertion collisions. Cleanup
removes the isolated W and retains all sampled vertices, including isolated
seeds; it cannot delete the private leaves, which have degree one. The trait
function at the removed W remains stored but inactive, so equality of total
trait functions is stronger than active agreement and is achieved by this
construction. Permutations are actual bijections, with no default extension
chosen by the definition. There are no numerical quotients, real partial
functions, measures, infima/suprema or infinite limits in this closure.

## Closure coverage

The five closure lists contain respectively 80,80,34,43,39 entries. All source
definitions, structure fields/constructors and generated declarations in their
union were read. The generated numeric proofs, pattern matchers, recursive scan
auxiliaries and default cell were separately printed by Lean. No Solution or
proof body for the audited theorems was needed or inspected.
