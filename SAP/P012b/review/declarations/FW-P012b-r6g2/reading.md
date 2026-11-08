# Blind reading

Saved before opening claims.json, record.json, earlier.json, or architect-report.md.
The five theorem docstrings, theorem types, and all declarations listed by their
closure entries have been read. Source locations below use the current files
(the closure's line numbers sometimes point to the start of a docstring).
The generated dependency declarations were also printed by Lean in
scratch/BlindPrint.lean; scratch/BlindPrint.out contains the inspected output.

## Common mathematical expansion

This notation expands the shared definitions for all five sections; subsequent
uses of these mathematical symbols mean exactly these finite-set expressions.
There are no unexpanded SAP predicates implicit in the notation.

A vertex is an element of the disjoint union N + (N x N). Write s(i) for the
left injection of i and u(i,k) for the right injection of (i,k). A datum D is a
tuple (S,B,a,t,d,z), where S and B are finite subsets of N; a,t,d are total maps
N -> N; and z is a total map N -> {false,true}. In particular, B is the seed
set, a is the parent map, t the sampling rank, and d the observed degree. Its
nonseeds are J=S\B, sampled vertices are V_S={s(i):i in S}, and recruitment
edges are E_R={{s(a(j)),s(j)}:j in J}, a finite set of finite vertex sets. Let
r(i)=#{e in E_R:s(i) in e}. Spare degree is the natural-number subtraction
d(i)-r(i), hence max(d(i)-r(i),0). For b in {false,true}, the sampled trait
degree is q_b=sum_{i in S,z(i)=b} d(i). Children of i are {j in J:a(j)=i}.

Admissibility means, conjunctively: B subset S; t is injective on S; for every
j in J, a(j) in S and t(a(j))<t(j); and for every i in S, r(i)<=d(i).
Thus recruitment edges have two different endpoints, and the spare subtraction
is ordinary subtraction on sampled indices.

A state H=(V,E,Z) has a finite vertex set V, a finite set E of finite vertex
sets, and a total Boolean trait map Z on the entire disjoint union. Its degree
k_H(v)=#{e in E:v in e}. Simplicity says that every e in E has cardinality two
and is a subset of V. Augmentation says simplicity and that every e in E
contains s(i) for some i in S. Compatibility with D says augmentation;
V_S subset V; E_R subset E; Z(s(i))=z(i) for i in S; every v in V\V_S is
adjacent to some sampled s(i); and k_H(s(i))=d(i) for i in S. Thus there are
no edges between two unsampled vertices, no extra isolated unsampled vertices,
and all sampled vertices, including isolated ones, are retained. An unsampled
vertex means any v in V\V_S; it can have either injection's syntactic form.
These definitions impose no global population-size bound.

For a state set m=#E, A(v,w)=1 if v!=w and {v,w} in E, and 0 otherwise;
x(v)=1 if Z(v)=true, and 0 otherwise. All divisions and sums below are in R:

N_H = sum_{v in V} sum_{w in V}
        [A(v,w)-k_H(v)k_H(w)/(2m)] x(v)x(w),
Q_H = sum_{v in V} sum_{w in V}
        [1_{v=w}k_H(v)-k_H(v)k_H(w)/(2m)] x(v)x(w).

The raw h-value is N_H/Q_H. Its domain predicate is m>0 and Q_H!=0.
The actual homophily statistic is the Option real Some(N_H/Q_H) on this
domain and None otherwise. These are ordered double sums, not edge sums.

For a recruitment event j, a vertex v is not yet sampled if v=s(k) and
(k notin S or t(j)<=t(k)), or if v=u(k,l), in which case it is always not yet
sampled. Define U(i,j)={v in V:{s(i),v} in E and v is not yet sampled at j}
and U_same(i,j)={v in U(i,j):Z(v)=Z(s(i))}. Define

c_D,H(j)=1_{Z(s(j))=Z(s(a(j)))}-#U_same(a(j),j)/#U(a(j),j),
P_D,H=sum_{j in J} c_D,H(j),  p_D,H=P_D,H/#J.

The preferential domain predicate is #J>0 and #U(a(j),j)>0 for every j in J.
The statistic is Some(p_D,H) on that domain and None otherwise. At an
admissible compatible state, s(j) belongs to its recruiter's susceptible set,
so every event's denominator is positive; the final average still requires
J nonempty. Equality time is included, so the recruit itself is susceptible.

The h-value set is {h in R:there exists a state compatible with D whose
homophily Option equals Some h}; the p-value set is defined the same way with
the preferential Option. A full h-region with endpoints L,U means EVERY
compatible state has m>0 and Q_H!=0; L belongs to the h-value set and is <=
every member; and U belongs to the h-value set and is >= every member.
A full p-region makes the analogous total-domain assertion and attained
least/greatest assertions for p. Thus these are attained containing intervals,
not assertions that every intermediate real value is realizable. Point
identification means that the value set equals {r} for some real r; an empty
value set does not qualify.

The recruitment state has V=V_S, E=E_R, and trait z(i) at s(i), false at
right-injection vertices. A private-leaf completion has V=V_S union
{u(i,k):i in S, k<d(i)-r(i)} and E=E_R union
{{s(i),u(i,k)}:i in S,k<d(i)-r(i)}. Its sampled traits are z(i). A parameter
b=true gives every private leaf its sampled neighbor's trait; b=false gives
the complement. A trait flip at v keeps V,E fixed and replaces Z(v) by !Z(v),
using a total function update, leaving all other traits as before.

### Shared convention inventory

* Finite sets remove repeated vertices and edges. A pair {v,v} has cardinality
  one; the simplicity hypothesis excludes it. Degrees count incident edges
  once, rather than counting a loop twice. This cannot affect a simple state.
* Natural-number subtraction truncates. Admissibility prevents truncation in
  sampled spare degrees; t(i)=i-1 in one example is explicitly a truncated
  natural rank and equals 0 at i=0,1. Only i=1,2 are sampled there.
* Real division by zero is zero. N_H and Q_H contain /(2m), the raw h-value
  contains /Q_H, and the p-value contains susceptible-set denominators and
  /#J. The Option guards exclude undefined h,p values from their value sets.
  Raw quotients in conclusions must be checked against the corresponding
  domain separately. General equality of Options also allows None=None.
* Finite sums over empty finite sets are zero. Empty samples, seeds, edge
  sets, event sets, and susceptible sets are representable. Their treatment
  follows the explicit hypotheses and Option guards, not a positivity default.
* All cardinalities and degrees cast from N to R are exact nonnegative real
  integers. All displayed fractional endpoints are real divisions, not natural
  divisions. There is no integer rounding in those expressions.
* Trait, parent, degree and time maps are total. Values outside the displayed
  sample or state have no partial-function default. They matter only where
  explicitly queried. In particular, an unused left-injection label is treated
  as unsampled by the disjunction k notin S.
* No logarithm, square root, rpow, integral, expectation, ENNReal.toReal,
  infimum, supremum, limsup or liminf occurs in these statements' closures.
  The interval predicates use membership and order, not empty-set extrema.
* The 27 generated dependency declarations have been read with #print.
  All _proof_* constants just construct Nat.AtLeastTwo evidence for ordinary
  numerals (used in elaboration). The two match_1 declarations are exhaustive
  Sum/Prod case eliminators. None introduces an assumption, axiom, partial
  default, or additional mathematical clause.

## SAP.P012b.T18

Source: Challenge/Part1.lean:46-53; expanded statement WholeW1.lean:191-204.

The conclusion is a conjunction of a universal invariance statement and a
closed, explicitly instantiated example. First, for every pair of states H,K,
if V_H=V_K, E_H=E_K, and Z_H(v)=Z_K(v) for every v in V_H, their homophily
Options are equal. There is no admissibility, simplicity, compatibility,
nonempty-edge, or nonzero-denominator hypothesis in this first component.
It includes agreement when both values are undefined.

The closed example has S={1,2,3}, B={1}, t(i)=i, d(1)=3 and d(i)=2 otherwise,
and z(i)=true exactly when i=3. The star parent map is constantly 1. The chain
changes only the parent map, to a(3)=2 and a(i)=1 otherwise. The reordered
star changes only t: t(2)=3, t(3)=2, t(i)=i otherwise. The common state has
V={s(1),s(2),s(3),u(0,0)}, E={{s(1),s(2)},{s(1),s(3)},
{s(2),s(3)},{s(1),u(0,0)}}, and Z(v)=true exactly at s(3).

The statement asserts all three data are admissible and this very state is
compatible with each; the chain and reordered data are exactly the indicated
single-field updates; the star and chain recruitment edge sets differ; the
star and reordered recruitment edge sets agree; t_star(2)<t_star(3), while
t_reordered(3)<t_reordered(2); and the three preferential Options are,
respectively, Some(-1/12), Some(1/6), Some(-1/3). All quantifiers in this
component have been discharged by the fixed named data: these are assertions,
not hypotheses about unspecified examples.

Convention effect: the universal part intentionally covers the raw zero-edge
and zero-denominator cases through None. Its meaning is equality of partial
statistics, not an assertion that every state has ordinary h. The explicit
preferential results are Some values, so their guards enforce genuine nonempty
event sets and denominators. There are no additional junk-value uses here.
The docstring accurately describes the literal mathematical type on its face.

## SAP.P012b.T19

Source: Challenge/Part1.lean:55-57; Part4.lean:48-51; proposal definitions
Part2.lean:13-69.

This is the negation of the universal preservation property: NOT(for every
D,H,K, if D is admissible, H is compatible with D, and K is a proposal from H
with repaired=false, then K is compatible with D). Classically this supplies
some D,H,K satisfying all three premises with incompatible output. There are
no h- or p-domain hypotheses in this declaration.

Here is the complete finite relational definition of a proposal. Removing an
edge erases {v,w} from E, adding one inserts it, and adding a vertex inserts it
into V and updates its trait to a specified Boolean. The replacement pool for
sampled i is {v in V_H\V_S:{s(i),v} notin E_H}. A replacement from a pending
state P either chooses v in that pool and returns P unchanged, or chooses
v notin V_P and an arbitrary Boolean trait, returning P with v inserted and
that trait set. The pool is always computed from the original state H.
Cleanup with repaired=false retains precisely vertices of positive degree,
without changing edges or traits; repaired=true would additionally retain
all sampled vertices. Only false is used in T19.

A graph proposal is exactly one of these four constructors:

1. Choose i in S, j in V_H, s(i)!=j, an existing non-recruitment edge
   {s(i),j}, and j notin V_S. Remove this edge; replace at sampled i using
   the rule above, yielding P and replacement v; add BOTH {s(i),v} and {j,v};
   then clean up. (The repaired=true variant would add just {s(i),v}.)
2. Choose distinct i,j in S and an existing non-recruitment edge {s(i),s(j)}.
   Remove it and replace at i, giving v,P. From P with {s(i),v} added, replace
   at j, giving w,Q. Insert {s(j),w} and clean up.
3. Choose i in S and j in V_H with s(i)!=j and {s(i),j} absent. Choose
   v,w in V_H\V_S such that {s(i),v} and {j,w} are existing edges. Erase those
   two edges, insert {s(i),j}, and clean up. No v!=w premise is imposed.
4. Choose i in S and j in V_H, s(i)!=j, such that the edge is not both present
   and outside E_R, and such that it is not both absent and equipped with
   v,w as in branch 3. Return the cleanup of H itself.

A trait proposal chooses v in V_H\V_S and flips only its trait. The additional
empty-pool identity constructor requires repaired=true and is therefore
unavailable. Proposal is the disjunction of graph and trait proposals.
There are no selection probabilities or transition probabilities in this
statement; it asserts failure for a legal execution of the relation.

Convention effect: finite insertion is idempotent; existing/fresh rules are
membership conditions, not choice functions with defaults. Empty pools can
prevent a constructor but do not select junk. Natural admissibility and finite
graph conventions are as above. No statistical quotient is used in T19.
The docstring calls this a refutation of printed compatibility preservation;
that comparison requires reading the claim and the printed mechanisms later.

## SAP.P012b.T20

Source: Challenge/Part1.lean:59-61; Part4.lean:53-54;
Part2.lean:97-111.

For every ordered triple of data (D_sex,D_crack,D_home), it is NOT the case
that all the following hold:

* Every datum among this three-element list is admissible, has #S=527,
  #B=6, and sum_{i in S} d(i)=4487.
* The three samples agree and the three seed sets agree. At every nonseed
  of the first datum their parent maps agree, and at every sampled index
  their degrees and times agree. Traits are permitted to differ.
* There exist six real numbers Ls,Us,Lc,Uc,Lh,Uh such that each datum has
  a full h-region with its respective endpoints, in the sense expanded above,
  and
  |Ls+7027/10000|<=1/20000, |Us-8292/10000|<=1/20000,
  |Lc+6918/10000|<=1/20000, |Uc-8231/10000|<=1/20000,
  |Lh+7179/10000|<=1/20000, |Uh-8242/10000|<=1/20000.

The outer triple is universal, the six endpoints existential inside the
negation. It is impossibility of simultaneous full compatible-set extrema,
not impossibility of three individual graphs having particular statistics,
and it does not assert anything about preferential recruitment intervals.
All rounding tolerances are inclusive real bounds of 0.00005.

Convention effect: full-region assertions require ordinary h at EVERY
compatible state and attained endpoints, so no zero-denominator default is
accepted as a reported interval. A possible empty compatible class would
still fail the required endpoint memberships. No sInf/sSup convention is
involved. Shared natural and finite-set conventions apply. The correctness
of the docstring's interpretation as the printed table must be checked later.

## SAP.P012b.T22

Source: Challenge/Part1.lean:63-74; Part5.lean:13-38;
WholeW1.lean:66-92 and 217-233.

This is a conjunction of five blocks; quantifier scope restarts for each.

1. For every datum D, if D is admissible, q_false>0, q_true>0, and #B<#S,
   then all four assertions hold: (a) the h-value set and p-value set are
   BOTH singletons iff d(i)=r(i) for every i in S; (b) that zero-spare condition
   is equivalent to every compatible state having V=V_S and E=E_R;
   (c) existence of an i in S with r(i)<d(i) implies the h-value set is not
   a singleton; and (d) zero spare degree implies every compatible state
   has exactly V_S,E_R and the observed traits at all displayed vertices.
2. For every admissible D with q_false,q_true positive, and every i in S
   with r(i)<d(i), the same-trait private-leaf completion H and its trait
   flip K at u(i,0) are both compatible, and N_H/Q_H != N_K/Q_K.
   This block does not require #B<#S.
3. For every admissible D with q_false,q_true positive and #B<#S, the
   p-value set is a singleton iff for every i in S, nonemptiness of
   {j in S\B:a(j)=i} implies d(i)=r(i). Thus only actual recruiters
   need have zero spare degree for p alone to be identified.
4. For every admissible D with both q values positive, and every sampled i
   with r(i)<d(i), let H be the same-trait completion and K its flip at
   u(i,0). Both h-domain predicates hold; u(i,0) belongs to V_H\V_S,
   k_H(u(i,0))=1, and its traits are respectively z(i),!z(i). Let E0 be
   E_H with {s(i),u(i,0)} erased; x and y be the real casts of the numbers
   of all-true and all-false edges in E0; and c the real cast of the number
   of edges in E0 having at least one true and one false endpoint. IF z(i)
   is true, then 2y+c>0 and, with phi(x,y,c)=1-c/(2x+c)-c/(2y+c),
   h_H=phi(x+1,y,c), h_K=phi(x,y,c+1),
   h_H-h_K=2(x+c+1)/[(2x+c+1)(2x+c+2)]
             +2y/[(2y+c+1)(2y+c)]>0.
   The detailed formula is conditional on the true trait; the preceding
   distinctness block covers both traits.
5. The fixed one-leaf datum has S={1,2}, B={1}, a constantly 1, t(i)=i-1,
   d(1)=1,d(i)=2 otherwise, and z(i)=true iff i=2. It is admissible.
   For EACH Boolean b the state with V={s(1),s(2),u(0,0)},
   E={{s(1),s(2)},{s(2),u(0,0)}}, Z(s(2))=true,
   Z(u(0,0))=b, all other Z=false, is compatible. For EVERY compatible
   H there is a vertex v, disjoint from {s(1),s(2)}, such that
   V_H={s(1),s(2)} union {v}, E_H={{s(1),s(2)},{s(2),v}},
   preferential=Some 0, homophily=Some(-1/3) if Z(v) is true and Some(-1)
   otherwise, and V_H!=V_S. The h-value set is exactly {-1,-1/3}, the
   p-value set exactly {0}. There are full h- and p-regions [-1,-1/3]
   and [0,0]. Each is the smallest containing interval: its value set is
   a subset of its closed interval, and for EVERY order-connected subset
   I of R containing the value set, that closed interval is a subset of I.
   Order-connected means that between any two members, every intermediate
   real number belongs. This includes open, unbounded and singleton intervals.

Convention effect: admissibility removes sampled spare truncation; spare>0
ensures u(i,0) actually exists. Positivity of sampled degree in both traits
ensures ordinary h in the completions, and the detailed flip block states
those domains explicitly. Nonempty recruitment is explicit where p singletons
are discussed. Every phi denominator in the conditional flip formula is
positive (x,y,c>=0 and 2y+c>0); its closed-example occurrences are also
ordinary fractions. Singleton and smallest-interval claims use no default
extremum. The one-leaf universal description is up to arbitrary vertex names,
not literal equality of total trait functions outside the graph. The
mathematical type visibly distinguishes joint identification from p alone.

## SAP.P012b.T23

Source: Challenge/Part1.lean:76-88; WholeW2.lean:13-30 and 40-115;
Part2.lean:92-95.

The underlying datum has S={1,2,3,4,5}, B={1}, a(3)=a(5)=2 and a(j)=1
otherwise; degrees on S are (5,4,3,3,2), with d(i)=3 at unspecified other
indices except the named cases; traits on S are (true,true,true,false,true).
For EVERY total map tau:N->N that is strictly increasing on S (for i,j in S,
i<j implies tau(i)<tau(j)), replace its time field by tau, giving D_tau.
The following entire conjunction is then asserted:

* Arithmetic: #J=4; q_false,q_true>0; the recruitment degrees at indices
  [1,2,3,4,5] are [2,3,1,1,1]; spare degrees are [3,1,2,2,1]. In E_R there
  are 3 all-true edges, 0 all-false edges, and 1 mixed edge. The sums of
  spare degrees at sampled true and false vertices are 7 and 2; their total
  is 9. The real function phi defined above obeys phi(3,0,10)=-5/8 and
  phi(10,2,1)=79/105. In the same-trait private-leaf completion, the four
  real contributions c_D,H(2),...,c_D,H(5) are [1/5,0,-3/4,0]; in the
  opposite-trait completion they are [4/5,1/3,0,1/2].
* For D_tau: admissibility; full h-region [-5/8,79/105]; full p-region
  [-11/80,49/120]. For every compatible H its Option statistics are Some
  of their raw quotients, those real values lie in the stated intervals,
  and both also lie in [-1,1]. Furthermore, there exist TWO compatible
  states H,K with preferential Option Some(-11/80) that cannot be related
  by any permutation of the whole vertex type fixing every sampled s(i),
  mapping V_H onto V_K, mapping every edge image onto E_K, and preserving
  displayed traits. This is genuine nonuniqueness modulo names.
* All assertions in the preceding bullet also hold for the datum obtained
  by replacing every observed z(i) by !z(i). The preceding arithmetic
  bullet, including the trait-specific counts, is NOT asserted verbatim
  for the complemented datum.
* For every H compatible with D_tau, the state with the same V,E and all
  Z(v) complemented is compatible with the complemented datum. Its h Option
  equals that of H, and its preferential Option under the complemented datum
  equals that of H under D_tau.

Quantifier order is: tau, then its strict-order hypothesis, then a conjunction
of arithmetic, original statistical assertions, complemented statistical
assertions, and a universal assertion about compatible H. The nonunique
endpoint witnesses are existential inside each statistical assertion and can
depend on tau and the trait coding. There is no claim that every point in
the rectangle is jointly attainable or that extrema are unique.

Convention effect: strict increase on the five-element sample has ordinary
instances, for example tau=id. Only ranks/order enter susceptible sets.
The two trait classes have positive sampled degree and there are four events;
full-region and Some assertions exclude every undefined quotient on compatible
states. The phi arithmetic uses positive denominators. The permutation is a
bijection of an infinite countable disjoint union, but only its restriction
to displayed finite states is constrained. Unspecified external traits have
no role in the equivalence. No partial-choice default or cardinality cast
changes any endpoint or summand. The docstring limits coding-specific counts
to the displayed coding, consistently with the literal statement.

## Closure coverage ledger

Every entry below was inspected in its source definition (constructors and
projections in the structure/inductive declaration) or in BlindPrint.out for
line-zero generated declarations. Repetition reflects shared dependencies.

### SAP.P012b.T18 dependencies

- SAP.P012b.Admissible — SAP/P012b/Defs/Part1.lean:50
- SAP.P012b.Augmented — SAP/P012b/Defs/Part1.lean:59
- SAP.P012b.Compatible — SAP/P012b/Defs/Part1.lean:62
- SAP.P012b.Data — SAP/P012b/Defs/Part1.lean:19
- SAP.P012b.Data.degree — SAP/P012b/Defs/Part1.lean:24
- SAP.P012b.Data.mk — SAP/P012b/Defs/Part1.lean:19
- SAP.P012b.Data.parent — SAP/P012b/Defs/Part1.lean:22
- SAP.P012b.Data.sampled — SAP/P012b/Defs/Part1.lean:20
- SAP.P012b.Data.seeds — SAP/P012b/Defs/Part1.lean:21
- SAP.P012b.Data.time — SAP/P012b/Defs/Part1.lean:23
- SAP.P012b.Data.trait — SAP/P012b/Defs/Part1.lean:25
- SAP.P012b.HomophilyDefined — SAP/P012b/Defs/Part1.lean:88
- SAP.P012b.PreferentialDefined — SAP/P012b/Defs/Part1.lean:112
- SAP.P012b.SamePair — SAP/P012b/Defs/WholeW1.lean:12
- SAP.P012b.Simple — SAP/P012b/Defs/Part1.lean:56
- SAP.P012b.State — SAP/P012b/Defs/Part1.lean:27
- SAP.P012b.State.edges — SAP/P012b/Defs/Part1.lean:29
- SAP.P012b.State.mk — SAP/P012b/Defs/Part1.lean:27
- SAP.P012b.State.trait — SAP/P012b/Defs/Part1.lean:30
- SAP.P012b.State.vertices — SAP/P012b/Defs/Part1.lean:28
- SAP.P012b.T14WholeStatement._proof_1 — SAP/P012b/Defs/WholeW1.lean:0
- SAP.P012b.T18WholeStatement — SAP/P012b/Defs/WholeW1.lean:184
- SAP.P012b.T18WholeStatement._proof_1 — SAP/P012b/Defs/WholeW1.lean:0
- SAP.P012b.T18WholeStatement._proof_2 — SAP/P012b/Defs/WholeW1.lean:0
- SAP.P012b.Vertex — SAP/P012b/Defs/Part1.lean:13
- SAP.P012b.adjacency — SAP/P012b/Defs/Part1.lean:70
- SAP.P012b.chainHistory — SAP/P012b/Defs/WholeW1.lean:51
- SAP.P012b.graphDegree — SAP/P012b/Defs/Part1.lean:39
- SAP.P012b.hDenominator — SAP/P012b/Defs/Part1.lean:80
- SAP.P012b.hNumerator — SAP/P012b/Defs/Part1.lean:75
- SAP.P012b.hNumerator._proof_1 — SAP/P012b/Defs/Part1.lean:0
- SAP.P012b.hValue — SAP/P012b/Defs/Part1.lean:86
- SAP.P012b.historyState — SAP/P012b/Defs/WholeW1.lean:41
- SAP.P012b.homophily — SAP/P012b/Defs/Part1.lean:90
- SAP.P012b.nonseeds — SAP/P012b/Defs/Part1.lean:32
- SAP.P012b.notYetSampled — SAP/P012b/Defs/Part1.lean:93
- SAP.P012b.notYetSampled.match_1 — SAP/P012b/Defs/Part1.lean:0
- SAP.P012b.pSum — SAP/P012b/Defs/Part1.lean:104
- SAP.P012b.pValue — SAP/P012b/Defs/Part1.lean:110
- SAP.P012b.preferential — SAP/P012b/Defs/Part1.lean:116
- SAP.P012b.recruitmentDegree — SAP/P012b/Defs/Part1.lean:42
- SAP.P012b.recruitmentEdges — SAP/P012b/Defs/Part1.lean:36
- SAP.P012b.reorderedHistory — SAP/P012b/Defs/WholeW1.lean:54
- SAP.P012b.s — SAP/P012b/Defs/Part1.lean:15
- SAP.P012b.sameSusceptible — SAP/P012b/Defs/Part1.lean:101
- SAP.P012b.sampledVertices — SAP/P012b/Defs/Part1.lean:34
- SAP.P012b.starHistory — SAP/P012b/Defs/WholeW1.lean:47
- SAP.P012b.susceptible — SAP/P012b/Defs/Part1.lean:98
- SAP.P012b.u — SAP/P012b/Defs/Part1.lean:17
- SAP.P012b.z — SAP/P012b/Defs/Part1.lean:73

### SAP.P012b.T19 dependencies

- SAP.P012b.Admissible — SAP/P012b/Defs/Part1.lean:50
- SAP.P012b.Augmented — SAP/P012b/Defs/Part1.lean:59
- SAP.P012b.Compatible — SAP/P012b/Defs/Part1.lean:62
- SAP.P012b.Data — SAP/P012b/Defs/Part1.lean:19
- SAP.P012b.Data.degree — SAP/P012b/Defs/Part1.lean:24
- SAP.P012b.Data.mk — SAP/P012b/Defs/Part1.lean:19
- SAP.P012b.Data.parent — SAP/P012b/Defs/Part1.lean:22
- SAP.P012b.Data.sampled — SAP/P012b/Defs/Part1.lean:20
- SAP.P012b.Data.seeds — SAP/P012b/Defs/Part1.lean:21
- SAP.P012b.Data.time — SAP/P012b/Defs/Part1.lean:23
- SAP.P012b.Data.trait — SAP/P012b/Defs/Part1.lean:25
- SAP.P012b.GraphProposal — SAP/P012b/Defs/Part2.lean:35
- SAP.P012b.GraphProposal.addObserved — SAP/P012b/Defs/Part2.lean:50
- SAP.P012b.GraphProposal.deleteObserved — SAP/P012b/Defs/Part2.lean:44
- SAP.P012b.GraphProposal.deleteUnobserved — SAP/P012b/Defs/Part2.lean:36
- SAP.P012b.GraphProposal.unchanged — SAP/P012b/Defs/Part2.lean:57
- SAP.P012b.Proposal — SAP/P012b/Defs/Part2.lean:68
- SAP.P012b.Replacement — SAP/P012b/Defs/Part2.lean:29
- SAP.P012b.Replacement.existing — SAP/P012b/Defs/Part2.lean:30
- SAP.P012b.Replacement.fresh — SAP/P012b/Defs/Part2.lean:32
- SAP.P012b.Simple — SAP/P012b/Defs/Part1.lean:56
- SAP.P012b.State — SAP/P012b/Defs/Part1.lean:27
- SAP.P012b.State.edges — SAP/P012b/Defs/Part1.lean:29
- SAP.P012b.State.mk — SAP/P012b/Defs/Part1.lean:27
- SAP.P012b.State.trait — SAP/P012b/Defs/Part1.lean:30
- SAP.P012b.State.vertices — SAP/P012b/Defs/Part1.lean:28
- SAP.P012b.T19Statement — SAP/P012b/Defs/Part4.lean:48
- SAP.P012b.TraitProposal — SAP/P012b/Defs/Part2.lean:64
- SAP.P012b.TraitProposal.empty — SAP/P012b/Defs/Part2.lean:66
- SAP.P012b.TraitProposal.flip — SAP/P012b/Defs/Part2.lean:65
- SAP.P012b.Vertex — SAP/P012b/Defs/Part1.lean:13
- SAP.P012b.addEdge — SAP/P012b/Defs/Part2.lean:16
- SAP.P012b.addVertex — SAP/P012b/Defs/Part2.lean:19
- SAP.P012b.cleanup — SAP/P012b/Defs/Part2.lean:25
- SAP.P012b.flipTrait — SAP/P012b/Defs/Part1.lean:159
- SAP.P012b.graphDegree — SAP/P012b/Defs/Part1.lean:39
- SAP.P012b.nonseeds — SAP/P012b/Defs/Part1.lean:32
- SAP.P012b.recruitmentDegree — SAP/P012b/Defs/Part1.lean:42
- SAP.P012b.recruitmentEdges — SAP/P012b/Defs/Part1.lean:36
- SAP.P012b.removeEdge — SAP/P012b/Defs/Part2.lean:13
- SAP.P012b.replacementPool — SAP/P012b/Defs/Part2.lean:22
- SAP.P012b.s — SAP/P012b/Defs/Part1.lean:15
- SAP.P012b.sampledVertices — SAP/P012b/Defs/Part1.lean:34
- SAP.P012b.unsampled — SAP/P012b/Defs/Part1.lean:162

### SAP.P012b.T20 dependencies

- SAP.P012b.Admissible — SAP/P012b/Defs/Part1.lean:50
- SAP.P012b.Augmented — SAP/P012b/Defs/Part1.lean:59
- SAP.P012b.Compatible — SAP/P012b/Defs/Part1.lean:62
- SAP.P012b.Data — SAP/P012b/Defs/Part1.lean:19
- SAP.P012b.Data.degree — SAP/P012b/Defs/Part1.lean:24
- SAP.P012b.Data.mk — SAP/P012b/Defs/Part1.lean:19
- SAP.P012b.Data.parent — SAP/P012b/Defs/Part1.lean:22
- SAP.P012b.Data.sampled — SAP/P012b/Defs/Part1.lean:20
- SAP.P012b.Data.seeds — SAP/P012b/Defs/Part1.lean:21
- SAP.P012b.Data.time — SAP/P012b/Defs/Part1.lean:23
- SAP.P012b.Data.trait — SAP/P012b/Defs/Part1.lean:25
- SAP.P012b.FullHomophilyRegion — SAP/P012b/Defs/Part1.lean:130
- SAP.P012b.HomophilyDefined — SAP/P012b/Defs/Part1.lean:88
- SAP.P012b.Simple — SAP/P012b/Defs/Part1.lean:56
- SAP.P012b.State — SAP/P012b/Defs/Part1.lean:27
- SAP.P012b.State.edges — SAP/P012b/Defs/Part1.lean:29
- SAP.P012b.State.mk — SAP/P012b/Defs/Part1.lean:27
- SAP.P012b.State.trait — SAP/P012b/Defs/Part1.lean:30
- SAP.P012b.State.vertices — SAP/P012b/Defs/Part1.lean:28
- SAP.P012b.T20Statement — SAP/P012b/Defs/Part4.lean:53
- SAP.P012b.Vertex — SAP/P012b/Defs/Part1.lean:13
- SAP.P012b.adjacency — SAP/P012b/Defs/Part1.lean:70
- SAP.P012b.graphDegree — SAP/P012b/Defs/Part1.lean:39
- SAP.P012b.hDenominator — SAP/P012b/Defs/Part1.lean:80
- SAP.P012b.hNumerator — SAP/P012b/Defs/Part1.lean:75
- SAP.P012b.hNumerator._proof_1 — SAP/P012b/Defs/Part1.lean:0
- SAP.P012b.hValue — SAP/P012b/Defs/Part1.lean:86
- SAP.P012b.hValues — SAP/P012b/Defs/Part1.lean:126
- SAP.P012b.homophily — SAP/P012b/Defs/Part1.lean:90
- SAP.P012b.nonseeds — SAP/P012b/Defs/Part1.lean:32
- SAP.P012b.printed_table_intervals — SAP/P012b/Defs/Part2.lean:97
- SAP.P012b.printed_table_intervals._proof_1 — SAP/P012b/Defs/Part2.lean:0
- SAP.P012b.printed_table_intervals._proof_2 — SAP/P012b/Defs/Part2.lean:0
- SAP.P012b.printed_table_intervals._proof_3 — SAP/P012b/Defs/Part2.lean:0
- SAP.P012b.printed_table_intervals._proof_4 — SAP/P012b/Defs/Part2.lean:0
- SAP.P012b.printed_table_intervals._proof_5 — SAP/P012b/Defs/Part2.lean:0
- SAP.P012b.printed_table_intervals._proof_6 — SAP/P012b/Defs/Part2.lean:0
- SAP.P012b.printed_table_intervals._proof_7 — SAP/P012b/Defs/Part2.lean:0
- SAP.P012b.printed_table_intervals._proof_8 — SAP/P012b/Defs/Part2.lean:0
- SAP.P012b.recruitmentDegree — SAP/P012b/Defs/Part1.lean:42
- SAP.P012b.recruitmentEdges — SAP/P012b/Defs/Part1.lean:36
- SAP.P012b.s — SAP/P012b/Defs/Part1.lean:15
- SAP.P012b.sampledVertices — SAP/P012b/Defs/Part1.lean:34
- SAP.P012b.z — SAP/P012b/Defs/Part1.lean:73

### SAP.P012b.T22 dependencies

- SAP.P012b.Admissible — SAP/P012b/Defs/Part1.lean:50
- SAP.P012b.Augmented — SAP/P012b/Defs/Part1.lean:59
- SAP.P012b.Compatible — SAP/P012b/Defs/Part1.lean:62
- SAP.P012b.Data — SAP/P012b/Defs/Part1.lean:19
- SAP.P012b.Data.degree — SAP/P012b/Defs/Part1.lean:24
- SAP.P012b.Data.mk — SAP/P012b/Defs/Part1.lean:19
- SAP.P012b.Data.parent — SAP/P012b/Defs/Part1.lean:22
- SAP.P012b.Data.sampled — SAP/P012b/Defs/Part1.lean:20
- SAP.P012b.Data.seeds — SAP/P012b/Defs/Part1.lean:21
- SAP.P012b.Data.time — SAP/P012b/Defs/Part1.lean:23
- SAP.P012b.Data.trait — SAP/P012b/Defs/Part1.lean:25
- SAP.P012b.FullHomophilyRegion — SAP/P012b/Defs/Part1.lean:130
- SAP.P012b.FullPreferentialRegion — SAP/P012b/Defs/Part1.lean:134
- SAP.P012b.HomophilyDefined — SAP/P012b/Defs/Part1.lean:88
- SAP.P012b.PointIdentified — SAP/P012b/Defs/Part1.lean:138
- SAP.P012b.PreferentialDefined — SAP/P012b/Defs/Part1.lean:112
- SAP.P012b.Simple — SAP/P012b/Defs/Part1.lean:56
- SAP.P012b.SmallestValueInterval — SAP/P012b/Defs/WholeW1.lean:27
- SAP.P012b.StarAtTwo — SAP/P012b/Defs/WholeW1.lean:17
- SAP.P012b.State — SAP/P012b/Defs/Part1.lean:27
- SAP.P012b.State.edges — SAP/P012b/Defs/Part1.lean:29
- SAP.P012b.State.mk — SAP/P012b/Defs/Part1.lean:27
- SAP.P012b.State.trait — SAP/P012b/Defs/Part1.lean:30
- SAP.P012b.State.vertices — SAP/P012b/Defs/Part1.lean:28
- SAP.P012b.T14WholeStatement._proof_1 — SAP/P012b/Defs/WholeW1.lean:0
- SAP.P012b.T22Statement — SAP/P012b/Defs/Part5.lean:13
- SAP.P012b.T22WholeStatement — SAP/P012b/Defs/WholeW1.lean:206
- SAP.P012b.Vertex — SAP/P012b/Defs/Part1.lean:13
- SAP.P012b.WholeLeafFlip — SAP/P012b/Defs/WholeW1.lean:74
- SAP.P012b.adjacency — SAP/P012b/Defs/Part1.lean:70
- SAP.P012b.children — SAP/P012b/Defs/Part1.lean:171
- SAP.P012b.flipTrait — SAP/P012b/Defs/Part1.lean:159
- SAP.P012b.graphDegree — SAP/P012b/Defs/Part1.lean:39
- SAP.P012b.hDenominator — SAP/P012b/Defs/Part1.lean:80
- SAP.P012b.hNumerator — SAP/P012b/Defs/Part1.lean:75
- SAP.P012b.hNumerator._proof_1 — SAP/P012b/Defs/Part1.lean:0
- SAP.P012b.hValue — SAP/P012b/Defs/Part1.lean:86
- SAP.P012b.hValues — SAP/P012b/Defs/Part1.lean:126
- SAP.P012b.homophily — SAP/P012b/Defs/Part1.lean:90
- SAP.P012b.leafCompletion — SAP/P012b/Defs/Part1.lean:146
- SAP.P012b.leafCompletion.match_1 — SAP/P012b/Defs/Part1.lean:0
- SAP.P012b.leafEdges — SAP/P012b/Defs/Part1.lean:143
- SAP.P012b.leafVertices — SAP/P012b/Defs/Part1.lean:140
- SAP.P012b.nonseeds — SAP/P012b/Defs/Part1.lean:32
- SAP.P012b.notYetSampled — SAP/P012b/Defs/Part1.lean:93
- SAP.P012b.notYetSampled.match_1 — SAP/P012b/Defs/Part1.lean:0
- SAP.P012b.oneLeafData — SAP/P012b/Defs/WholeW1.lean:57
- SAP.P012b.oneLeafState — SAP/P012b/Defs/WholeW1.lean:62
- SAP.P012b.pSum — SAP/P012b/Defs/Part1.lean:104
- SAP.P012b.pValue — SAP/P012b/Defs/Part1.lean:110
- SAP.P012b.pValues — SAP/P012b/Defs/Part1.lean:128
- SAP.P012b.preferential — SAP/P012b/Defs/Part1.lean:116
- SAP.P012b.recruitmentDegree — SAP/P012b/Defs/Part1.lean:42
- SAP.P012b.recruitmentEdges — SAP/P012b/Defs/Part1.lean:36
- SAP.P012b.recruitmentState — SAP/P012b/Defs/Part1.lean:122
- SAP.P012b.s — SAP/P012b/Defs/Part1.lean:15
- SAP.P012b.sameSusceptible — SAP/P012b/Defs/Part1.lean:101
- SAP.P012b.sampledTraitDegree — SAP/P012b/Defs/Part1.lean:47
- SAP.P012b.sampledVertices — SAP/P012b/Defs/Part1.lean:34
- SAP.P012b.spare — SAP/P012b/Defs/Part1.lean:45
- SAP.P012b.susceptible — SAP/P012b/Defs/Part1.lean:98
- SAP.P012b.u — SAP/P012b/Defs/Part1.lean:17
- SAP.P012b.unsampled — SAP/P012b/Defs/Part1.lean:162
- SAP.P012b.wholeEdgeCount — SAP/P012b/Defs/WholeW1.lean:66
- SAP.P012b.wholeMixedCount — SAP/P012b/Defs/WholeW1.lean:69
- SAP.P012b.wholePhi — SAP/P012b/Defs/WholeW1.lean:72
- SAP.P012b.wholePhi._proof_1 — SAP/P012b/Defs/WholeW1.lean:0
- SAP.P012b.z — SAP/P012b/Defs/Part1.lean:73

### SAP.P012b.T23 dependencies

- SAP.P012b.Admissible — SAP/P012b/Defs/Part1.lean:50
- SAP.P012b.Augmented — SAP/P012b/Defs/Part1.lean:59
- SAP.P012b.Compatible — SAP/P012b/Defs/Part1.lean:62
- SAP.P012b.Data — SAP/P012b/Defs/Part1.lean:19
- SAP.P012b.Data.degree — SAP/P012b/Defs/Part1.lean:24
- SAP.P012b.Data.mk — SAP/P012b/Defs/Part1.lean:19
- SAP.P012b.Data.parent — SAP/P012b/Defs/Part1.lean:22
- SAP.P012b.Data.sampled — SAP/P012b/Defs/Part1.lean:20
- SAP.P012b.Data.seeds — SAP/P012b/Defs/Part1.lean:21
- SAP.P012b.Data.time — SAP/P012b/Defs/Part1.lean:23
- SAP.P012b.Data.trait — SAP/P012b/Defs/Part1.lean:25
- SAP.P012b.FullHomophilyRegion — SAP/P012b/Defs/Part1.lean:130
- SAP.P012b.FullPreferentialRegion — SAP/P012b/Defs/Part1.lean:134
- SAP.P012b.HomophilyDefined — SAP/P012b/Defs/Part1.lean:88
- SAP.P012b.PreferentialDefined — SAP/P012b/Defs/Part1.lean:112
- SAP.P012b.Simple — SAP/P012b/Defs/Part1.lean:56
- SAP.P012b.State — SAP/P012b/Defs/Part1.lean:27
- SAP.P012b.State.edges — SAP/P012b/Defs/Part1.lean:29
- SAP.P012b.State.mk — SAP/P012b/Defs/Part1.lean:27
- SAP.P012b.State.trait — SAP/P012b/Defs/Part1.lean:30
- SAP.P012b.State.vertices — SAP/P012b/Defs/Part1.lean:28
- SAP.P012b.T23WholeStatement — SAP/P012b/Defs/WholeW2.lean:94
- SAP.P012b.Vertex — SAP/P012b/Defs/Part1.lean:13
- SAP.P012b.WholeFigure1Arithmetic — SAP/P012b/Defs/WholeW2.lean:77
- SAP.P012b.WholeFigure1Arithmetic._proof_1 — SAP/P012b/Defs/WholeW2.lean:0
- SAP.P012b.WholeFigure1Arithmetic._proof_2 — SAP/P012b/Defs/WholeW2.lean:0
- SAP.P012b.WholeFigure1Arithmetic._proof_3 — SAP/P012b/Defs/WholeW2.lean:0
- SAP.P012b.WholeFigure1Assertions — SAP/P012b/Defs/WholeW2.lean:62
- SAP.P012b.WholeFigure1Assertions._proof_1 — SAP/P012b/Defs/WholeW2.lean:0
- SAP.P012b.WholeFigure1Assertions._proof_2 — SAP/P012b/Defs/WholeW2.lean:0
- SAP.P012b.WholeFigure1Assertions._proof_3 — SAP/P012b/Defs/WholeW2.lean:0
- SAP.P012b.WholeFigure1Assertions._proof_4 — SAP/P012b/Defs/WholeW2.lean:0
- SAP.P012b.WholeFigure1Assertions._proof_5 — SAP/P012b/Defs/WholeW2.lean:0
- SAP.P012b.WholeFigure1Assertions._proof_6 — SAP/P012b/Defs/WholeW2.lean:0
- SAP.P012b.WholeFigure1Assertions._proof_7 — SAP/P012b/Defs/WholeW2.lean:0
- SAP.P012b.WholeFigure1Assertions._proof_8 — SAP/P012b/Defs/WholeW2.lean:0
- SAP.P012b.adjacency — SAP/P012b/Defs/Part1.lean:70
- SAP.P012b.figureData — SAP/P012b/Defs/Part2.lean:92
- SAP.P012b.graphDegree — SAP/P012b/Defs/Part1.lean:39
- SAP.P012b.hDenominator — SAP/P012b/Defs/Part1.lean:80
- SAP.P012b.hNumerator — SAP/P012b/Defs/Part1.lean:75
- SAP.P012b.hNumerator._proof_1 — SAP/P012b/Defs/Part1.lean:0
- SAP.P012b.hValue — SAP/P012b/Defs/Part1.lean:86
- SAP.P012b.hValues — SAP/P012b/Defs/Part1.lean:126
- SAP.P012b.homophily — SAP/P012b/Defs/Part1.lean:90
- SAP.P012b.leafCompletion — SAP/P012b/Defs/Part1.lean:146
- SAP.P012b.leafCompletion.match_1 — SAP/P012b/Defs/Part1.lean:0
- SAP.P012b.leafEdges — SAP/P012b/Defs/Part1.lean:143
- SAP.P012b.leafVertices — SAP/P012b/Defs/Part1.lean:140
- SAP.P012b.nonseeds — SAP/P012b/Defs/Part1.lean:32
- SAP.P012b.notYetSampled — SAP/P012b/Defs/Part1.lean:93
- SAP.P012b.notYetSampled.match_1 — SAP/P012b/Defs/Part1.lean:0
- SAP.P012b.pSum — SAP/P012b/Defs/Part1.lean:104
- SAP.P012b.pValue — SAP/P012b/Defs/Part1.lean:110
- SAP.P012b.pValues — SAP/P012b/Defs/Part1.lean:128
- SAP.P012b.preferential — SAP/P012b/Defs/Part1.lean:116
- SAP.P012b.recruitmentDegree — SAP/P012b/Defs/Part1.lean:42
- SAP.P012b.recruitmentEdges — SAP/P012b/Defs/Part1.lean:36
- SAP.P012b.recruitmentState — SAP/P012b/Defs/Part1.lean:122
- SAP.P012b.s — SAP/P012b/Defs/Part1.lean:15
- SAP.P012b.sameSusceptible — SAP/P012b/Defs/Part1.lean:101
- SAP.P012b.sampledTraitDegree — SAP/P012b/Defs/Part1.lean:47
- SAP.P012b.sampledVertices — SAP/P012b/Defs/Part1.lean:34
- SAP.P012b.spare — SAP/P012b/Defs/Part1.lean:45
- SAP.P012b.susceptible — SAP/P012b/Defs/Part1.lean:98
- SAP.P012b.u — SAP/P012b/Defs/Part1.lean:17
- SAP.P012b.wholeComplementData — SAP/P012b/Defs/WholeW2.lean:13
- SAP.P012b.wholeComplementState — SAP/P012b/Defs/WholeW2.lean:17
- SAP.P012b.wholeEdgeCount_W2 — SAP/P012b/Defs/WholeW2.lean:46
- SAP.P012b.wholeFigureData — SAP/P012b/Defs/WholeW2.lean:29
- SAP.P012b.wholeMixedCount_W2 — SAP/P012b/Defs/WholeW2.lean:50
- SAP.P012b.wholePContribution — SAP/P012b/Defs/WholeW2.lean:40
- SAP.P012b.wholePhi_W2 — SAP/P012b/Defs/WholeW2.lean:59
- SAP.P012b.wholePhi_W2._proof_1 — SAP/P012b/Defs/WholeW2.lean:0
- SAP.P012b.wholeRelabeling — SAP/P012b/Defs/WholeW2.lean:21
- SAP.P012b.wholeTraitSpare — SAP/P012b/Defs/WholeW2.lean:55
- SAP.P012b.z — SAP/P012b/Defs/Part1.lean:73
