# Blind reading of the Lean statements

Saved before opening `claims.json` or `record.json`. Sources read: all five
`SAP/P012b/Defs/Part*.lean` files, both aggregate imports, and
`SAP/P012b/Challenge/Part1.lean`. This is a reading of the statements, not of
their proofs. Challenge declarations are stubs.

## Common objects and fully expanded conventions

* The ambient vertex set is the disjoint union `N + (N x N)`. Write `s_i`
  for a vertex in the first summand and `u_(i,k)` for one in the second.
  These labels never coincide. A vertex `s_i` whose index is not sampled
  can also be an unsampled vertex; the second summand is not the definition
  of being unsampled.
* A datum D consists of finite sets S of sampled indices and M of seed
  indices, total functions parent, time, degree from N to N, and a total
  Boolean trait function x on N. Put R = S minus M, V_S = {s_i : i in S},
  E_R = {{s_parent(j),s_j} : j in R}, r_i = the number of members of E_R
  containing s_i, and d_i = degree(i). Images and edge sets discard
  duplicates. `children D i` is {j in R : parent(j)=i}.
* `Admissible D` means, in order: M is a subset of S; time is injective on
  S; every j in R has parent(j) in S with time(parent(j)) < time(j);
  and r_i <= d_i for every i in S. It imposes no conditions on these
  total functions outside S except through the displayed expressions.
* A state H consists of a finite vertex set V, a finite set E of finite
  vertex sets, and a total Boolean trait function z_bool on the ambient
  vertex set. Write k_v = #{e in E : v in e} and m = #E. `Simple H`
  means every e in E has exactly two elements and is contained in V.
  This encodes finite undirected graphs with neither loops nor repeated
  edges. `Augmented D H` adds that every edge contains some s_i with i in S.
* `GraphCompatible D H` means H is augmented, V_S is contained in V,
  E_R is contained in E, every v in V minus V_S has a sampled neighbor,
  and k_(s_i) = d_i for all i in S. `Compatible` additionally requires
  z_bool(s_i)=x_i for every i in S. Isolated sampled vertices are allowed;
  isolated unsampled vertices and edges with two unsampled endpoints are
  disallowed. These predicates do not themselves include Admissible.
* Put A_vw = 1 if v != w and {v,w} is in E, and 0 otherwise, and z_v = 1
  for a true trait and 0 for a false trait. All the following sums are
  finite sums. The raw homophily numerator and denominator are

      N_h(H) = sum_(v,w in V) (A_vw - k_v k_w/(2m)) z_v z_w,
      B_h(H) = sum_(v,w in V) ([v=w] k_v - k_v k_w/(2m)) z_v z_w.

  The raw `hValue` is N_h/B_h. `HomophilyDefined` is m>0 and B_h != 0.
  `homophily` returns `some(hValue)` exactly in this domain, and `none`
  otherwise. In particular `none` is not the number zero.
* A neighbor v is not yet sampled at recruitment event j when v=s_k and
  either k is outside S or time(j)<=time(k), or whenever v is in the
  second summand. Define C_(i,j)(H) to be the neighbors of s_i in V that
  meet this condition, and C^=_(i,j)(H) its subset with trait equal to
  the trait of s_i. The recruited vertex at time(j) is included rather
  than excluded. Write c_(i,j)=#C_(i,j) and a_(i,j)=#C^=_(i,j). Then

      P_sum(D,H) = sum_(j in R)
        ([z_bool(s_j)=z_bool(s_parent(j))] - a_(parent(j),j)/c_(parent(j),j)),
      p(D,H) = P_sum(D,H)/#R.

  `PreferentialDefined D H` means #R>0 and c_(parent(j),j)>0 for every
  j in R. `preferential` returns `some(p)` on this domain and `none`
  otherwise. Neither raw hValue nor raw pValue is itself partial.
* Q_b(D) = sum_(i in S, x_i=b) d_i is `sampledTraitDegree D b`.
  K_b(H) = sum_(v in V, z_bool(v)=b) k_v is `traitDegree H b`.
  `degreeTraitSum H` is sum_(v in V) k_v z_v, as a real number.
* `hValues D` is {r in R : there exists H with Compatible D H and
  homophily H=some r}; `pValues` is analogous. `PointIdentified A`
  means there exists a real r such that A={r}, so an empty set is not
  point identified.
* `FullHomophilyRegion D L U` means every compatible H has homophily
  defined, L belongs to hValues and is <= every member, and U belongs
  to hValues and is >= every member. Thus both extrema are attained.
  `FullPreferentialRegion` has the corresponding three requirements.
  Neither predicate asserts that all intermediate real values occur.
* `spare D i` is natural subtraction d_i-r_i, truncated at zero.
  On sampled indices of admissible data it is ordinary nonnegative
  subtraction. `leafCompletion D same` has V_S and the vertices u_(i,k)
  for i in S and 0<=k<d_i-r_i, with E_R and all edges {s_i,u_(i,k)}.
  Its sampled traits are x_i. Its second-summand traits equal x_i when
  same=true and its Boolean negation when same=false (also for labels
  not in the vertex set).
* `recruitmentState D` has V_S, E_R, sampled traits x_i, and false traits
  on the second summand. `induced D H` has V_S, all edges of H contained
  in V_S, and H's total trait function. `InducedCompatible D J` means
  J is simple, its vertices equal V_S, E_R is contained in its edges,
  and its degree at every s_i for i in S is <= d_i. This last predicate
  has no trait-matching requirement.
* `flipTrait H v` preserves vertices and edges and negates H's trait
  at v only. `unsampled D H` is V minus V_S.

Mathlib foundations checked: `IsLeast`/`IsGreatest` are membership plus
lower/upper bound, not merely an infimum/supremum
(`Mathlib/Order/Bounds/Defs.lean`). `Monotone` means nondecreasing,
`Antitone` nonincreasing, and `StrictAntiOn f A` means f(b)<f(a) whenever
a,b are in A and a<b (`Order/Monotone/Defs.lean`). `Filter.Tendsto` is the
ordinary filter limit; atTop on N is eventual large natural indices and
atTop on R is divergence to positive infinity (`Order/Filter/Defs.lean`,
`Order/Filter/AtTopBot/Defs.lean`). Real division is total and x/0=0
(`Algebra/GroupWithZero/Basic.lean:402`). Real.log is the ordinary log on
positive arguments, with log(0)=0 and log(x)=log(abs x) for x<0
(`Analysis/SpecialFunctions/Log/Basic.lean`). Real real-exponent power on
positive bases is exp(exponent*log(base)) (`Analysis/SpecialFunctions/Pow/Real.lean`).
Function.update changes exactly one argument (`Logic/Function/Basic.lean`).
Finset set difference, image, union, biUnion, filter, cardinality and sum
have their usual finite-set meanings; range(n)={0,...,n-1}; an empty sum
is zero. All casts of cardinals and degrees in real formulas are ordinary
natural-to-real casts. There are no integrals, limsups or implicit finite
index types in these statements.

## SAP.P012b.T13

The statement is the conjunction of the following two independently
universally quantified assertions. Put n=#R and sigma_i=-1 if x_i=true,
and +1 if x_i=false.

1. For every datum D, proof of Admissible D, indices i,j in N, proof
   i in S, proof j in R, proof parent(j)=i, and proof r_i<d_i, there
   exist states H,K and a vertex v in unsampled D H such that all the
   following hold simultaneously:
   * H and K are compatible with D; v=u_(i,0); H's vertex and edge
     sets equal those of leafCompletion D true. H's other traits are
     not required to equal that completion's traits.
   * For every k in S, {s_k,v} is an edge of H iff k=i; H's trait at
     v is true; K=flipTrait H v.
   * For every ell in R, C_(parent(ell),ell)(H)=C_(parent(ell),ell)(K).
     For every ell in R, v belongs to this H-susceptible set iff
     parent(ell)=i.
   * p(D,H)-p(D,K) = (sigma_i/n) *
     sum_(ell in children(D,i)) 1/c_(i,ell)(H).
     These two raw p values differ, and pValues D is not a singleton.
   * If x_i=true, their difference is <= -1/(n*c_(i,j)(H)), this
     upper bound is strictly negative, and equality with this bound
     holds iff children(D,i)={j}.
2. For every D, proof of Admissible D, H, proof Compatible D H,
   indices i,j, proof i in S, proof j in R, proof parent(j)=i,
   vertex v, proof v in unsampled D H, proof that for every k in S
   {s_k,v} is an edge iff k=i, and proof H's trait at v is true,
   set K=flipTrait H v. Then K is compatible; all susceptible sets
   in the first assertion are unchanged and v belongs exactly at
   events whose parent is i; the same signed full-sum identity and
   inequality of raw p values hold; and, conditional on x_i=true,
   the same strictly negative bound and sole-child equality criterion
   hold. This second assertion does not explicitly repeat the
   non-point-identification conclusion or require a spare-degree
   hypothesis; it assumes an existing private unsampled neighbor.

## SAP.P012b.T14

This is a conjunction of four concrete assertions, with no outside
hypotheses. In each datum, the displayed functions are total, with the
values specified below determining the finite computations.

* A: S={1,2}, M={1}, parent is constantly 1, time(i)=i-1 in natural
  subtraction, degree is constantly 1, and all sampled traits are false.
  The dyad has vertices {s_1,s_2}, one edge, and both traits false.
  A is admissible, the dyad is compatible, its raw h numerator and
  denominator both equal 0, homophily is none, and preferential is some 0.
* B: A with M={1,2} and trait(i) the Boolean test i=2. Its dyad has
  traits false,true. B is admissible and this dyad compatible;
  homophily is some(-1); #R=0; P_sum is 0; and for every state H
  (without a compatibility hypothesis), preferential B H is none.
* C: S=M={1}, parent constantly 1, time identity, degree constantly 0,
  traits constantly false. Its state has the single vertex s_1, no
  edges, and all traits false. C is admissible, the state compatible,
  its edge cardinal is 0, and both partial values are none.
* D: S={1,2}, M={1}, parent constantly 1, time(i)=i-1, degree(1)=1
  and degree(i)=4 otherwise, and all traits true. For every triple
  t3,t4,t5 of Booleans, use vertices {s_1,s_2,u_(3,0),u_(4,0),u_(5,0)}
  and edges {s_1,s_2} and {s_2,u_(q,0)} for q=3,4,5. The three
  unsampled traits are the respective parameters; other traits are
  true. D is admissible, and all eight states are compatible.
  The all-true state's raw h numerator and denominator are 0 and its
  homophily is none. Homophily for triples (false,false,false),
  (true,false,false), (true,true,false) is respectively some(-3/5),
  some(-1/3), some(-1/7). For every triple preferential is some 0.

## SAP.P012b.T15

Conjunction of a graph assertion and an assertion about every admissible D.

1. For every H, proof Simple H and proof m>0, the following all hold:
   degreeTraitSum(H)=K_true; K_true+K_false=2m;
   B_h=K_true-K_true^2/(2m)=K_true*K_false/(2m)
   =K_true*(2m-K_true)/(2m);
   B_h>0 iff K_false>0 and K_true>0;
   HomophilyDefined H iff K_false>0 and K_true>0;
   and if K_true=0 or K_true=2m then N_h=B_h=0.
2. For every D and proof Admissible D:
   * For every H, if Compatible D H, then PreferentialDefined D H
     iff #M<#S, and for every j in R the vertex s_j belongs to
     C_(parent(j),j)(H), whose cardinality is positive.
   * (Every compatible H has homophily defined) iff Q_false(D)>0
     and Q_true(D)>0.
   * (Every compatible H has preferential defined) iff #M<#S.
   * If there exist i,j in S with r_i<d_i, r_j<d_j, and x_i != x_j,
     then Q_false(D)>0 and Q_true(D)>0.
   * If there exists j in R with r_parent(j)<d_parent(j), then #M<#S.
   * If Q_false(D)>0 and Q_true(D)>0, then for all real L,U,
     FullHomophilyRegion D L U iff L is the least and U the greatest
     member of hValues D.
   * If #M<#S, then for all real L,U the analogous equivalence holds
     for FullPreferentialRegion and pValues.
   * If the conjunction Q_false(D)>0 and Q_true(D)>0 fails, there
     do not exist real L,U satisfying FullHomophilyRegion D L U.

No existence of extrema is asserted in either of the two equivalences.

## SAP.P012b.T16

Conjunction of five assertions:

1. For every sequence T:N->R, proof that T(n)>0 for every n and proof
   T is nondecreasing, T does not tend to 0 as n tends to infinity.
2. For every real epsilon, there is no real T with
   T*(epsilon*log(1))=1. This uses a multiplication equation rather
   than assigning an ordinary reciprocal to zero.
3. For every real epsilon,T1, proof epsilon>0 and proof
   1/(epsilon*log(2))<=T1, define C(0)=T1 and
   C(n)=1/(epsilon*log(n+1)) for n>0. Then C(n)>0 for every n,
   C is nonincreasing on N, C(b)<C(a) whenever 1<=a<b, and C tends
   to 0 as n tends to infinity.
4. For every real epsilon,D,t, proof epsilon>0, proof t>=2, proof
   0<=D*epsilon and proof D*epsilon<=1,

       exp(-D/(1/(epsilon*log(t))))
        = exp(-D*epsilon*log(t)) = 1/t^(D*epsilon)

   and 1/t is at most this expression. Powers here have real exponents.
5. For every real epsilon,D, proof epsilon>0, proof 0<=D*epsilon<=1
   (two proofs), and every real first, the sequence

       first + sum_(n=0,...,N-1)
         exp(-D/(1/(epsilon*log(n+2))))

   tends to positive infinity as N tends to infinity.

There is no assertion here about convergence of an optimization algorithm,
a Markov chain, its transition probabilities, its depth, or an optimizer.

## SAP.P012b.T17

For every datum D, state H, proof Admissible D and proof
GraphCompatible D H, the sampled induced graph induced D H is
InducedCompatible with D, and

    (for every i in S its induced degree equals d_i)
      iff H.vertices=V_S.

The first conclusion is simplicity, vertex set V_S, inclusion of E_R,
and induced sampled degrees <= d_i. No trait requirement is present in
either GraphCompatible or InducedCompatible.

## SAP.P012b.T18

For every D1,D2,H,K, proofs Admissible D1 and Admissible D2,
proof Compatible D1 H, proof Compatible D2 K, proof H.vertices=K.vertices,
proof H.edges=K.edges, and proof that for every v in H.vertices the
two total trait functions agree at v, homophily H=homophily K as
Option R values. Thus both none and equal some-values count as equality.
No equality of histories, times, seed sets, or partial preferential
values is required or concluded.

## SAP.P012b.T19

Negation of the following universal assertion: for every D,H,K,
proof Admissible D, proof Compatible D H, and proof Proposal D false H K,
Compatible D K. Classically, it asserts there exist admissible D and
states H,K such that H is compatible, a literal proposal from H can
produce K, and K is incompatible.

Here is the complete proposal relation being negated. `removeEdge`
erases {v,w}; `addEdge` inserts {v,w}; neither changes vertices or traits.
`addVertex` inserts v and sets its trait to an arbitrary specified Boolean.
The replacement pool for sampled i is the unsampled vertices of the
original current state not adjacent to s_i. A replacement of a pending
state is either an existing member of that pool with no change to the
pending state, or any vertex absent from the pending state's vertices,
inserted with either Boolean trait. Pool membership uses the original
current state even after other edits. `cleanup D false` keeps precisely
the vertices of nonzero degree, changing neither edges nor traits.
For comparison, cleanup with true also preserves all sampled vertices.

`Proposal D false H K` is either one of these graph branches or a trait
branch:

* Choose i in S and j in H.vertices, s_i!=j, an edge {s_i,j} that is
  not in E_R, with j unsampled. Remove this edge, choose a replacement
  v for i with pending state P, add both {s_i,v} and {j,v}, and clean up.
  The extra {j,v} is present specifically in the false branch.
* Choose distinct i,j in S with non-recruitment edge {s_i,s_j}.
  Remove it; choose replacement v for i, add {s_i,v}; choose replacement
  w for j in this new pending state, add {s_j,w}; then clean up.
  Both existing replacement pools are evaluated at H.
* Choose i in S and j in H.vertices, s_i!=j, and {s_i,j} absent.
  Choose unsampled v,w in H with edges {s_i,v} and {j,w}. Remove those
  two edges, add {s_i,j}, and clean up. v=w is not excluded.
* Choose i in S, j in H.vertices distinct from s_i, such that no
  deletable non-recruitment edge {s_i,j} exists and it is not the case
  that {s_i,j} is absent with such a pair of unsampled neighbors.
  Return cleanup D false H.
* Choose any unsampled v in H and return flipTrait H v. The trait
  relation also has an unchanged-state constructor requiring
  repaired=true and no unsampled vertices, which cannot apply here.

These are relations of possible outcomes, not probability distributions.

## SAP.P012b.T20

For all data Dsex,Dcrack,Dhome, `printed_table_intervals` fails.
Expanded, no such three data can simultaneously satisfy all of:

* Each datum is admissible, #S=527, #M=6, and sum_(i in S) d_i=4487.
* All three sampled sets coincide; all three seed sets coincide;
  parents agree for each nonseed of Dsex; and degrees and times agree
  for each sampled index of Dsex. Their traits need not agree.
* There exist real Ls,Us,Lc,Uc,Lh,Uh, in that quantifier order, with
  FullHomophilyRegion(Dsex,Ls,Us), FullHomophilyRegion(Dcrack,Lc,Uc),
  FullHomophilyRegion(Dhome,Lh,Uh), and the six absolute differences
  from the respective targets are all <=1/20000:

      Ls: -7027/10000, Us: 8292/10000,
      Lc: -6918/10000, Uc: 8231/10000,
      Lh: -7179/10000, Uh: 8242/10000.

The statement concerns attained extrema for all compatible states and
has no preferential intervals, observed individual records, or fitted
point estimates as inputs. The labels sex/crack/home are variable names.

## SAP.P012b.T22

Conjunction of three blocks:

1. For every D, proof Admissible D, proof Q_false(D)>0,
   proof Q_true(D)>0, and proof #M<#S, all four assertions hold:
   * hValues and pValues are both singletons iff, for every i in S,
     d_i=r_i.
   * (For every i in S, d_i=r_i) iff, for every compatible H,
     H.vertices=V_S and H.edges=E_R.
   * If some i in S has r_i<d_i, hValues is not a singleton.
   * If all sampled degrees equal r_i, then every compatible H has
     the same vertices and edges as recruitmentState D and, for every
     v in H.vertices, the same trait as recruitmentState D.
2. For every D, proof Admissible D, proof Q_false(D)>0,
   proof Q_true(D)>0, index i, proof i in S and proof r_i<d_i,
   leafCompletion D true is compatible, its trait flip at u_(i,0)
   is compatible, and their raw hValues differ. This block has no
   hypothesis #M<#S and no newly existentially selected leaf or state.
3. For every D, proof Admissible D, proof Q_false(D)>0,
   proof Q_true(D)>0 and proof #M<#S, pValues is a singleton iff,
   for every i in S, nonemptiness of children(D,i) implies d_i=r_i.

All graph uniqueness here is equality of vertex and edge sets and, in
the last clause of block 1, of traits on actual vertices. Equality of
the total trait functions outside the graph is not asserted.

## SAP.P012b.T23

An unconditional conjunction about the fixed datum figureData:
S={1,2,3,4,5}, M={1}, time(i)=i, parent(3)=parent(5)=2 and
parent(j)=1 for all other j; degree(1)=5, degree(2)=4, degree(5)=2,
degree(i)=3 otherwise; trait false exactly at index 4 and true elsewhere.

It is admissible; FullHomophilyRegion has L=-5/8,U=79/105;
FullPreferentialRegion has L=-11/80,U=49/120; and, for every compatible H,
homophily H=some(hValue H), preferential figureData H=some(pValue figureData H),
the raw h value lies in the real closed interval [-5/8,79/105], and the
raw p value lies in [-11/80,49/120]. The two full-region assertions
each entail existence of compatible states attaining both marginal
extrema. They need not be the same states across the two parameters.
There is no nonuniqueness assertion about extremizers, joint feasible
region characterization, or claim that all points of the rectangle occur.
