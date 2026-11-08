# Blind reading

Saved before opening `claims.json`, `record.json`, `earlier.json`, or
`architect-report.md`. This reading uses the current Challenge declarations, all
the declarations listed in `closure.json`, and Mathlib definitions. It does not
infer a claim from an audit label.

Common notation: `[n]` means `Fin n`, the natural numbers less than n; an
assignment is a function `[n] → Bool`. All sums indexed by a finite type range
over its entire `Finset.univ`. For any finite type Ω and scalar-valued functions
p,X, write E_p X = Σω p(ω)X(ω). This is the definition `expect`, a finite weighted
sum, with no normalization or nonnegativity built into it. `prob p A` is
Σω p(ω)1_A(ω). Wherever p is called a probability law below, its normalization
must follow from the particular construction, rather than these two definitions.

## SAP.P045b.T27

Source: `Challenge/Part2.lean:16–19`; statement: `Defs/Part5.lean:27–29`.

The theorem asserts the negation of the following universal equivalence:
for every natural n, every simple undirected network A on `[n]`, every Boolean
assignment z, and every i in `[n]`,

    #{j in N[i] : z(j) = true} < #N[i]
       iff
    for every j in N[i], z(j) = false.

Equivalently, there exist n,A,z,i for which the equivalence fails. These are all
the quantifiers and there are no additional premises. A `Network n` is a Boolean
adjacency function A:[n]×[n]→Bool with A(i,j)=A(j,i) and A(i,i)=false. `Network.mk`
constructs such a function with these two proofs; `Network.adj` projects it.
`neighborhood A i` is the closed neighborhood {i} union the set of j with
A(i,j)=true. `neighborhoodCount` counts treated vertices in that closed
neighborhood. `badAllControl` is exactly the strict inequality above: it means
there is at least one control in the closed neighborhood, rather than that all
vertices are controls. The docstring describes a disagreement between a
documented full-neighborhood control indicator and the coded indicator, and
calls it a refutation of the documented equivalence for the implementation.

Junk/edge conventions: counts are natural numbers but there is no subtraction or
cast in this statement. Finite sets remove duplicate insertion of i. Even without
looplessness this would not duplicate i. A vertex i implies n>0, and N[i]
contains i. For n=0 the inner universal statement is empty, which cannot itself
witness the negated universal. No division, infinite sum, integral, partial
function, or other analytic junk value occurs. A mixed closed neighborhood of
size two is a direct mathematical witness of inequivalence.

Closure read: `Assignment`, `Network`, `Network.adj`, `Network.mk`,
`T27Statement`, `badAllControl`, `neighborhood`, `neighborhoodCount`.

## SAP.P045b.T29

Source: `Challenge/Part2.lean:21–24`; statement: `Defs/Part5.lean:31–36`.

For a finite vertex set `[n]`, let G be any Mathlib simple graph (an undirected,
irreflexive adjacency relation) and d=G.edist. Its values are in the extended
natural numbers `ℕ∞`, with the ordinary graph distance on connected vertices and
∞ between disconnected vertices. More explicitly, d(u,v) is the infimum of the
lengths of all G-walks from u to v. Let p be real.

Here are the complete sampler definitions, with general radius ε where the
code accepts it:

* `separated d ε S`: for every distinct s,t in S, ε≤d(s,t).
* `covers d ε S`: for every v outside S, there exists s in S with
  d(s,v)≤ε−1, with subtraction performed in the naturals.
* `epsilonNet`: the conjunction of those two properties.
* `marked d ε S`: all v for which some s in S satisfies d(s,v)≤ε−1.
* `centreDraw d ε coded S v`: put R=[n] minus marked(S). If coded=true
  and #R=1, let u be the first member of R in its finite-set list (falling back
  to v if that list is empty); the mass of v is 1/(u.val+1) when
  v.val≤u.val and zero otherwise. In every other case the mass is 1/#R on
  R and zero off R. In the singleton case this is uniform on labels 0,…,u.val,
  rather than uniform on the singleton {u}.
* For a list c=(c₀,…,cₜ₋₁), `traceMass` is zero unless every strict prefix
  leaves at least one vertex unmarked and the whole list marks every vertex.
  When these conditions hold its mass is the product, over j<t, of
  centreDraw(prefix centers,cⱼ). Centers are obtained from lists by `toFinset`,
  so repeated draws remain in the trace but not multiply in the center set.
* `terminalCentres d ε coded S` is Σ′_{t∈ℕ} Σ_{z:[t]→[n]}
  1_{set(List.ofFn z)=S} traceMass(List.ofFn z). Thus all finite stopped retry
  traces with exactly S as their set of centers are included.
* `nearestCentre d S v` sorts S first by increasing distance to v, with
  increasing vertex label as the tie breaker, and returns the optional first
  member of the sorted list. It is `none` if S is empty.
* `bernoulli p c` for c:[n]→Bool is ∏i (p if c(i)=true, otherwise 1−p).
* `clusterProb d S p z` sums this Bernoulli mass over c such that, for every
  v, some s satisfies nearestCentre(S,v)=some s and z(v)=c(s). It is the
  induced assignment mass when each center gets an independent Bernoulli p
  bit and every vertex takes its nearest center's bit; unused bits are summed
  out. There is no fallback center when S is empty.
* `clusteredTreatment d coded p z` is Σ_S terminalCentres(d,3,coded,S)
  clusterProb(d,S,p,z).

The theorem is the negation of the following statement, in this exact order:
for every n, if 0<n, for every simple graph G on `[n]` and real p, if
0≤p and p≤1, all three of the following hold for the coded sampler:

1. Σ_S terminalCentres(d,3,true,S)=1.
2. Σ_S terminalCentres(d,3,true,S)1_{epsilonNet(d,3,S)}=1.
3. For every assignment z, clusteredTreatment(d,true,p,z) equals its defining
   sum over terminal center sets and their cluster assignment masses.

The third assertion is definitionally an equality. The theorem can therefore
be witnessed by a failure of either of the first two clauses; it does not
formally isolate a failure of clause 2. The docstring says the implementation
need not return a three-net, includes the singleton-number behavior and retry
traces, and expressly excludes the intended sampler that draws among unmarked
vertices.

Junk/edge conventions:

* Natural ε−1 truncates at zero for ε=0. The theorem calls all relevant
  definitions with ε=3, so the actual radius is the ordinary number 2.
* `edist` uses an infimum in a complete lattice: with no walk the infimum of
  the empty set is ∞. This correctly represents disconnection. Finite radii
  never mark a disconnected component from another component.
* The real `tsum` in `terminalCentres` is zero by convention for a nonsummable
  series. One must establish summability to read it as a probability. For the
  finite graph/ε=3 situation, every nonterminal draw has a positive chance to
  mark a new vertex: uniform unmarked draws do so surely, and a singleton
  branch hits the unmarked u with probability 1/(u.val+1)≥1/n. Marked sets
  increase and contain each center. There are at most n strict increases.
  This bounds retry tails geometrically and gives termination and summability;
  no divergence is needed for the natural separation counterexample.
* When R is empty the ordinary uniform expression has denominator zero,
  but no v is in R, and all draw masses are zero. The trace stopping guards
  disallow taking a draw from such a state. When #R=1 the `head?.getD v`
  fallback is unreachable; its list has its unique element. The denominator
  u.val+1 is positive, and casts from ℕ into ℝ preserve its value.
* Empty S yields nearestCentre=none. For n>0, clusterProb then has no
  satisfying assignment of center bits. An empty trace is permitted only
  if the empty center set marks every vertex, which does not occur for n>0.
* Real division is total with inverse zero equal to zero. Parameter p lies
  in [0,1], so the Bernoulli products are probability masses, including at
  the endpoints. No integrals, roots, logs, or limiting sequence notions
  occur beyond the retry `tsum` just discussed.

Closure read: `Assignment`, `T29Statement`, `bernoulli`, `centreDraw`,
`clusterProb`, `clusteredTreatment`, `covers`, `epsilonNet`, `expect`,
`marked`, `nearestCentre`, `prob`, `separated`, `terminalCentres`, `traceMass`.

## SAP.P045b.T30

Source: `Challenge/Part2.lean:26–28`; statement: `Defs/Part5.lean:38–44`.

Quantifiers, in order: for every natural n with 0<n; every type Δ with a finite
enumeration and decidable equality; every design p on assignments `[n]→Bool`;
every mapping D:(assignments)→[n]→Δ; every potential outcome table
y:[n]→Δ→ℝ; and every k∈Δ such that all its marginal exposure probabilities
are strictly positive, the following conjunction holds. Its second part
universally quantifies l∈Δ and assumes all marginal probabilities for l
are strictly positive.

A `Design Ω` is a real mass function on a finite Ω with proofs p(ω)≥0 for
every ω and Σω p(ω)=1. `Design.mk` takes the function and these two proofs;
`Design.mass` projects the function. Here Ω is the full Boolean assignment
space, so designs with a smaller support are represented by zero masses.
Write πᵢ(d)=Σ_z p(z)1_{D(z,i)=d}; this is `exposureProb` after unfolding
`prob` and `expect`. The observed outcome is `observed D y z i`=y(i,D(z,i)).

The HT total for d is H_d(z)=Σ_i 1_{D(z,i)=d} y(i,D(z,i))/πᵢ(d),
where the conditional summand is zero off the exposure cell. The HT contrast
is (H_k(z)−H_l(z))/n. The target `effect y k l` is
(Σ_i y(i,k))/n − (Σ_i y(i,l))/n. These are `htTotal`, `htContrast`, and
`effect` with `mean` unfolded.

The conclusions are E_p H_k=Σ_i y(i,k), and, for every l with all πᵢ(l)>0,
E_p[(H_k−H_l)/n] = (Σ_i y(i,k))/n−(Σ_i y(i,l))/n. Correct specification of
the mapping is built into taking the observed outcome to be exactly
y(i,D(z,i)); no additional arbitrary observed outcome variable is present.
The statement does not require k≠l. It allows k=l, where the contrast is zero.
It proves no property of outcomes outside their assigned exposure, of an
estimated probability, or of an infinite assignment space.

Junk/edge conventions: all uses of division by πᵢ(k), and of πᵢ(l) in the
second clause, have positive denominators under the corresponding premises.
Both population means and the contrast divide by the cast of positive n.
The general `mean` definition assigns zero to an empty population through
0/0=0, but n>0 excludes that here. An empty Δ admits no k and hence no
instantiation; there are nonempty instances. All expectations are finite
sums of finite real numbers, so integrability issues and infinite values
are absent. No other junk-value convention is used.

Closure read: `Assignment`, `Design`, `Design.mass`, `Design.mk`,
`T30Statement`, `effect`, `expect`, `exposureProb`, `htContrast`, `htTotal`,
`mean`, `observed`, `prob`.

## SAP.P045b.T31

Source: `Challenge/Part2.lean:30–32`; statement: `Defs/Part5.lean:46–51`.

For every natural N_c>0, every binary mediator response table
m:[N_c]→Bool→Bool, and every real potential outcome table
y:[N_c]→Bool→Bool→ℝ, define

    I = (1/N_c) Σ_i [y(i,true,m(i,true)) − y(i,false,m(i,false))],
    C(z) = (1/N_c) Σ_i [y(i,z,m(i,true)) − y(i,z,m(i,false))],
    O(z) = (1/N_c) Σ_i [y(i,true,m(i,z)) − y(i,false,m(i,z))].

These are exactly `indirectHousehold`, `contagion`, and `otherMechanisms`,
respectively, using `mean x`=(Σ_i x(i))/(Fintype.card [N_c]). The theorem
asserts I=C(true)+O(false), I=C(false)+O(true), and the following pointwise
conditional statement: for every i, if m(i,true)=m(i,false), then for every
Boolean z, y(i,z,m(i,true))−y(i,z,m(i,false))=0. The third clause concerns
each summand; it does not assume all mediators are unchanged. No
randomization, independence, monotonicity, probability law, or identification
assumption is part of the statement. It is an algebraic identity for all
such tables, not an inferential identification result.

Junk/edge conventions: the generic `mean` is total, assigning zero when its
index type is empty, but N_c>0 makes every mean denominator positive here.
The outcomes are finite real numbers; the mediator and treatment inputs are
ordinary total Boolean functions. No partial function, undefined conditional
mean, integral, infinite value, or domain-sensitive analytic function occurs.

Closure read: `T31Statement`, `contagion`, `indirectHousehold`, `mean`,
`otherMechanisms`.

## SAP.P045b.T32

Source: `Challenge/Part2.lean:34–38`; statement and certificate:
`Defs/Part6.lean:35–119`; generic estimators: `Defs/Part3.lean`.

The outer statement is existential: there exist a type E (in `Type`),
a decidable equality on E, a bijection labels:[4]≃E, and tables
f:[66]→[12]→E, w:[66]→[12]→E→ℚ,
q:[66]→[12]→[12]→E→E→ℚ satisfying every conjunct of `T32Facts`.
E therefore has exactly four elements even though no `Fintype E` is needed.
There is no universally quantified input or antecedent requiring the caller
to supply any of the identities in that certificate.

The concrete objects are as follows.

* `cliquePairs` lists all 66 unordered pairs 0≤a<b<12 in lexicographic order.
  `cliqueAssignments r` treats exactly the two vertices of pair r.
* `cliqueAdj i j` is true exactly when i≠j and floor(i/4)=floor(j/4).
  This is the disjoint union of three four-vertex cliques.
* `retainedAssignments t r` is cliqueAssignments(t.succAbove r), where
  `succAbove` is the order-preserving inclusion [65]→[66] that skips t.
  Thus each retained table is all assignments except one, without repetition.
* `fourExposure labels A z i` counts treated adjacent vertices, excluding
  self for this A, and returns labels(0) for treated/positive count,
  labels(1) for treated/zero count, labels(2) for control/positive count,
  labels(3) for control/zero count. In this certificate k=labels(2),
  l=labels(3), and every potential outcome y(i,a) is the rational number 1.
* The analysis design p is uniform on the 66 pair assignments, p(r)=1/66.
  `cliqueJointMass false (t,z)` is 1/4356 for all ordered pairs, i.e. t and
  z are independent uniform indices. `cliqueJointMass true (t,z)` is zero
  for t=z and 1/4290 otherwise. Here t is the omitted assignment of the
  retained table, and z is the analysis assignment. In the latter regime
  z belongs to the retained table. Both are laws on 66×66 ordered pairs.

All generic estimator definitions, fully unfolded to finite arithmetic:

For a finite sample space Ω, exposure map f, potential outcomes y and arbitrary
positive/zero weight tables w,q, define

    M_i(a) = Σ_ω 1_{f(ω,i)=a} p(ω),
    J_ij(a,b) = Σ_ω 1_{f(ω,i)=a and f(ω,j)=b} p(ω),
    H_a(ω) = (1/N) Σ_i [y(i,a)/w(i,a) if f(ω,i)=a, else 0],
    T(ω) = H_k(ω) − H_l(ω),
    Var_p(T) = Σ_ω p(ω)T(ω)^2 − (Σ_ω p(ω)T(ω))^2,
    effect(y,a,b) = (Σ_i[y(i,a)−y(i,b)])/N.

These are respectively `exposureMarginal`, `exposureJoint`, `weightedMean`
(whose summand is `weightedTerm`), `weightedContrast`, `momentVariance`,
and `exposureEffect`.

For each a, `totalVarianceEstimate` is the sum over all ordered i,j of

    1_{q_ij(a,a)>0} 1_{f_i=a,f_j=a}
        y(i,a)y(j,a)[1/(w(i,a)w(j,a))−1/q_ij(a,a)]
      + 1_{i≠j,q_ij(a,a)=0}
        [1_{f_i=a} y(i,a)^2/(2w(i,a))
         + 1_{f_j=a} y(j,a)^2/(2w(j,a))].

`totalCovarianceEstimate(a,b)` is the ordered i,j sum of

    1_{q_ij(a,b)>0} 1_{f_i=a,f_j=b}
        y(i,a)y(j,b)[1/(w(i,a)w(j,b))−1/q_ij(a,b)]
      − 1_{q_ij(a,b)=0}
        [1_{f_i=a} y(i,a)^2/(2w(i,a))
         + 1_{f_j=b} y(j,b)^2/(2w(j,b))].

`varianceEstimate(k,l)` is [totalVarianceEstimate(k)+totalVarianceEstimate(l)
−2 totalCovarianceEstimate(k,l)]/N². These definitions also specify their
behavior for q<0 (the positive branch and the zero correction both vanish).

For an R-row exposure table g, `exposureCount g i a` counts rows r with
g(r,i)=a, and `jointCount g i j a b` counts rows with both specified
exposures. `smoothedWeight` is (exposureCount+1)/(R+1).
`smoothedJoint` is (jointCount+1_{i=j})/(R+1) when a=b, and jointCount/R
when a≠b. In this statement R=65; the resulting rational tables are w_t,q_t,
computed from f∘t.succAbove. q_t is constrained by these formulas only for
a,b in {k,l}, which are the only exposure labels read by the contrast
variance estimator. The other entries of q are immaterial existential data.
Write T_t(z),V_t(z) for these simulated-weight estimators with y=1.

`T32Facts` asserts all the following, as conclusions rather than premises:

1. f is exactly the four-condition exposure table of the clique assignments.
   An assignment treats two vertices iff it is cliqueAssignments(r) for some r;
   cliqueAssignments is injective. cliqueAdj is symmetric and loopless and
   every vertex has a neighbor. Every retainedAssignments(t) is injective
   and omits cliqueAssignments(t). w and the relevant entries of q have the
   smoothed formulas above. w_t(i,k) and w_t(i,l) are positive for all t,i.
2. The target effect is zero. For every i the full design has 27 k-exposures
   and 28 l-exposures, with exact probabilities 9/22 and 14/33 respectively,
   both positive. For distinct i,j the k,k joint counts are 17 if they share
   a clique and 9 otherwise; l,l counts are 28 or 6; k,l counts are 0 or 15.
3. Each assignment has k-cell size 2 and l-cell size 8 when its treated pair
   is in one clique, and sizes 6 and 4 otherwise. There are 18 assignments
   of the first type and 48 of the second.
4. With exact weights M,J the point contrast is −220/189 on the first type
   and 55/126 on the second. Its expectation is zero, its variance is
   6050/11907, and the expectation of the exact variance estimate equals
   6050/11907.
5. For each of the two joint laws all masses are nonnegative and sum to one.
   Under the independent (false) law:

       E T = −67/53592,
       Var T = 113448938731/232640299584,
       E V = 1040129476423/2326402995840,
       E V − Var T = −953130413/23499020160.

   Under the included (true) law:

       E T = −67/52780,
       Var T = 11375808887/23342482800,
       E V = 4673362763/10414338480,
       E V − Var T = −20161943/522324075.

   For each law E V < Var T and E V < 6050/11907.
6. For every fixed omitted index t, with analysis z independently uniform
   over all 66 assignments, Var_p T_t is 2810528137/5767941312 when t's pair
   shares a clique and 937589375/1922647104 otherwise. E_p V_t is
   267260522663/634473544320 or 4830430961/10574559072 respectively. The
   respective differences are −1551761941/23499020160 and
   −72513467/2349902016. In both cases E_p V_t < Var_p T_t.
7. For every t there is a permutation e of [12] preserving cliqueAdj and
   satisfying cliqueAssignments(t)(e(i))=cliqueAssignments(r₀)(i), where
   r₀=0 for a same-clique pair and r₀=3 otherwise. The representatives
   correspond to pairs (0,1) and (0,4).
8. For each included flag, cast the joint mass and w,q from ℚ into ℝ and
   recompute the real point and variance estimators from those real tables
   and real unit outcomes. These real masses are nonnegative and normalized,
   and E V_real < Var(T_real) and E V_real < 6050/11907.

The last clause explicitly concerns the real-valued functions recomputed by
the estimator, rather than an unspecified embedding or some unrelated field.
The docstring calls this an audit counterexample to a stronger finite-simulation
extension and expressly says it does not refute the contextual exact-probability
assertion. The statement contains no theorem about independent identically
distributed simulation rows: its retained rows enumerate 65 distinct members
of a 66-member design. The independence of t and analysis z under one law
does not make the 65 rows independent of one another.

Junk/edge conventions:

* The relevant generic field divisions are total (inverse zero=zero), but
  actual denominators are 12, 12², 65, 66, positive marginal weights, and
  positive q values in the explicitly guarded inverse-q branches. Every
  w_t(i,a) is (count+1)/66 and is positive, even for exposure labels beyond
  k,l. Zero q is handled by the displayed structural-zero correction, with
  no active inverse-q term. Exact marginals for k,l are positive.
* `smoothedJoint` in general has division by R for different labels; R=65
  here. Generic functions with N=0 or R=0 would use total field division,
  but neither can occur in this certificate. The generic `Field` could
  have positive characteristic; here every actual calculation is in ℚ
  or its canonical characteristic-zero real embedding.
* Naturals used as indices/counts have exact ℚ and ℝ casts. The integer
  division i.val/4 is intentional clique indexing for 0≤i<12, not a
  truncated subtraction. `Fin` numerals are valid literal indices in the
  displayed arrays and exposure labels. succAbove skips one valid index.
  No out-of-range array access or partial map occurs.
* Empty finite sums in the general definitions are zero; actual unit,
  assignment and replicate types here are nonempty. Empty exposure cells
  contribute zero as specified by the indicator branches. Some joint
  cells are structurally empty, as the certificate explicitly records.
* `momentVariance` has the usual variance meaning because all the actual
  p and joint masses are nonnegative and normalized, as asserted in the
  certificate. It would be just a moment polynomial for arbitrary masses.
* There are no Bochner integrals, infinities converted to reals, limits,
  sInf/sSup, logs, square roots or real powers in this closure.

All six generated proof declarations listed in the closure were read using
`#print` in `scratch/Blind.lean`: `T32Facts._proof_1` supplies `NeZero 66`;
`T32Facts._proof_2` and `_proof_3` supply `AtLeastTwo 6050` and
`AtLeastTwo 11907`; `cliquePairs._proof_1` supplies `NeZero 12`;
`fourExposure._proof_1` supplies `NeZero 4`; and
`totalVarianceEstimate._proof_1` supplies `AtLeastTwo 2`. They certify
literal/numeral elaboration only and add no substantive premise or axiom.

Remaining closure read: `Assignment`, `T32Facts`, `T32Statement`, `cliqueAdj`,
`cliqueAssignments`, `cliqueJointMass`, `cliquePairs`, `expect`,
`exposureCount`, `exposureEffect`, `exposureJoint`, `exposureMarginal`,
`fourExposure`, `jointCount`, `momentVariance`, `retainedAssignments`,
`smoothedJoint`, `smoothedWeight`, `totalCovarianceEstimate`,
`totalVarianceEstimate`, `varianceEstimate`, `weightedContrast`,
`weightedMean`, `weightedTerm`.
