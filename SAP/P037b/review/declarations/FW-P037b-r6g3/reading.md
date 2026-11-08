# Blind reading

Saved before opening `claims.json` or `record.json`. Sources read: the three Challenge docstrings and statements, all named definitions in their closures, and every generated auxiliary declaration listed in `closure.json`. `scratch/Blind.lean` prints the auxiliaries and elaborated statements; its successful output is in `scratch/Blind.out`. This reading describes the Lean statements without assuming the claims' intended content.

## SAP.P037b.T32

The Challenge docstring describes a restricted result about normalization of blocked school assignment masses, uniform selection marginals and pairs, and a local half-treatment mixture. It explicitly lists omitted independence, numerical specializations, exposure/population/estimand comparisons, joint/variance comparisons, and sampler repair certification.

Definitions, unfolded:

* `blockedSchoolAssignments B` is the finite set of subsets `s` of `Fin B × Fin 4` such that, for each `b : Fin B`, exactly two elements of `s` have first coordinate `b`. Thus it represents selecting two of four schools in each of B labelled blocks.
* `blockedAssignmentMass s` is the real number `6^(-(B : ℤ))` if `s` belongs to that set and zero otherwise. This uses integer exponentiation of the nonzero real number 6.
* `unblockedSchoolAssignments n m` is the set of all m-element subsets of `Fin n`.
* `uniformSchoolEventProbability n m E` is the real cardinality of the m-element subsets satisfying the arbitrary predicate E, divided by the real cast of `Nat.choose n m`.

`T32Statement` is a conjunction of two independently quantified assertions:

1. For every `B n m : ℕ`, first assuming `2 ≤ n` and then `m ≤ n`, all five following assertions hold: the blocked set has cardinality `6^B`; summing `blockedAssignmentMass s` over that set gives 1; the unblocked set has cardinality `Nat.choose n m`; for every `h : Fin n`, its membership probability under uniform m-subset sampling is `(m : ℝ)/n`; and for every `h j : Fin n`, assuming `h ≠ j`, their joint membership probability is `((m : ℝ)*((m : ℝ)-1))/((n : ℝ)*((n : ℝ)-1))`. The subtractions in this last expression elaborate as real subtraction, not natural subtraction.
2. For arbitrary types Ω, U, K, finite enumerations of Ω and U, and decidable equality on K, take `p : Ω → ℝ`, `q : U → ℝ`, and `S : Ω → Bool`. Assume first `Σz p(z) 1[S(z)=true] = 1/2`, then `Σz p(z)=1`. For every `f : Bool → U → K` and `k : K`, assume next `∀z, 0 ≤ p(z)`, `∀u, 0 ≤ q(u)`, and `Σu q(u)=1`. The conclusion is

   `Σz Σu p(z)q(u) 1[f(S(z),u)=k] = (1/2) Σu q(u)1[f(false,u)=k] + (1/2) Σu q(u)1[f(true,u)=k]`.

   This is explicitly a product joint mass p(z)q(u); f can depend on the school assignment only through S. The statement contains no general correlated joint law, and imposes the half marginal rather than proving it for a specified school law.

Closure auxiliaries: `T30Statement._proof_2` proves `Nat.AtLeastTwo (1+1)` for the numeral 2, and `blockedAssignmentMass._proof_1` proves `Nat.AtLeastTwo (5+1)` for the numeral 6. Their printed bodies use standard natural-number instances. They contain no substantive assumption or statistical content.

Junk and boundary cases:

* Real division is totalized with `x/0=0`, but `m ≤ n` ensures `choose n m > 0`, and `n ≥ 2` ensures both n and n-1 are nonzero. The half denominators are 2. No asserted probability uses division by zero.
* m may be 0 or 1; real subtraction m-1 is intentional, and its product with m gives the correct zero pair probability when m=0. There is no truncated subtraction in this statement.
* B may be zero. There is one subset of the empty school universe (the empty subset), the block condition is vacuous, `6^0=1`, and its mass is 1. This is an ordinary empty product case.
* Empty Ω or U makes its normalization `0=1` impossible; these are impossible parameter instances, not the only parameter instances. An empty K supplies no k. Nonnegative masses may be zero, which is legitimate; no division by these masses occurs.
* The cast B to ℤ preserves its value and its negation is integer negation. Negative integer powers use inversion, but the base 6 is nonzero. All other natural casts to ℝ are exact. No Fin numeral in these formulas wraps.
* There are no integrals, means of non-integrable functions, extended-real conversions, logarithms, roots, real powers, extrema, limits, or partial-function defaults here.

## SAP.P037b.T25

The Challenge docstring asserts two explicitly specified nomination networks give different exposure labels and positive exposure probabilities under nomination and either-direction rows. It states no restriction.

Definitions, unfolded:

* A graph is a Boolean function `B : Fin n → Fin n → Bool`; true at (i,j) means the directed edge i→j.
* `peerUnion B i j = B i j || B j i`.
* `directedIndegree B j` is the cardinality of `{i : Fin n | B i j = true}`.
* To compute `indegreeQuantile90 B`, form the list of all n natural indegrees, sort it in nondecreasing order by `mergeSort (≤)`, and let `h=9*(n-1)` in ℕ, `a=h/10`, `r=h%10`. The real result is `((10-r : ℕ):ℝ)/10 * (sorted.getD a 0 : ℝ) + (r:ℝ)/10 * (sorted.getD (a+1) 0 : ℝ)`. This is linear interpolation at position .9(n-1) with zero-based positions, and default 0 for an invalid position.
* `referentStudents B` is `{j | indegreeQuantile90 B < (directedIndegree B j : ℝ)}`. The inequality is strict.
* `seedPeerCount B i seeds` counts seeds j with B(i,j)=true. `referentSeedPeerCount B γ seeds i` counts seeds j with B(i,j)=true and j∈γ.
* `nonseedExposureLabel t r : Fin 3` is 0 if t=0, otherwise 1 if r=0, otherwise 2. `networkExposureLabel B γ seeds i` applies that rule to the two counts above. There is no seed-self or school-control branch in this helper; it is the treated nonseed three-label rule.
* `nominationGraph10` on vertices 0,…,9 has exactly edges 1→0, 2→1, 3→1.
* `nominationGraph20` on vertices 0,…,19 has exactly edges 1→0; 0→2; 0→4; a→1 for a=8,…,13; and a→2 for a=14,…,19.
* `eligibleStudents20 : Fin 6 → Fin 20` is the injective list `[1,2,4,5,6,7]`.
* `graphExposureProbability20 B k : ℝ`, for k∈`Fin 4`, is 1/2 if k=0; otherwise it counts 3-element subsets s of `Fin 6` for which `networkExposureLabel B (referentStudents nominationGraph20) (s.image eligibleStudents20) 0`, converted to its natural value and increased by 1, equals k's value, then divides that count by 40. Thus referents always come from the original twenty-vertex graph, even when B is its union. This is an unconditional half-control, half-uniform-3-of-6 probability for vertex 0, which is never an eligible seed. Probability labels 0,1,2,3 mean control, treated with no seed peer, treated with nonreferent seed peers only, and treated with a referent seed peer, respectively.

The theorem has no external hypotheses or existential quantifiers. `T25Statement` is the conjunction of these explicit certificates (all k or i quantifiers range over the indicated finite vertex/label sets):

1. The ten-vertex quantile is 11/10 and its referents are `{1}`. With seeds `{1}`, the network label of vertex 0 is 0 using the directed row and 2 using the union row, with referents held fixed.
2. The twenty-vertex quantile is 3/2 and its referents are `{1,2}`. For every k∈`Fin 4`, the directed and union exposure probabilities are respectively `[1/2,1/10,3/20,1/4](k)` and `[1/2,1/40,3/40,2/5](k)`. Each of these eight probabilities is strictly between 0 and 1.
3. The full indegree vectors are `[1,2,0,0,0,0,0,0,0,0]` and `[1,6,7,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]`. For every vertex in each graph, its diagonal entry is false and its real indegree differs from that graph's quantile.
4. For the ten-vertex graph, vertex 0 and seeds `{1}` have total/referent outgoing counts 0/0 and total/referent union counts 1/1. The twenty-vertex directed and union rows of vertex 0 are exactly `{2,4}` and `{1,2,4}`.
5. There are 20 three-element subsets of `Fin 6`. For every k∈`Fin 4`, the histograms of their shifted labels at vertex 0 are `[0,4,6,10](k)` under the directed graph and `[0,1,3,16](k)` under the union graph, using fixed referents `{1,2}`.
6. For every k∈`Fin 3`, at probability index `k.succ` (indices 1,2,3), the directed and union probabilities differ and their reciprocals differ.

Every generated closure declaration was printed and read. They are solely `Nat.AtLeastTwo`/`NeZero` instances for literal representation: `T19Statement._proof_1` (3 at least two), `_proof_5` (40), `_proof_6` (6), `_proof_8` (4); `T21Statement._proof_4` (4); `T23Statement._proof_11` (3 nonzero), `_proof_3` (10 at least two), `_proof_5` (20); `T25Statement._proof_1` (11 at least two), `_proof_2` (10 nonzero), `_proof_3` (20 nonzero); `bandOutcomes._proof_1` (10 at least two), `_proof_3` (2); `graphExposureProbability20._proof_1` (40 at least two); `nominationGraph20._proof_1` (20 nonzero); `nonseedExposureLabel._proof_1` (3 nonzero); `rareExposure._proof_1` (10 nonzero); and `treatmentPair._proof_1` (4 nonzero). The appearances of other statements' names are sharing of numeral instances, not dependencies on those statements' propositions.

Junk and boundary cases:

* Natural subtraction n-1 truncates at 0 in the generic quantile definition. The targets only use n=10 and n=20, so it does not truncate. `10-r` never truncates because r<10. `/10` and `%10` on naturals are quotient and remainder, as required by interpolation.
* The quantile uses `List.getD` with default 0. Its accessed positions are 8,9 for n=10 and 17,18 for n=20, all valid. Generally n=1 has a zero-weight out-of-range second lookup, and n=0 returns zero by defaults; neither case is used here.
* All real divisors 2,10,40 are positive. The reciprocals in clause 6 use probabilities whose strict positivity is explicitly certified, so totalized inversion at zero plays no role.
* Fin numeral construction uses residues modulo the nonzero bound, but each actual index and vertex literal is in range. Vector notation is indexed by the exact corresponding `Fin` length; no indexing default is used. Natural casts and the `.val+1` shift are exact and not truncated.
* Both vertex universes and the six eligible indices are nonempty; all seed selections have cardinality three, their images have cardinality three, and vertex 0 is excluded. Counts and expectations are finite. There are no integrals, extended-real conversions, logs, square roots, real powers, extrema, or limits.

## SAP.P037b.T26

The Challenge docstring describes a restriction to union-graph properties, two count decompositions, scalar label criteria and implications, and positive-weight probability comparisons. It discloses omitted graph subset inequalities, a reciprocal-seed sufficient condition, concrete examples, and script/Fig. S5 verification; it specifies the scalar hypotheses r≤c and q≤b.

Definitions, unfolded independently: `peerUnion B i j` is the Boolean disjunction B(i,j) or B(j,i), for a Boolean directed adjacency array on `Fin n`. `nonseedExposureLabel c r : Fin 3` is 0 when c=0, 1 when c≠0 and r=0, and 2 when both are nonzero. These represent the three treated nonseed classes. The theorem has four independently quantified conjuncts:

1. For every natural n and Boolean graph B, first assume `∀i, B(i,i)=false`. Then the union is symmetric; has false diagonal; contains every directed edge; and for every i,j, `(union(i,j)=true ∧ B(i,j)=false) ↔ (B(j,i)=true ∧ B(i,j)=false)`.
2. For every natural n, Boolean graph B (without a diagonal assumption), Boolean functions z,γ on `Fin n`, and vertex i, the number of j with `union(i,j) && z(j)` equals the number with `B(i,j) && z(j)` plus the number with `!B(i,j) && B(j,i) && z(j)`. The same identity holds with γ(j) added to each of the three conjunctions. Each count is literally a sum of natural indicators over all j. Thus incoming-only vertices and outgoing vertices are disjoint by construction.
3. For every `c b r q : ℕ`, first assume r≤c and then q≤b. The equality `label(c,r)=label(c+b,r+q)` holds iff `(0<c ∨ b=0) ∧ (0<r ∨ q=0)`. Also `label(c+b,r+q)=0` implies `label(c,r)=0`, and `label(c,r)=2` implies `label(c+b,r+q)=2`.
4. For every finite type Ω, real weights p, first assume `∀z, 0<p(z)`. For arbitrary natural-valued functions c,b,r,q on Ω, assume pointwise r≤c, pointwise q≤b, and then `Σz p(z)=1`. Write L(z)=label(c(z),r(z)) and L'(z)=label(c(z)+b(z),r(z)+q(z)). Then `Σz p(z)1[L'=0] ≤ Σz p(z)1[L=0]` and `Σz p(z)1[L=2] ≤ Σz p(z)1[L'=2]`. The first is strict if there exists z with L=0 and L'≠0; the second is strict if there exists z with L≠2 and L'=2. Each existential is an antecedent of its own strict conclusion, not a hypothesis needed for the two weak comparisons. No graph realization of the scalar functions is asserted.

Closure auxiliaries `T23Statement._proof_11` and `nonseedExposureLabel._proof_1` are both standard proofs that the natural bound 3 is nonzero. Their bodies were printed and read. They support numeral construction in `Fin 3` and introduce no mathematical hypotheses.

Junk and boundary cases:

* All sums and counts are finite; no divisions or subtraction occur in the scalar label/probability statement. Natural addition cannot overflow and no signed information is lost. Labels are the in-range literals 0,1,2 of `Fin 3`.
* n=0 makes the graph assertions vacuous and supplies no vertex i for clause 2; nonempty graph instances are also permitted. Empty Ω makes the normalization impossible, while nonempty instances with positive mass are available. The strictness antecedents require genuine points; positive p ensures those points have positive mass.
* r≤c and q≤b make the counts consistent with subset counts; the label function by itself would also accept inconsistent inputs, but these are excluded in the scalar assertions. Zero counts correctly represent absence, rather than a default for an undefined quantity.
* There are no partial-function defaults, integrals, means, logarithms, roots, real powers, infinities, extrema, or limits in this closure.
