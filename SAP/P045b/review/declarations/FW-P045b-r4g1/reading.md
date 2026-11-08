# Blind reading

This file was written and saved before opening `claims.json` or `record.json`. The sources read were `closure.json`, the Challenge declarations and their docstrings, all source definitions named in the five closures, and the relevant Mathlib definitions of tuple removal and graph distance. `scratch/Blind.lean` was compiled to print the elaborated statements and every generated proof/auxiliary declaration in the closures. Nothing in this reading presupposes the canonical claims or the architect's decisions.

## SAP.P045b.T17

The docstring describes retaining empty realized exposure cells in Horvitz–Thompson estimation, unconditional and conditional expectation identities, and undefined empty-cell Hájek ratios and ordinary means.

Quantifiers, in order: for every natural number `n > 0`; every type Δ with a finite enumeration and decidable equality; every probability design `p` on the binary assignments `{0,…,n−1} → Bool`; every exposure map `D : ({0,…,n−1} → Bool) → {0,…,n−1} → Δ`; every real potential-outcome array `y : {0,…,n−1} → Δ → ℝ`; and every pair of labels `k,l ∈ Δ`, assume `k ≠ l`, and assume positive exposure probabilities for both labels for every individual. A design is exactly a real mass function `p(z) ≥ 0` on all `2^n` assignments with `Σ_z p(z) = 1`. No independence or full-support hypothesis occurs.

Here are all SAP definitions used in the statement, expanded into finite sums. Write `1_E` for the ordinary real indicator, and write `I = {0,…,n−1}`:

* `expect p X = Σ_z p(z)X(z)` and `prob p E = Σ_z p(z)1_E(z)`.
* `condMean p E X = (Σ_z p(z)1_E(z)X(z))/(Σ_z p(z)1_E(z))`, with the conditional numerator implemented by an `if`.
* `π_i(d) = exposureProb p D i d = Σ_z p(z)1_{D(z,i)=d}`.
* `observed D y z i = y(i,D(z,i))`.
* `H_d(z) = htTotal p D y d z = Σ_i [if D(z,i)=d then y(i,D(z,i))/π_i(d) else 0]`.
* `htContrast p D y k l z = (H_k(z)−H_l(z))/n`.
* `mean x = (Σ_i x(i))/|I|`; consequently `effect y k l = (Σ_i y(i,k))/n − (Σ_i y(i,l))/n`.
* Put `W_d(z) = Σ_i [if D(z,i)=d then 1/π_i(d) else 0]`. `hajek` returns `none` when `W_d(z)=0`, and otherwise `some(H_d(z)/W_d(z))`.
* Put `m_d(z) = |{i : D(z,i)=d}|`. `exposureSampleMean` returns `none` when `m_d(z)=0`, and otherwise returns `some((Σ_i 1_{D(z,i)=d} y(i,D(z,i)))/m_d(z))`.

The conclusion is a conjunction of six clauses, all under the preceding universal quantifiers and hypotheses:

1. For every assignment `z` (including assignments of zero design probability), if `D(z,i) ≠ k` for all `i`, then `H_k(z)=0`, the contrast is `−H_l(z)/n`, `W_k(z)=0`, and both the Hájek estimate and ordinary exposure-cell mean are `none`.
2. `Σ_z p(z)H_k(z) = Σ_i y(i,k)`.
3. The expectation of the contrast equals the population mean contrast stated above.
4. Write `A={z : ∃i, D(z,i)=k}` and `q=P(A)`. If `q>0`, then `E[H_k | A]=(Σ_i y(i,k))/q`.
5. If `q>0`, `P(Aᶜ)>0`, and `Σ_i y(i,k) ≠ 0`, then `E[H_k | A] ≠ Σ_i y(i,k)`.
6. The separate real-number identity `20/(20/45)=45` holds. There is no experiment or potential-outcome array attached to these constants in the statement.

Junk conventions: real division is total and `a/0=0` in Lean. The HT and reciprocal-weight denominators for the labels used here are strictly positive by hypothesis; `n` and the cardinality used by the population means are positive. Every asserted conditional-mean formula or inequality is guarded by a positive event probability. The `Option` definitions explicitly avoid treating an empty cell's `0/0` as a mean or Hájek estimate. On a nonempty cell the positivity hypotheses make `W_k>0`, although that converse domain fact is not an explicit conclusion. Outside the theorem's hypotheses the underlying definitions allow zero exposure probabilities, zero population size, and zero-probability conditioning; their totalized values do not drive this theorem. All sums are finite real sums, so there are no nonintegrable integrals. Δ cannot be empty or a singleton when distinct `k,l` are supplied. Generated `_proof_1` and `_proof_2` merely certify the real numeral-denominator elaboration for 20 and 45; they add no hypotheses. No logarithm, square root, real power, infinity conversion, supremum/infimum, or limit occurs.

## SAP.P045b.T18

The docstring describes ordered deletion of one's own treatment coordinate and the resulting unique reexpression of an arbitrary outcome function.

`Assignment m` means `Fin m → Bool`. `withoutCoordinate i z` is Mathlib's `Fin.removeNth i z`, namely `j ↦ z(i.succAbove j)`: for the natural values of indices, it is `z(j)` if `j<i`, and `z(j+1)` if `j≥i`. The former uses `Fin.castSucc` and the latter `Fin.succ` to keep both indices in `Fin(n+1)`.

The first conjunct quantifies over every natural `n` and every index `i ∈ {0,…,n}`. For that index it asserts, together:

1. For every binary vector `z` of length `n+1` and every `j ∈ {0,…,n−1}`, the deletion formula just given holds.
2. For every pair `z,z'`, if `z(j)=z'(j)` at every index `j ≠ i`, then the deleted vectors agree.
3. The map `z ↦ (z(i), withoutCoordinate i z)` is a bijection from binary vectors of length `n+1` to `Bool × (Fin n → Bool)`; bijection means both injectivity and surjectivity.
4. For every real-valued function `y` of the full vector, there is exactly one function `f : Bool × (Fin n → Bool) → ℝ` such that, for every `z`, `f(z(i), withoutCoordinate i z)=y(z)`. Uniqueness is equality of functions on the entire product, not merely on a selected support.

The second conjunct independently asserts, for every length-four `z`, `withoutCoordinate 2 z = ![z 0,z 1,z 3]`. Coordinates are zero based, so index 2 denotes the third individual.

Junk conventions: no division, subtraction, partial indexing/default, expectation, or analytic operation occurs. `Fin` indices carry valid bounds. Numerals in `Fin m` use its numeral instance (generally reduction modulo `m`), but 0,1,2,3 are all in range for the particular length-four example, so no wraparound occurs. The generated proof certifies `NeZero 4`. When `n=0`, the deleted index type is empty, and its function type has a unique empty vector; the original vector still has one coordinate, so the product bijection and uniqueness are meaningful. The non-own-coordinate and deletion-formula universal assertions then have no indices to check, which is appropriate at this boundary. There is no assumption that an outcome ignores own treatment: only the deleted vector ignores it.

## SAP.P045b.T19

The docstring describes the peer-treatment count under an exactly fixed group treatment count and the resulting correction to a saturation expression.

For a binary vector `z : Fin n → Bool`, `bit(z(j))` is the real number 1 if `z(j)=true` and 0 otherwise. `treatedCount z` is the natural cardinality of `{j ∈ Fin n : z(j)=true}`. `coMembers i z` is the real finite sum `Σ_{j∈Fin n, j≠i} bit(z(j))`, hence the number of treated peers excluding `i`.

The statement is the conjunction of the following general assertion, a universal three-person example, and a numerical comparison:

* For every natural `n,K`, a proof `2≤n`, a real number ψ, proofs `0<ψ<1` and `(K:ℝ)=ψ(n:ℝ)`, every binary vector `z` with `treatedCount z=K`, and every `i∈Fin n`, the peer count equals `(K:ℝ)−bit(z(i))`. Moreover, if `z(i)=true`, the count equals `ψn−1`, the excess `ψ(n−1)−coMembers(i,z)` equals `1−ψ`, and `coMembers(i,z)<ψ(n−1)`. If `z(i)=false`, its peer count equals `ψn`.
* For every `z : Fin 3 → Bool` with exactly two true coordinates, and every `i`, a true coordinate has peer count 1 and a false coordinate has peer count 2.
* The real identity `(2/3)(3−1)=4/3` holds.

All SAP definitions are the finite cardinality, real bit, and peer sum expanded above; `T19Statement` includes the whole proposition `T19General` without changing its hypotheses. This is a deterministic combinatorial statement; it imposes no distribution on assignments.

Junk conventions: the count cardinality is cast from ℕ to ℝ faithfully. `K−bit(z(i))`, `ψn−1`, and `n−1` in `ψ(n−1)` are real subtractions, not truncated natural subtractions. In particular `coMembers` is not defined by subtracting from a natural count. The fixed-count and saturation hypotheses imply `0<K<n` and impose the integer feasibility of ψn; assignments with this count do exist, for example `n=3,K=2,ψ=2/3`. There is no variable denominator. The displayed rational constants have nonzero real denominators. Generated proofs establish the numeral instances for 2,3,4. `n≥2` prevents an empty peer universe in the general statement. There is no infinity, integral, default, logarithm, root, real power, or limit.

## SAP.P045b.T20

The docstring distinguishes a literal pairwise-distance-at-most-three interpretation from a corrected separation interpretation, and claims the latter has exactly thirteen sets on a nine-vertex path.

The vertex type is `Fin 9={0,…,8}`. `pathDistance(i,j)` is `Nat.dist i.val j.val`, cast to the extended natural numbers `ℕ∞ = ℕ ∪ {∞}`. On these vertices it is exactly `|i−j|`, always finite, i.e. shortest-path distance on the unit-edge path. In general `Nat.dist a b=(a−b)+(b−a)` with natural truncated subtractions, equivalently `max(a,b)−min(a,b)`; these yield the intended absolute difference.

For any extended-natural-valued distance `d`, natural ε, and finite vertex set `S`, the definitions are:

* `separated d ε S` means `∀s∈S, ∀t∈S, s≠t → ε≤d(s,t)`.
* `covers d ε S` means `∀v∉S, ∃s∈S, d(s,v)≤ε−1`, where ε−1 is taken in ℕ before being cast to ℕ∞.
* `epsilonNet d ε S` is the conjunction of those two predicates.
* `withinThree S` means `∀s∈S, ∀t∈S, pathDistance(s,t)≤3`, including equal pairs.

The theorem has no hypotheses. Its three conjunctions are: (1) for every `S⊆{0,…,8}`, it is not the case that all pairwise distances in `S` are at most 3 and every vertex outside `S` is within 2 of a member of `S`; (2) the finite collection of subsets with all distinct pairwise distances at least 3 and every outside vertex within 2 has cardinality 13; and (3) for every `S`, it has these corrected properties if and only if it is one of

`{1,6}, {2,6}, {2,7}, {0,3,6}, {0,3,7}, {0,3,8}, {0,4,7}, {0,4,8}, {0,5,8}, {1,4,7}, {1,4,8}, {1,5,8}, {2,5,8}`.

The outer `univ` ranges over all finite subsets of `Fin 9`, not merely over vertices. The decidability instances and their generated auxiliaries decide exactly the bounded quantifiers in separation/covering and their conjunction; they introduce no semantic extra conditions. The generated proof associated with the listed sets establishes `NeZero 9`. `withinThree`'s generated proof supplies the numeral instance for 3.

Junk conventions: ε is 3 throughout, so the truncated subtraction `ε−1` is the ordinary value 2. All path-distance values are finite natural casts; no infinity is collapsed to a real value. All listed vertex numerals lie between 0 and 8, so there is no Fin numeral wraparound. Empty `S` satisfies the pairwise conditions vacuously, but fails covering because the vertex universe is nonempty; it is not counted as a net. No division, integral, extremum, or limit is used. This statement refutes only the particular conjunction in its first clause and asserts the separate corrected enumeration; its own text does not identify that conjunction with a canonical claim.

## SAP.P045b.T21

The docstring describes corrected nets as maximal separated sets, bounded greedy construction, and the same thirteen path examples.

Quantifiers in the general conjunct: for every natural `n,ε` with `1≤ε`, and every Mathlib `SimpleGraph` `G` on `Fin n` (an undirected, loopless graph), use Mathlib's `G.edist`. This is the infimum in ℕ∞ of the natural lengths of all walks between the given vertices. It is the shortest walk length when there is a walk, and ∞ when there is none. The predicates `separated`, `covers`, and `epsilonNet` have exactly the unfolded meanings in the T20 section.

Two more SAP definitions occur. `marked d ε S` is the finite set `{v : ∃s∈S, d(s,v)≤ε−1}`. `greedyRun d ε cs`, for a finite vertex list `cs`, asserts for every position `k<length(cs)` that `cs[k]` is outside the marked set of the set of the first `k` entries. List indexing uses the bound-carrying type `Fin cs.length`; `take k` denotes the prefix and `toFinset` forgets order and repetitions. There is no randomness or prescribed tie-breaking in this predicate.

For every such `n,ε,G`, the conclusion is the conjunction of:

1. For every finite `S`, if distinct members of `S` have distance at least ε, then covering is equivalent to: for every `v∉S`, inserting `v` destroys separation. This is maximality by inclusion (expressed by failure of every one-point extension), not maximum cardinality.
2. For every finite list `cs`, if each entry was unmarked relative to its prefix, then the list has no repetitions, its length is at most `n`, its underlying set is separated, and if its final marked set is all vertices then its underlying set is a net.
3. There exists a list `cs` satisfying the prefix condition and marking all vertices.
4. There exists a finite net `S`.

After that entire universal graph conjunct, independently, the statement includes the count 13 and the exact same universal characterization/list of thirteen subsets of `Fin 9` as in T20, using `pathDistance` and ε=3. The same decidability declarations and `NeZero 9` generated proof occur in its closure, with precisely the meanings already expanded above.

Junk conventions: `ε−1` is natural truncated subtraction in covering and marking, but the hypothesis `1≤ε` prevents saturation at the wrong radius; at ε=1 its intended value is 0. Graph distance's infimum over no walks is ∞, the intended extended graph distance, so disconnected graphs are covered without assigning artificial distance zero. There is no `toReal ∞`, real division, real power, integral, supremum or limit. All list accesses are within bounds. If `n=0`, the vertex type is empty: the empty set is both separated and covering, the empty list is a terminal greedy run, and the maximality characterization is vacuous in exactly the usual empty-graph way. For a nonempty graph an empty centre set cannot cover it. The statement gives correctness for every legal finite prefix, an existence result for a terminal prefix, and a universal length bound; it does not specify a random law on outputs. No conclusion is assumed as a hypothesis.
