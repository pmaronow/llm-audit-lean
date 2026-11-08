# Blind reading (written before opening claims.json / record.json)

Common definitions (SAP/P030/Defs/Part1.lean), unfolded to Mathlib notions:

- `Assignment N = FixedIndicator N = Fin N → Bool` (unit `i` treated iff `z i = true`; zero-based indices);
  `AssignmentSet N = Finset (Fin N → Bool)`; `PotentialOutcomes N = Fin N → (Fin N → Bool) → ℝ`, `Y i z` = outcome of unit i
  under the whole assignment z.
- `conditionalAssignments Ω S obs = Ω.filter (fun z => ∀ i, S i = true → z i = obs i)` (Part1:19): the design support restricted
  to assignments that agree with the observation on every fixed unit.
- `NoEffects Ω Y`: `∀ i, ∀ z z' ∈ Ω, Y i z = Y i z'` (Part1:24).
- `NoInterference Ω Y`: `∀ i, ∀ z z' ∈ Ω, z i = z' i → Y i z = Y i z'` (Part1:28): outcome depends only on own treatment (within Ω).
- `FixedOutcomeNull Ω' S Y`: `∀ i, S i → ∀ z z' ∈ Ω', Y i z = Y i z'` (Part1:31).
- `fixedOutcomes S Y z : {i // S i} → ℝ := fun i => Y i z` (Part1:35).
- `statistic S Y g z = g (fixedOutcomes S Y z) z` (actual statistic when z is realised) (Part1:38).
- `referenceStatistic S Y g obs z = g (fixedOutcomes S Y obs) z` (imputed statistic: observed fixed outcomes, reference assignment z) (Part1:42).
- `FiniteLaw A`: a finset `support`, `mass : A → ℝ` nonnegative on the support, `∑_{support} mass = 1` (Part1:47).
  `probability μ P = ∑_{z ∈ support} [P z] mass z` (Part1:53); `lowerTail μ f x = P(f ≤ x)`, `upperTail μ f x = P(x ≤ f)` (inclusive tails).
- `uniformProbability Ω P = #(Ω.filter P) / #Ω` (Part1:64). Junk: `= 0` when `Ω = ∅` (division by zero).
- `printedReject α p := p < α/2 ∨ 1 - α/2 < p` (Part1:76) — the "two-tailed" rule applied to a single (lower-tail) p-value.
- `correctedReject α pL pU := pL < α/2 ∨ pU < α/2` (Part1:77) — reject on either inclusive tail.
- `twoTailP pL pU := min 1 (2 * min pL pU)` (Part1:78).
- `averageRank a k = #{l | a l < a k} + (#{l | a l = a k} + 1)/2` (Part1:81): the midrank (correct with ties).
- `centeredRanks a k = averageRank a k - (n+1)/2` (Part1:86) (mean of midranks is (n+1)/2, so this is the centred rank).
- `rankCross a b = Σ_k c_a(k) c_b(k)`, `rankSquares a = Σ_k c_a(k)^2` (Part1:88-89).
- `spearman a b = rankCross a b / √(rankSquares a · rankSquares b)` (Part1:90): Pearson correlation of midranks = Spearman's ρ with ties.
  Junk: `x / 0 = 0` when either vector is constant (rankSquares = 0), and `Real.sqrt` of a product (never negative here).
- `nearestDistance x S z i = min_{j : S j = false ∧ z j = true} |x i - x j|` if that set is nonempty, else junk `0` (Part1:98).

Example data (SAP/P030/Defs/Part2.lean):

- Five-unit example: positions `fiveX = (0,4,8,-1,-2)`; fixed units `fiveS` = units 1,2,3 (indices 0,1,2);
  `fiveY i z = (0,1,2,0,0)_i` (constant in z); `fiveAssignment a` treats exactly unit 4+a (index a+3), a ∈ Fin 2;
  `fiveΩ = {fiveAssignment 0, fiveAssignment 1}`; `fiveFixed i = i` (Fin 3 → Fin 5); `fiveOutcomes = fiveY ∘ fiveFixed` at
  `fiveAssignment 0`; `fiveDistances a i` = distance of fixed unit i to the nearest treated non-fixed unit under assignment a;
  `fiveStatistic a = spearman (fiveDistances a) fiveOutcomes`.
- Ten-unit example: positions `tenX i = i+1`; fixed units `tenS` = units 1,8,9,10 (indices 0,7,8,9); `tenAssignment j` treats
  exactly unit j; `tenΩ` = the 10 single-treatment assignments; `tenYnull i z = (1,2,2,2,2,3,2,3,2,1)_i` (constant in z);
  `tenFixed = (0,7,8,9)`; `tableTreatment r = r+1` (units 2..7); `tableΩ` = assignments treating one of units 2..7;
  observed assignment `tenAssignment 6` (unit 7 treated); `tableY` = null fixed outcomes at the observation = (1,3,2,1);
  `tableDistances r` = nearest-treated distances of the 4 fixed units when unit r+2 is treated; `tableRho r = spearman (tableDistances r) tableY`;
  `tableValues = (-1/√90, -1/√90, -1/√90, -5/6, -3/√10, -3/√10)`;
  `tenG y z = spearman (nearest distances of fixed units under z) (y restricted to the fixed units in order 1,8,9,10)`.

---

## SAP.P030.T1 (Challenge/Part1.lean:7-10) : `T1Statement` (Defs/Part4.lean:57)

Plain mathematics. A closed proposition (no parameters) about the five-unit example. It asserts the conjunction of:

1. `∀ i z z'`, `fiveY i z = fiveY i z'` (no effects under *every* binary assignment), `NoEffects fiveΩ fiveY`, `NoInterference fiveΩ fiveY`.
2. `|fiveΩ| = 2`; `conditionalAssignments fiveΩ fiveS (fiveAssignment 0) = fiveΩ` (conditioning on the fixed units removes nothing);
   uniform design gives each of the two assignments probability 1/2; in every `z ∈ fiveΩ` all fixed units are untreated;
   each `fiveAssignment a` treats exactly one unit.
3. Observed fixed outcomes `(0,1,2)`; distances `(1,5,9)` for a=0 and `(2,6,10)` for a=1.
4. Midranks of outcomes `(1,2,3)`, centred `(-1,0,1)`; for each a: midranks of distances `(1,2,3)`, centred `(-1,0,1)`,
   cross-sum 2, both square sums 2 (> 0), `fiveStatistic a = 1`; the treated-variant set is nonempty (so `nearestDistance` is not junk).
5. For each a, uniform over `Fin 2`: `P_b(fiveStatistic b ≤ fiveStatistic a) = 1` and `P_b(fiveStatistic a ≤ fiveStatistic b) = 1`
   (both inclusive tail p-values are 1).
6. `∀ α, 0 < α < 1`: probability (uniform over the two assignments, indexed by `Fin 2`) that `printedReject α (lower p)` holds is 1;
   probability that `correctedReject α (lower p) (upper p)` holds is 0; and `α < 1` (a restatement of the hypothesis).
7. Arithmetic `(1/20)/2 = 1/40`, `1 - (1/20)/2 = 39/40 < 1`, and `printedReject (1/20) 1` (i.e. `1 < 1/40 ∨ 39/40 < 1`).

Observations.
- The randomisation law in items 5–6 is the uniform law on `Fin 2` (the index of the treated unit), not literally
  `uniformProbability fiveΩ` with `statistic`/`referenceStatistic`; this is equivalent because `fiveAssignment` is injective,
  `fiveΩ` is its image, item 2 gives mass 1/2 to each, and `fiveStatistic` uses the observed outcomes `fiveOutcomes`
  (which, by no effects, are the fixed outcomes under either assignment).
- The p-value is the lower inclusive tail `P(T ≤ t_obs)`; the corrected rule also uses the upper inclusive tail.

Junk values. `uniformProbability` divides by `|Fin 2| = 2` (no junk). `spearman` denominators are √(2·2) = 2 (positivity is
asserted, item 4). `nearestDistance` is applied only to nonempty treated-variant sets (asserted). `averageRank` uses ℕ→ℝ casts
of cardinalities (harmless). No `sInf`/`log`/truncated subtraction. No junk value affects the meaning.

## SAP.P030.T2 (Challenge/Part1.lean:12-13) : `T2WholeStatement` (Defs/WholeW1.lean:65)

Plain mathematics. A closed proposition about the ten-unit example with the constant ("null") outcome schedule `tenYnull`.
Conjunction of:

A. `T2Statement` (Part4:88):
   1. `tenYnull` constant in z for every binary assignment; `NoEffects tenΩ tenYnull`; `NoInterference tenΩ tenYnull`.
   2. `TableDesign` (Part4:11): `|tenΩ| = 10`, `|tableΩ| = 6`, `conditionalAssignments tenΩ tenS (tenAssignment 6) = tableΩ`,
      `P_{tenΩ}(z agrees with obs on fixed units) = 3/5`, each `tenAssignment j` treats exactly one unit,
      `P_{tenΩ}(z = tenAssignment j) = 1/10`, `P_{tableΩ}(z = tenAssignment(r+1)) = 1/6`, and that 1/6 equals the elementary
      conditional probability `(1/10)/(3/5)`.
   3. `TableNumerics` (Part4:23): `tableY = (1,3,2,1)`; the six distance rows
      `(1,6,7,8),(2,5,6,7),(3,4,5,6),(4,3,4,5),(5,2,3,4),(6,1,2,3)`; `tableRho = tableValues`; nonempty treated-variant sets;
      `rankSquares (tableDistances r) > 0`; `rankSquares tableY = 9/2`; strict order `-3/√10 < -5/6 < -1/√90 < 0`;
      every `tableRho r < 0`; roundings `-1/√90 ≈ -0.105`, `-5/6 ≈ -0.833`, `-3/√10 ≈ -0.949` to within 0.0005.
   4. For each r: `statistic tenS tenYnull tenG (tenAssignment(r+1)) = tableRho r`, and for all r, s:
      `referenceStatistic … (obs = tenAssignment(r+1)) (tenAssignment(s+1)) = tableRho s`.
   5. Lower tails over `Fin 6`: `P_s(tableRho s ≤ tableRho r) = (1,1,1,1/2,1/3,1/3)_r`; upper tails
      `P_s(tableRho r ≤ tableRho s) = (1/2,1/2,1/2,2/3,1,1)_r`.
   6. `∀ α, 0 < α ≤ 2/3`: `P_{z∼U(tableΩ)}[printedReject α (P_{w∼U(tableΩ)}(refStat(z,w) ≤ stat(z)))] = 1/2` and
      `P_{z∼U(tableΩ)}[correctedReject α (lower p(z)) (upper p(z))] = 0`.
   7. `1/20 < 1/2`.
B. `TableRankDetails` (WholeW1:16): fixed-outcome midranks `(3/2,4,3,3/2)`, centred `(-1,3/2,1/2,-1)`; the six distance midrank
   rows and centred rows; cross sums `(-1/2,-1/2,-1/2,-15/4,-9/2,-9/2)`; square sums `(5,5,5,9/2,5,5)`; squared correlations
   `(1/90,1/90,1/90,25/36,9/10,9/10)`; `1/90 < 25/36 < 9/10`.
C. `NullReferenceDetails` (WholeW1:47): fixed outcomes under every assignment equal `tableY`; `referenceStatistic obs z = statistic z`
   for all obs, z (imputation exact); observed-data lower tails `tenNullLowerP` at the six table assignments `(1,1,1,1/2,1/3,1/3)`,
   upper tails `tenNullUpperP` `(1/2,1/2,1/2,2/3,1,1)`; the actual statistic takes exactly 3 distinct values on the six assignments.
D. `∀ α, 0 < α ≤ 2/3, ∀ r`: `printedReject α (pL(r)) ↔ pL(r) = 1`, `printedReject α (pL(r)) ↔ r < 3` (units 2,3,4 treated), and
   `¬ correctedReject α (pL(r)) (pU(r))`.
E. `∀ α, 0 < α < 1/2`: `α < P_{z∼U(tableΩ)}[printedReject α (pL(z))]` (printed size exceeds α).

Here `tenNullLowerP z = P_{w∼U(tableΩ)}(refStat(z,w) ≤ stat(z))`, `tenNullUpperP z = P_{w∼U(tableΩ)}(stat(z) ≤ refStat(z,w))`
(inclusive tails, assignments counted once each).

Observations. The population is *constant* (no effects of any kind), so the null is true and the outcomes are not the paper's
illustrative adjacency model (`tenYexample` is not used); the fixed outcomes (1,3,2,1) coincide with the illustrative observed
fixed outcomes. The reference law is the uniform law on the six conditional assignments (= conditional of the uniform design
on `tenΩ`, item A2). The conditional size statement is over the random observed assignment z drawn from the conditional law.

Junk values. `uniformProbability` over `tableΩ` (card 6) and `Fin 6`, `tenΩ` (card 10): nonzero denominators. `spearman`
denominators positive (A3). `nearestDistance` nonempty (A3). `tenG`'s subtype coercion is a proof term only. Real decimal
literals `0.105` etc. are exact rationals. No junk value affects the meaning.

## SAP.P030.T3 (Challenge/Part1.lean:15-18) : `T3Statement` (Defs/Part4.lean:110)

Plain mathematics. Universe-polymorphic. Conjunction of (I) and `T1Statement` (II, read above).

(I) For every type A, every finitely supported probability law μ on A (support finset, masses ≥ 0 summing to 1) and every
`f : A → ℝ`, writing `F(x) = μ(f ≤ x)`, `G(x) = μ(f ≥ x)`, `pL(z) = F(f z)`, `pU(z) = G(f z)`:
1. `∀ x`: `G(x) = 1 - F(x) + μ(f = x)` and `1 - F(x) ≤ G(x)`.
2. `∀ u ∈ [0,1]`: `μ(pL ≤ u) ≤ u` and `μ(pU ≤ u) ≤ u` (super-uniformity of both inclusive-tail p-values).
3. `∀ α ∈ (0,1)`:
   a. `μ(pL < α/2 ∨ pU < α/2) ≤ μ(pL ≤ α/2) + μ(pU ≤ α/2)` (union bound);
   b. `μ(pL ≤ α/2) + μ(pU ≤ α/2) ≤ α`;
   c. `μ(correctedReject) ≤ α` (size control of the corrected two-tail rule);
   d. `∀ x`, `G(x) < α/2 → 1 - α/2 < F(x)`;
   e. `∀ x`, `correctedReject α (F x) (G x) → printedReject α (F x)` (corrected rejection region ⊆ printed rejection region);
   f. `∀ pL pU ∈ ℝ`: `min 1 (2 min pL pU) ≤ α ↔ pL ≤ α/2 ∨ pU ≤ α/2`;
   g. `μ(min 1 (2 min(pL,pU)) ≤ α) ≤ α` (size control of the conventional doubled-minimum p-value).

(II) `T1Statement`: the five-unit example where printed rejection probability is 1 and corrected is 0, exhibiting that the
inclusion (e) is strict and the printed rule does not control size.

Observations. (I) is stated for an abstract finite law μ and an abstract statistic f, i.e. the reference law of the
randomisation test is not instantiated: the connection to the paper's test (μ = conditional randomisation law, f = statistic,
p-values computed by imputation) is left to the reader / other theorems (validity of imputation under the null is *not* part
of T3). α = 1 and α = 0 are excluded (at α = 1 item f would be false for, e.g., pL = pU = 1, so the restriction to α < 1 is
needed for f; size control at α = 1 is trivial).

Junk values. `probability` is a finite sum over the support; masses off the support are irrelevant. No division. For empty
A no `FiniteLaw` exists (total would be 0 ≠ 1) — vacuous only there. `twoTailP` caps at 1 (standard). None affects meaning.

## SAP.P030.T4 (Challenge/Part1.lean:20-22) : `T4Statement = ¬ PrintedTwoTailedExactness` (Defs/Part4:131, Part2:54)

Plain mathematics. `PrintedTwoTailedExactness` is:
for all `N`, finite design support `Ω ⊆ {0,1}^N`, fixed-unit indicator `S`, observed assignment `a` with nonempty conditional set
`C = {z ∈ Ω : z_S = a_S}`, all potential outcomes `Y`, all statistics `g : (ℝ^{fixed units}) → {0,1}^N → ℝ`, if
`NoInterference Ω Y`, then for all `α ∈ [0,1]`:
`P_{z∼U(C)}[ printedReject α ( P_{w∼U(C)}( g(Y_S(z), w) ≤ g(Y_S(z), z) ) ) ] ≤ α`.

T4 asserts its negation: there exist N, Ω, S, a with C ≠ ∅, Y with no interference on Ω, a statistic g, and α ∈ [0,1] such that
the printed rule, applied to the observed-data lower inclusive-tail p-value, rejects with conditional probability > α.

Observations. The design law is uniform on Ω (hence uniform on C); the null is "no interference" (own-treatment-only outcomes),
which, because fixed units share treatment across C, makes the fixed outcomes constant on C. The statistic g is arbitrary
(any function of fixed outcomes and assignment). The universal assertion is "size ≤ α" (not "= α", despite the name
"Exactness"); refuting "≤ α" is stronger than refuting "= α". The negation requires an α strictly inside (0,1): at α = 0 the
printed rule never rejects (p ∈ [0,1]) and at α = 1 the bound is trivial, so a witness must be genuine. The T1 example
(constant statistic, p = 1) is a natural witness.

Junk values. `uniformProbability` divides by `|C|`, nonzero by hypothesis. `uniformProbability` in the inner p-value same.
The statistic g is arbitrary; no definitional junk can produce a spurious witness: since `C ≠ ∅` the outer probability is a
genuine proportion; p ∈ [0,1].

## SAP.P030.T5 (Challenge/Part1.lean:24-25) : `T5WholeStatement` (Defs/WholeW1.lean:83)

Plain mathematics. Universe-polymorphic (`u`). Conjunction of:

A. `T5Statement` (Part4:133):
   1. `tenYnull` constant in z; `TableDesign`; `TableNumerics` (as in T2).
   2. `OutcomeNullNonconstant` (Part4:47): `NoEffects tenΩ tenYnull`, `NoInterference tenΩ tenYnull`, conditional set = `tableΩ`,
      `FixedOutcomeNull tableΩ tenS tenYnull`, the assignments treating unit 2 and unit 5 lie in `tableΩ`, `TableNumerics`,
      and `statistic(unit 2 treated) ≠ statistic(unit 5 treated)` (−1/√90 ≠ −5/6).
   3. `statistic tenS tenYnull tenG (tenAssignment(r+1)) = tableRho r` for every r.
   4. `P_{s∼U(Fin 6)}(tableRho s ≤ tableRho 5) = 1/3` (observed row: unit 7 treated).
   5. For every type A, nonempty finset Ω, and t : A → ℝ constant on Ω, and z ∈ Ω: `P_{w∼U(Ω)}(t w ≤ t z) = 1`.
B. `TableRankDetails`, `NullReferenceDetails` (as in T2).
C. `tenNullLowerP (tenAssignment 6) = 1/3` (observed-data p-value, observation = unit 7 treated, computed via referenceStatistic).
D. `|1/3 − 0.333| < 0.0005`.
E. For every type A (universe u), nonempty finset Ω, t constant on Ω, z ∈ Ω: `P_{w∼U(Ω)}(t w = t z) = 1` (point mass).

Observations. The content is: a no-effects (hence no-interference) population for which the actual conditional statistic
`T(z) = g(Y_S(z), z)` is not constant over the conditional set (3 distinct values), together with numeric details, the observed
p-value 1/3, and the contrasting fact that a constant statistic gives p = 1. The statistic here is the paper's Spearman
distance–outcome statistic `tenG`.

Junk values. As in T2. Clause 5/E: `uniformProbability` over a nonempty Ω (no division by zero). No junk value affects meaning.
