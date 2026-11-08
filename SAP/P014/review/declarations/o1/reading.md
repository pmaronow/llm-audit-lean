# Blind reading (written before opening claims.json / record.json)

Common objects (SAP/P014/Defs/Part1.lean, Part2.lean):

- `FiniteDistribution α` (Part1:12): a finset `atoms` and a weight function `weight : α → ℝ`; no validity built in.
  `IsDistribution L` (Part1:16): all atom weights `> 0` and `∑_{atoms} weight = 1`. Weights off the atoms are ignored
  by every derived notion below (all sums run over `atoms`).
- `expectation L f = ∑_{x∈atoms} w(x) f(x)`; `probability L P = ∑_{x∈atoms, P x} w(x)` (classical decidability).
- `pushforward L f` (Part1:26): atoms `f '' atoms`, weight `b ↦ probability L (f · = b)` — the image law.
- `TreatmentVector N = Fin N → Bool`, `PotentialOutcomes N = Fin N → TreatmentVector N → ℝ` (unit i's outcome under the
  whole assignment vector: arbitrary interference allowed).
- `thresholdAssignment x i = decide (0 ≤ x i)` (treated iff score ≥ 0); `insideWindow b x ↔ -b ≤ x ≤ b`;
  `windowSubjects b x = {i | -b ≤ x i ≤ b}`; `windowCDF S x t = #{i∈S : x i ≤ t} / |S|`.
- `armAssignments L i a = {z ∈ atoms : z i = a}`; `armProbability L i a = ∑_{z∈armAssignments} w(z) = P_L(Z_i = a)`;
  `armMoment L y i a = ∑_{z∈armAssignments} w(z) y_i(z) = E_L[1{Z_i=a} Y_i(Z)]`.
- `supportAverage L y i a = (∑_{z∈armAssignments} y_i(z)) / #armAssignments` — unweighted average over supported
  assignments with z_i = a (the "printed" average; each supported vector counted once).
- `conditionalAverage L y i a = armMoment / armProbability = E_L[Y_i(Z) | Z_i = a]` when the denominator is positive.
- `windowContrast S f = (∑_{i∈S} (f i true − f i false)) / |S|`.
- `armSize S z a = #{i∈S : z i = a}` (as a real); `observedArmTotal S y z a = ∑_{i∈S, z i = a} y_i(z)`;
  `differenceOfMeans S y z = observedArmTotal(true)/armSize(true) − observedArmTotal(false)/armSize(false)`.
- `ConditionallyUniform L S` (Part1:85): ∀ i∈S, ∀ a, ∀ z ∈ armAssignments L i a,
  `w(z)/P_L(Z_i=a) = 1/#armAssignments L i a` — the law of Z given Z_i = a is uniform on its support.
- `Noninterfering S y` (Part1:90): ∀ i∈S, y_i(z) depends only on z_i.
- `PositiveArms L S`: ∀ i∈S, ∀ a, `P_L(Z_i = a) > 0`.
- `DistinctNoTies L X S` (Part1:97): ∀ i,j ∈ S, i ≠ j → `P_L(X_i = X_j) = 0`.
- `PrintedLocalConditions L X b S` (Part1:103): (1) every atom has window `{i : |X_i| ≤ b} = S`; (2) a common window
  empirical CDF across atoms; (3) every supported full score vector has probability `1/|S|!`; (4) `DistinctNoTies`;
  (5) every atom has `0 < #treated in S < |S|`.
- `eventProbability μ P = (μ {ω | P ω}).toReal` (Part2:10). For a probability measure `μ` this is finite, so `toReal`
  is faithful; for a non-measurable set it is outer measure (only relevant if a hypothesis lacks measurability).
- `CorrectedLocalConditions μ X b S v` (Part2:13): (i) each coordinate `X_i` measurable; (ii) `P(|X_i| ≤ b) = 1` for
  i ∈ S and `= 0` for i ∉ S (window a.s. equal to S); (iii) for every permutation σ of S,
  `P(∀ i∈S, X_i = v(σ i)) = 1/|S|!` (with v injective, these |S|! disjoint events exhaust the mass, so the local score
  vector is a.s. a uniformly random arrangement of the fixed values v).
- `permutationAssignment S v c σ` (Part2:28): treatment vector with `z_i = [v(σ i) ≥ 0]` for i ∈ S and `z_i = c_i` outside.

---

## SAP.P014.T2 (Challenge/Part1.lean:21) — `T2WholeStatement = T2AssignmentWholePart ∧ T2ScoreWholePart`

### (A) `T2AssignmentWholePart` (WholeW1:81)
For every universe-u type Ω with σ-algebra, probability measure μ, N ∈ ℕ, **measurable** Z : Ω → {0,1}^N, every
finset S ⊆ Fin N, every potential-outcome function y (y_i(z) arbitrary real for every full vector z), every m ∈ ℕ with
**0 < m < |S|**, if **a.s. #{i∈S : Z_i = 1} = m** and **∀ i∈S, P(Z_i = 1) = m/|S|**, then `WeightedIdentity μ Z S y m`,
where with L = `assignmentLaw μ Z` (WholeW1:17; atoms = {z : P(Z=z) > 0}, weight z = P(Z = z)):
1. L is a valid finite distribution;
2. every i∈S has P_L(Z_i=a) > 0 for both a;
3. ∀ i∈S, ∀ a: P_L(Z_i=a) = P(Z_i=a); `conditionalAverage L y i a` = `eventConditionalMean` =
   (∫_{Z_i=a} y_i(Z) dμ)/P(Z_i=a) (WholeW1:27) — i.e. E[Y_i(Z) | Z_i = a]; y_i(Z) and 1{Z_i=a} y_i(Z) are integrable;
4. ∀ i∈S: P_L(Z_i=1) = m/|S|, P_L(Z_i=0) = (|S| − m)/|S| (real subtraction);
5. every supported z has #treated = m, #control = |S| − m, both > 0, and
   DM(z) = T_1(z)/m − T_0(z)/(|S|−m);
6. the same a.s. for Z(ω);
7. ∀ i∈S, ∀ a: ∫ 1{Z_i=a} y_i(Z) dμ = armMoment = P(Z_i=a)·E[Y_i|Z_i=a];
8. armMoment(true) = (m/|S|)·E[Y_i|Z_i=1], armMoment(false) = ((|S|−m)/|S|)·E[Y_i|Z_i=0];
9. DM(Z) integrable and ∫ DM(Z) dμ = E_L[DM];
10. ∫ DM(Z) = (∑_i armMoment_i(1))/m − (∑_i armMoment_i(0))/(|S|−m);
11. = (1/m)(m/|S|) ∑_i E[Y_i|Z_i=1] − (1/(|S|−m))((|S|−m)/|S|) ∑_i E[Y_i|Z_i=0];
12. = windowContrast S (E[Y_·|Z_·=·]) = |S|⁻¹ ∑_{i∈S} (E[Y_i(Z)|Z_i=1] − E[Y_i(Z)|Z_i=0]);
13. windowContrast = (∑ E[Y_i|Z_i=1] − ∑ E[Y_i|Z_i=0])/|S|.

So: fixed treated count m in the window + common propensity m/|S| ⇒ the unweighted difference in means is unbiased
for the window average of the probability-weighted (conditional-expectation) own-arm contrasts, with every displayed
step stated.

### (B) `T2ScoreWholePart` (WholeW1:90)
For every Ω, prob. μ, scores X : Ω → ℝ^N, b, S, v : S → ℝ, m, if 0 < b, v injective, all v-values in [−b,b],
0 < m < |S|, #{i∈S : v_i ≥ 0} = m, and `CorrectedLocalConditions μ X b S v`, then with Z = threshold(X):
a.s. #treated in S = m; ∀ i∈S, P(Z_i = 1) = m/|S|; and for every y, `WeightedIdentity μ Z S y m` (the whole list
above). Outside coordinates of X are only required measurable and a.s. outside the window; their law and dependence on
the local arrangement are unrestricted.

### Quantifiers
Universal over Ω (in a fixed universe u — harmless), μ, Z/X, S, y, m. No existential.

### Junk values
- `conditionalAverage` divides by armProbability: conclusion 2 asserts positivity, so not junk.
- `eventConditionalMean` divides by `eventProbability`: positive by 2–3; the set integral is of an integrable function
  (asserted in 3).
- `differenceOfMeans` divides by armSize: asserted positive on all atoms and a.s.
- `windowContrast` divides by |S| > m > 0.
- `(S.card : ℝ) − m` is real subtraction (positive since m < |S|). `m : ℕ` cast to ℝ; 0 < m.
- `eventProbability` = toReal of a probability-measure value (finite); sets are measurable since Z (resp. X_i) are.
- Bochner integrals: integrability asserted in the conclusion, so the integral equalities are meaningful.
None affects the meaning.

### Nonvacuity
Hypotheses are satisfiable: Ω = Bool with μ = ½δ_true + ½δ_false, N = 2, S = univ, Z ω = (ω, ¬ω), m = 1;
for (B), X ω = (1,−1) or (−1,1), v = (1,−1), b = 2 (compiled in scratch, see findings).

---

## SAP.P014.T8 (Challenge/Part1.lean:60) — `T8Statement` (Part5:97)
For every N, every S ⊆ Fin N, every f : Fin N → Bool → ℝ, if S is nonempty, then
`(∑_{i∈S} (f i 1 − f i 0))/|S| = (∑_{i∈S} f i 1 − ∑_{i∈S} f i 0)/|S|`.
Pure algebra (linearity of the finite sum). The hypothesis `S.Nonempty` is not needed for truth (with |S| = 0 both
sides are 0/0 = 0 in Lean), but it only restricts to the meaningful case.

Junk values: division by |S|; excluded by `S.Nonempty`. None.
Nonvacuity: S = {0} ⊆ Fin 1, any f.

---

## SAP.P014.T3 (Challenge/Part1.lean:29) — `T3Statement = Conditional ∧ Uniform ∧ FixedOutside ∧ Noninterference ∧ Necessity` (Part4:107)

(a) `T3ConditionalPart` (Part4:43): ∀ N, L valid finite law on {0,1}^N, S, y, m with 0 < m < |S|, every atom has
exactly m treated in S, ∀ i∈S P_L(Z_i=1) = m/|S|, and `ConditionallyUniform L S` ⇒
∀ i∈S, ∀ a: {z∈atoms : z_i = a} ≠ ∅ and supportAverage = conditionalAverage; E_L[DM] = windowContrast S supportAverage;
and windowContrast(supportAverage) = (∑ sA(1) − ∑ sA(0))/|S|.
I.e. conditional uniformity of Z given Z_i makes the printed (support-average) target correct.

(b) `T3UniformPart` (Part4:56): ∀ valid L, S: if every atom has weight 1/|atoms| (uniform law on its support), then
`ConditionallyUniform L S`.

(c) `T3FixedOutsidePart` (Part4:61): ∀ Ω, prob μ, X, b, S, v, valid finite A on {0,1}^N, c ∈ {0,1}^N, y, m, with
0 < b, v injective, v ⊂ [−b,b], 0 < m < |S|, #{v ≥ 0} = m, `CorrectedLocalConditions μ X b S v`, A equal to the law of
threshold(X) (∀ z, P(threshold(X) = z) = A.weight z if z∈A.atoms, 0 otherwise), and a.s. threshold(X)_i = c_i for all
i ∉ S ⇒ |A.atoms| = C(|S|, m); every atom z is hit by exactly m!(|S|−m)! permutations σ (via permutationAssignment)
and has weight m!(|S|−m)!/|S|! = 1/C(|S|,m); every atom has m treated in S; common propensity m/|S|;
ConditionallyUniform A S; E_A[DM] = windowContrast S (supportAverage A y); and every z agreeing with c off S with m
treated in S is an atom with that count and weight 1/C(|S|,m). (ℕ subtraction |S|−m inside factorial: m < |S|, safe.)

(d) `T3NoninterferencePart` (Part4:90): valid L, S, y, m, 0<m<|S|, fixed count m, common propensity m/|S|, and
`Noninterfering S y` ⇒ ∀ i∈S, ∀ a, ∀ z with z_i = a: supportAverage L y i a = y_i(z) = conditionalAverage L y i a;
and E_L[DM] = windowContrast S supportAverage.

(e) `T3NecessityPart` (Part4:100): valid L, i, a with P_L(Z_i=a) > 0: if supportAverage L y i a =
conditionalAverage L y i a for **every** y, then the conditional law of Z given Z_i = a is uniform on its support.

### Junk values
- `supportAverage` divides by #armAssignments: (a),(c),(d) — nonempty because propensities m/|S| ∈ (0,1); (a) states
  nonemptiness; (e) — positive arm probability ⇒ nonempty.
- `conditionalAverage` divides by armProbability: positive in all parts where used ((a),(d) by m/|S| ∈ (0,1); (e) by
  hypothesis).
- `ConditionallyUniform` is vacuous for an arm with no supported assignments (no z) — not reachable under (a)'s hypotheses.
- `differenceOfMeans` denominators: m and |S|−m > 0 on every atom.
- ℕ subtraction `S.card - m` in (c) under m < |S|: exact. `Nat.choose` cast: positive.
- `eventProbability` in (c) on measurable sets (X_i measurable). None affects the meaning.

---

## SAP.P014.T7 (Challenge/Part1.lean:56) — `T7Statement` (Part5:91)

(a) `T7GeneralPart` (Part5:69): ∀ Ω, prob μ, X : Ω → ℝ^N (no measurability), S:
 1. literal clause L := (∀ i∈S, ∀ j∈S, P(X_i = X_j) = 0) holds ⇔ S = ∅;
 2. ∀ i∈S, P(X_i = X_i) = 1;
 3. L ⇔ (∀ i≠j in S, P(X_i = X_j) = 0) ∧ (∀ i∈S, P(X_i = X_i) = 0) (literal = corrected + diagonal);
 4. ∀ m with 0 < m < |S|: |S| ≥ 2, S ≠ ∅ and L fails.
(b) `T7LocalPart` (Part5:81): ∀ Ω, prob μ, X, b, S, v, m with 0 < b, |S| ≥ 2, v injective, v ⊂ [−b,b], 0<m<|S|,
#{v ≥ 0} = m, `CorrectedLocalConditions` ⇒ ∀ distinct i,j ∈ S, P(X_i = X_j) = 0.
(c) `localThree.card = 3`; `DistinctNoTies uniformSix scoresK localThree` for K = 1, 5, 9 (the three specified
six-row designs; first three coordinates of each row are pairwise distinct).

### Junk values
- `eventProbability` of a possibly non-measurable set in (a): only the diagonal event (= Ω, measure 1) is evaluated in
  (a)1, (a)2, (a)4; (a)3 is propositional. In (b) the sets are measurable (X_i measurable). No effect.
- `probability` on finite laws in (c): plain sums. No effect.

---

## SAP.P014.T4 (Challenge/Part1.lean:34) — `T4Statement` (Part3:40)
A closed proposition about one explicit design (no quantifiers over data):
- Ω = Fin 6 with uniform weights 1/6 (`uniformSix`), valid;
- scores `scores1` (Part2:35), N = 4: rows (−2,−1,1,3), (−2,1,−1,−3), (−1,−2,1,−3), (−1,1,−2,−3), (1,−2,−1,−3),
  (1,−1,−2,−3); window b = 2, S = {0,1,2} (`localThree`);
- `assignmentDistribution` = image of `allocations` (Part2:39) under uniformSix: (0,0,1,1) 1/6, (0,1,0,0) 1/3,
  (0,0,1,0) 1/6, (1,0,0,0) 1/3 — valid;
- `PrintedLocalConditions uniformSix scores1 2 localThree` (window = S on every row; common window CDF; each full
  score vector has mass 1/3! = 1/6; no ties between distinct window subjects; 0 < #treated < 3 on every row);
- threshold(scores1 ω) = allocations ω for every ω;
- every permutation σ of (−2,−1,1) has probability 1/6 (equiprobable local permutations);
- `CommonWitnessCounts`: every assignment atom has exactly 1 treated in S, and P(Z_i = 1) = 1/3 for i ∈ S;
- `PositiveArms`;
- outcomes `outcomes1` (Part2:43): y_i(z) = z_3 for i ≠ 3, y_3 = 0 (window units' outcomes depend on the outside unit's
  treatment);
- E_L[DM] = 0; windowContrast S (supportAverage) = −1/18; E_L[DM] ≠ windowContrast(supportAverage).

Hand check: DM(z) = z_3 − z_3 = 0 on every atom; support averages: unit 0: (0, 1/3), unit 1: (0, 1/3),
unit 2: (1/2, 0) ⇒ (−1/3 − 1/3 + 1/2)/3 = −1/18. Consistent.

The docstring says "The printed claim is false … refuted by the explicit design satisfying the printed clauses and
equiprobable local permutations, with positive arm probabilities, expectation zero and target −1/18": the statement
supports exactly this *if* the printed claim is "under the printed local conditions, E[DM] equals the window average of
support-average contrasts". Whether outcomes with interference from an outside unit are within the printed claim's
scope, and whether the paper's printed average is the support average, must be checked against the claim.

### Junk values
- `supportAverage` divides by #armAssignments: each arm nonempty here (computed). Not junk.
- `windowCDF` division by |S| = 3. `differenceOfMeans` denominators 1 and 2 on every atom. `pushforward` weights are
  genuine probabilities. None affects meaning.
- `PrintedLocalConditions` reads the no-ties clause for distinct subjects only (docstring Part1:101 says so); the
  literal clause (with i = j) is unsatisfiable (T7).
