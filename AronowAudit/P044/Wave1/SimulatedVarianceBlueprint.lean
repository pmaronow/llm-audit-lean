import AronowAudit.P044.P044_NetworkSpillovers

/-!
# P044-T11: finite simulated exposure probabilities

P044 pp. 213 and 217 (PDF pp. 5, 9) describe "conservative" variance approximations
computed from finite simulated exposure probabilities. `PrintedSimulatedConservativeness`
quantifies over finite designs with true marginal support, ordered distinct banks drawn
by `distinctBankMass`, and smoothed inputs.

The counterexample has N = 12, three disjoint K4 cliques (`cliqueAdj`), and the design
uniform on the 66 treat-two profiles (`cliqueMass`, the pushforward of the uniform law on
`Fin 66` through `cliqueAssignments`). It uses R = 65, all outcomes 1 (`yR`), a = d01,
and b = d00. The first conjunct, with independent actual assignment, fails:
`E(V̂) - Var(T) = 1040129476423/2326402995840 - 113448938731/232640299584
 = -953130413/23499020160 < 0`. The included-first-bank regime is not needed.

The propositions below separate the finite counts, bank law, and moment identities.
Counts involve 66 profiles and 144 ordered unit pairs. Type counting reduces the
rational sums to 4 or 48 terms. Helper propositions such as `DesignFacts` and
`BankMassFormula` name intermediate conclusions; dependencies appear as hypotheses.
-/

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

/-- The negation of the printed conservativeness proposition. -/
def Target : Prop := ¬ PrintedSimulatedConservativeness

/-! ## Witness data -/

/-- The design: pushforward of the uniform law on the 66 enumerated treat-two profiles. -/
def cliqueMass (z : Assignment 12) : ℝ :=
  ∑ r : Fin 66, if cliqueAssignments r = z then (1 / 66 : ℝ) else 0

/-- Real outcome schedule: canonical embedding of `cliqueY` (all ones). -/
def yR : Fin 12 → Exposure → ℝ := fun i d => ((cliqueY i d : ℚ) : ℝ)

/-- Complete joint exposure-count table of the full design, for a unit pair classified by
`(i = j, same clique)` and an ordered label pair. The class `(true, false)` is impossible. -/
def cliqueJointTable : Bool → Bool → Exposure → Exposure → ℕ
  | true, _, a, b => if a = b then cliqueFullCount a else 0
  | false, true, .d00, .d00 => 28
  | false, true, .d01, .d01 => 17
  | false, true, .d01, .d10 => 8
  | false, true, .d01, .d11 => 2
  | false, true, .d10, .d01 => 8
  | false, true, .d11, .d01 => 2
  | false, true, .d11, .d11 => 1
  | false, true, _, _ => 0
  | false, false, .d00, .d00 => 6
  | false, false, .d00, .d01 => 15
  | false, false, .d00, .d10 => 4
  | false, false, .d00, .d11 => 3
  | false, false, .d01, .d00 => 15
  | false, false, .d01, .d01 => 9
  | false, false, .d01, .d10 => 3
  | false, false, .d10, .d00 => 4
  | false, false, .d10, .d01 => 3
  | false, false, .d10, .d10 => 1
  | false, false, .d11, .d00 => 3
  | false, false, _, _ => 0

/-- Number of ordered unit pairs `(i, j)` in each class `(i = j, same clique)`:
12 diagonal, 36 distinct same-clique, 96 different-clique. -/
def cliquePairClassCount : Bool → Bool → ℕ
  | true, true => 12
  | true, false => 0
  | false, true => 36
  | false, false => 96

/-- Smoothed marginal inputs computed from a bank. -/
def bankW (bank : Fin 65 → Assignment 12) : Fin 12 → Exposure → ℝ :=
  smoothedWeight (fun r => exposure cliqueAdj (bank r))

/-- Smoothed joint inputs computed from a bank. -/
def bankQ (bank : Fin 65 → Assignment 12) : Fin 12 → Fin 12 → Exposure → Exposure → ℝ :=
  smoothedJoint (fun r => exposure cliqueAdj (bank r))

/-- The independent-regime law of (bank, actual assignment). -/
def indepMass (P : FiniteDesign (Assignment 12))
    (x : (Fin 65 → Assignment 12) × Assignment 12) : ℝ :=
  distinctBankMass P x.1 * P.mass x.2

/-- The HT contrast in the independent regime. -/
def indepT (x : (Fin 65 → Assignment 12) × Assignment 12) : ℝ :=
  htContrast (fun z => exposure cliqueAdj z) yR (bankW x.1) .d01 .d00 x.2

/-- The variance estimate in the independent regime. -/
def indepV (x : (Fin 65 → Assignment 12) × Assignment 12) : ℝ :=
  varianceEstimate (fun z => exposure cliqueAdj z) yR (bankW x.1) (bankQ x.1) .d01 .d00 x.2

/-- Real embedding of the omission-formula weights `cliqueWeights t`. -/
def castW (t : Fin 66) : Fin 12 → Exposure → ℝ := fun i a => ((cliqueWeights t i a : ℚ) : ℝ)

/-- Real embedding of the omission-formula joints `cliqueJoints t`. -/
def castJ (t : Fin 66) : Fin 12 → Fin 12 → Exposure → Exposure → ℝ :=
  fun i j a b => ((cliqueJoints t i j a b : ℚ) : ℝ)

/-! ## Finite counts -/

/-- The 66 enumerated treat-two profiles are distinct. The treated set of
`cliqueAssignments r` is `{u, v}` with `(u, v) = cliquePairs r`, `u < v`,
and `cliquePairs` is injective. -/
def N1 : Prop := Function.Injective cliqueAssignments

/-- The full-design marginal counts are 3, 8, 27, and 28 at every unit.
These counts can be obtained by reindexing `r ↦ cliquePairs r` onto increasing pairs. -/
def N2 : Prop := ∀ (i : Fin 12) (a : Exposure), exposureCount cliqueF i a = cliqueFullCount a

/-- Every joint count of the full design is the class table entry. -/
def N3 : Prop :=
  ∀ (i j : Fin 12) (a b : Exposure),
    jointCount cliqueF i j a b = cliqueJointTable (decide (i = j)) (decide (i.val / 4 = j.val / 4)) a b

/-! ## Design and bank law -/

/-- Conclusion of N4: `cliqueMass` is a probability law and expectations under it are
averages over the 66 enumerated profiles. -/
def DesignFacts : Prop :=
  (∀ z, 0 ≤ cliqueMass z) ∧ (∑ z, cliqueMass z = 1) ∧
    ∀ F : Assignment 12 → ℝ, ∑ z, cliqueMass z * F z = (∑ r, F (cliqueAssignments r)) / 66

/-- The assignment pushforward preserves finite expectations; injectivity is not needed. -/
def N4 : Prop := DesignFacts

/-- Conclusion of N5: the support has 66 points (so `R = 65 ≤ #support`) and every unit has
true contrasted-label probabilities `27/66 = 9/22` and `28/66 = 14/33`. -/
def SupportMarginals : Prop :=
  (Finset.univ.filter (fun z => 0 < cliqueMass z)).card = 66 ∧
    ∀ i : Fin 12, marginal cliqueMass (fun z => exposure cliqueAdj z) i .d01 = 9 / 22 ∧
      marginal cliqueMass (fun z => exposure cliqueAdj z) i .d00 = 14 / 33

/-- From N1 (support equal to the range, mass 1/66 on it),
N2 (`cliqueF_is_exposure` and counts), and N4. -/
def N5 : Prop := N1 → N2 → DesignFacts → SupportMarginals

/-- Conclusion of N6: exact `distinctBankMass` of an ordered 65-bank. -/
def BankMassFormula : Prop :=
  ∀ P : FiniteDesign (Assignment 12), P.mass = cliqueMass → ∀ b : Fin 65 → Assignment 12,
    ((Function.Injective b ∧ ∀ r, b r ∈ Set.range cliqueAssignments) →
        distinctBankMass P b = 1 / (Nat.factorial 66 : ℝ)) ∧
    (¬ (Function.Injective b ∧ ∀ r, b r ∈ Set.range cliqueAssignments) →
        distinctBankMass P b = 0)

/-- A supported injective bank has mass
`∏_{r<65} (1/66)/(1 - r/66) = ∏_{r<65} 1/(66 - r) = 1/66!`; a non-injective bank
has mass 0 by definition; an injective bank with an unsupported entry has a zero factor
(`0 / x = 0`). Uses N1 (mass exactly 1/66 at each enumerated profile) and N4. -/
def N6 : Prop := N1 → DesignFacts → BankMassFormula

/-- Conclusion of N7: sums against the bank law are sums over embeddings `Fin 65 ↪ Fin 66`. -/
def BankSumFormula : Prop :=
  ∀ P : FiniteDesign (Assignment 12), P.mass = cliqueMass →
    ∀ G : (Fin 65 → Assignment 12) → ℝ,
      ∑ b, distinctBankMass P b * G b =
        (∑ σ : Fin 65 ↪ Fin 66, G (fun r => cliqueAssignments (σ r))) / (Nat.factorial 66 : ℝ)

/-- Banks of positive mass are exactly `cliqueAssignments ∘ σ` for a unique embedding
`σ` (N1); reindex the sum over the support. -/
def N7 : Prop := N1 → BankMassFormula → BankSumFormula

/-- Conclusion of N8: summing a function of the omitted point over all embeddings. -/
def EmbeddingFiberSum : Prop :=
  ∀ (F : (Fin 65 ↪ Fin 66) → ℝ) (g : Fin 66 → ℝ),
    (∀ (σ : Fin 65 ↪ Fin 66) (t : Fin 66), Finset.univ.map σ = Finset.univ.erase t → F σ = g t) →
      ∑ σ, F σ = (Nat.factorial 65 : ℝ) * ∑ t, g t

/-- Every embedding misses exactly one point (cardinality 65 of the image);
the fibre of `t` is in bijection with `Fin 65 ↪ {x // x ≠ t}` of cardinality `65!`.
Summing over these fibres gives the stated identity. -/
def N8 : Prop := EmbeddingFiberSum

/-- Conclusion of N9: a bank enumerating the 66 profiles minus `t` (in any order) has exactly
the omission-formula smoothed inputs, at every label. -/
def RetainedInputs : Prop :=
  ∀ (σ : Fin 65 ↪ Fin 66) (t : Fin 66), Finset.univ.map σ = Finset.univ.erase t →
    bankW (fun r => cliqueAssignments (σ r)) = castW t ∧
      bankQ (fun r => cliqueAssignments (σ r)) = castJ t

/-- Counts over the bank are counts over `univ.erase t` (order-invariant,
`cliqueF_is_exposure`), equal to full counts minus the omitted indicator
(as in `count_delete_atom`); full counts by N2 and N3.
The function `cliqueFullJoint` agrees with `cliqueJointTable` at every label.
Casting uses `(65:ℝ)+1 = 66`. -/
def N9 : Prop := N2 → N3 → RetainedInputs

/-- Conclusion of N10: every statistic of (bank inputs, actual assignment) has the same
expectation under the independent bank/assignment law as under the reduced law
`cliqueJointMass false` (uniform 1/4356 on (omitted t, actual r)). -/
def IndependentTransport : Prop :=
  ∀ P : FiniteDesign (Assignment 12), P.mass = cliqueMass →
    ∀ φ : (Fin 12 → Exposure → ℝ) → (Fin 12 → Fin 12 → Exposure → Exposure → ℝ) →
        Assignment 12 → ℝ,
      expect (indepMass P) (fun x => φ (bankW x.1) (bankQ x.1) x.2) =
        expect (fun x : Fin 66 × Fin 66 => ((cliqueJointMass false x : ℚ) : ℝ))
          (fun x => φ (castW x.1) (castJ x.1) (cliqueAssignments x.2))

/-- Split the product sum, apply N4 to the actual assignment, N7, then N8 with
`g t = (∑ r, φ (castW t) (castJ t) (cliqueAssignments r)) / 66` justified by N9;
`65!/66!/66 = 1/4356`. -/
def N10 : Prop :=
  DesignFacts → BankSumFormula → EmbeddingFiberSum → RetainedInputs → IndependentTransport

/-- Conclusion of N11: at the reduced law's points the real statistics are the embeddings of
the rational `cliqueT`, `cliqueV`. -/
def StatisticIdentification : Prop :=
  ∀ t r : Fin 66,
    htContrast (fun z => exposure cliqueAdj z) yR (castW t) .d01 .d00 (cliqueAssignments r) =
        ((cliqueT t r : ℚ) : ℝ) ∧
      varianceEstimate (fun z => exposure cliqueAdj z) yR (castW t) (castJ t) .d01 .d00
          (cliqueAssignments r) = ((cliqueV t r : ℚ) : ℝ)

/-- `cliqueF_is_exposure`, then `ratCast_htContrast` and `ratCast_varianceEstimate`. -/
def N11 : Prop := StatisticIdentification

/-! ## Moments of the reduced law -/

/-- Conditional moments given the omitted profile `t` in the independent regime. -/
def ConditionalMoments : Prop :=
  ∀ t : Fin 66,
    expect (fun _ : Fin 66 => (1 / 66 : ℚ)) (cliqueT t) = cliqueConditionalMean t false ∧
    expect (fun _ : Fin 66 => (1 / 66 : ℚ)) (fun z => cliqueT t z ^ 2) =
      cliqueConditionalSecond t false ∧
    expect (fun _ : Fin 66 => (1 / 66 : ℚ)) (cliqueV t) = cliqueConditionalV t false

/-- The independent conditional moments follow from exhaustive exposure probabilities
and the marginal and joint counts N2 and N3. -/
def N12 : Prop := N2 → N3 → ConditionalMoments

/-- Conclusion of N13: one-unit type counting over (omitted profile, unit). -/
def TypeCount1 : Prop :=
  ∀ Φ : Exposure → ℚ,
    ∑ t : Fin 66, ∑ i : Fin 12, Φ (cliqueF t i) = 12 * ∑ d : Exposure, (cliqueFullCount d : ℚ) * Φ d

/-- Swap the sums and group by the exposure label, using N2. -/
def N13 : Prop := N2 → TypeCount1

/-- Conclusion of N14: pair type counting over (omitted profile, unit pair). -/
def TypeCount2 : Prop :=
  ∀ Ψ : Bool → Bool → Exposure → Exposure → ℚ,
    ∑ t : Fin 66, ∑ i : Fin 12, ∑ j : Fin 12,
        Ψ (decide (i = j)) (decide (i.val / 4 = j.val / 4)) (cliqueF t i) (cliqueF t j) =
      ∑ e : Bool, ∑ s : Bool, (cliquePairClassCount e s : ℚ) *
        ∑ d : Exposure, ∑ d' : Exposure, (cliqueJointTable e s d d' : ℚ) * Ψ e s d d'

/-- Swap sums, group the inner sum by `(cliqueF t i, cliqueF t j)` and use N3,
then group unit pairs by class, with class sizes 12, 36, and 96. -/
def N14 : Prop := N3 → TypeCount2

/-- Conclusion of N15: average conditional mean of the HT contrast. -/
def MeanValue : Prop :=
  expect (fun _ : Fin 66 => (1 / 66 : ℚ)) (fun t => cliqueConditionalMean t false) = -67 / 53592

/-- The summand of `cliqueConditionalMean t false` at unit `i` is a function of
`cliqueF t i`; applying TypeCount1 reduces it to a 4-term rational sum. -/
def N15 : Prop := TypeCount1 → MeanValue

/-- Conclusion of N16: average conditional second moment of the HT contrast. -/
def SecondValue : Prop :=
  expect (fun _ : Fin 66 => (1 / 66 : ℚ)) (fun t => cliqueConditionalSecond t false) =
    234399385 / 480661776

/-- The `(i, j)` summand of `cliqueConditionalSecond t false` is a function of
`(i = j, same clique, cliqueF t i, cliqueF t j)` (relevant `cliqueFullJoint` entries depend
only on the class); applying TypeCount2 reduces it to a 48-term rational sum. -/
def N16 : Prop := TypeCount2 → SecondValue

/-- Average over the omitted profile of the same-label double sum
`V̂_a` (a = d01) of the expected variance estimate. -/
def SameLabelValueD01 : Prop :=
  expect (fun _ : Fin 66 => (1 / 66 : ℚ)) (fun t =>
      expectedTotalVariance (cliqueObservationMarginal t false) (cliqueObservationJoint t false)
        cliqueY (cliqueWeights t) (cliqueJoints t) .d01) = 3564985 / 349272

/-- The `(i, j)` summand of `expectedTotalVariance ... .d01` (both guards `0 < q`
and `i ≠ j ∧ q = 0` included) is a function of
`(i = j, same clique, cliqueF t i, cliqueF t j)`; applying TypeCount2 reduces it
to a 48-term rational sum. -/
def N17 : Prop := TypeCount2 → SameLabelValueD01

/-- The analogue of N17 for the label d00. -/
def SameLabelValueD00 : Prop :=
  expect (fun _ : Fin 66 => (1 / 66 : ℚ)) (fun t =>
      expectedTotalVariance (cliqueObservationMarginal t false) (cliqueObservationJoint t false)
        cliqueY (cliqueWeights t) (cliqueJoints t) .d00) = 188343164 / 20398455

/-- As N17. -/
def N18 : Prop := TypeCount2 → SameLabelValueD00

/-- Average of the cross-label double sum `Ĉ_ab`; the cross zero adjustment
includes every same-clique pair and the diagonal. -/
def CrossLabelValue : Prop :=
  expect (fun _ : Fin 66 => (1 / 66 : ℚ)) (fun t =>
      expectedTotalCovariance (cliqueObservationMarginal t false) (cliqueObservationJoint t false)
        cliqueY (cliqueWeights t) (cliqueJoints t) .d01 .d00) = -3863683 / 171941

/-- As N17 for
`expectedTotalCovariance ... .d01 .d00`. -/
def N19 : Prop := TypeCount2 → CrossLabelValue

/-- Conclusion of N20: average conditional expected variance estimate. -/
def VarianceEstimateValue : Prop :=
  expect (fun _ : Fin 66 => (1 / 66 : ℚ)) (fun t => cliqueConditionalV t false) =
    1040129476423 / 2326402995840

/-- The conditional identity is `E(V|t) = (B_a + B_b - 2C)/144`, where `B_a` and
`B_b` are the same-label sums and `C` is the cross-label sum. Unfold
`cliqueConditionalV` and `expectedVariance`, use `(N : ℚ)^2 = 144`, split the
expectation linearly, and combine N17-N19. -/
def N20 : Prop :=
  SameLabelValueD01 → SameLabelValueD00 → CrossLabelValue → VarianceEstimateValue

/-- Conclusion of N21: the three real moments of the printed independent regime. -/
def RealMoments : Prop :=
  ∀ P : FiniteDesign (Assignment 12), P.mass = cliqueMass →
    expect (indepMass P) indepT = -67 / 53592 ∧
    expect (indepMass P) (fun x => indepT x ^ 2) = 234399385 / 480661776 ∧
    expect (indepMass P) indepV = 1040129476423 / 2326402995840

/-- Apply IndependentTransport to the HT contrast, its square, and the variance
estimate; rewrite by StatisticIdentification, `ratCast_expect`,
`clique_joint_expectation false`, `clique_observation_independent_mass`,
ConditionalMoments, and the three values. -/
def N21 : Prop :=
  IndependentTransport → StatisticIdentification → ConditionalMoments → MeanValue →
    SecondValue → VarianceEstimateValue → RealMoments

/-- Instantiate the printed proposition at the witness; its first conjunct would give
`Var(T) ≤ E(V̂)`, contradicting the exact values. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6) (h7 : N7)
    (h8 : N8) (h9 : N9) (h10 : N10) (h11 : N11) (h12 : N12) (h13 : N13) (h14 : N14)
    (h15 : N15) (h16 : N16) (h17 : N17) (h18 : N18) (h19 : N19) (h20 : N20)
    (h21 : N21) : Target := by
  intro h
  obtain ⟨hsupp, hmarg⟩ := h5 h1 h2 h4
  let P : FiniteDesign (Assignment 12) := ⟨cliqueMass, h4.1, h4.2.1⟩
  obtain ⟨hT, hT2, hV⟩ :=
    h21 (h10 h4 (h7 h1 (h6 h1 h4)) h8 (h9 h2 h3)) h11 (h12 h2 h3) (h15 (h13 h2))
      (h16 (h14 h3)) (h20 (h17 (h14 h3)) (h18 (h14 h3)) (h19 (h14 h3))) P rfl
  have hle := (h 12 65 (by norm_num) (by norm_num) P
    (by
      change 65 ≤ (Finset.univ.filter (fun z => 0 < cliqueMass z)).card
      rw [hsupp]
      norm_num)
    cliqueAdj (fun i => by simp [cliqueAdj]) yR .d01 .d00 (by decide)
    (fun i => by
      change 0 < marginal cliqueMass (fun z => exposure cliqueAdj z) i .d01
      rw [(hmarg i).1]
      norm_num)
    (fun i => by
      change 0 < marginal cliqueMass (fun z => exposure cliqueAdj z) i .d00
      rw [(hmarg i).2]
      norm_num)).1
  change designVariance (indepMass P) indepT ≤ expect (indepMass P) indepV at hle
  unfold designVariance at hle
  rw [hT, hT2, hV] at hle
  norm_num at hle

end

end AronowAudit.P044.Wave1.SimulatedVariance
