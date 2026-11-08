import Mathlib
import SAP.P037b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037b
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Number of occurrences of an event in a supported sequence. -/
noncomputable def hitCountW2 {Ω : Type} {J : ℕ}
    (E : Ω → Prop) (draws : Fin J → Ω) : ℕ :=
  (Finset.univ.filter (fun j => E (draws j))).card

/-- Empirical frequency; statements using it require a positive draw count. -/
noncomputable def frequencyW2 {Ω : Type} {J : ℕ}
    (E : Ω → Prop) (draws : Fin J → Ω) : ℝ := (hitCountW2 E draws : ℝ) / J

/-- Product masses encode independent draws, rather than an arbitrary coupling. -/
noncomputable def iidMassW2 {Ω : Type} {J : ℕ}
    (mass : Ω → ℝ) (draws : Fin J → Ω) : ℝ := ∏ j, mass (draws j)

/-- Expectation under the indicated finite product law. -/
noncomputable def iidExpectationW2 {Ω : Type} [Fintype Ω] (mass : Ω → ℝ)
    (J : ℕ) (Y : (Fin J → Ω) → ℝ) : ℝ :=
  ∑ draws, iidMassW2 mass draws * Y draws

/-- Event probability under the indicated finite product law. -/
noncomputable def iidProbabilityW2 {Ω : Type} [Fintype Ω] (mass : Ω → ℝ)
    (J : ℕ) (E : (Fin J → Ω) → Prop) : ℝ :=
  iidExpectationW2 mass J (fun draws => if E draws then 1 else 0)

/-- The four indirect empirical probabilities; the fifth label is direct exposure. -/
noncomputable def estimatedExposureW2 {Ω I : Type} {J : ℕ}
    (D : Ω → I → Fin 5) (draws : Fin J → Ω) (i : I) (k : Fin 4) : ℝ :=
  ((Finset.univ.filter (fun j => D (draws j) i = k.castSucc)).card : ℝ) / J

/-- Finite version of exactly the outcome-specific analysis mask. -/
noncomputable def analysisFinsetW2 {Ω I : Type} [Fintype I]
    (estimated : I → Fin 4 → ℝ) (seed outcome baseline screen : Ω → I → Prop)
    (z : Ω) : Finset I :=
  Finset.univ.filter (fun i => i ∈ analysisPopulation estimated seed outcome baseline screen z)

/-- The code's fitted-prediction average; its use is guarded by a nonempty set. -/
noncomputable def analysisPredictionMeanW2 {Ω I : Type} [Fintype I]
    (estimated : I → Fin 4 → ℝ) (seed outcome baseline screen : Ω → I → Prop)
    (z : Ω) (prediction : I → Fin 4 → ℝ) (k : Fin 4) : ℝ :=
  let A := analysisFinsetW2 estimated seed outcome baseline screen z
  (∑ i ∈ A, prediction i k) / (A.card : ℝ)

/-- The printed fixed-population prediction average, whose denominator is the
cardinality of the all-four-positive population. Its use requires nonemptiness. -/
noncomputable def printedPredictionMeanW2 {I : Type} [Fintype I]
    (π : I → Fin 4 → ℝ) (prediction : I → Fin 4 → ℝ) (k : Fin 4) : ℝ :=
  let B := Finset.univ.filter (fun i => ∀ l, 0 < π i l)
  (∑ i ∈ B, prediction i k) / (B.card : ℝ)

/-- A legal six-of-twelve block. Four copies give 48 eligible students. -/
abbrev CutoffBlockW2 := {s : Finset (Fin 12) // s.card = 6}

/-- A fair school indicator and four independently selected legal blocks. -/
abbrev CutoffAssignmentsW2 := Bool × (Fin 4 → CutoffBlockW2)

/-- Number of legal local seed subsets, without enumerating the full support. -/
theorem cutoffBlockCardW2 : Fintype.card CutoffBlockW2 = 924 := by
  rw [Fintype.card_of_subtype ((Finset.univ : Finset (Fin 12)).powersetCard 6)
    (by intro s; simp)]
  norm_num [Finset.card_powersetCard, Nat.choose]

/-- Cardinality of the four-block support, kept as a separate certificate. -/
theorem cutoffAssignmentsCardW2 : Fintype.card CutoffAssignmentsW2 = 2 * 924^4 := by
  calc
    _ = Fintype.card Bool * Fintype.card (Fin 4 → CutoffBlockW2) := Fintype.card_prod _ _
    _ = 2 * (Fintype.card CutoffBlockW2)^4 := by rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    _ = _ := by rw [cutoffBlockCardW2]

/-- Uniform law of the legal four-block design. The focal peers are in block zero. -/
noncomputable def cutoffDesignW2 : ProbabilityDesign CutoffAssignmentsW2 where
  mass := fun _ => 1 / (2 * 924^4)
  positive := fun _ => by norm_num
  total := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, cutoffAssignmentsCardW2]
    norm_num

/-- Correct five-label exposure when the focal student's traits lie in block zero. -/
def cutoffExposureW2 (self peers refs : Finset (Fin 12))
    (z : CutoffAssignmentsW2) : Fin 5 :=
  if z.1 then localTreatedLabel self peers refs (z.2 0).val else 0

/-- Lift a supported local assignment to four legal blocks. This is only used
for deterministic witnesses, with no independence claim about their ordering. -/
def liftCutoffAssignmentW2 (z : Bool × Finset (Fin 12))
    (hz : z.2 ∈ seedSubsets 12 6) : CutoffAssignmentsW2 :=
  (z.1, fun _ => ⟨z.2, (Finset.mem_powersetCard.mp hz).2⟩)

/-- Two focal networks from T21: the background student is ineligible; student 2 is eligible. -/
def cutoffNetworkW2 (z : CutoffAssignmentsW2) (i : Fin 2) : Fin 5 :=
  if i = 0 then cutoffExposureW2 ∅ {0,1,2,3,4,5} {0} z
  else cutoffExposureW2 {2} {0,1} {0} z

/-- T22(c): strictness in an actual supported, four-block design and sequence. -/
def T22StrictW2 : Prop :=
  let π : Unit → Fin 4 → ℝ := fun _ k =>
    eventProbability cutoffDesignW2 (fun z => cutoffExposureW2 ∅ {0,1,2,3,4,5} {0} z = k.castSucc)
  () ∈ positiveExposurePopulation π ∧
  () ∉ exposureProbabilityCutoff π (1/100) ∧
  ∃ draws : Fin 10000 → CutoffAssignmentsW2,
    let phat : Unit → Fin 4 → ℝ := fun _ k =>
      estimatedExposureW2 (fun z (_ : Unit) => cutoffExposureW2 ∅ {0,1,2,3,4,5} {0} z) draws () k
    (∀ k, phat () k = (![1/2,1/2000,499/2000,1/4] : Fin 4 → ℝ) k) ∧
    () ∈ exposureProbabilityCutoff phat 0 ∧
    () ∉ exposureProbabilityCutoff phat (1/100)

/-- The joint screen and explicit supported passing/failing sequences under independent
10000-draw simulation. Constant sequences miss at least three indirect labels. -/
def T22JointCutoffW2 : Prop :=
  ∀ {Ω I : Type} [Fintype Ω] (P : ProbabilityDesign Ω)
    (D : Ω → I → Fin 5) (i : I),
    i ∈ positiveExposurePopulation
      (fun i k => eventProbability P (fun z => D z i = k.castSucc)) →
    (∃ representatives : Fin 4 → Ω,
      (∀ k, D (representatives k) i = k.castSucc) ∧
      ∃ draws : Fin 10000 → Ω,
        (∀ j, ∃ k, draws j = representatives k) ∧
        (∀ k : Fin 4, hitCountW2 (fun z => D z i = k.castSucc) draws = 2500) ∧
        i ∈ exposureProbabilityCutoff (estimatedExposureW2 D draws) (1/100) ∧
        0 < iidMassW2 P.mass draws) ∧
    (∃ w : Ω,
      3 ≤ (Finset.univ.filter (fun k : Fin 4 =>
        estimatedExposureW2 D (fun _ : Fin 10000 => w) i k = 0)).card ∧
      i ∉ exposureProbabilityCutoff
        (estimatedExposureW2 D (fun _ : Fin 10000 => w)) (1/100) ∧
      0 < iidMassW2 P.mass (fun _ : Fin 10000 => w)) ∧
    0 < iidProbabilityW2 P.mass 10000
      (fun draws => i ∈ exposureProbabilityCutoff (estimatedExposureW2 D draws) (1/100)) ∧
    iidProbabilityW2 P.mass 10000
      (fun draws => i ∈ exposureProbabilityCutoff (estimatedExposureW2 D draws) (1/100)) < 1

/-- For a finite design, almost sure constancy means probability one of equality
to a single fixed set; the probability uses the realized assignment, not simulation. -/
def AlmostSurelyConstantW2 {Ω I : Type} [Fintype Ω]
    (P : ProbabilityDesign Ω) (M : Ω → Set I) : Prop :=
  ∃ A : Set I, eventProbability P (fun z => M z = A) = 1

/-- One legal design and a fixed supported simulation illustrate both possibilities:
complete observations permit assignment dependence, whereas withholding only the
eligible student's outcome leaves the constant nonempty singleton of the never-seed
background student. The eligible student's direct probability remains 1/4. -/
def T22MaskExamplesW2 : Prop :=
  eventProbability cutoffDesignW2 (fun z => cutoffNetworkW2 z 1 = 4) = 1/4 ∧
  ∃ draws : Fin 10000 → CutoffAssignmentsW2,
    (∀ (i : Fin 2) (k : Fin 4), estimatedExposureW2 cutoffNetworkW2 draws i k = 1/4) ∧
    (∀ z : CutoffAssignmentsW2,
      analysisFinsetW2 (estimatedExposureW2 cutoffNetworkW2 draws)
        (fun z i => cutoffNetworkW2 z i = 4) (fun _ i => i = 0)
        (fun _ _ => True) (fun _ _ => True) z = {0}) ∧
    (∃ a b : CutoffAssignmentsW2,
      cutoffNetworkW2 a 1 = 4 ∧ cutoffNetworkW2 b 1 = 1 ∧
      analysisFinsetW2 (estimatedExposureW2 cutoffNetworkW2 draws)
        (fun z i => cutoffNetworkW2 z i = 4) (fun _ _ => True)
        (fun _ _ => True) (fun _ _ => True) a = {0} ∧
      analysisFinsetW2 (estimatedExposureW2 cutoffNetworkW2 draws)
        (fun z i => cutoffNetworkW2 z i = 4) (fun _ _ => True)
        (fun _ _ => True) (fun _ _ => True) b = {0,1})

/-- P037-T22; main p. 568 (PDF p. 3); SI Appendix pp. 14, 18 and 19;
Table S5 note, SI p. 40. Corrected canonical claim, 2026-11-04.
The positive-probability population equals the all-four-positive population;
the exact and simulated .01 screens have all stated inclusions, with strictness
in a legal design. Five-label probabilities sum to one, and the four indirect
probabilities sum to at most one. Zero exact probability forces zero supported
simulation frequency. Under 10000 independent design draws, exposure counts have
the binomial law, the scalar cutoff is count at least 101, and both scalar and
joint four-cutoff membership have probability strictly between zero and one for
students of the positive-probability population. A balanced supported sequence
passes, a constant sequence fails, and retained inverse frequencies are at most
10000/101 < 100. For each fixed supported simulation, the outcome-specific analysis
set excludes realized seeds, with exclusion probability at least the direct
probability. Positive seed probability alone permits a constant nonempty analysis
set; positive seed and positive inclusion probabilities together imply inclusion
probability at most one minus the direct probability and strictly between zero
and one, so the set is not almost surely constant. Predictions are averaged over
this same outcome-specific set with its own cardinality whenever it is nonempty;
the printed comparison averages over the fixed all-four-positive population.
The usual measure-theoretic conditions are assumed; here all laws are finite.
No historical or public-rerun sample size is asserted. -/
def T22WholeStatement_W2 : Prop :=
  T22Statement.{0,0,0,0,0} ∧
  (∀ {Ω I : Type} [Fintype Ω] (P : ProbabilityDesign Ω)
    (D : Ω → I → Fin 5) (J : ℕ) (_hJ : 0 < J) (draws : Fin J → Ω)
    (i : I) (k : Fin 5),
    eventProbability P (fun z => D z i = k) = 0 →
      frequencyW2 (fun z => D z i = k) draws = 0) ∧
  (∀ {Ω I : Type} [Fintype Ω] (P : ProbabilityDesign Ω)
    (D : Ω → I → Fin 5) (i : I),
    (∑ k : Fin 5, eventProbability P (fun z => D z i = k)) = 1 ∧
    (∑ k : Fin 4, eventProbability P (fun z => D z i = k.castSucc)) +
      eventProbability P (fun z => D z i = 4) = 1 ∧
    (∑ k : Fin 4, eventProbability P (fun z => D z i = k.castSucc)) ≤ 1) ∧
  T22StrictW2 ∧
  (∀ {Ω I : Type} [Fintype Ω] (P : ProbabilityDesign Ω)
    (D : Ω → I → Fin 5) (i : I) (k : Fin 4),
    let E := fun z => D z i = k.castSucc
    let p := eventProbability P E
    (∀ r : ℕ,
      iidProbabilityW2 P.mass 10000 (fun draws => hitCountW2 E draws = r) =
        (Nat.choose 10000 r : ℝ) * p^r * (1-p)^(10000-r)) ∧
    (∀ draws : Fin 10000 → Ω,
      (10000 : ℝ) * frequencyW2 E draws = hitCountW2 E draws ∧
      (frequencyW2 E draws > 1/100 ↔ 101 ≤ hitCountW2 E draws)) ∧
    (i ∈ positiveExposurePopulation
        (fun i l => eventProbability P (fun z => D z i = l.castSucc)) →
      0 < iidProbabilityW2 P.mass 10000 (fun draws => frequencyW2 E draws > 1/100) ∧
      iidProbabilityW2 P.mass 10000 (fun draws => frequencyW2 E draws > 1/100) < 1) ∧
    (∀ draws : Fin 10000 → Ω,
      i ∈ exposureProbabilityCutoff (estimatedExposureW2 D draws) (1/100) →
      1 / estimatedExposureW2 D draws i k ≤ 10000/101 ∧ (10000/101 : ℝ) < 100)) ∧
  T22JointCutoffW2 ∧
  (∀ {Ω I : Type} [Fintype Ω] (P : ProbabilityDesign Ω)
    (D : Ω → I → Fin 5) (estimated : I → Fin 4 → ℝ)
    (outcome baseline screen : Ω → I → Prop) (i : I),
    let M := analysisPopulation estimated (fun z i => D z i = 4) outcome baseline screen
    let pD := eventProbability P (fun z => D z i = 4)
    let pM := eventProbability P (fun z => i ∈ M z)
    (∀ z, M z ⊆ {j | D z j ≠ 4}) ∧
    pD ≤ eventProbability P (fun z => i ∉ M z) ∧
    pM ≤ 1 - pD ∧
    (0 < pD → 0 < pM →
      0 < pM ∧ pM ≤ 1-pD ∧ 1-pD < 1 ∧ pM < 1 ∧
      ¬AlmostSurelyConstantW2 P M) ∧
    @Measurable Ω (Set I) ⊤ ⊤ M) ∧
  T22MaskExamplesW2 ∧
  (∀ {Ω I : Type} [Fintype Ω] [Fintype I] (P : ProbabilityDesign Ω)
    (D : Ω → I → Fin 5) (J : ℕ) (_hJ : 0 < J) (draws : Fin J → Ω)
    (outcome baseline : Ω → I → Prop) (peerConflict : Bool)
    (schoolMean : Ω → I → ℝ) (z : Ω) (prediction : I → Fin 4 → ℝ) (k : Fin 4),
    let π := fun i l => eventProbability P (fun w => D w i = l.castSucc)
    let estimated := estimatedExposureW2 D draws
    let seed := fun z i => D z i = 4
    let screen := fun z i => peerConflict = false ∨ passesConflictThreshold (schoolMean z i)
    let A := analysisFinsetW2 estimated seed outcome baseline screen z
    let B := Finset.univ.filter (fun i => ∀ l, 0 < π i l)
    A.Nonempty →
      analysisPredictionMeanW2 estimated seed outcome baseline screen z prediction k =
        (∑ i ∈ A, prediction i k) / (A.card : ℝ) ∧ 0 < (A.card : ℝ) ∧
      B.Nonempty ∧ printedPredictionMeanW2 π prediction k =
        (∑ i ∈ B, prediction i k) / (B.card : ℝ) ∧ 0 < (B.card : ℝ))

end SAP.P037b
