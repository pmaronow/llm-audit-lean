import Mathlib
import SAP.P037b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037b
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Number of occurrences of an event in a supported sequence. -/
noncomputable def hitCountW1 {Ω : Type} {J : ℕ}
    (E : Ω → Prop) (draws : Fin J → Ω) : ℕ :=
  (Finset.univ.filter (fun j => E (draws j))).card

/-- Empirical frequency; statements using it require a positive draw count. -/
noncomputable def frequencyW1 {Ω : Type} {J : ℕ}
    (E : Ω → Prop) (draws : Fin J → Ω) : ℝ := (hitCountW1 E draws : ℝ) / J

/-- Product masses encode independent draws, rather than an arbitrary coupling. -/
noncomputable def iidMassW1 {Ω : Type} {J : ℕ}
    (mass : Ω → ℝ) (draws : Fin J → Ω) : ℝ := ∏ j, mass (draws j)

/-- Expectation under the indicated finite product law. -/
noncomputable def iidExpectationW1 {Ω : Type} [Fintype Ω] (mass : Ω → ℝ)
    (J : ℕ) (Y : (Fin J → Ω) → ℝ) : ℝ :=
  ∑ draws, iidMassW1 mass draws * Y draws

/-- Event probability under the indicated finite product law. -/
noncomputable def iidProbabilityW1 {Ω : Type} [Fintype Ω] (mass : Ω → ℝ)
    (J : ℕ) (E : (Fin J → Ω) → Prop) : ℝ :=
  iidExpectationW1 mass J (fun draws => if E draws then 1 else 0)

/-- Variance centered at the actual expectation under the finite product law. -/
noncomputable def iidVarianceW1 {Ω : Type} [Fintype Ω] (mass : Ω → ℝ)
    (J : ℕ) (Y : (Fin J → Ω) → ℝ) : ℝ :=
  iidExpectationW1 mass J (fun draws =>
    (Y draws - iidExpectationW1 mass J Y)^2)

/-- The four indirect empirical probabilities; the fifth label is direct exposure. -/
noncomputable def estimatedExposureW1 {Ω I : Type} {J : ℕ}
    (D : Ω → I → Fin 5) (draws : Fin J → Ω) (i : I) (k : Fin 4) : ℝ :=
  ((Finset.univ.filter (fun j => D (draws j) i = k.castSucc)).card : ℝ) / J

/-- Finite version of exactly the outcome-specific analysis mask. -/
noncomputable def analysisFinsetW1 {Ω I : Type} [Fintype I]
    (estimated : I → Fin 4 → ℝ) (seed outcome baseline screen : Ω → I → Prop)
    (z : Ω) : Finset I :=
  Finset.univ.filter (fun i => i ∈ analysisPopulation estimated seed outcome baseline screen z)

/-- The code's fitted-prediction average; its use is guarded by a nonempty set. -/
noncomputable def analysisPredictionMeanW1 {Ω I : Type} [Fintype I]
    (estimated : I → Fin 4 → ℝ) (seed outcome baseline screen : Ω → I → Prop)
    (z : Ω) (prediction : I → Fin 4 → ℝ) (k : Fin 4) : ℝ :=
  let A := analysisFinsetW1 estimated seed outcome baseline screen z
  (∑ i ∈ A, prediction i k) / (A.card : ℝ)

/-- The printed fixed-population prediction average, whose denominator is the
cardinality of the all-four-positive population. Its use requires nonemptiness. -/
noncomputable def printedPredictionMeanW1 {I : Type} [Fintype I]
    (π : I → Fin 4 → ℝ) (prediction : I → Fin 4 → ℝ) (k : Fin 4) : ℝ :=
  let B := Finset.univ.filter (fun i => ∀ l, 0 < π i l)
  (∑ i ∈ B, prediction i k) / (B.card : ℝ)

/-- A legal six-of-twelve block. Four copies give 48 eligible students. -/
abbrev CutoffBlockW1 := {s : Finset (Fin 12) // s.card = 6}

/-- A fair school indicator and four independently selected legal blocks. -/
abbrev CutoffAssignmentsW1 := Bool × (Fin 4 → CutoffBlockW1)

/-- Number of legal local seed subsets, without enumerating the full support. -/
theorem cutoffBlockCardW1 : Fintype.card CutoffBlockW1 = 924 := by
  rw [Fintype.card_of_subtype ((Finset.univ : Finset (Fin 12)).powersetCard 6)
    (by intro s; simp)]
  norm_num [Finset.card_powersetCard, Nat.choose]

/-- Cardinality of the four-block support, kept as a separate certificate. -/
theorem cutoffAssignmentsCardW1 : Fintype.card CutoffAssignmentsW1 = 2 * 924^4 := by
  calc
    _ = Fintype.card Bool * Fintype.card (Fin 4 → CutoffBlockW1) := Fintype.card_prod _ _
    _ = 2 * (Fintype.card CutoffBlockW1)^4 := by rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    _ = _ := by rw [cutoffBlockCardW1]

/-- Uniform law of the legal four-block design. The focal peers are in block zero. -/
noncomputable def cutoffDesignW1 : ProbabilityDesign CutoffAssignmentsW1 where
  mass := fun _ => 1 / (2 * 924^4)
  positive := fun _ => by norm_num
  total := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, cutoffAssignmentsCardW1]
    norm_num

/-- Correct five-label exposure when the focal student's traits lie in block zero. -/
def cutoffExposureW1 (self peers refs : Finset (Fin 12))
    (z : CutoffAssignmentsW1) : Fin 5 :=
  if z.1 then localTreatedLabel self peers refs (z.2 0).val else 0

/-- Lift a supported local assignment to four legal blocks. This is only used
for deterministic witnesses, with no independence claim about their ordering. -/
def liftCutoffAssignmentW1 (z : Bool × Finset (Fin 12))
    (hz : z.2 ∈ seedSubsets 12 6) : CutoffAssignmentsW1 :=
  (z.1, fun _ => ⟨z.2, (Finset.mem_powersetCard.mp hz).2⟩)

/-- Two local focal networks: W1 is ineligible; W2 is eligible student 2. -/
def cutoffNetworkW1 (z : CutoffAssignmentsW1) (i : Fin 2) : Fin 5 :=
  if i = 0 then cutoffExposureW1 ∅ {0,1,2,3,4,5} {0} z
  else cutoffExposureW1 {2} {0,1} {0} z

/-- T22(c): strictness in an actual supported, four-block design and sequence. -/
def T22StrictW1 : Prop :=
  let π : Unit → Fin 4 → ℝ := fun _ k =>
    eventProbability cutoffDesignW1 (fun z => cutoffExposureW1 ∅ {0,1,2,3,4,5} {0} z = k.castSucc)
  () ∈ positiveExposurePopulation π ∧
  () ∉ exposureProbabilityCutoff π (1/100) ∧
  ∃ draws : Fin 10000 → CutoffAssignmentsW1,
    let phat : Unit → Fin 4 → ℝ := fun _ k =>
      estimatedExposureW1 (fun z (_ : Unit) => cutoffExposureW1 ∅ {0,1,2,3,4,5} {0} z) draws () k
    (∀ k, phat () k = (![1/2,1/2000,499/2000,1/4] : Fin 4 → ℝ) k) ∧
    () ∈ exposureProbabilityCutoff phat 0 ∧
    () ∉ exposureProbabilityCutoff phat (1/100)

/-- T22(d): the joint four-cutoff screen, rather than just each scalar event,
has probability strictly between zero and one under independent simulation. -/
def T22JointCutoffW1 : Prop :=
  ∀ {Ω I : Type} [Fintype Ω] (P : ProbabilityDesign Ω)
    (D : Ω → I → Fin 5) (i : I),
    i ∈ positiveExposurePopulation
      (fun i k => eventProbability P (fun z => D z i = k.castSucc)) →
    0 < iidProbabilityW1 P.mass 10000
      (fun draws => i ∈ exposureProbabilityCutoff (estimatedExposureW1 D draws) (1/100)) ∧
    iidProbabilityW1 P.mass 10000
      (fun draws => i ∈ exposureProbabilityCutoff (estimatedExposureW1 D draws) (1/100)) < 1

/-- T22(e): complete observations give a legal instance of genuine realized
assignment dependence, with passing simulated cutoffs and positive direct probability.
The ineligible background student stays in the averaging set, so it is never empty. -/
def T22DependenceExampleW1 : Prop :=
  eventProbability cutoffDesignW1 (fun z => cutoffNetworkW1 z 1 = 4) = 1/4 ∧
  ∃ draws : Fin 10000 → CutoffAssignmentsW1,
    (∀ (i : Fin 2) (k : Fin 4), estimatedExposureW1 cutoffNetworkW1 draws i k = 1/4) ∧
    ∃ a b : CutoffAssignmentsW1,
      cutoffNetworkW1 a 1 = 4 ∧ cutoffNetworkW1 b 1 = 1 ∧
      analysisFinsetW1 (estimatedExposureW1 cutoffNetworkW1 draws)
        (fun z i => cutoffNetworkW1 z i = 4) (fun _ _ => True)
        (fun _ _ => True) (fun _ _ => True) a = {0} ∧
      analysisFinsetW1 (estimatedExposureW1 cutoffNetworkW1 draws)
        (fun z i => cutoffNetworkW1 z i = 4) (fun _ _ => True)
        (fun _ _ => True) (fun _ _ => True) b = {0,1}

/-- P037-T22; main p. 568 (PDF p. 3); SI Appendix pp. 14, 18 and 19;
Table S5 note, SI p. 40.
The positive-probability population and the exact and simulated .01 screens obey
all stated inclusions and strictness examples. Supported simulation has no false
positive exposure. Independent 10000-draw counts have the binomial law, the scalar
and joint cutoffs are nondegenerate, and retained inverse frequencies are at most
10000/101 < 100. The outcome-specific analysis set is a random set contained in the
realized nonseeds, with exclusion probability at least the direct-exposure probability;
a legal complete-observation example changes it with the realized assignment.
Fitted predictions are averaged over that same outcome-specific set, using its
cardinality, whenever this average exists. The usual measure-theoretic conditions
are assumed; here all laws are finite. A random set may be constant for particular
availability masks. No shared historical sample size or public-rerun size is asserted. -/
def T22WholeStatement : Prop :=
  T22Statement.{0,0,0,0,0} ∧
  (∀ {Ω I : Type} [Fintype Ω] (P : ProbabilityDesign Ω)
    (D : Ω → I → Fin 5) (J : ℕ) (_hJ : 0 < J) (draws : Fin J → Ω)
    (i : I) (k : Fin 5),
    eventProbability P (fun z => D z i = k) = 0 →
      frequencyW1 (fun z => D z i = k) draws = 0) ∧
  (∀ {Ω I : Type} [Fintype Ω] (P : ProbabilityDesign Ω)
    (D : Ω → I → Fin 5) (i : I),
    (∑ k : Fin 5, eventProbability P (fun z => D z i = k)) = 1) ∧
  T22StrictW1 ∧
  (∀ {Ω I : Type} [Fintype Ω] (P : ProbabilityDesign Ω)
    (D : Ω → I → Fin 5) (i : I) (k : Fin 4),
    let E := fun z => D z i = k.castSucc
    let p := eventProbability P E
    (∀ r : ℕ, r ≤ 10000 →
      iidProbabilityW1 P.mass 10000 (fun draws => hitCountW1 E draws = r) =
        (Nat.choose 10000 r : ℝ) * p^r * (1-p)^(10000-r)) ∧
    (∀ draws : Fin 10000 → Ω,
      (10000 : ℝ) * frequencyW1 E draws = hitCountW1 E draws ∧
      (frequencyW1 E draws > 1/100 ↔ 101 ≤ hitCountW1 E draws)) ∧
    (∀ draws : Fin 10000 → Ω,
      i ∈ exposureProbabilityCutoff (estimatedExposureW1 D draws) (1/100) →
      1 / estimatedExposureW1 D draws i k ≤ 10000/101 ∧ (10000/101 : ℝ) < 100)) ∧
  T22JointCutoffW1 ∧
  (∀ {Ω I : Type} [Fintype Ω] (P : ProbabilityDesign Ω)
    (D : Ω → I → Fin 5) (estimated : I → Fin 4 → ℝ)
    (outcome baseline screen : Ω → I → Prop) (i : I),
    let M := analysisPopulation estimated (fun z i => D z i = 4) outcome baseline screen
    eventProbability P (fun z => D z i = 4) ≤ eventProbability P (fun z => i ∉ M z) ∧
    @Measurable Ω (Set I) ⊤ ⊤ M) ∧
  T22DependenceExampleW1 ∧
  (∀ {Ω I : Type} [Fintype Ω] [Fintype I] (P : ProbabilityDesign Ω)
    (D : Ω → I → Fin 5) (J : ℕ) (_hJ : 0 < J) (draws : Fin J → Ω)
    (outcome baseline : Ω → I → Prop) (peerConflict : Bool)
    (schoolMean : Ω → I → ℝ) (z : Ω) (prediction : I → Fin 4 → ℝ) (k : Fin 4),
    let π := fun i l => eventProbability P (fun w => D w i = l.castSucc)
    let estimated := estimatedExposureW1 D draws
    let seed := fun z i => D z i = 4
    let screen := fun z i => peerConflict = false ∨ passesConflictThreshold (schoolMean z i)
    let A := analysisFinsetW1 estimated seed outcome baseline screen z
    let B := Finset.univ.filter (fun i => ∀ l, 0 < π i l)
    A.Nonempty →
      analysisPredictionMeanW1 estimated seed outcome baseline screen z prediction k =
        (∑ i ∈ A, prediction i k) / (A.card : ℝ) ∧ 0 < (A.card : ℝ) ∧
      B.Nonempty ∧ printedPredictionMeanW1 π prediction k =
        (∑ i ∈ B, prediction i k) / (B.card : ℝ))

/-- A legal five-of-ten block from the rare-exposure design. -/
abbrev RareBlockW1 := {s : Finset (Fin 10) // s.card = 5}

/-- Joint selections of the first two blocks, in local coordinates. -/
abbrev RarePairW1 := RareBlockW1 × RareBlockW1

/-- No focal peer is selected in either of the two blocks. -/
def rareAvoidsPairW1 (s : RarePairW1) : Prop :=
  Disjoint s.1.val {0,1,2,3,4} ∧ Disjoint s.2.val {0,1,2,3,4}

/-- In global numbering this is ({5,...,9},{15,...,19}). -/
def rareAvoidingPairW1 : RarePairW1 :=
  (⟨{5,6,7,8,9}, by norm_num⟩, ⟨{5,6,7,8,9}, by norm_num⟩)

/-- T29(i): actual selection counts, uniform pair marginal, and named unique
peer-avoiding selection, with 0 the sole referent peer. -/
def T29SelectionsW1 : Prop :=
  Nat.choose 10 5 = 252 ∧ Nat.choose 9 4 = 126 ∧
  Fintype.card RareBlockW1 = 252 ∧ Fintype.card RarePairW1 = 63504 ∧
  (∀ s : RarePairW1,
    (∑ z : RareSeedAssignments, rareAssignmentMass z *
      (if (z.2 0, z.2 1) = s then (1 : ℝ) else 0)) = 1/63504) ∧
  (Finset.univ.filter rareAvoidsPairW1).card = 1 ∧
  (∀ s, rareAvoidsPairW1 s ↔ s = rareAvoidingPairW1) ∧
  (Finset.univ.filter (fun s : RarePairW1 => (0 : Fin 10) ∈ s.1.val)).card = 31752 ∧
  (Finset.univ.filter (fun s : RarePairW1 =>
    (0 : Fin 10) ∉ s.1.val ∧ ¬rareAvoidsPairW1 s)).card = 31751

/-- P037-T29; SI Appendix p. 14; the general simulation statement and J are
on SI p. 18.
In the stated synthetic four-block, forty-eligible school, exactly one of 63504
uniform first-two-block selections avoids all ten peers; 31752 contain referent 0,
and 31751 hit only nonreferent peers. The exposure vector is
(1/2, 1/127008, 31751/127008, 1/4), sums to one, and is strictly positive and below one.
Every supported 10000-draw frequency misses the school-exposure probability by at
least that probability, with the stated sharper zero/positive-count alternatives,
regardless of dependence. For independent design draws, the count has the full
binomial law, expected count 625/7938, and zero-hit probability strictly between .9
and .95. The school-exposure frequency (count divided by 10000) has variance
127007/161310320640000, relative variance 127007/10000, and relative standard error
above 3.5. The control frequency has variance 1/40000 and standard
error 1/200. The usual measure-theoretic conditions are assumed; all quantities
here are finite sums under explicit finite product laws. This is a synthetic
witness and asserts no occurrence in the study. -/
def T29WholeStatement : Prop :=
  T29Statement ∧ T29SelectionsW1 ∧
  (∑ k : Fin 4, rareExposureProbability k) = 1 ∧
  (∀ z : RareSeedAssignments,
    0 < rareAssignmentMass z ∧
    rareAssignmentMass z = (1/2 : ℝ) * ∏ _h : Fin 4, (1/252 : ℝ)) ∧
  (∑ draws : Fin 10000 → RareSeedAssignments,
    iidMassW1 rareAssignmentMass draws) = 1 ∧
  (let p : ℝ := 1/127008
   0 < p ∧ p < 1/20000 ∧ p/2 = 1/254016 ∧
   ∀ draws : Fin 10000 → RareSeedAssignments,
    let r := hitCountW1 (fun z => rareExposure z = 1) draws
    r ≤ 10000 ∧
    (r = 0 → |(r : ℝ)/10000-p| = p) ∧
    (1 ≤ r → 1/10000-p ≤ |(r : ℝ)/10000-p| ∧ p < 1/10000-p) ∧
    p ≤ |(r : ℝ)/10000-p| ∧ p/2 < |(r : ℝ)/10000-p|) ∧
  (let E := fun z => rareExposure z = 1
   let p : ℝ := 1/127008
   let V := iidVarianceW1 rareAssignmentMass 10000 (frequencyW1 E)
   (∀ r : ℕ, r ≤ 10000 →
    iidProbabilityW1 rareAssignmentMass 10000 (fun draws => hitCountW1 E draws = r) =
      (Nat.choose 10000 r : ℝ) * p^r * (1-p)^(10000-r)) ∧
   iidExpectationW1 rareAssignmentMass 10000 (frequencyW1 E) = p ∧
   V = 127007/161310320640000 ∧ V/p^2 = 127007/10000 ∧
   Real.sqrt V / p > 7/2 ∧
   iidProbabilityW1 rareAssignmentMass 10000 (fun draws => frequencyW1 E draws = 0) =
     (127007/127008 : ℝ)^10000 ∧
   (9/10 : ℝ) < iidProbabilityW1 rareAssignmentMass 10000
     (fun draws => frequencyW1 E draws = 0)) ∧
  (let V := iidVarianceW1 rareAssignmentMass 10000
    (frequencyW1 (fun z => rareExposure z = 0))
   iidExpectationW1 rareAssignmentMass 10000
     (frequencyW1 (fun z => rareExposure z = 0)) = 1/2 ∧
   V = 1/40000 ∧ Real.sqrt V = 1/200)

end SAP.P037b
