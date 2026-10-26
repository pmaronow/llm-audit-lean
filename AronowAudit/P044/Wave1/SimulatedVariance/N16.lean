import AronowAudit.P044.Wave1.SimulatedVariance.N15

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

/-- Only the two contrasted labels need the explicit part of `cliqueFullJoint`.
This is a definitional case split, independent of all enumeration certificates. -/
theorem momentFullJoint_eq (i j : Fin 12) (a b : Exposure)
    (ha : a = .d01 ∨ a = .d00) (hb : b = .d01 ∨ b = .d00) :
    cliqueFullJoint i j a b =
      cliqueJointTable (decide (i = j)) (decide (i.val / 4 = j.val / 4)) a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    by_cases hij : i = j <;> by_cases hs : i.val / 4 = j.val / 4 <;>
    simp [cliqueFullJoint, cliqueJointTable, hij, hs]

theorem momentObservationJoint_eq (t : Fin 66) (i j : Fin 12) (a b : Exposure)
    (ha : a = .d01 ∨ a = .d00) (hb : b = .d01 ∨ b = .d00) :
    cliqueObservationJoint t false i j a b =
      (cliqueJointTable (decide (i = j)) (decide (i.val / 4 = j.val / 4)) a b : ℚ) / 66 := by
  change (cliqueFullJoint i j a b : ℚ) / 66 = _
  rw [momentFullJoint_eq i j a b ha hb]

/-- The estimated joint input as a function of the pair class and omitted labels.
Natural subtraction, diagonal smoothing, and the two denominators are kept literally. -/
def momentTypeJoint (e s : Bool) (d d' a b : Exposure) : ℚ :=
  let c := cliqueJointTable e s a b - if d = a ∧ d' = b then 1 else 0
  if a = b then ((c + if e then 1 else 0 : ℕ) : ℚ) / 66 else (c : ℚ) / 65

theorem momentJoints_eq (t : Fin 66) (i j : Fin 12) (a b : Exposure)
    (ha : a = .d01 ∨ a = .d00) (hb : b = .d01 ∨ b = .d00) :
    cliqueJoints t i j a b =
      momentTypeJoint (decide (i = j)) (decide (i.val / 4 = j.val / 4))
        (cliqueF t i) (cliqueF t j) a b := by
  simp [cliqueJoints, momentTypeJoint, momentFullJoint_eq i j a b ha hb]

/-- The 16 omitted-label entries within one unit-pair class. -/
def momentTypeRow (Ψ : Bool → Bool → Exposure → Exposure → ℚ) (e s : Bool) : ℚ :=
  ∑ d : Exposure, ∑ d' : Exposure, (cliqueJointTable e s d d' : ℚ) * Ψ e s d d'

/-- The right-hand side of `TypeCount2`. -/
def momentTypeSum (Ψ : Bool → Bool → Exposure → Exposure → ℚ) : ℚ :=
  ∑ e : Bool, ∑ s : Bool, (cliquePairClassCount e s : ℚ) * momentTypeRow Ψ e s

theorem momentTypeSum_eq (Ψ : Bool → Bool → Exposure → Exposure → ℚ) :
    momentTypeSum Ψ = 12 * momentTypeRow Ψ true true +
      36 * momentTypeRow Ψ false true + 96 * momentTypeRow Ψ false false := by
  simp [momentTypeSum, Fintype.sum_bool, cliquePairClassCount, add_assoc]

theorem moment_pair_average (htypes : TypeCount2)
    (Ψ : Bool → Bool → Exposure → Exposure → ℚ) :
    expect (fun _ : Fin 66 => (1 / 66 : ℚ)) (fun t =>
      ∑ i : Fin 12, ∑ j : Fin 12,
        Ψ (decide (i = j)) (decide (i.val / 4 = j.val / 4)) (cliqueF t i) (cliqueF t j)) =
      momentTypeSum Ψ / 66 := by
  rw [moment_average]
  exact congrArg (fun x : ℚ => x / 66) (htypes Ψ)

/-- The summand in the conditional second moment before division by 144. -/
def momentSecondTerm (e s : Bool) (d d' : Exposure) : ℚ :=
  ((cliqueJointTable e s .d01 .d01 : ℚ) / 66) /
      (momentTypeWeight d .d01 * momentTypeWeight d' .d01) +
    ((cliqueJointTable e s .d00 .d00 : ℚ) / 66) /
      (momentTypeWeight d .d00 * momentTypeWeight d' .d00) -
    ((cliqueJointTable e s .d01 .d00 : ℚ) / 66) /
      (momentTypeWeight d .d01 * momentTypeWeight d' .d00) -
    ((cliqueJointTable e s .d00 .d01 : ℚ) / 66) /
      (momentTypeWeight d .d00 * momentTypeWeight d' .d01)

theorem momentSecond_reduction (t : Fin 66) :
    cliqueConditionalSecond t false =
      (∑ i : Fin 12, ∑ j : Fin 12,
        momentSecondTerm (decide (i = j)) (decide (i.val / 4 = j.val / 4))
          (cliqueF t i) (cliqueF t j)) / 144 := by
  unfold cliqueConditionalSecond
  apply congrArg (fun x : ℚ => x / 144)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold momentSecondTerm
  simp only [momentObservationJoint_eq t i j .d01 .d01 (Or.inl rfl) (Or.inl rfl),
    momentObservationJoint_eq t i j .d00 .d00 (Or.inr rfl) (Or.inr rfl),
    momentObservationJoint_eq t i j .d01 .d00 (Or.inl rfl) (Or.inr rfl),
    momentObservationJoint_eq t i j .d00 .d01 (Or.inr rfl) (Or.inl rfl),
    momentTypeWeight_eq]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem n16_proof : N16 := by
  intro htypes
  change expect (fun _ : Fin 66 => (1 / 66 : ℚ))
    (fun t => cliqueConditionalSecond t false) = 234399385 / 480661776
  have hdiag : momentTypeRow momentSecondTerm true true = 100268421 / 329672 := by
    norm_num [momentTypeRow, moment_sum_exposure, momentSecondTerm,
      momentTypeWeight, cliqueJointTable, cliqueFullCount]
  have hsame : momentTypeRow momentSecondTerm false true = 19775250143 / 80110296 := by
    norm_num [momentTypeRow, moment_sum_exposure, momentSecondTerm,
      momentTypeWeight, cliqueJointTable, cliqueFullCount]
  have hdiff : momentTypeRow momentSecondTerm false false = -81404719 / 989016 := by
    norm_num [momentTypeRow, moment_sum_exposure, momentSecondTerm,
      momentTypeWeight, cliqueJointTable, cliqueFullCount]
  have havg : expect (fun _ : Fin 66 => (1 / 66 : ℚ))
      (fun t => cliqueConditionalSecond t false) = momentTypeSum momentSecondTerm / 66 / 144 := by
    simp_rw [momentSecond_reduction]
    rw [expect_div, moment_pair_average htypes momentSecondTerm]
  rw [havg, momentTypeSum_eq, hdiag, hsame, hdiff] <;> norm_num

end

end AronowAudit.P044.Wave1.SimulatedVariance
