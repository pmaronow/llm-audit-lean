import AronowAudit.P044.Wave1.SimulatedVarianceBlueprint

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

theorem n21_proof : N21 := by
  intro htransport hidentify hconditional hmean hsecond hvariance P hP
  change expect (fun _ : Fin 66 => (1 / 66 : ℚ))
    (fun t => cliqueConditionalMean t false) = -67 / 53592 at hmean
  change expect (fun _ : Fin 66 => (1 / 66 : ℚ))
    (fun t => cliqueConditionalSecond t false) = 234399385 / 480661776 at hsecond
  change expect (fun _ : Fin 66 => (1 / 66 : ℚ))
    (fun t => cliqueConditionalV t false) = 1040129476423 / 2326402995840 at hvariance
  -- The identity follows from the product law and rational casting.
  have hreal (u : Fin 66 → Fin 66 → ℚ) (v : Fin 66 → ℚ)
      (hu : ∀ t : Fin 66, expect (fun _ : Fin 66 => (1 / 66 : ℚ)) (u t) = v t) :
      expect (fun x : Fin 66 × Fin 66 => ((cliqueJointMass false x : ℚ) : ℝ))
        (fun x => ((u x.1 x.2 : ℚ) : ℝ)) =
        ((expect (fun _ : Fin 66 => (1 / 66 : ℚ)) v : ℚ) : ℝ) := by
    rw [ratCast_expect, clique_joint_expectation false u]
    simp_rw [clique_observation_independent_mass, hu]
  refine ⟨?_, ?_, ?_⟩
  · calc
      expect (indepMass P) indepT =
          expect (fun x : Fin 66 × Fin 66 => ((cliqueJointMass false x : ℚ) : ℝ))
            (fun x => htContrast (fun z => exposure cliqueAdj z) yR
              (castW x.1) .d01 .d00 (cliqueAssignments x.2)) :=
        htransport P hP (fun w _ z =>
          htContrast (fun z' => exposure cliqueAdj z') yR w .d01 .d00 z)
      _ = expect (fun x : Fin 66 × Fin 66 => ((cliqueJointMass false x : ℚ) : ℝ))
          (fun x => ((cliqueT x.1 x.2 : ℚ) : ℝ)) := by
        apply congrArg (expect _)
        funext x
        exact (hidentify x.1 x.2).1
      _ = ((expect (fun _ : Fin 66 => (1 / 66 : ℚ))
          (fun t => cliqueConditionalMean t false) : ℚ) : ℝ) :=
        hreal (fun t r => cliqueT t r) (fun t => cliqueConditionalMean t false)
          (fun t => (hconditional t).1)
      _ = -67 / 53592 := by norm_num [hmean]
  · calc
      expect (indepMass P) (fun x => indepT x ^ 2) =
          expect (fun x : Fin 66 × Fin 66 => ((cliqueJointMass false x : ℚ) : ℝ))
            (fun x => htContrast (fun z => exposure cliqueAdj z) yR
              (castW x.1) .d01 .d00 (cliqueAssignments x.2) ^ 2) :=
        htransport P hP (fun w _ z =>
          htContrast (fun z' => exposure cliqueAdj z') yR w .d01 .d00 z ^ 2)
      _ = expect (fun x : Fin 66 × Fin 66 => ((cliqueJointMass false x : ℚ) : ℝ))
          (fun x => ((cliqueT x.1 x.2 ^ 2 : ℚ) : ℝ)) := by
        apply congrArg (expect _)
        funext x
        rw [(hidentify x.1 x.2).1, Rat.cast_pow]
      _ = ((expect (fun _ : Fin 66 => (1 / 66 : ℚ))
          (fun t => cliqueConditionalSecond t false) : ℚ) : ℝ) :=
        hreal (fun t r => cliqueT t r ^ 2) (fun t => cliqueConditionalSecond t false)
          (fun t => (hconditional t).2.1)
      _ = 234399385 / 480661776 := by norm_num [hsecond]
  · calc
      expect (indepMass P) indepV =
          expect (fun x : Fin 66 × Fin 66 => ((cliqueJointMass false x : ℚ) : ℝ))
            (fun x => varianceEstimate (fun z => exposure cliqueAdj z) yR
              (castW x.1) (castJ x.1) .d01 .d00 (cliqueAssignments x.2)) :=
        htransport P hP (fun w q z =>
          varianceEstimate (fun z' => exposure cliqueAdj z') yR w q .d01 .d00 z)
      _ = expect (fun x : Fin 66 × Fin 66 => ((cliqueJointMass false x : ℚ) : ℝ))
          (fun x => ((cliqueV x.1 x.2 : ℚ) : ℝ)) := by
        apply congrArg (expect _)
        funext x
        exact (hidentify x.1 x.2).2
      _ = ((expect (fun _ : Fin 66 => (1 / 66 : ℚ))
          (fun t => cliqueConditionalV t false) : ℚ) : ℝ) :=
        hreal (fun t r => cliqueV t r) (fun t => cliqueConditionalV t false)
          (fun t => (hconditional t).2.2)
      _ = 1040129476423 / 2326402995840 := by norm_num [hvariance]

end

end AronowAudit.P044.Wave1.SimulatedVariance
