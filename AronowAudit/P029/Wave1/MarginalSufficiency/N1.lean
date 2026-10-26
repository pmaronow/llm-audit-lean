import AronowAudit.P029.Wave1.MarginalSufficiencyBlueprint

namespace AronowAudit.P029.Wave1.MarginalSufficiency

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029 AronowAudit.P029.Wave1.FiniteMeasure

noncomputable section

/-- The marginal-independence law fails latent ignorability at the profile `false`. -/
theorem n1_proof : N1 := by
  classical
  intro hFM1 hFM2 hFM3 hFM6
  rcases marginal_independence_counterexample with
    ⟨hfiv, _hindep, _ht1, _ht0, hx0, _hx1, hs0, hs1, _hsl0, _hsl1,
      hce0, hcc0, _hce1, _hcc1, _hmean, _hwald, _hweightMean, _hweighted⟩
  have hp : ValidLaw marginalJoint := hfiv.1
  obtain ⟨hprob, _hIntegral, hMass, hCE⟩ := hFM1 marginalJoint hp
  have hiv : IVAssumptions (atomicMeasure marginalJoint)
      (liftUnit independenceUnit) Prod.snd :=
    hFM3 hFM1 hFM2 marginalJoint (liftUnit independenceUnit) Prod.snd hfiv
  have hScore := (hFM6 hFM1 marginalJoint hp (liftUnit independenceUnit) Prod.snd).2
  have hpos : ∀ x : Bool,
      0 < mP (atomicMeasure marginalJoint) {i | (liftUnit independenceUnit i).x = x} →
        0 < scoreAt (atomicMeasure marginalJoint) (liftUnit independenceUnit) x := by
    intro x _hx
    cases x
    · rw [hScore false, hs0]
      norm_num
    · rw [hScore true, hs1]
      norm_num
  have hprofile : mP (atomicMeasure marginalJoint)
      {i | (liftUnit independenceUnit i).x = false} = 5 / 8 := by
    rw [hMass]
    simpa only [Set.mem_setOf_eq, liftUnit] using hx0
  have hmeanX : mCE (atomicMeasure marginalJoint) (fun i => (liftUnit independenceUnit i).tau)
      {i | (liftUnit independenceUnit i).x = false} = 2 / 5 := by
    rw [hCE]
    simpa only [Set.mem_setOf_eq, liftUnit] using hce0
  have hmeanC : mCE (atomicMeasure marginalJoint) (fun i => (liftUnit independenceUnit i).tau)
      {i | (liftUnit independenceUnit i).complier ∧ (liftUnit independenceUnit i).x = false} =
      1 / 4 := by
    rw [hCE]
    simpa only [Set.mem_setOf_eq, liftUnit] using hcc0
  refine ⟨hprob, hiv, hpos, ?_, ?_⟩
  · rw [hprofile]
    norm_num
  · intro hlatent
    unfold latentAt at hlatent
    have hbad : (2 / 5 : ℝ) = 1 / 4 := hmeanX.symm.trans (hlatent.trans hmeanC)
    norm_num at hbad

end

end AronowAudit.P029.Wave1.MarginalSufficiency
