import AronowAudit.P029.Wave1.ConditionalSufficiencyBlueprint

namespace AronowAudit.P029.Wave1.ConditionalSufficiency

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029 AronowAudit.P029.Wave1.FiniteMeasure

noncomputable section

/-- The conditional-independence law has unweighted IV 5/8 and ATE 1/2. -/
theorem n1_proof : N1 := by
  classical
  intro hFM1 hFM2 hFM3 hFM6
  rcases conditional_independence_counterexample with
    ⟨hfiv, _hci, _hli, hs0, hs1, _hsl0, _hsl1, _hce0, _hce1,
      hmean, _hct, hwald, _hweighted⟩
  have hp : ValidLaw conditionalJoint := hfiv.1
  obtain ⟨hprob, hIntegral, _hMass, _hCE⟩ := hFM1 conditionalJoint hp
  have hiv : IVAssumptions (atomicMeasure conditionalJoint)
      (liftUnit independenceUnit) Prod.snd :=
    hFM3 hFM1 hFM2 conditionalJoint (liftUnit independenceUnit) Prod.snd hfiv
  obtain ⟨hWald, hScore⟩ :=
    hFM6 hFM1 conditionalJoint hp (liftUnit independenceUnit) Prod.snd
  have hpos : ∀ x : Bool,
      0 < mP (atomicMeasure conditionalJoint) {i | (liftUnit independenceUnit i).x = x} →
        0 < scoreAt (atomicMeasure conditionalJoint) (liftUnit independenceUnit) x := by
    intro x _hx
    cases x
    · rw [hScore false, hs0]
      norm_num
    · rw [hScore true, hs1]
      norm_num
  have hWaldM : mWald (atomicMeasure conditionalJoint) (liftUnit independenceUnit)
      Prod.snd (fun _ => 1) = 5 / 8 :=
    (hWald (fun _ => 1)).trans hwald
  have hMeanM : (∫ i, (liftUnit independenceUnit i).tau ∂(atomicMeasure conditionalJoint)) =
      1 / 2 :=
    (hIntegral (fun i => (liftUnit independenceUnit i).tau)).2.trans hmean
  refine ⟨hprob, hiv, hpos, ?_⟩
  intro heq
  have hbad : (5 / 8 : ℝ) = 1 / 2 := hWaldM.symm.trans (heq.trans hMeanM)
  norm_num at hbad

end

end AronowAudit.P029.Wave1.ConditionalSufficiency
