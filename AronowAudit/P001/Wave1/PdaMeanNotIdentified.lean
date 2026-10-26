import AronowAudit.P001.Wave1.PdaMeanNotIdentifiedBlueprint
import AronowAudit.P001.Wave1.PdaMeanNotIdentified.N1
import AronowAudit.P001.Wave1.PdaMeanNotIdentified.N2
import AronowAudit.P001.Wave1.PdaMeanNotIdentified.N3
import AronowAudit.P001.Wave1.PdaMeanNotIdentified.N4
import AronowAudit.P001.Wave1.PdaMeanNotIdentified.N5
import AronowAudit.P001.Wave1.PdaMeanNotIdentified.N6
import AronowAudit.P001.Wave1.PdaMeanNotIdentified.N7
import AronowAudit.P001.Wave1.PdaMeanNotIdentified.N8
import AronowAudit.P001.Wave1.PdaMeanNotIdentified.N9

namespace AronowAudit.P001.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidableP001cFinalPdaMeanNotIdentified (p : Prop) : Decidable p := Classical.propDecidable p

theorem pda_at_mean_not_identified :
    IsProbabilityMeasure gapJointLaw ∧
    HasJointPDF gapJointLaw (fun xy => gapPDF xy.1 *
      (if xy.2 ∈ Set.Icc (-1 : ℝ) 1 then 1 / 2 else 0)) ∧
    HasPDF (gapJointLaw.map Prod.fst) gapPDF ∧
    gapJointLaw.map Prod.snd = uniformLaw (-1) 1 ∧
    gapJointLaw = (gapJointLaw.map Prod.fst).prod (gapJointLaw.map Prod.snd) ∧
    (∀ᵐ xy ∂gapJointLaw,
      xy.1 ∈ Set.Icc (-2 : ℝ) 2 ∧ xy.2 ∈ Set.Icc (-1 : ℝ) 1) ∧
    mean gapJointLaw Prod.fst = 0 ∧ gapPDF 0 = 0 ∧
    IsCEF gapJointLaw Prod.fst Prod.snd (fun _ => 0) ∧
    ContDiff ℝ 1 pdaBump ∧
    (∀ a : ℝ, IsCEF gapJointLaw Prod.fst Prod.snd (fun x => a * pdaBump x) ∧
      deriv (fun x => a * pdaBump x) (mean gapJointLaw Prod.fst) = a) ∧
    ¬ (∀ m m' : ℝ → ℝ,
      IsCEF gapJointLaw Prod.fst Prod.snd m →
      IsCEF gapJointLaw Prod.fst Prod.snd m' →
      (∀ x, 0 < gapPDF x → DifferentiableAt ℝ m x) →
      (∀ x, 0 < gapPDF x → DifferentiableAt ℝ m' x) →
      ∃ a : ℝ, HasDerivAt m a (mean gapJointLaw Prod.fst) ∧
        HasDerivAt m' a (mean gapJointLaw Prod.fst)) :=
  PdaMeanNotIdentified.assemble PdaMeanNotIdentified.n1_proof PdaMeanNotIdentified.n2_proof
    PdaMeanNotIdentified.n3_proof PdaMeanNotIdentified.n4_proof PdaMeanNotIdentified.n5_proof
    PdaMeanNotIdentified.n6_proof PdaMeanNotIdentified.n7_proof PdaMeanNotIdentified.n8_proof
    PdaMeanNotIdentified.n9_proof

end
end AronowAudit.P001.Wave1
