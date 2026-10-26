import AronowAudit.P004.Wave1.NedHeadlineBlueprint
import AronowAudit.P004.Wave1.NedHeadline.RATIO
import AronowAudit.P004.Wave1.NedHeadline.DEN
import AronowAudit.P004.Wave1.NedHeadline.H2
import AronowAudit.P004.Wave1.NedHeadline.H3
import AronowAudit.P004.Wave1.NedHeadline.H4
import AronowAudit.P004.Wave1.DesignLimits.DL4
import AronowAudit.P004.Wave1.DesignLimits.DL5

universe u

namespace AronowAudit.P004.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators

theorem ned_headline_under_uniform_spacing
    {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    (P : PopulationSequence Space) (p d : ℝ)
    (hp : 0 < p ∧ p < 1) (hd : 0 ≤ d) (hb : BoundedOutcomes P)
    (hWD : ∀ᶠ N in atTop, WellDefined (P N) d) (hNED : NEDConditions P p d)
    (hmetric : MetricNodeDistances P) (hspacing : QuadraticSpacing P) :
    (∀ N, expect (fun _ => p) (ht (fun _ => p) (circleAverage (P N) d)) =
      ame (fun _ => p) (circleAverage (P N) d)) ∧
    Asymptotics.IsBigO atTop
      (fun N => variance (fun _ => p) (ht (fun _ => p) (circleAverage (P N) d)))
      (fun N => (N : ℝ)⁻¹) ∧
    InProb (fun _ _ => p) (fun N z => Real.sqrt N *
      (linearHajek (fun _ => p) (circleAverage (P N) d) z - hajek (circleAverage (P N) d) z)) ∧
    (Nondegenerate (fun N => variance (fun _ => p)
        (linearHajek (fun _ => p) (circleAverage (P N) d))) →
      NormalLimit (fun _ _ => p) (fun N z =>
        (hajek (circleAverage (P N) d) z - ame (fun _ => p) (circleAverage (P N) d)) /
          Real.sqrt (variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage (P N) d))))) := by
  exact NedHeadline.assemble NedHeadline.h2_proof NedHeadline.h3_proof NedHeadline.h4_proof
    dl3_proof dl4_proof dl5_proof P p d hp hd hb hWD hNED hmetric hspacing

end
end AronowAudit.P004.Wave1
