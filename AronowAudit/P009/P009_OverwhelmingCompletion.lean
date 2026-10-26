/- Complete-randomization overwhelming-fraction mixing, derived from the finite mask bound and explicit quarter-power degree thresholds. -/
import AronowAudit.P009.P009_MixingAsymptotic
import AronowAudit.P009.P009_CompleteMixing
namespace AronowAudit.P009
open Filter
open scoped Topology
noncomputable section
theorem corrected_exceptional_pair_mixing_completed (S : Study)
    (hCR : ∀ t, ∃ m, Complete (S.experiment t) m)
    (hBound : ∃ D, ∀ᶠ t in atTop, dAvg (S.experiment t) ≤ D) :
    ∃ exceptions : (t : ℕ) → Finset (Fin (S.N t) × Fin (S.N t)),
      (∀ t, ∀ ij ∈ exceptions t, d (S.experiment t) ij.1 ij.2 = 0) ∧
      Tendsto (fun t => (exceptions t).card / ((Finset.univ.filter
        (fun ij : Fin (S.N t) × Fin (S.N t) => d (S.experiment t) ij.1 ij.2 = 0)).card : ℝ))
        atTop (nhds 0) ∧
      (∀ ε > 0, ∀ᶠ t in atTop, ∀ i j, d (S.experiment t) i j = 0 →
        (i,j) ∉ exceptions t →
        alpha (S.experiment t).design (masked (S.experiment t) i) (masked (S.experiment t) j) < ε) := by
  obtain ⟨hpos,hgrow,hsmall,hsq⟩:=MixingAsymptotic.quarter_power_parameters S
  apply MixingAsymptotic.overwhelming_fraction_from_threshold S ?_ hCR hBound
    (fun t=>(size S t)^(1/4:ℝ)) hpos hgrow hsmall hsq
  intro n E m hm i j hij hs
  exact CompleteMixing.complete_mask_mixing_finite_completed E m hm i j hij hs
end
end AronowAudit.P009

namespace AronowAudit.P009
open Filter
open scoped Topology BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
theorem corrected_exceptional_pair_mixing (S : Study)
    (hCR : ∀ t, ∃ m, Complete (S.experiment t) m)
    (hBound : ∃ D, ∀ᶠ t in atTop, dAvg (S.experiment t) ≤ D) :
    ∃ exceptions : (t : ℕ) → Finset (Fin (S.N t) × Fin (S.N t)),
      (∀ t, ∀ ij ∈ exceptions t, d (S.experiment t) ij.1 ij.2 = 0) ∧
      Tendsto (fun t => (exceptions t).card / ((Finset.univ.filter
        (fun ij : Fin (S.N t) × Fin (S.N t) => d (S.experiment t) ij.1 ij.2 = 0)).card : ℝ))
        atTop (nhds 0) ∧
      (∀ ε > 0, ∀ᶠ t in atTop, ∀ i j, d (S.experiment t) i j = 0 →
        (i,j) ∉ exceptions t →
        alpha (S.experiment t).design (masked (S.experiment t) i) (masked (S.experiment t) j) < ε) := by
  exact corrected_exceptional_pair_mixing_completed S hCR hBound

end
end AronowAudit.P009
