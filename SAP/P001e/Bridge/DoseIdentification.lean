import SAP.P001e.Defs.DoseIdentification
import SAP.P001e.Bridge
import AronowAudit.P001.Wave1.Gap.DecisionT91
import AronowAudit.P001.Wave1.Gap.GP0014B3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e.Bridge
universe u v w

/-- The unused zero-mass terms of the exported sum are all zero. -/
theorem positiveCellAverage_eq {Ω E : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → E) (m : E → ℝ) :
    positiveCellAverage μ X m = ∑' x : E, m x * probability μ {ω | X ω=x} := by
  unfold positiveCellAverage
  apply tsum_congr
  intro x
  by_cases hx : 0 < probability μ {ω | X ω=x}
  · simp only [hx, if_pos]
  · have hz : probability μ {ω | X ω=x}=0 :=
      le_antisymm (not_lt.mp hx) ENNReal.toReal_nonneg
    simp [hz]

/-- Apply the positive-mass declaration at each selected dose and subtract. -/
theorem t91_positive_mass : T91Statement.{u,v} := by
  have h : PositiveMassDose.{u,v} := PositiveMassDose_iff.mpr
    (@AronowAudit.P001.Wave1.positive_mass_dose_identification_proof)
  intro Ω E _ _ _ _ μ _ X D hX hD Y hY hi hobs hobsI hind d d' hpos
  have ha := h μ X D hX hD Y hY hi hobs hobsI hind d (fun x hx => (hpos x hx).1)
  have hb := h μ X D hX hD Y hY hi hobs hobsI hind d' (fun x hx => (hpos x hx).2)
  have hs : expectation μ (fun ω => Y d' ω-Y d ω) =
      expectation μ (Y d')-expectation μ (Y d) := integral_sub (hi d') (hi d)
  have had : expectation μ (Y d)=standardizedDoseMean μ X D (fun ω => Y (D ω) ω) d :=
    ha.2.trans (standardizedDoseMean_eq μ X D _ d).symm
  have hbd : expectation μ (Y d')=standardizedDoseMean μ X D (fun ω => Y (D ω) ω) d' :=
    hb.2.trans (standardizedDoseMean_eq μ X D _ d').symm
  exact ⟨fun x hx => ⟨ha.1 x hx,hb.1 x hx⟩,had,hbd,by rw [hs,had,hbd]⟩

/-- Use the evaluation-ready declaration exactly with its state contract. -/
theorem t91_continuous : T91ContinuousIdentification.{u,v,w} := by
  intro Ω E V _ _ _ _ _ μ _ X D hX hD curve hcurve eval heval hfaithful hind hi hobs
    d d' hm hsupp
  have h := AronowAudit.P001.Wave1.continuous_dose_identified_evaluation_ready
    μ X D hX hD curve hcurve eval heval hfaithful hind hi hobs d d' hm hsupp
  dsimp only at h ⊢
  rcases h with ⟨hcef,hcontrast,hversions⟩
  refine ⟨hcef,?_,?_,?_⟩
  · intro t
    rw [positiveCellAverage_eq]
    exact (AronowAudit.P001.Wave1.DecisionT91_standardization
      μ X hX (fun ω => eval t (curve ω)) (hi t)).tsum_eq.symm
  · simpa only [positiveCellAverage_eq, expectation_eq, cellMean_eq, probability_eq] using hcontrast
  · intro mobs hversion
    obtain ⟨hvalues,hmean⟩ := hversions mobs hversion
    exact ⟨hvalues, by
      simpa only [positiveCellAverage_eq, expectation_eq, probability_eq] using hmean⟩

end SAP.P001e.Bridge
