import AronowAudit.P009.Wave1.Gap.GLP0092B2
import AronowAudit.P009.Wave1.Gap.GLP0091B8

namespace AronowAudit.P009.Wave1

open scoped BigOperators Topology
open Filter

noncomputable section

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

open BernoulliCompletion MixingBasics

/-- Proposition 6 with the observed maximum at the fixed common constant `k`
and any admissible potential exponent `s`. The maximum premise identifies the
paper's exponent; the proof needs only its admissibility in `hReg`.
The `hajek` definition sets the entire contrast to zero when either arm is empty. -/
theorem arbitrary_ADSE_consistency_paper
    (S : AronowAudit.P009.Study) (k : ℝ)
    (q s : AronowAudit.P009.MomentIndex)
    (hReg : AronowAudit.P009.RegularMix S k q s)
    (hQMax : ∀ r : AronowAudit.P009.MomentIndex, 2 ≤ r →
      (∀ t i, AronowAudit.P009.MomentBound (S.experiment t).design
        ((S.experiment t).outcome i) k r) → r ≤ q)
    (hRestricted : AronowAudit.P009.Restricted S)
    (hExt : AronowAudit.P009.LittleO
      (fun t => AronowAudit.P009.alphaExt (S.experiment t)
        (AronowAudit.P009.extExponent q)) (AronowAudit.P009.size S)) :
    AronowAudit.P009.EstimatorClaims S
      (fun t => AronowAudit.P009.adse (S.experiment t))
      (fun t => AronowAudit.P009.bernoulliRate S t +
        Real.sqrt (AronowAudit.P009.alphaExt (S.experiment t)
          (AronowAudit.P009.extExponent q)) /
          Real.sqrt (AronowAudit.P009.size S t)) := by
  have hHT : Op S (fun t z => ht (S.experiment t) z-adse (S.experiment t))
      (t46A_rate S q) :=
    op_of_second_moment S _ (t46A_rate S q) (4*(40*k^4+k^2))
      (by have hk := hReg.1; positivity)
      (t46A_rate_pos S q) (t46A_ht_mse S k q s hReg)
  have hHJ := t46A_hajek_op S k q s hReg hRestricted hExt
  have hzero := t46A_rate_zero S q hRestricted hExt
  exact ⟨probability_of_op_zero S _ _ hzero hHT,
    probability_of_op_zero S _ _ hzero hHJ, hHT, hHJ⟩

/-- Proposition 1 with an explicit completion convention: `hajek` is the Hájek
contrast with the entire contrast set to zero when either arm is empty.
Definition 6 of the paper leaves it undefined there. -/
theorem unrestricted_inconsistency_zero_completion
    (S : AronowAudit.P009.Study) (k : ℝ) (hk : 0 < k)
    (hA : ∀ t i, k⁻¹ ≤ AronowAudit.P009.marginal (S.experiment t) i true ∧
      AronowAudit.P009.marginal (S.experiment t) i true ≤ 1-k⁻¹)
    (hFail : ¬ AronowAudit.P009.Restricted S) :
    ∃ y : (t : ℕ) → Fin (S.N t) → AronowAudit.P009.Assignment (S.N t) → ℝ,
      let S' : AronowAudit.P009.Study := {S with experiment := fun t =>
        {S.experiment t with outcome := y t}}
      (∃ K q s, AronowAudit.P009.RegularSequence S' K q s) ∧
      (∃ L > 0,
        AronowAudit.P009.HasLimsup
          (fun t => AronowAudit.P009.dAvg (S.experiment t) /
            AronowAudit.P009.size S t) L ∧
        AronowAudit.P009.HasLimsup
          (fun t => AronowAudit.P009.dAvg (S'.experiment t) /
            AronowAudit.P009.size S' t) L) ∧
      ¬ AronowAudit.P009.InProbability S'
        (fun t z => AronowAudit.P009.ht (S'.experiment t) z -
          AronowAudit.P009.eate (S'.experiment t)) ∧
      ¬ AronowAudit.P009.InProbability S'
        (fun t z => AronowAudit.P009.hajek (S'.experiment t) z -
          AronowAudit.P009.eate (S'.experiment t)) := by
  exact unrestricted_inconsistency_proof S k hk hA hFail

end

end AronowAudit.P009.Wave1
