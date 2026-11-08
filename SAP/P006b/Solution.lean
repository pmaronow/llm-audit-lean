import SAP.P006b.T26Repair
import SAP.P006b.WH.W1.Proofs.T17
import SAP.P006b.WH.W1.Proofs.T18
import SAP.P006b.WH.W1.Proofs.T25
import SAP.P006b.WH.W1.Proofs.T29
import SAP.P006b.WH.W1.Proofs.T30
import SAP.P006b.Defs
import SAP.P006b.Bridge
import AronowAudit.P006.P006_CounterfactualMetrics
import AronowAudit.P006.Wave1.Gap.GLP006B1
import AronowAudit.P006.Wave1.Gap.GP006B1
import AronowAudit.P006.Wave1.Gap.GP006B2
import AronowAudit.P006.Wave1.AverageBestResponse
import AronowAudit.P006.Wave1.TTAlignment

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P006b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem T16 : T16Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro Ω X U mΩ mX mU hU n E hS PX hPX κ hκ hjoint PiSet hπ hq hcond
      hminmax hmax hest γ hint hγ b s hb hs
    have h := AronowAudit.P006.Wave1.T16_corrected_agent_data_bound_proof
      (Bridge.toProject E) (Bridge.standing_toProject hS) PX hPX κ hκ hjoint
      PiSet hπ hq hcond hminmax hmax hest γ hint hγ b s hb hs
    refine ⟨?_, ?_, h.2⟩
    · intro π hp
      obtain ⟨hlaw,hscore,hbias,hmaxbias⟩ := h.1 π hp
      exact ⟨hlaw,hscore,hbias,hmaxbias,hmaxbias.trans hγ,
        hbias.trans (hmaxbias.trans hγ)⟩
    · change AronowAudit.P006.bestValue PiSet E.V-E.V b = E.V s-E.V b
      rw [AronowAudit.P006.bestValue_eq hs]
  · exact @AronowAudit.P006.T16_sufficient_positivity
  · intro X U mX mU κ hκ p b0 x hx
    have hne : 1-p x ≠ 0 := by linarith
    simpa [selectedBaseline, untreatedProbability] using
      mul_div_cancel_right₀ (b0 x) hne

theorem T17 : SAP.P006b.T17WholeStatement :=
  SAP.P006b.WH.W1.T17_whole

theorem T18 : SAP.P006b.T18WholeStatement :=
  SAP.P006b.WH.W1.T18_whole

theorem T19 : T19Statement := by
  refine ⟨@AronowAudit.P006.T19_corrected_regret, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp _
    exact AronowAudit.P006.T19_corrected_regret_tendsto p hp
  · intro p β π
    refine ⟨rfl,rfl,?_⟩
    dsimp [binaryWelfare,effectP1]
    ring
  · intro m hm
    have h := AronowAudit.P006.T19_corrected_regret (1/2) (2*m)
      (by norm_num) (by linarith)
    have he : regret binaryPolicies (binaryWelfare (1/2) (effectP1 (2*m))) (0,1) =
        1-2*(1/2)+(1/2)*(2*m) := h.2.2.2.1
    rw [he]; ring
  · intro β hβ
    dsimp [effectP1]
    linarith
  · intro p β
    constructor
    · simp [binaryWelfare,effectP1]
    · ring
  · intro p hp hp1
    have he : (fun β : ℝ => 1-2*p+p*β) =ᶠ[atTop]
        (fun β : ℝ => regret binaryPolicies (binaryWelfare p (effectP1 β)) (0,1)) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with β hβ
      exact (AronowAudit.P006.T19_corrected_regret p β ⟨hp,hp1⟩ hβ).2.2.2.1.symm
    exact (AronowAudit.P006.T19_corrected_regret_tendsto p hp).congr' he

theorem T20 : T20Statement := by
  have h := AronowAudit.P006.T20_logistic_counterexample
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  refine ⟨⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩, ?_, ?_, by norm_num, ?_⟩
  · change AronowAudit.P006.logistic 0 ≠ 0
    rw [h4]; norm_num
  · change AronowAudit.P006.logistic (-Real.log 3) ≠ -1/2
    rw [h5]; norm_num
  · change AronowAudit.P006.logistic (-Real.log 3)-AronowAudit.P006.logistic 0 = -1/4
    rw [h4,h5]; norm_num

theorem T21 : T21Statement := by
  refine ⟨?_, @AronowAudit.P006.logistic_bounds, ?_⟩
  · intro d β x
    exact AronowAudit.P006.T21_corrected_logistic_mean (Bridge.fitToProject β) x
  · intro z
    change AronowAudit.P006.signedBernoulliMean (logistic z) = _
    rw [AronowAudit.P006.signed_mean_formula]
    ring

theorem T22 : T22Statement := by
  refine ⟨@AronowAudit.P006.T22_corrected_empirical_mean,
    AronowAudit.P006.T22_two_row_example, ?_⟩
  intro C hC n X m hn
  rfl

theorem T23 : T23Statement := by
  refine ⟨AronowAudit.P006.T23_missing_outcome_counterexample, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [missingObservedMass, missingRecord, missingWorldMass, missingWorldPrevalence,
      missingObservationProbability, coinMass, Fintype.sum_bool]
  · norm_num [missingObservedMass, missingRecord, missingWorldMass, missingWorldPrevalence,
      missingObservationProbability, coinMass, Fintype.sum_bool]
  · norm_num [missingObservedMass, missingRecord, missingWorldMass, missingWorldPrevalence,
      missingObservationProbability, coinMass, Fintype.sum_bool]
  · norm_num [missingObservedMass, missingRecord, missingWorldMass, missingWorldPrevalence,
      missingObservationProbability, coinMass, Fintype.sum_bool]
  · intro world
    have h := AronowAudit.P006.T23_missing_outcome_counterexample.2.2.2.1 world
    change (∑ y0 : Bool, AronowAudit.P006.missingWorldMass world y0 false true) /
      (∑ y0 : Bool, ∑ r : Bool, AronowAudit.P006.missingWorldMass world y0 false r) = 1/2
    rw [h.1,h.2]
    norm_num

theorem T24 : T24Statement := by
  exact @AronowAudit.P006.Wave1.T24_corrected_identification_proof

theorem T25 : SAP.P006b.T25WholeStatement :=
  SAP.P006b.WH.W1.T25_whole

theorem T26 : T26Statement := T26Repair.refutation

theorem T27 : T27Statement := by
  intro h
  apply AronowAudit.P006.Wave1.printed_TT_alignment_refuted
  intro Ω C mΩ mC n E hS PiSet hπ hU
  exact h (Bridge.fromProject E) (Bridge.standing_fromProject hS) PiSet hπ hU

theorem T29 : SAP.P006b.T29WholeStatement :=
  SAP.P006b.WH.W1.T29_whole

theorem T30 : SAP.P006b.T30WholeStatement :=
  SAP.P006b.WH.W1.T30_whole

end
end SAP.P006b
