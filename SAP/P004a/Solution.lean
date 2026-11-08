import SAP.P004a.Defs
import SAP.P004a.Bridge
import AronowAudit.P004.Wave1.Gap.DecideP004T1
import AronowAudit.P004.Wave1.Gap.GLP0042B1
import AronowAudit.P004.Wave1.Gap.GLP0042B3
import AronowAudit.P004.Wave1.AreaSum
import AronowAudit.P004.Wave1.Gap.GLP0042B5
import AronowAudit.P004.Wave1.Gap.GP0042B2b
import AronowAudit.P004.Wave1.Gap.GLP0042B6
import AronowAudit.P004.Wave1.Gap.GLP0041B1
import AronowAudit.P004.Wave1.Gap.GLP0041B2
import AronowAudit.P004.Wave1.Gap.GP0041B1
import AronowAudit.P004.Wave1.Gap.FidP004
import AronowAudit.P004.P004_SpatialAlgebraCompletion
import AronowAudit.P004.P004_ConfidenceCompletion
import SAP.P004a.WH.W1.Proofs.T15
import SAP.P004a.WH.W1.Proofs.T1
import SAP.P004a.WH.W1.Proofs.T3
import SAP.P004a.WH.W1.Proofs.T4
import SAP.P004a.WH.W1.Proofs.T5
import SAP.P004a.WH.W2.Proofs.T8
import SAP.P004a.WH.W2.Proofs.T9
import SAP.P004a.WH.W2.Proofs.T14

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a
universe u v
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Classical Topology ENNReal NNReal
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
variable {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]

theorem T1 : SAP.P004a.T1WholeStatement := SAP.P004a.WH.W1.T1_whole

theorem T2 : T2Statement (Space := Space) := by
  constructor
  · intro k P O θ₀ Θ θhat d h hd hh hP hWD hloc hlog hinterior hoverlap
    exact AronowAudit.P004.Wave1.corrected_ipw_asymptotics_proof
      (Bridge.toSequence P) O θ₀ Θ θhat d h hd hh hP hWD hloc hlog hinterior hoverlap
  · intro N k p R O B hN hp _hunit hself hsymm houtside
    have hf := AronowAudit.P004.corrected_ipw_finite p R O hp
    have ho := AronowAudit.P004.corrected_ipw_oracle p R O B hN hp hself hsymm houtside
    refine ⟨?_, hf.1, hf.2.1, hf.2.2, ?_, ho.1, ho.2⟩
    · intro i
      exact AronowAudit.P004.corrected_fits (p i)
        (printedFits p R O i true - printedFits p R O i false)
        (dot (O i) (scoreGamma p R O)) (hp i).1.ne' (sub_pos.mpr (hp i).2).ne'
    · exact AronowAudit.P004.augmented_variance p R B (scoreFits p R O) hN hp hself houtside

theorem T3 : SAP.P004a.T3WholeStatement := SAP.P004a.WH.W1.T3_whole

theorem T4 : SAP.P004a.T4WholeStatement := SAP.P004a.WH.W1.T4_whole

theorem T5 : SAP.P004a.T5WholeStatement := SAP.P004a.WH.W1.T5_whole

theorem T6 : T6Statement.{u} := by
  refine ⟨?_, @AronowAudit.P004.randomization_scaling, ?_⟩
  · intro A _ N m ζ B Y p _hN hm hB hdis hmass hint hp
    let a := fun i k => (ζ (B i k)).toReal
    let R := fun k i z => (∫ x in B i k, Y x z ∂ζ) / a i k
    let whole := fun i z => (∫ x in ⋃ k, B i k, Y x z ∂ζ) / (ζ (⋃ k, B i k)).toReal
    have ha (i : Fin N) (k : Fin m) : 0 < a i k :=
      ENNReal.toReal_pos (hmass i k).1.ne' (hmass i k).2.ne
    have he (i : Fin N) (z : Assignment N) : whole i z = finiteAverage (a i) (fun k => R k i z) := by
      simpa only [whole, R, a, finiteAverage, Finset.sum_div, div_mul_eq_mul_div] using
        AronowAudit.P004.area_partition_identity ζ (B i) (fun x => Y x z) hm
          (hB i) (hdis i) (hmass i) (fun k => hint i k z)
    have hw : whole = fun i z => finiteAverage (a i) (fun k => R k i z) :=
      funext (fun i => funext (he i))
    have h := AronowAudit.P004.bin_effect_aggregation p R a hp ha
    have hnode (i : Fin N) : nodeEffect p whole i = finiteAverage (a i) (fun k => nodeEffect p (R k) i) :=
      (congrArg (fun F => nodeEffect p F i) hw).trans (h.1 i)
    refine ⟨he, ?_, hnode, (congrArg (ame p) hw).trans h.2, ?_, ?_⟩
    · exact fun i arm => (congrArg (fun F => marginal p F i arm) hw).trans
        (AronowAudit.P004.marginal_bin_average p R a i arm)
    · intro i lo hi hbounds
      change lo ≤ nodeEffect p whole i ∧ nodeEffect p whole i ≤ hi
      rw [hnode i]
      exact (AronowAudit.P004.weighted_effect_bounds (a i) _ hm (ha i)).1 lo hi hbounds
    · intro i c hc
      exact (hnode i).trans ((AronowAudit.P004.weighted_effect_bounds (a i) _ hm (ha i)).2 c hc)
  · intro N w T obs c hc
    simp_rw [AronowAudit.P004.randomization_scaling c _ _ hc]

theorem T7 : T7Statement := by
  have hf := AronowAudit.P004.adjusted_pd_finite_counterexample
  have ha := AronowAudit.P004.Wave1.adjusted_pd_asymptotic_counterexample_proof
  refine ⟨⟨hf, ?_, ?_⟩, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1,
    ha.2.2.2.2.1, ?_, ha.2.2.2.2.2.1, ?_, ha.2.2.2.2.2.2.2.2.2.2.2⟩
  · have hV : kernelVariance starAssignment20 (residual (starBlockTable 4) starAssignment20)
        (starBlockKernel 4 true) = 4/25 := hf.2.2.2.2.2.1
    have hμ : adjustmentMu starAssignment20 (starBlockKernel 4 true) = 101/100 := hf.2.2.2.2.2.2.2.1
    rw [hV, hμ]
    exact AronowAudit.P004.adjusted_pd_constants.1
  · have hV : kernelVariance starAssignment20 (residual (starBlockTable 4) starAssignment20)
        (starBlockKernel 4 false) = 4/25 := hf.2.2.2.2.1
    have hμ : adjustmentMu starAssignment20 (starBlockKernel 4 false) = 41/50 := hf.2.2.2.2.2.2.1
    rw [hV, hμ]
    exact AronowAudit.P004.adjusted_pd_constants.2.1
  · intro N i j hij
    exact AronowAudit.P004.Wave1.t7_star_local N 0 i j (lt_trans (by norm_num) hij)
  · intro ε hε
    have ht := (tendsto_order.mp ha.2.2.2.2.2.2.2.2.2.2.1).2
      (2*normalCDF (normalQuantile (39/40)*Real.sqrt (15/16))-1+ε) (lt_add_of_pos_right _ hε)
    filter_upwards [ht] with m hm
    refine lt_of_le_of_lt ?_ hm
    exact AronowAudit.P004.Wave1.GP0042B2b_capped_pd_prob_mono
      (fun _ => 1/2) (fun _ => by norm_num) _ _ (fun z hz => hz.2.2.2.2)

theorem T8 : SAP.P004a.T8WholeStatement.{u} := SAP.P004a.WH.W2.T8_whole.{u}

theorem T9 : SAP.P004a.T9WholeStatement := SAP.P004a.WH.W2.T9_whole

theorem T10 : T10Statement := by
  exact @AronowAudit.P004.Wave1.corrected_mle_proof

theorem T11 : T11Statement := by
  constructor
  · intro N p R hN hp
    exact ⟨AronowAudit.P004.ht_unbiased p R hp,
      AronowAudit.P004.printed_obs_ht_expectation p R hN hp⟩
  · intro N hN
    have hp : ∀ _i : Fin N, 0 < (1/4 : ℝ) ∧ (1/4 : ℝ) < 1 := fun _ => by norm_num
    have hm (i : Fin N) (a : Bool) :
        AronowAudit.P004.marginal (fun _ : Fin N => 1/4) (fun _ _ => 1) i a = 1 := by
      rw [AronowAudit.P004.marginal_is_marginalization _ _ i a hp]
      exact AronowAudit.P004.expect_const _ 1
    have he := AronowAudit.P004.printed_obs_ht_expectation
      (fun _ : Fin N => 1/4) (fun _ _ => 1) hN hp
    have hame : ame (fun _ : Fin N => 1/4) (fun _ _ => 1) = 0 := by
      change AronowAudit.P004.ame _ _ = 0
      simp only [AronowAudit.P004.ame, AronowAudit.P004.nodeEffect, hm, sub_self,
        Finset.sum_const_zero, zero_div]
    refine ⟨hame, ?_, ?_⟩
    · change AronowAudit.P004.expect (fun _ : Fin N => 1/4)
        (AronowAudit.P004.printedObsHT (fun _ => 1/4) (fun _ _ => 1)) = -2
      rw [he.1]
      simp only [hm]
      norm_num [Finset.sum_const, hN.ne']
      field_simp
    · exact (AronowAudit.P004.ht_unbiased _ _ hp).trans hame

theorem T12 : T12Statement := by
  exact ⟨AronowAudit.P004.Wave1.mc_signed_spatial_counterexample_proof,
    AronowAudit.P004.Wave1.mc_level_spatial_counterexample_proof⟩

theorem T13 : T13Statement := by
  refine ⟨@AronowAudit.P004.Wave1.mc_exact_level, ?_, by norm_num⟩
  intro N P T draws hP
  have hB : mcExceedances T draws ≤ P := by
    unfold mcExceedances
    calc
      _ ≤ (Finset.univ.erase (0 : Fin (P+1))).card := Finset.card_le_card (by
        intro r hr
        exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hr).2.1, Finset.mem_univ r⟩)
      _ = P := by simp
  exact AronowAudit.P004.mc_plus_one_identity P (mcExceedances T draws) hP hB

theorem T14 : SAP.P004a.T14WholeStatement := SAP.P004a.WH.W2.T14_whole

theorem T15 : SAP.P004a.T15WholeStatement.{u,v} := SAP.P004a.WH.W1.T15_whole.{u,v}

end
end SAP.P004a
