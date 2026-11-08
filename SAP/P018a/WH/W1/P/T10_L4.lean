import SAP.P018a.WH.W1.Leaves
import AronowAudit.P018.Wave1.WeightedConsistency.M10

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

noncomputable section

open SAP.P018a Finset Matrix MeasureTheory ProbabilityTheory Filter
open AronowAudit.P018.Wave1.WeightedConsistency
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

theorem SAP.P018a.WH.W1.T10_L4_proof : SAP.P018a.WH.W1.T10_L4 := by
  intro U _ k R K dir v C H hS hreg hGram hScore
  let R' : AronowAudit.P018.RepeatedKernel U k := SAP.P018a.Bridge.toRepeated R
  let β : Vec k := SAP.P018a.populationBeta K
  have hβ : β = popBeta (K.μ) K.X K.Y := rfl
  have hμ : R'.μ = K.μ := hS.2.1.1
  letI instUnitProbability : IsProbabilityMeasure R'.μ := by
    rw [hμ]
    exact hS.1.1
  letI instSamplesProbability : ∀ N,
      IsProbabilityMeasure (AronowAudit.P018.repeatedLaw R' N) := by
    intro N
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => R'.μ))
    infer_instance
  have hHdet : H.det ≠ 0 := ne_of_gt hS.2.2.2.1.det_pos
  have hc : ContinuousAt (fun A : Mat k => A⁻¹) H := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hHdet
  have hlim : Tendsto (fun N : ℕ => AronowAudit.P018.recordWeightedH R' (v N))
      atTop (𝓝 H) := by
    change Tendsto (fun N : ℕ => SAP.P018a.recordWeightedH R (v N)) atTop (𝓝 H)
    exact hS.2.2.2.2
  have hA : AronowAudit.P018.inProbability (AronowAudit.P018.repeatedLaw R')
      (fun N ω => AronowAudit.P018.Wave1.WeightedConsistency.normGram R' v N ω - H) := by
    change AronowAudit.P018.inProbability (AronowAudit.P018.repeatedLaw R')
      (fun N ω => AronowAudit.P018.Wave1.WeightedConsistency.normGram R' v N ω -
        AronowAudit.P018.recordWeightedH R' (v N)) at hGram
    have hd : AronowAudit.P018.inProbability (AronowAudit.P018.repeatedLaw R')
        (fun N (_ : Fin N → U) => AronowAudit.P018.recordWeightedH R' (v N) - H) :=
      AronowAudit.P018.Wave1.WeightedConsistency.inProbability_deterministic
        (AronowAudit.P018.repeatedLaw R') _
        (by convert hlim.sub_const H using 1 <;> simp only [sub_self] <;> rfl)
    have hh := AronowAudit.P018.Wave1.WeightedConsistency.inProbability_add
      (AronowAudit.P018.repeatedLaw R') hGram hd
    simpa only [sub_add_sub_cancel] using hh
  have hi := AronowAudit.P018.Wave1.WeightedConsistency.inProbability_continuousAt
    (AronowAudit.P018.repeatedLaw R') hc hA
  let s := fun N (ω : Fin N → U) =>
    (AronowAudit.P018.Dreal N)⁻¹ • ∑ d : Dyad N,
      AronowAudit.P018.recordWeightedBlockScore R' (v N) β ω d
  have hprod : AronowAudit.P018.inProbability (AronowAudit.P018.repeatedLaw R')
      (fun N ω => (AronowAudit.P018.Wave1.WeightedConsistency.normGram R' v N ω)⁻¹.mulVec (s N ω)) :=
    AronowAudit.P018.Wave1.WeightedConsistency.inProbability_product_null
      (AronowAudit.P018.repeatedLaw R')
      (fun (A : Mat k) (z : Vec k) => A.mulVec z) (k : ℝ)
      (Nat.cast_nonneg k) (norm_mulVec_le (k := k))
      (fun N ω => (AronowAudit.P018.Wave1.WeightedConsistency.normGram R' v N ω)⁻¹)
      H⁻¹ s hi hScore
  let φ : Mat k → Vec k := fun A => A⁻¹.mulVec (A.mulVec β) - β
  have hφcont : ContinuousAt φ H := by
    unfold φ
    have hm : Continuous (fun p : Mat k × Vec k => p.1.mulVec p.2) :=
      continuous_fst.matrix_mulVec continuous_snd
    have hinner : ContinuousAt (fun A : Mat k => A.mulVec β) H :=
      (continuous_id.matrix_mulVec continuous_const).continuousAt
    exact (hm.continuousAt.comp (hc.prodMk hinner)).sub continuousAt_const
  have hφzero : φ H = 0 := by
    dsimp [φ]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hHdet),
      Matrix.one_mulVec, sub_self]
  have hrest : AronowAudit.P018.inProbability (AronowAudit.P018.repeatedLaw R')
      (fun N ω => φ (AronowAudit.P018.Wave1.WeightedConsistency.normGram R' v N ω)) := by
    have hh := AronowAudit.P018.Wave1.WeightedConsistency.inProbability_continuousAt
      (AronowAudit.P018.repeatedLaw R') hφcont hA
    simpa only [hφzero, sub_zero] using hh
  have hsum := AronowAudit.P018.Wave1.WeightedConsistency.inProbability_add
    (AronowAudit.P018.repeatedLaw R') hprod hrest
  have hcoef : CoefConsistent R' v β := by
    change AronowAudit.P018.inProbability (AronowAudit.P018.repeatedLaw R')
      (fun N ω => AronowAudit.P018.recordWeightedOLS R' (v N) ω - β)
    apply AronowAudit.P018.Wave1.WeightedConsistency.inProbability_eventually_eq
      (AronowAudit.P018.repeatedLaw R')
      (f := fun N ω => (AronowAudit.P018.Wave1.WeightedConsistency.normGram R' v N ω)⁻¹.mulVec
        (s N ω) + φ (AronowAudit.P018.Wave1.WeightedConsistency.normGram R' v N ω))
      (g := fun N ω => AronowAudit.P018.recordWeightedOLS R' (v N) ω - β) _ hsum
    filter_upwards [eventually_ge_atTop 2] with N hN ω
    have hD := AronowAudit.P018.Wave1.WeightedConsistency.Dreal_ne_zero hN
    have hscaled : (AronowAudit.P018.Wave1.WeightedConsistency.normGram R' v N ω)⁻¹.mulVec
        ((AronowAudit.P018.Dreal N)⁻¹ • AronowAudit.P018.recordWeightedXY R' (v N) ω) =
          AronowAudit.P018.recordWeightedOLS R' (v N) ω := by
      dsimp [AronowAudit.P018.Wave1.WeightedConsistency.normGram,
        AronowAudit.P018.recordWeightedOLS]
      rw [AronowAudit.P018.matrix_inverse_scale_total _ _ (inv_ne_zero hD), inv_inv,
        Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
      simp only [mul_inv_cancel₀ hD, inv_mul_cancel₀ hD, one_smul]
    have hs : s N ω = (AronowAudit.P018.Dreal N)⁻¹ •
        AronowAudit.P018.recordWeightedXY R' (v N) ω -
        (AronowAudit.P018.Wave1.WeightedConsistency.normGram R' v N ω).mulVec β := by
      change (AronowAudit.P018.Dreal N)⁻¹ •
          (∑ d : Dyad N, AronowAudit.P018.recordWeightedBlockScore R' (v N) β ω d) =
        (AronowAudit.P018.Dreal N)⁻¹ • AronowAudit.P018.recordWeightedXY R' (v N) ω -
          ((AronowAudit.P018.Dreal N)⁻¹ • AronowAudit.P018.recordWeightedGram R' (v N) ω).mulVec β
      have hne := congrArg (fun z : Vec k => (AronowAudit.P018.Dreal N)⁻¹ • z)
        (AronowAudit.P018.Wave1.WeightedConsistency.weighted_normal_equation R'
          (v N) β ω)
      have hne' := by simpa only [smul_sub] using hne
      rw [Matrix.smul_mulVec]
      exact hne'
    rw [hs, Matrix.mulVec_sub, ← hscaled]
    dsimp [φ]
    abel

  have hcoefTarget : CoefConsistent R' v (SAP.P018a.populationBeta K) := by
    simpa only [β] using hcoef

  obtain ⟨B, hB, hb⟩ := hreg.2
  let Lq : ℝ := |C| * (B + (k : ℝ) * B * ‖β‖) * B
  let Bq : ℝ := 2 * Lq
  let L : ℝ := 2 * (|C| * (k : ℝ) * B^2)
  have hLq : 0 ≤ Lq := by dsimp [Lq]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hBq : 0 ≤ Bq := by dsimp [Bq]; positivity
  have hq : ∀ N (d : Dyad N),
      ∀ᵐ ω ∂AronowAudit.P018.repeatedLaw R' N,
      ‖AronowAudit.P018.recordWeightedBlockScore R' (v N) β ω d‖ ≤ Bq := by
    intro N d
    filter_upwards [ae_all_iff.mpr (fun t => hb N d t)] with ω hω
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro a
    simp only [AronowAudit.P018.recordWeightedBlockScore, Finset.sum_apply,
      AronowAudit.P018.score, Pi.smul_apply,
      smul_eq_mul, Real.norm_eq_abs]
    change |∑ t, v N d t *
      (AronowAudit.P018.repeatedY R' ω d t -
        AronowAudit.P018.dot (AronowAudit.P018.repeatedX R' ω d t) β) *
        AronowAudit.P018.repeatedX R' ω d t a| ≤ Bq
    calc
      _ ≤ ∑ t, |v N d t *
          (AronowAudit.P018.repeatedY R' ω d t -
            AronowAudit.P018.dot (AronowAudit.P018.repeatedX R' ω d t) β) *
            AronowAudit.P018.repeatedX R' ω d t a| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t : Fin (R'.T N d), Lq := by
        apply Finset.sum_le_sum
        intro t ht
        have hw : |v N d t| ≤ |C| := by
          rw [abs_of_pos (hS.2.2.1 N d t).1]
          exact (hS.2.2.1 N d t).2.trans (le_abs_self C)
        have he : |AronowAudit.P018.repeatedY R' ω d t -
            AronowAudit.P018.dot (AronowAudit.P018.repeatedX R' ω d t) β| ≤
            B + (k : ℝ) * B * ‖β‖ :=
          (abs_sub _ _).trans (add_le_add (hω t).2
            (abs_dot_le_of_norm_le _ _ B (hω t).1))
        have hx : |AronowAudit.P018.repeatedX R' ω d t a| ≤ B :=
          (norm_le_pi_norm (AronowAudit.P018.repeatedX R' ω d t) a).trans (hω t).1
        simp only [abs_mul]
        dsimp [Lq]
        exact mul_le_mul (mul_le_mul hw he (abs_nonneg _) (abs_nonneg _)) hx
          (abs_nonneg _) (by positivity)
      _ = (R'.T N d : ℝ) * Lq := by simp
      _ ≤ 2 * Lq := by
        have hcard : R'.T N d ≤ 2 := by
          change R.T N d ≤ 2
          simpa using Fintype.card_le_of_injective (dir N d) (hS.2.1.2.1 N d)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hLq
      _ = Bq := by rfl

  let δ := fun N (ω : Fin N → U) => AronowAudit.P018.recordWeightedOLS R' (v N) ω - β
  have hnull : AronowAudit.P018.inProbability (AronowAudit.P018.repeatedLaw R') (fun N ω =>
      16 * (2 * Bq * (L * ‖δ N ω‖) + (L * ‖δ N ω‖)^2)) := by
    let ψ : Vec k → ℝ := fun z => 16 * (2 * Bq * (L * ‖z‖) + (L * ‖z‖)^2)
    have hψ : ContinuousAt ψ 0 := by unfold ψ; fun_prop
    have hψ0 : ψ 0 = 0 := by simp [ψ]
    change AronowAudit.P018.inProbability (AronowAudit.P018.repeatedLaw R')
      (fun N ω => δ N ω) at hcoef
    have hh := AronowAudit.P018.Wave1.WeightedConsistency.inProbability_continuousAt
      (AronowAudit.P018.repeatedLaw R') (f := δ) hψ
      (by simpa only [sub_zero] using hcoef)
    simpa only [ψ, hψ0, sub_zero] using hh
  have hsub : SubstitutionNull R' v β := by
    apply AronowAudit.P018.Wave1.WeightedConsistency.inProbability_ae_norm_le
      (AronowAudit.P018.repeatedLaw R') _ _ hnull
    filter_upwards [eventually_ge_atTop 2] with N hN
    filter_upwards [ae_all_iff.mpr (fun d => ae_all_iff.mpr (fun t => hb N d t)),
      ae_all_iff.mpr (fun d => hq N d)] with ω hdata hqω
    have hchange (d : SAP.P018a.Dyad N) :
        ‖AronowAudit.P018.recordWeightedBlockScore R' (v N) β ω d -
          AronowAudit.P018.recordWeightedBlockScore R' (v N)
            (AronowAudit.P018.recordWeightedOLS R' (v N) ω) ω d‖ ≤
          L * ‖δ N ω‖ := by
      apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      intro a
      have hid : (AronowAudit.P018.recordWeightedBlockScore R' (v N) β ω d -
          AronowAudit.P018.recordWeightedBlockScore R' (v N)
            (AronowAudit.P018.recordWeightedOLS R' (v N) ω) ω d) a =
          ∑ t, v N d t * AronowAudit.P018.dot
            (AronowAudit.P018.repeatedX R' ω d t) (δ N ω) *
            AronowAudit.P018.repeatedX R' ω d t a := by
        simp only [AronowAudit.P018.recordWeightedBlockScore, AronowAudit.P018.score,
          Pi.smul_apply, Pi.sub_apply,
          smul_eq_mul, Finset.sum_apply, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro t ht
        change Fin (R.T N d) at t
        have hdot : AronowAudit.P018.dot (AronowAudit.P018.repeatedX R' ω d t) (δ N ω) =
            AronowAudit.P018.dot (AronowAudit.P018.repeatedX R' ω d t)
              (AronowAudit.P018.recordWeightedOLS R' (v N) ω) -
              AronowAudit.P018.dot (AronowAudit.P018.repeatedX R' ω d t) β := by
          simp only [δ, AronowAudit.P018.dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
        rw [hdot]
        generalize hW : v N d t = w
        generalize hY : AronowAudit.P018.repeatedY R' ω d t = y
        generalize hB : AronowAudit.P018.dot (AronowAudit.P018.repeatedX R' ω d t) β = b
        generalize hF : AronowAudit.P018.dot (AronowAudit.P018.repeatedX R' ω d t)
          (AronowAudit.P018.recordWeightedOLS R' (v N) ω) = f
        generalize hX : AronowAudit.P018.repeatedX R' ω d t a = x
        ring
      simp only [Real.norm_eq_abs]
      rw [hid]
      calc
        _ ≤ ∑ t, |v N d t * AronowAudit.P018.dot
            (AronowAudit.P018.repeatedX R' ω d t) (δ N ω) *
            AronowAudit.P018.repeatedX R' ω d t a| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _t : Fin (R'.T N d), |C| *
            ((k : ℝ) * B * ‖δ N ω‖) * B := by
          apply Finset.sum_le_sum
          intro t ht
          have hw : |v N d t| ≤ |C| := by
            rw [abs_of_pos (hS.2.2.1 N d t).1]
            exact (hS.2.2.1 N d t).2.trans (le_abs_self C)
          rw [abs_mul, abs_mul]
          exact mul_le_mul (mul_le_mul hw
            (abs_dot_le_of_norm_le _ _ B (hdata d t).1) (abs_nonneg _) (abs_nonneg _))
            ((norm_le_pi_norm _ a).trans (hdata d t).1) (abs_nonneg _) (by positivity)
        _ ≤ 2 * (|C| * ((k : ℝ) * B * ‖δ N ω‖) * B) := by
          simp only [sum_const, nsmul_eq_mul, Finset.card_fin]
          have hcard : R'.T N d ≤ 2 := by
            change R.T N d ≤ 2
            simpa using Fintype.card_le_of_injective (dir N d) (hS.2.1.2.1 N d)
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
        _ = L * ‖δ N ω‖ := by dsimp [L]; ring_nf
    have hmeat := AronowAudit.P018.Wave1.WeightedConsistency.meat_difference_norm_bound
      AronowAudit.P018.members
      (AronowAudit.P018.recordWeightedBlockScore R' (v N) β ω)
      (AronowAudit.P018.recordWeightedBlockScore R' (v N)
        (AronowAudit.P018.recordWeightedOLS R' (v N) ω) ω)
      Bq (L * ‖δ N ω‖) hBq (by positivity) hqω hchange
    have hP : 0 ≤ 2 * Bq * (L * ‖δ N ω‖) + (L * ‖δ N ω‖)^2 := by positivity
    change ‖AronowAudit.P018.Wave1.WeightedConsistency.scaledMeatAt R' v N
      (AronowAudit.P018.recordWeightedOLS R' (v N) ω) ω -
      AronowAudit.P018.Wave1.WeightedConsistency.scaledMeatAt R' v N β ω‖ ≤
      ‖16 * (2 * Bq * (L * ‖δ N ω‖) + (L * ‖δ N ω‖)^2)‖
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (show 0 ≤ 16 *
      (2 * Bq * (L * ‖δ N ω‖) + (L * ‖δ N ω‖)^2) by positivity)]
    unfold AronowAudit.P018.Wave1.WeightedConsistency.scaledMeatAt
    rw [← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ (N : ℝ) / (AronowAudit.P018.Dreal N)^2 by positivity)]
    calc
      _ ≤ ((N : ℝ) / (AronowAudit.P018.Dreal N)^2) *
          ((N : ℝ)^3 * (2 * Bq * (L * ‖δ N ω‖) + (L * ‖δ N ω‖)^2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hmeat.trans (mul_le_mul_of_nonneg_right
          (AronowAudit.P018.Wave1.WeightedConsistency.g4_proof N).1 hP)
      _ = (((N : ℝ) / (AronowAudit.P018.Dreal N)^2) * (N : ℝ)^3) *
          (2 * Bq * (L * ‖δ N ω‖) + (L * ‖δ N ω‖)^2) := by ring
      _ ≤ 16 * (2 * Bq * (L * ‖δ N ω‖) + (L * ‖δ N ω‖)^2) :=
        mul_le_mul_of_nonneg_right
          (AronowAudit.P018.Wave1.WeightedConsistency.normalized_dyad_count_le hN) hP
      _ = _ := by ring

  exact ⟨hcoefTarget, by simpa only [β] using hsub⟩

end
