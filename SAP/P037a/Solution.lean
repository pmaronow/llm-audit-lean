import SAP.P037a.Defs
import SAP.P037a.Bridge
import AronowAudit.P037.P037_FiniteDesign
import AronowAudit.P037.P037_ReportedNumbers
import AronowAudit.P037.P037_Bootstrap
import AronowAudit.P037.Wave1.Gap.GP037B4b
import AronowAudit.P037.Wave1.Gap.GLP037B1
import SAP.P037a.WH.W1.Proofs.T1
import SAP.P037a.WH.W1.Proofs.T3
import SAP.P037a.WH.W1.Proofs.T4
import SAP.P037a.WH.W2.Proofs.T5

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P037a

open MeasureTheory Set Filter Bridge
open scoped BigOperators ENNReal NNReal Classical Topology

theorem T1 : SAP.P037a.T1WholeStatement := SAP.P037a.WH.W1.T1_whole

theorem T2 : T2Statement := by
  refine ⟨AronowAudit.P037.stratified_composition_design_moments,
    AronowAudit.P037.design_mean_equal_sampling_fraction,
    AronowAudit.P037.unequal_strata_design_mean_certificate, ?_,
    AronowAudit.P037.composition_innovation_decomposition, ?_, ?_, ?_,
    AronowAudit.P037.composition_centering_special_case,
    AronowAudit.P037.witness_repaired_regression_comparisons, ?_, ?_, ?_⟩
  · intro Ω K _ _ B d X alpha theta err Y hY he
    exact AronowAudit.P037.correctly_specified_composition_model
      (toDesign d) X alpha theta err Y hY he
  · intro Ω _ B d D R hR V
    exact AronowAudit.P037.composition_innovation_orthogonality (toDesign d) D R hR V
  · intro Ω K _ _ B d D C μ a t W b beta delta hR hN hv
    exact AronowAudit.P037.design_mean_centered_common_slope
      (toDesign d) D C μ a t W b beta delta hR hN hv
  · intro Ω K _ _ _ B d W R Z Y e hZ delta beta
    exact AronowAudit.P037.adding_eligible_interaction_equivalent
      (toDesign d) W R Z Y e hZ delta beta
  · intro Ω _ B d D R hR V
    change AronowAudit.P037.designMean (toDesign d) (fun w => ∑ i, V (D w) i * R w i) = 0
    rw [AronowAudit.P037.designMean_sum]
    simp only [show ∀ i, AronowAudit.P037.designMean (toDesign d)
      (fun w => V (D w) i * R w i) = 0 from fun i => hR (fun v => V v i) i,
      Finset.sum_const_zero]
  · intro Ω K _ _ B d D R hR A W b beta delta hN
    change AronowAudit.P037.AugmentedNormalEquations (toDesign d) (fun k w => W k (D w)) R
      (fun w i => A (D w) i + b*R w i) delta beta at hN
    have hA := AronowAudit.P037.composition_innovation_orthogonality (toDesign d) D R hR A
    have hW := fun l => AronowAudit.P037.composition_innovation_orthogonality
      (toDesign d) D R hR (W l)
    have hrow := hN.2
    simp_rw [AronowAudit.P037.withinBlocksCross_add,
      AronowAudit.P037.withinBlocksCross_mul] at hrow
    rw [AronowAudit.P037.designMean_add, AronowAudit.P037.designMean_mul, hA] at hrow
    change beta * AronowAudit.P037.designMean (toDesign d)
      (fun w => AronowAudit.P037.withinBlocksCross (R w) (R w)) =
      b * AronowAudit.P037.designMean (toDesign d)
        (fun w => AronowAudit.P037.withinBlocksCross (R w) (R w))
    simpa only [hW, mul_zero, Finset.sum_const_zero, zero_add] using hrow.symm
  · intro Ω K _ _ _ B d D C μ a t W e b beta delta hcol hR hN hv
    have hZ : ∀ w i, (if D w i then (1:ℝ) else 0)*C w i =
        (if D w i then (1:ℝ) else 0)*(C w i-μ i)+W e (D w) i := by
      intro w i
      rw [hcol]
      ring
    have hcenter := (AronowAudit.P037.adding_eligible_interaction_equivalent (toDesign d)
      (fun k w => W k (D w))
      (fun w i => (if D w i then (1:ℝ) else 0)*(C w i-μ i))
      (fun w i => (if D w i then (1:ℝ) else 0)*C w i)
      (fun w i => a i+(if D w i then (1:ℝ) else 0)*t i+
        b*(if D w i then (1:ℝ) else 0)*C w i) e hZ delta beta).mp hN
    exact AronowAudit.P037.design_mean_centered_common_slope
      (toDesign d) D C μ a t W b beta _ hR hcenter hv

theorem T3 : SAP.P037a.T3WholeStatement := SAP.P037a.WH.W1.T3_whole

theorem T4 : SAP.P037a.T4WholeStatement := SAP.P037a.WH.W1.T4_whole

theorem T5 : SAP.P037a.T5WholeStatement_W2 := SAP.P037a.WH.W2.T5_whole

theorem T6 : T6Statement := by
  exact ⟨AronowAudit.P037.corrected_reduction_arithmetic,
    AronowAudit.P037.rounded_totals_reduction,
    AronowAudit.P037.mixed_basis_cannot_round_to_25⟩

theorem T7 : T7Statement := by
  refine ⟨?_, ?_, ?_⟩
  · rcases AronowAudit.P037.printed_exposure_counterexamples with
      ⟨ha, hb, hc, hd, he, hf, hg, hh⟩
    exact ⟨ha, hb, hc, fun h => hd (congrArg toCase h),
      he, hf, hg, fun h => hh (congrArg toCase h)⟩
  · rintro ⟨f, hf⟩
    apply AronowAudit.P037.printed_exposure_not_single_valued
    refine ⟨fun x => toCase (f (fromData x)), ?_⟩
    intro x hx e he
    have h := congrArg toCase (hf (fromData x) hx (fromCase e)
      ((printed_back x e).mpr he))
    simpa only [to_from_case] using h
  · intro x hx
    have h := AronowAudit.P037.printed_exposure_overlaps (toData x) hx
    exact ⟨fun hs => h.1 hs, fun hs hz hr => h.2 hs hz hr⟩

theorem T8 : T8Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨e, he, hu⟩ := AronowAudit.P037.corrected_exposure_partition (toData x) hx
    refine ⟨fromCase e, (corrected_back x e).mp he, ?_⟩
    intro e' he'
    apply case_injective
    simpa only [to_from_case] using hu (toCase e') ((corrected_iff x e').mpr he')
  · exact ⟨rfl, rfl, rfl⟩
  · rfl

theorem T9 : T9Statement := by
  refine ⟨?_, AronowAudit.P037.printed_monte_carlo_last_draw,
    AronowAudit.P037.exposure_frequency_printed_example⟩
  intro Ω _ d E _
  let X : Ω → ℝ := fun w => if E w then 1 else 0
  have hx : ∀ w, X w = 0 ∨ X w = 1 := by
    intro w
    dsimp [X]
    split_ifs <;> simp
  refine ⟨AronowAudit.P037.exposure_indicator_moments (toDesign d) E, ?_, ?_⟩
  · intro J hJ
    exact AronowAudit.P037.monte_carlo_frequency_moments
      (AronowAudit.P037.productDesign (fun _ : Fin J => toDesign d)) J hJ
      (fun j w => X (w j)) (mean d X) (fun j w => hx (w j))
      (fun j => AronowAudit.P037.product_design_coordinate_mean
        (fun _ : Fin J => toDesign d) j X)
      (fun j k hjk => by
        simpa only [pow_two, mean_eq] using AronowAudit.P037.product_design_coordinate_pair
          (fun _ : Fin J => toDesign d) j k hjk X X)
  · intro eps heps
    exact AronowAudit.P037.monte_carlo_frequency_consistent
      (fun J => Fin (J+1) → Ω)
      (fun J => AronowAudit.P037.productDesign (fun _ : Fin (J+1) => toDesign d))
      (fun J j w => X (w j)) (mean d X) (fun J j w => hx (w j))
      (fun J j => AronowAudit.P037.product_design_coordinate_mean
        (fun _ : Fin (J+1) => toDesign d) j X)
      (fun J j k hjk => by
        simpa only [pow_two, mean_eq] using AronowAudit.P037.product_design_coordinate_pair
          (fun _ : Fin (J+1) => toDesign d) j k hjk X X) eps heps

theorem T10 : T10Statement := by
  refine ⟨AronowAudit.P037.block_design_constraints,
    AronowAudit.P037.within_block_dependence, ?_,
    AronowAudit.P037.between_block_independence, by norm_num, fun _ _ => rfl⟩
  intro Ω _ d T hb hc hm
  exact AronowAudit.P037.fixed_count_forces_dependence (toDesign d) T hb hc hm

theorem T11 : T11Statement := by
  refine ⟨?_, AronowAudit.P037.augmented_contribution_bound, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ω _ d I pi y g hp hi
    exact AronowAudit.P037.augmented_contribution_unbiased (toDesign d) I pi y g hp hi
  · intro B r b
    exact AronowAudit.P037.oracle_block_unbiased (toRow r) b
  · intro B r _
    exact AronowAudit.P037.oracle_row_unbiased (toRow r)
  · intro B r f
    exact AronowAudit.P037.product_design_mean_product (toRow r).law
      (fun b z => f b (AronowAudit.P037.oracleBlockTotal (toRow r) b z))
  · intro r m c eta K h B eps heps
    exact AronowAudit.P037.oracle_row_finite_bounds (fun B => toRow (r B))
      m c eta K h B eps heps
  · intro r m c eta K h eps heps
    exact AronowAudit.P037.independent_blocks_oracle_consistent
      (fun B => toRow (r B)) m c eta K h eps heps
  · intro r m c eta K sigmaSquared h hs hv
    exact AronowAudit.P037.independent_blocks_oracle_normal
      (fun B => toRow (r B)) m c eta K sigmaSquared h hs hv
  · intro B r m eta K he hK hn hb
    exact AronowAudit.P037.oracle_block_centered_bound (toRow r) m eta K he hK hn hb
  · intro B r hn w
    have hN : (populationSize r : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
    simp_rw [show ∀ b, mean (r.law b) (blockTotal r b) = ∑ i, r.y b i from
      fun b => AronowAudit.P037.oracle_block_unbiased (toRow r) b,
      Finset.sum_sub_distrib]
    unfold oracleMean potentialMean
    field_simp
  · intro B r _ s m eta K he hK hn hb h2
    exact AronowAudit.P037.oracle_contrast_finite_facts (toRow r) (toPaired r s)
      m eta K he hK hn hb h2
  · intro r s m c eta K h h2
    exact AronowAudit.P037.independent_blocks_exposure_contrasts
      (fun B => toRow (r B)) (fun B => toPaired (r B) (s B)) m c eta K h h2
  · intro r s m c eta K h h2 B eps heps
    have hv := AronowAudit.P037.BlockCLT.contrast_variance_bound
      (fun B => toRow (r B)) (fun B => toPaired (r B) (s B)) m c eta K h h2 B
    have hm := (AronowAudit.P037.oracle_contrast_finite_facts (toRow (r B))
      (toPaired (r B) (s B)) m eta K h.2.1 h.2.2.1
      (fun b => ((h.2.2.2 B).2 b).1) (fun b i => ((h.2.2.2 B).2 b).2 i) (h2 B)).1
    have hp := AronowAudit.P037.finite_chebyshev
      (AronowAudit.P037.productDesign (toRow (r B)).law)
      (AronowAudit.P037.oracleRowContrast (toRow (r B)) (toPaired (r B) (s B))) eps heps
    rw [hm] at hp
    refine ⟨hv, le_trans hp ?_⟩
    simpa only [div_div] using div_le_div_of_nonneg_right hv (sq_nonneg eps)
  · intro r s m c eta K v h h2 hv hvB B eps heps hsmall
    have hb := (AronowAudit.P037.oracle_contrast_finite_facts (toRow (r B))
      (toPaired (r B) (s B)) m eta K h.2.1 h.2.2.1
      (fun b => ((h.2.2.2 B).2 b).1) (fun b i => ((h.2.2.2 B).2 b).2 i) (h2 B)).2.2.1
    have ht := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hvB B)) heps.le
    apply Finset.sum_eq_zero
    intro b _
    have hm := AronowAudit.P037.bounded_design_mean ((toRow (r B)).law b)
      (AronowAudit.P037.oracleContrastBlock (toRow (r B)) (toPaired (r B) (s B)) b)
      (2*m*(K+2*K/eta)) (hb b)
    change |mean ((r B).law b) (contrastBlockTotal (r B) (s B) b)| ≤
      2*m*(K+2*K/eta) at hm
    change ∀ b z, |contrastBlockTotal (r B) (s B) b z| ≤ 2*m*(K+2*K/eta) at hb
    change mean ((r B).law b) _ = 0
    have hz : ∀ z, |contrastBlockTotal (r B) (s B) b z -
        mean ((r B).law b) (contrastBlockTotal (r B) (s B) b)| ≤ 4*m*(K+2*K/eta) := by
      intro z
      exact le_trans (abs_sub _ _) (by linarith [hb b z])
    change (∑ z, ((r B).law b).weight z *
      ((contrastBlockTotal (r B) (s B) b z -
        mean ((r B).law b) (contrastBlockTotal (r B) (s B) b))^2 *
      if eps*Real.sqrt (∑ b, variance ((r B).law b) (contrastBlockTotal (r B) (s B) b)) <
        |contrastBlockTotal (r B) (s B) b z -
          mean ((r B).law b) (contrastBlockTotal (r B) (s B) b)| then 1 else 0)) = 0
    apply Finset.sum_eq_zero
    intro z _
    have hlt : ¬ eps * Real.sqrt (∑ b, variance ((r B).law b)
        (contrastBlockTotal (r B) (s B) b)) <
        |contrastBlockTotal (r B) (s B) b z -
          mean ((r B).law b) (contrastBlockTotal (r B) (s B) b)| := by
      linarith [hz z]
    simp only [if_neg hlt, mul_zero]
  · intro B q r _ x bh bs p w hp
    exact AronowAudit.P037.fitted_mean_subtraction_identities (toRow r) x bh bs p w hp
  · intro q r x p m c eta K L Q v hb hx hQ hv hpos hp hSim hg
    exact AronowAudit.P037.Wave1.fitted_block_estimator_limit_proof
      (fun B => toRow (r B)) x p m c eta K L Q v hb hx hQ hv hpos hp hSim hg

theorem T12 : T12Statement := by
  exact ⟨AronowAudit.P037.seed_interpolation_no_tie,
    AronowAudit.P037.seed_count_bounds_monotone,
    AronowAudit.P037.seed_count_cap_and_examples,
    AronowAudit.P037.seed_count_shares⟩

theorem T13 : T13Statement := by
  refine ⟨AronowAudit.P037.composition_prediction_printed_arithmetic,
    AronowAudit.P037.composition_prediction_intervals, ?_⟩
  intro t b ht hb
  have h := AronowAudit.P037.composition_prediction_intervals t b (222/1000)
    ht hb (by norm_num)
  exact ⟨h.1, h.2.1⟩

end SAP.P037a
