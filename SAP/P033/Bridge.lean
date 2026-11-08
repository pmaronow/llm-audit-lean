import SAP.P033.Defs
import AronowAudit.P010.Wave1.Gap.GP010P033B1b
import AronowAudit.P010.Wave1.Gap.GP010P033B2
import AronowAudit.P033.P033_Audit
import AronowAudit.P033.Wave1.Gap.GLP010P033P033B1
import AronowAudit.P033.Wave1.Gap.GLP010P033P033B2
import AronowAudit.P033.Wave1.Gap.GLP010P033P033B3

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace SAP.P033.Bridge

theorem T1_correspondence : SAP.P033.T1CoreStatement ↔
    (type_of% @AronowAudit.P033.Wave1.diagnostic_counterexample_proof) := Iff.rfl

theorem T2_correspondence : SAP.P033.T2CoreStatement.{u, v, w} ↔
    (type_of% @AronowAudit.P033.Wave1.diagnostic_correction_proof.{u, v, w}) := Iff.rfl

theorem T3_correspondence : SAP.P033.T3CoreStatement ↔
    (type_of% @AronowAudit.P033.clustered_variance_counterexample) := Iff.rfl

theorem T4_correspondence : SAP.P033.T4Statement.{u, v} ↔
    (type_of% @AronowAudit.P033.clustered_variance_correction.{u, v}) := Iff.rfl

theorem T6_correspondence : SAP.P033.T6Statement.{u} ↔
    (type_of% @AronowAudit.P033.Wave1.binary_standardization_correction_proof.{u}) := Iff.rfl

theorem T7_correspondence : SAP.P033.T7CoreStatement ↔
    (type_of% @AronowAudit.P033.Wave1.caliper_counterexamples_proof) := Iff.rfl

theorem T8_correspondence : SAP.P033.T8CoreStatement ↔
    (type_of% @AronowAudit.P033.Wave1.caliper_correction_proof) := Iff.rfl

theorem T9_correspondence : SAP.P033.T9CoreStatement.{u, v} ↔
    (type_of% @AronowAudit.P033.Wave1.native_power_correction_proof.{u, v}) := Iff.rfl

theorem T10_correspondence : SAP.P033.T10CoreStatement ↔
    (type_of% @AronowAudit.P033.funnel_counterexample) := Iff.rfl

theorem T11_correspondence : SAP.P033.T11CoreStatement ↔
    (type_of% @AronowAudit.P033.funnel_correction) := Iff.rfl

theorem T12_correspondence : SAP.P033.T12Statement ↔
    (type_of% @AronowAudit.P033.Wave1.pseudo_p_counterexample_proof) := Iff.rfl

theorem T13_correspondence : SAP.P033.T13Statement ↔
    (type_of% @AronowAudit.P033.Wave1.pseudo_p_correction_proof) := Iff.rfl

theorem T14_correspondence : SAP.P033.T14Statement ↔
    (type_of% @AronowAudit.P033.interval_rule_counterexample) := Iff.rfl

theorem T15_correspondence : SAP.P033.T15Statement ↔
    (type_of% @AronowAudit.P033.interval_rule_correction) := Iff.rfl

theorem M1Certificate_correspondence : SAP.P033.M1Certificate ↔
    (type_of% @AronowAudit.P033.m1_exact_certificate) := Iff.rfl

theorem M2Certificate_correspondence : SAP.P033.M2Certificate ↔
    (type_of% @AronowAudit.P033.m2_polynomial_certificate) := Iff.rfl

theorem ClusterCertificate_correspondence : SAP.P033.ClusterCertificate ↔
    (type_of% @AronowAudit.P033.cluster_exact_certificate) := Iff.rfl

theorem M1WLSCertificate_correspondence : SAP.P033.M1WLSCertificate ↔
    (type_of% @AronowAudit.P033.m1_wls_rows) := Iff.rfl

theorem ClusterWLSCertificate_correspondence : SAP.P033.ClusterWLSCertificate ↔
    (type_of% @AronowAudit.P033.cluster_wls_rows) := Iff.rfl

/-- The scaling assertion is used only when the effect and its divisor exist. -/
theorem T5_of_project (h : type_of% @AronowAudit.P033.count_standardization_counterexample) :
    SAP.P033.T5Statement := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15, h16, h17, h18, h19, h20, h21,
    fun yE yI dE dI sd scale hs _ _ => h22 yE yI dE dI sd scale hs, h23⟩

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

/-- Product-window mass and a finite-set inclusion guard the conditioning event. -/
theorem linear_count_positive :
    0 < (SAP.P033.caliperDataLaw 19 SAP.P033.linearCaliperDensity).real
      {X | SAP.P033.caliperCount (SAP.P033.caliperCutoff/5) X = 19} := by
  let ν := volume.withDensity (fun x => ENNReal.ofReal (AronowAudit.P033.linearCaliperDensity x))
  let W := Icc (AronowAudit.P033.caliperCutoff-AronowAudit.P033.caliperCutoff/5)
    (AronowAudit.P033.caliperCutoff+AronowAudit.P033.caliperCutoff/5)
  letI : IsFiniteMeasure ν := AronowAudit.P033.Wave1.caliper_counterexample.linear_density_finite
  have hi := AronowAudit.P033.Wave1.caliper_counterexample.linear_integrable
  have hmass : ν.real W = 2401/12500 := by
    dsimp [ν, W]
    rw [AronowAudit.P033.Wave1.caliper_counterexample.density_interval
      _ hi AronowAudit.P033.Wave1.caliper_counterexample.linear_nonneg _ _
      (by norm_num [AronowAudit.P033.caliperCutoff])]
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      hi.intervalIntegrable hi.intervalIntegrable
      (a := AronowAudit.P033.caliperCutoff-AronowAudit.P033.caliperCutoff/5)
      (b := AronowAudit.P033.caliperCutoff)
      (c := AronowAudit.P033.caliperCutoff+AronowAudit.P033.caliperCutoff/5)
    change AronowAudit.P033.caliperBelow _ _ + AronowAudit.P033.caliperAbove _ _ = _ at hadd
    rw [AronowAudit.P033.linear_caliper_witness.2.2.2.2.1,
      AronowAudit.P033.linear_caliper_witness.2.2.2.2.2.1] at hadd
    linarith
  have hp : 0 < (Measure.pi (fun _ : Fin 19 => ν)).real (Set.pi univ (fun _ => W)) := by
    simp only [measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
    change 0 < ∏ _ : Fin 19, ν.real W
    simp only [hmass, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    positivity
  have hsub : Set.pi univ (fun _ : Fin 19 => W) ⊆
      {X | AronowAudit.P033.caliperCount (AronowAudit.P033.caliperCutoff/5) X = 19} := by
    intro X hX
    have hxi (i : Fin 19) : X i ∈ W := hX i (mem_univ i)
    change (Finset.univ.filter (fun i : Fin 19 => X i ∈ W)).card = 19
    rw [Finset.filter_true_of_mem (fun i _ => hxi i)]
    simp
  exact hp.trans_le (measureReal_mono hsub)

end SAP.P033.Bridge
