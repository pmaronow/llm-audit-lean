import SAP.P009b.Defs
import SAP.P009b.Bridge
import SAP.P009b.WH.W1.Proofs.T27
import SAP.P009b.WH.W1.Proofs.T18
import SAP.P009b.WH.W1.Proofs.T20
import SAP.P009b.WH.W2.Proofs.T22
import SAP.P009b.WH.W2.Proofs.T26
import SAP.P009b.WH.W3.Proofs.T29
import SAP.P009b.WH.W4.Proofs.T34
import AronowAudit.P009.P009_AtomCompletion
import AronowAudit.P009.P009_Audit
import AronowAudit.P009.P009_BernoulliCompletion
import AronowAudit.P009.P009_FullBiasCompletion
import AronowAudit.P009.P009_MinimizerCompletion
import AronowAudit.P009.P009_OneSourceCompletion
import AronowAudit.P009.P009_PairedCompletion
import AronowAudit.P009.P009_PaperDomains
import AronowAudit.P009.Wave1.Gap.GLP0091B4
import AronowAudit.P009.Wave1.Gap.GLP0091B5
import AronowAudit.P009.Wave1.Gap.GP0091B1b
import AronowAudit.P009.Wave1.SimulationVarianceTailC

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Topology
open Filter

namespace SAP.P009b
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

theorem T18 : T18WholeStatement := SAP.P009b.WH.W1.T18_whole

theorem T19 : T19Statement := by
  have h : T19CoreStatement := Bridge.T19Core_transport (@AronowAudit.P009.pair_witness_counterexample)
  refine ⟨h, ?_⟩
  have hin : ∀ j, (Interferes (fairExperiment 6 sixOutcome) j 0 ↔ j = 0 ∨ j = 2 ∨ j = 4) ∧
      (Interferes (fairExperiment 6 sixOutcome) j 1 ↔ j = 1 ∨ j = 3 ∨ j = 5) :=
    AronowAudit.P009.six_incoming_certificate
  refine ⟨AronowAudit.P009.sixPartner_involution, hin, ?_, ?_⟩
  · intro i j hj0 hj1
    have hh := AronowAudit.P009.interferes_sum_bit
      (Bridge.toExperiment (fairExperiment 6 sixOutcome)) j i {j} (by
        intro z
        change sixOutcome j z = ∑ ℓ ∈ ({j} : Finset (Fin 6)), bit (z ℓ)
        simp [sixOutcome, hj0, hj1])
    change (Interferes (fairExperiment 6 sixOutcome) i j ↔ i = j ∨ i ∈ ({j} : Finset (Fin 6))) at hh
    simpa only [Finset.mem_singleton, or_self] using hh
  · intro ℓ
    have hd : d (fairExperiment 6 sixOutcome) 0 1 = 0 := h.1
    fin_cases ℓ <;> norm_num [I, hd, (hin _).1, (hin _).2, sixPairing, sixPartner]

theorem T20 : T20WholeStatement := SAP.P009b.WH.W1.T20_whole

private theorem T21_six_unit_facts (x ε : Fin 6 → ℝ)
    (_hSupport : UniformBaselineSupport6 x ε) :
    let c := fun i => x i + ε i
    let E := fairExperiment 6 (oneSourceOutcome 4 c)
    Bernoulli E ∧ dAvg E = 3 ∧ msq E = 1 ∧
      B1 E = (1 + 2 * c 0) / 3 ∧ B2 E = 1/3 ∧
      B2 E ≠ (4:ℝ)*3/(6+4*3) ∧
      (6:ℝ)/dAvg E *
        (mean E.design (vBER E) - var E.design (ht E)) =
          -(1 + 2 * c 0) / 3 := by
  let c : Fin 6 → ℝ := fun i => x i + ε i
  let E : Experiment 6 := fairExperiment 6 (oneSourceOutcome 4 c)
  have hforms : T22FiniteStatement :=
    Bridge.T22Finite_transport
      (@AronowAudit.P009.Wave1.corrected_one_source_formulas_proof)
  have hformula := hforms (n := 6) (by norm_num) 4 (by norm_num) c
  rcases hformula with ⟨hdegree, hmsq, hB2, hB1, hvariance, _, _, _⟩
  have hD : dAvg E = 3 := by
    norm_num at hdegree
    linarith
  have hBernoulli : Bernoulli E := by
    exact AronowAudit.P009.SparseCompletion.fair_BER 6
      (AronowAudit.P009.oneSourceOutcome 4 c)
  have hB1' : B1 E = (1 + 2 * c 0) / 3 := by
    rw [hB1]
    norm_num
    ring
  have hB2' : B2 E = 1/3 := by
    rw [hB2]
    norm_num
  have hvariance' :
      (36:ℝ) * (mean E.design (vBER E) - var E.design (ht E)) =
        -6 - 12 * c 0 := by
    norm_num at hvariance
    nlinarith [hvariance]
  have hgap :
      (6:ℝ)/dAvg E *
        (mean E.design (vBER E) - var E.design (ht E)) =
          -(1 + 2 * c 0) / 3 := by
    rw [hD]
    norm_num
    field_simp
    nlinarith [hvariance']
  have hB2ne : B2 E ≠ (4:ℝ)*3/(6+4*3) := by
    rw [hB2']
    norm_num
  exact ⟨hBernoulli, hD, hmsq, hB1', hB2', hB2ne, hgap⟩

theorem T21 : T21Statement := by
  constructor
  · intro x ε hSupport
    exact T21_six_unit_facts x ε hSupport
  · intro x ε hSupport
    rcases T21_six_unit_facts x ε hSupport with
      ⟨_, hD, hmsq, hB1, hB2, _, _⟩
    constructor
    · rw [hD]
      norm_num
    constructor
    · rw [hmsq, hD, hB1, hB2]
      ring
    · norm_num

theorem T22 : T22WholeStatement := SAP.P009b.WH.W2.T22_whole

theorem T23 : T23Statement := by
  exact Bridge.T23Core_transport (@AronowAudit.P009.Wave1.simulation_sampling_variance_proof)

theorem T24 : T24Statement := by
  have h : T24CoreStatement := Bridge.T24Core_transport (@AronowAudit.P009.full_interference_bias)
  refine ⟨h, ?_⟩
  intro n hn heven E b hy hDesign
  rcases h hn heven E b hy hDesign with ⟨_hE, _hpoint, _hHT, _hHA, h1, h2, _hMSE, _hMSEHA⟩
  rw [h1, h2]
  norm_num

theorem T25 : T25Statement := by
  refine ⟨Bridge.T25Caption_transport (@AronowAudit.P009.absolute_bias_caption), Bridge.T25Population_transport (@AronowAudit.P009.absolute_bias_population), ?_⟩
  norm_num [T25SignLossStatement, empiricalBias, reportedBias]

theorem T26 : T26WholeStatement := SAP.P009b.WH.W2.T26_whole

theorem T27 : T27WholeStatement.{u} := SAP.P009b.WH.W1.T27_whole

theorem T28 : T28Statement.{u} := by
  have hfinite : T28FiniteStatement.{u} := Bridge.T28Finite_transport (@AronowAudit.P009.three_point_centering)
  have heventual : T28EventualStatement := Bridge.T28Eventual_transport (@AronowAudit.P009.centering_shift_eventually)
  refine ⟨?_, hfinite, heventual, ?_⟩
  · intro Ω inst P F hF
    simp only [prob, mean]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    rcases hF ω with h | h | h <;> norm_num [h]
  · intro Ω inst P F hF hMean x hx
    have hd : 0 < threePointDistance x := by
      obtain ⟨t, ht⟩ := (heventual (fun _ => 0) tendsto_const_nhds x hx).exists
      simpa only [abs_zero] using ht
    refine ⟨hd, ?_⟩
    filter_upwards [heventual (fun t => mean (P t) (F t)) hMean x hx] with t ht
    exact ⟨ht, hfinite (P t) (F t) (hF t) x hx ht,
      not_lt.mpr (le_of_lt ((le_abs_self _).trans_lt ht))⟩

theorem T29 : T29WholeStatement_W3 := SAP.P009b.WH.W3.T29_whole

theorem T30 : T30Statement := by
  exact Bridge.T30Core_transport (@AronowAudit.P009.corrected_inflated_estimator_names)

theorem T31 : T31Statement.{u} := by
  exact ⟨Bridge.T31Finite_transport (@AronowAudit.P009.corrected_three_point_CDF), Bridge.T31Limit_transport (@AronowAudit.P009.three_point_CDF_limit)⟩

theorem T32 : T32Statement := by
  exact ⟨Bridge.T32Update_transport (@AronowAudit.P009.balance_update), @AronowAudit.P009.balance_flip,
    Bridge.T32Crossings_transport (@AronowAudit.P009.multiplier_crossings), Bridge.T32Paired_transport (@AronowAudit.P009.balance_paired_flip)⟩

theorem T33 : T33Statement := by
  exact Bridge.T33Core_transport (@AronowAudit.P009.corrected_one_source_spillover)

theorem T34 : T34WholeStatement_W4 := SAP.P009b.WH.W4.T34_whole


end
end SAP.P009b
