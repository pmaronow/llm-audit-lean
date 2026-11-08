import SAP.P011b.WH.W2.Proofs.T16
import SAP.P011b.Defs
import AronowAudit.P011.Wave1.Gap.GLP011B4
import AronowAudit.P011.Wave1.Gap.GLP011B5
import AronowAudit.P011.Wave1.Gap.Fid2P011
import AronowAudit.P011.Wave1.Checks.FidP011Contracts
import AronowAudit.P011.P011_AuxiliaryCompletion
import AronowAudit.P011.P011_CorrelationCompletion
import AronowAudit.P011.P011_BlockOLSCompletion
import AronowAudit.P011.P011_StarCompletion
import AronowAudit.P011.P011_PathFiniteCompletion
import AronowAudit.P011.P011_FiniteCompletion
import AronowAudit.P011.P011_ThreePointCompletion
import SAP.P011b.Bridge
import SAP.P011b.WH.W1.Proofs.T15
import SAP.P011b.WH.W1.Proofs.T19

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P011b
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

theorem SAP.P011b.T15 : SAP.P011b.T15WholeStatement := SAP.P011b.WH.W1.T15_whole

theorem SAP.P011b.T16 : SAP.P011b.T16WholeStatement_W2 := SAP.P011b.WH.W2.T16_whole

theorem SAP.P011b.T17
    {n : ℕ} (hn : 0 < n) (m : Model n) (i j k l : Fin n) : SAP.P011b.T17Statement hn m i j k l := by
  exact (Bridge.T17Statement_correspondence hn m i j k l).mpr
    (AronowAudit.P011.Wave1.corrected_covariance_expansion_moments hn (Bridge.toModel m) i j k l)

theorem SAP.P011b.T18 : SAP.P011b.T18Statement := by
  have h : T18Core :=
    Bridge.T18Core_correspondence.mpr AronowAudit.P011.printed_expansion_counterexample
  have ha := Bridge.cwActualCovariance_correspondence
  have hb : cwBracketOnlyRepair = -70 :=
    Bridge.cwBracketOnlyRepair_correspondence.trans h.2.2.2.2.1
  refine ⟨h, ha, hb, ?_⟩
  rw [ha, hb, h.2.1]
  norm_num

theorem SAP.P011b.T19 : SAP.P011b.T19WholeStatement := SAP.P011b.WH.W1.T19_whole

theorem SAP.P011b.T20 : SAP.P011b.T20Statement := by
  refine ⟨Bridge.signCertificate_correspondence.mpr
    AronowAudit.P011.Wave1.printed_sign_counterexample_full, ?_, Bridge.sign_details⟩
  intro h
  exact AronowAudit.P011.Wave1.printed_sign_counterexample_full_printed_negation
    (Bridge.printedSignAssertion_correspondence.mp h)

theorem SAP.P011b.T21 {n : ℕ} (hn : 0 < n) (m : SAP.P011b.Model n)
    (hdep : SAP.P011b.Dependency m) (hs : SAP.P011b.Homoskedastic m)
    (hL2 : ∀ i, MemLp (fun y => SAP.P011b.weighted m y i) 2 m.law) :
    SAP.P011b.T21Statement hn m hdep hs hL2 := by
  exact ⟨(Bridge.correlationIdentity_correspondence hn m hdep hs hL2).mpr
    (AronowAudit.P011.pairwise_correlation_repair hn (Bridge.toModel m) hdep hs hL2),
    Bridge.pathCorrelations_correspondence.mpr AronowAudit.P011.path_correlation_instance⟩

theorem SAP.P011b.T22 {n : ℕ} (hn : 0 < n) : SAP.P011b.T22Statement hn := by
  exact (Bridge.T22Statement_correspondence hn).mpr (AronowAudit.P011.upper_program_equivalence hn)

theorem SAP.P011b.T23 : SAP.P011b.T23Statement := by
  exact ⟨Bridge.variablesCounterexample_correspondence.mpr
    AronowAudit.P011.printed_variables_counterexample, Bridge.variables_details,
    fun A hA => (Bridge.variablesOptimum_correspondence A hA).mpr
      (AronowAudit.P011.printed_variables_optimum A hA)⟩

theorem SAP.P011b.T24 {n : ℕ} (R G : Graph n) (d : Fin n → ℕ)
    (hv : Compatible R d G) : SAP.P011b.T24Statement R G d hv := by
  exact (Bridge.T24Statement_correspondence R G d hv).mpr (AronowAudit.P011.corrected_notation R G d hv)

theorem SAP.P011b.T25 {n : ℕ} (hn : 1 < n) (R : SAP.P011b.Graph n) (d : Fin n → ℕ)
    (x : Fin n → ℝ) : SAP.P011b.T25Statement hn R d x := by
  exact ⟨(Bridge.helperCorrection_correspondence hn R d x).mpr
    (AronowAudit.P011.helper_correction hn R d x),
    fun A => (Bridge.helperDenominators_correspondence hn A d x).mpr
      (AronowAudit.P011.helper_denominators hn A d x)⟩

theorem SAP.P011b.T26 : SAP.P011b.T26Statement := by
  exact ⟨Bridge.helperExamples_correspondence.mpr AronowAudit.P011.helper_counterexamples,
    Bridge.threePointScaling_correspondence.mpr AronowAudit.P011.helper_witness_scaling,
    Bridge.threePointWitness_correspondence.mpr AronowAudit.P011.helper_witness_law,
    Bridge.helper_details⟩

theorem SAP.P011b.T27 {n : ℕ} (hn : 0 < n) (R G : SAP.P011b.Graph n) (d : Fin n → ℕ)
    (hv : SAP.P011b.Compatible R d G) (x : Fin n → ℝ) :
    SAP.P011b.T27Statement hn R G d hv x := by
  refine ⟨Set.toFinite _, ⟨G, hv⟩, ?_, ?_, ?_⟩
  · intro f
    exact (Bridge.sharpOracleBound_correspondence R G d hv f).mpr
      (AronowAudit.P011.oracle_sharp_bound R G d hv f)
  · exact (Bridge.integerPrograms_correspondence hn R d x).mpr
      (AronowAudit.P011.integer_program_estimators hn R d x)
  · exact (Bridge.T22Statement_correspondence hn).mpr
      (AronowAudit.P011.upper_program_equivalence hn)

theorem SAP.P011b.T28 {n : ℕ} (hn : 0 < n) (R G A : Graph n) (d : Fin n → ℕ)
    (hv : Compatible R d G) (x : Fin n → ℝ)
    (hm : Maximizes R d (fun B => V2 B x) A) : SAP.P011b.T28Statement hn R G A d hv x hm := by
  exact (Bridge.T28Statement_correspondence hn R G A d hv x hm).mpr
    (AronowAudit.P011.lemma_one hn R G A d hv x hm)

