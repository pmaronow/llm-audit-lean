import SAP.P002b.WH.W1.Proofs.T20
import SAP.P002b.WH.W1.Proofs.T22
import SAP.P002b.WH.W1.Proofs.T26
import SAP.P002b.WH.W2.Proofs.T21
import SAP.P002b.Defs
import SAP.P002b.Bridge
import AronowAudit.P002.P002_ConfidenceCompletion
import AronowAudit.P002.Wave1.PrintedTheorem2
import AronowAudit.P002.Wave1.Gap.GLP0021B2
import AronowAudit.P002.Wave1.Gap.GP0022B1
import AronowAudit.P002.Wave1.Algorithm2
import AronowAudit.P002.Wave1.H1
import AronowAudit.P002.Wave1.QuantileIndexInterval
import AronowAudit.P002.Wave1.AlgorithmSupport.N1
import AronowAudit.P002.Wave1.AlgorithmSupport.N7
import AronowAudit.P002.Wave1.AlgorithmSupport.N8
import AronowAudit.P002.Wave1.AlgorithmSupport.N9
import AronowAudit.P002.Wave1.Gap.RepairT21
import AronowAudit.P002.Wave1.Lib.FinitePopulationCLT

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P002b SAP.P002b.Bridge
open scoped BigOperators ENNReal Matrix
open Filter MeasureTheory

/-- P002-T16: the explicit counterexample facts. -/
theorem SAP.P002b.T16 : SAP.P002b.T16Statement := by
  exact AronowAudit.P002.maximum_counterexample.2

/-- P002-T17: the corrected finite inequalities and order bound. -/
theorem SAP.P002b.T17 : SAP.P002b.T17Statement := by
  exact ⟨@AronowAudit.P002.corrected_E14, @AronowAudit.P002.corrected_E14_order⟩

/-- P002-T18: corrected subtraction and inverse-Gram expansions. -/
theorem SAP.P002b.T18 : SAP.P002b.T18Statement := by
  intro n k P β S _ hS h1 h0
  exact ⟨AronowAudit.P002.corrected_adjusted_difference (toCovPopulation P) β S,
    AronowAudit.P002.corrected_E21_E23 (toCovPopulation P) β S hS h1 h0⟩

/-- P002-T19: the corrected signs, with the cross term written as an arm mean. -/
theorem SAP.P002b.T19 : SAP.P002b.T19Statement := by
  intro n k P β S a _ _
  dsimp only
  intro h
  exact corrected_arm_identity P β S a h

/-- P002-T20: the complete corrected oracle expansion and control-remainder limit. -/
theorem SAP.P002b.T20 : SAP.P002b.T20WholeStatement :=
  SAP.P002b.WH.W1.T20_whole

/-- P002-T21: apply the existing tail theorem to the existing CLT, then
transport its nested suprema. No ordinary inner-limit existence is asserted. -/
theorem SAP.P002b.T21 : SAP.P002b.T21WholeStatement :=
  SAP.P002b.WH.W2.T21_whole

/-- P002-T22: completed runs are transported through the interval adapter. -/
theorem SAP.P002b.T22 : SAP.P002b.T22WholeStatement :=
  SAP.P002b.WH.W1.T22_whole

/-- P002-T23: the exported closed-gap equality, including its quantile index. -/
theorem SAP.P002b.T23 : SAP.P002b.T23Statement := by
  intro M Qf Qg α hM hα hd hf hg J ps hne hrun
  dsimp only
  intro p hp
  have H := AronowAudit.P002.Wave1.H1_paper M (toQuadratic Qf)
    (fun m => toQuadratic (Qg m)) α hM hα (dataGenerated_to Qf Qg hd) hf hg
    J (ps.map toPiece) hne ((algorithm1Run_map _ _ _ _).mpr hrun)
  exact H (toPiece p) (List.mem_map_of_mem hp)

/-- P002-T24: all corrected identities, without a global nonzero contrast premise. -/
theorem SAP.P002b.T24 : SAP.P002b.T24Statement := by
  intro n k P S Y D β _ _ h1 h0
  exact AronowAudit.P002.corrected_I1_I2 (toCovPopulation P) S Y D β h1 h0

/-- P002-T25: recovery and finite-sample validity of both full-distribution sets. -/
theorem SAP.P002b.T25 : SAP.P002b.T25Statement := by
  intro n k P β hv hm hc hy
  have H := AronowAudit.P002.constant_effect_coverage (toCovPopulation P) β (1/2)
    hv hm hc hy (by constructor <;> norm_num)
  refine ⟨?_, H.1, ?_⟩
  · intro S
    exact AronowAudit.P002.constant_effect_adjusted_outcomes (toPopulation P.pop) β hy S
  · intro α hα
    exact (AronowAudit.P002.constant_effect_coverage (toCovPopulation P) β α
      hv hm hc hy hα).2

/-- P002-T26: affine identity, guarded Wald membership, and guarded IV equality. -/
theorem SAP.P002b.T26 : SAP.P002b.T26WholeStatement :=
  SAP.P002b.WH.W1.T26_whole

/-- P002-T27: all four interval and endpoint conclusions. -/
theorem SAP.P002b.T27 : SAP.P002b.T27Statement := by
  intro M Qf Qg α hM hα hd hf hg l u hlu hc
  exact AronowAudit.P002.Wave1.quantile_index_interval_paper M (toQuadratic Qf)
    (fun m => toQuadratic (Qg m)) α hM hα (dataGenerated_to Qf Qg hd) hf hg l u hlu hc

/-- P002-T28: corrected algorithm returns, including the no-intersection branch. -/
theorem SAP.P002b.T28 : SAP.P002b.T28Statement := by
  intro M Qf Qg α hM hα hd hf hg
  dsimp only
  let f := arFunction Qf
  let g := fun m => arFunction (Qg m)
  have hreg := AronowAudit.P002.arFamily_regular (fun m => toQuadratic (Qg m)) hg
  have hn : ∀ m β, 0 ≤ g m β := hreg.2.1
  have hf' : ∀ β, 0 ≤ f β := fun β => div_nonneg (hf.2 β) (hf.1 β).le
  have hall : ∀ β, (mcIndices g α β).Nonempty := fun β =>
    (AronowAudit.P002.Wave1.AlgorithmSupport.n1_proof M g α β hM hα (fun m => hn m β)).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact AronowAudit.P002.Wave1.AlgorithmSupport.n8_proof M g hreg
  · intro J hJ
    obtain ⟨ps, hps⟩ := AronowAudit.P002.Wave1.AlgorithmSupport.n9_proof M g α J hJ hall
    refine ⟨ps.map fromPiece, (algorithm1Run_map g α J _).mp ?_⟩
    simpa only [List.map_map, Function.comp_def, to_fromPiece, List.map_id'] using hps
  · intro J ps hps
    have H := AronowAudit.P002.Wave1.AlgorithmSupport.glue_algorithm1_returned
      AronowAudit.P002.Wave1.AlgorithmSupport.n2_proof
      AronowAudit.P002.Wave1.AlgorithmSupport.n3_proof
      AronowAudit.P002.Wave1.AlgorithmSupport.n4_proof
      AronowAudit.P002.Wave1.AlgorithmSupport.n5_proof
      AronowAudit.P002.Wave1.AlgorithmSupport.n6_proof
      AronowAudit.P002.Wave1.AlgorithmSupport.n7_proof
      f g α hM hα hreg.1 hn hf' J (ps.map toPiece)
      ((algorithm1Run_map g α J ps).mpr hps)
    change AronowAudit.P002.returnedSet f g (ps.map toPiece) = mcSet f g α at H
    rw [returnedSet_map] at H
    exact H
  · intro J hJ hne
    obtain ⟨ps, hps⟩ := (AronowAudit.P002.Wave1.algorithm2_paper M (toQuadratic Qf)
      (fun m => toQuadratic (Qg m)) α hM hα (dataGenerated_to Qf Qg hd)
      hf hg J hJ hne).1
    change AronowAudit.P002.Algorithm2Run (fun m => arFunction (Qg m)) α J ps at hps
    refine ⟨ps.map fromPiece, (algorithm2Run_map _ _ _ _).mp ?_⟩
    simpa only [List.map_map, Function.comp_def, to_fromPiece, List.map_id'] using hps
  · intro J ps hps
    have H := (SAP.P002b.T22 M Qf Qg α hM hα hf hg J hps.1 hps.2.1).2 ps hps
    exact H.2.2.2.2.2.2
  · intro J hJ hnil
    refine ⟨hall, ?_⟩
    have hcross : ∀ x ∈ openInterval ⊥ ⊤, ¬ crossing g x := by
      intro x _ hx
      have H := (hJ.2 x).mpr hx
      simp only [hnil, List.not_mem_nil] at H
    have HI := SAP.P002b.T27 M Qf Qg α hM hα hd hf hg ⊥ ⊤ bot_lt_top hcross
    have hreal (x : ℝ) : x ∈ openInterval ⊥ ⊤ :=
      ⟨EReal.bot_lt_coe x, EReal.coe_lt_top x⟩
    intro β m hm
    ext x
    have hm' : m ∈ mcIndices g α x := by
      rw [← HI.1 β (hreal β) x (hreal x)]
      exact hm
    have hcrit : Real.sqrt (g m x) = mcCritical g α x := (Finset.mem_filter.mp hm').2
    change f x ≤ g m x ↔ Real.sqrt (f x) ≤ mcCritical g α x
    rw [← hcrit]
    exact (Real.sqrt_le_sqrt_iff (hn m x)).symm

/-- P002-T29: transport the refutation of the universal printed limit. -/
theorem SAP.P002b.T29 : SAP.P002b.T29Statement := by
  intro h
  apply AronowAudit.P002.ConfidenceFollowup.printed_theorem1_refuted
  intro δ r A α hδ hr hA hα
  simpa only [← infCoverageTheta_eq] using h δ r A α hδ hr hA hα

/-- P002-T30: transport the refutation of the universal printed adjusted limit. -/
theorem SAP.P002b.T30 : SAP.P002b.T30Statement := by
  intro h
  apply AronowAudit.P002.Wave1.printed_theorem2_refuted
  intro k δ e A B r α hk hδ he hA hB hr hα
  simpa only [← infCoverageXi_eq] using h k δ e A B r α hk hδ he hA hB hr hα
