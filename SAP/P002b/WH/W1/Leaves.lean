import SAP.P002b.WH.W1.Leaves.Part1
import SAP.P002b.Defs.WholeW1
import SAP.P002b.WH.W1.PrintedIndex
import SAP.P002b.WH.W1.QuadraticIntersections
import SAP.P002b.Bridge
import AronowAudit.P002.Wave1.Gap.GLP0021B2
import AronowAudit.P002.Wave1.Gap.GP0022B1
import AronowAudit.P002.Wave1.Gap.RepairT21
import AronowAudit.P002.Wave1.Lib.FinitePopulationCLT
import AronowAudit.P002.Wave1.Algorithm2
import AronowAudit.P002.Wave1.AlgorithmSupport.N6
import AronowAudit.P002.Wave1.AlgorithmSupport.N7
import AronowAudit.P002.Wave1.AlgorithmSupport.N8
import AronowAudit.P002.Wave1.AlgorithmSupport.N9

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace SAP.P002b.WH.W1
noncomputable section
open SAP.P002b SAP.P002b.Bridge
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
/-- The intercept normal equation identifies the adjusted arm mean. -/
theorem arm_adjusted_mean {n k : ℕ} (x : Fin n → Fin k → ℝ)
    (A : Finset (Fin n)) (q : Fin n → ℝ) (hA : A.Nonempty)
    (hg : (gram x A).det ≠ 0) :
    groupMean A (fun i => q i - slopeDot (x i) (ols x A q)) = ols x A q none := by
  have hs : score x A (fun i => q i - dotProduct (augmented x i) (ols x A q)) = 0 := by
    change AronowAudit.P002.score x A
      (fun i => q i - dotProduct (AronowAudit.P002.augmented x i) (AronowAudit.P002.ols x A q)) = 0
    rw [AronowAudit.P002.score_residual, AronowAudit.P002.ols_normal_equations x A q hg,
      sub_self]
  have hz : groupMean A (fun i => q i - dotProduct (augmented x i) (ols x A q)) = 0 := by
    have H := congrFun hs none
    simpa only [score, augmented, one_mul, Pi.zero_apply] using H
  have heq : (fun i => q i - slopeDot (x i) (ols x A q)) =
      (fun i => (q i - dotProduct (augmented x i) (ols x A q)) + ols x A q none) := by
    funext i
    simp only [dotProduct, Fintype.sum_option, augmented, one_mul, slopeDot]
    ring
  rw [heq]
  change AronowAudit.P002.groupMean A
    (fun i => (q i - dotProduct (augmented x i) (ols x A q)) + ols x A q none) = _
  rw [AronowAudit.P002.groupMean_add_const A _ _ hA]
  change groupMean A (fun i => q i - dotProduct (augmented x i) (ols x A q)) + _ = _
  rw [hz, zero_add]

/-- Separate arm fits and the interacted treatment coefficient agree under
the change of intercept coordinates in the definition. -/
theorem interacted_coefficient_eq {n k : ℕ} (P : CovPopulation n k)
    (q : Fin n → ℝ) (S : Finset (Fin n)) (hv : ValidDesign P.pop)
    (hS : S ∈ assignments P.pop) (h1 : (gram P.x S).det ≠ 0)
    (h0 : (gram P.x Sᶜ).det ≠ 0) :
    interactedTreatmentCoefficient P q S = adjustedTau P q S := by
  have hn1 : S.Nonempty :=
    AronowAudit.P002.Wave1.RepairT21_arm_nonempty (toPopulation P.pop) hv S hS true
  have hn0 : Sᶜ.Nonempty :=
    AronowAudit.P002.Wave1.RepairT21_arm_nonempty (toPopulation P.pop) hv S hS false
  unfold interactedTreatmentCoefficient adjustedTau adjustedWith fitted
  simp only [Bool.false_eq_true, ite_false, ite_true]
  rw [arm_adjusted_mean P.x S q hn1 h1, arm_adjusted_mean P.x Sᶜ q hn0 h0]

/-- Quadratic variance algebra, the finite order partition, finite quantile
rank invariance, and the elementary cell decomposition give the interval result.
Only regressions actually used by the full randomization law require rank. -/
theorem fixed_confidence_finite_intervals (h1 : T26_L1) (h2 : T26_L2)
    (h3 : T26_L3) (h4 : T26_L4) {n k : ℕ} (P : CovPopulation n k)
    (Y D : Fin n → ℝ) (S : Finset (Fin n)) (α : ℝ)
    (hv : ValidDesign P.pop) (hS : S ∈ assignments P.pop) (hα : 0 < α ∧ α < 1)
    (hrank : ∀ R ∈ assignments P.pop, (gram P.x R).det ≠ 0 ∧ (gram P.x Rᶜ).det ≠ 0) :
    FiniteIntervalUnion (fixedAdjustedConfidenceSet P Y D S α) := by
  let I := {R : Finset (Fin n) // R ∈ assignments P.pop}
  let t : I → Polynomial ℝ := fun R =>
    Polynomial.C (adjustedTau P Y R.val) - Polynomial.X * Polynomial.C (adjustedTau P D R.val)
  let v : I → Polynomial ℝ := fun R =>
    Polynomial.C (adjustedSigma2 P Y R.val) -
      Polynomial.C (2 * adjustedVarianceCross P Y D R.val) * Polynomial.X +
        Polynomial.X^2 * Polynomial.C (adjustedSigma2 P D R.val)
  have ht (R : I) (β : ℝ) : Polynomial.eval β (t R) =
      adjustedTau P (fun i => Y i - β * D i) R.val := by
    have H : adjustedTau P (fun i => Y i - β * D i) R.val =
        adjustedTau P Y R.val - β * adjustedTau P D R.val :=
      (AronowAudit.P002.corrected_I1_I2 (toCovPopulation P) R.val Y D β
        (hrank R.val R.property).1 (hrank R.val R.property).2).2.1
    simpa only [t, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X] using H.symm
  have hd (R : I) (β : ℝ) : Polynomial.eval β (v R) =
      adjustedSigma2 P (fun i => Y i - β * D i) R.val := by
    have H : adjustedSigma2 P (fun i => Y i - β * D i) R.val =
        adjustedSigma2 P Y R.val - 2 * β * adjustedVarianceCross P Y D R.val +
          β^2 * adjustedSigma2 P D R.val :=
      AronowAudit.P002.adjustedSigma2_affine (toCovPopulation P) Y D R.val
        (hrank R.val R.property).1 (hrank R.val R.property).2 β
    simp only [v, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_pow]
    rw [H]
    ring
  have hvnonneg : ∀ R β, 0 ≤ Polynomial.eval β (v R) := by
    intro R β
    rw [hd]
    unfold adjustedSigma2 rss
    positivity
  obtain ⟨cuts, hcuts⟩ := h2 h1 I t v hvnonneg
  apply h4 (fixedAdjustedConfidenceSet P Y D S α) cuts
  intro x y hxy
  apply (h3 P.pop S α hv hS hα
    (fun R => adjustedAR P (fun i => Y i - x * D i) R)).2
      (fun R => adjustedAR P (fun i => Y i - y * D i) R)
  intro R hR T hT
  have H := hcuts x y hxy ⟨R, hR⟩ ⟨T, hT⟩
  simpa only [ht, hd, adjustedAR] using H

/-- All original algebraic clauses are proved by checked donors or short normal
equation arguments. New leaves supply the real-order decomposition, the witness,
and the IV product identity with its exact hypothesis scope. -/
theorem T26_assembly (h1 : T26_L1) (h2 : T26_L2) (h3 : T26_L3)
    (h4 : T26_L4) (h5 : T26_L5) (h6 : T26_L6) : T26WholeStatement := by
  refine ⟨?_, h6 h3⟩
  intro n k P Y D S hv hS hx h1rank h0rank
  refine ⟨?_, interacted_coefficient_eq P Y S hv hS h1rank h0rank,
    interacted_coefficient_eq P D S hv hS h1rank h0rank, ?_, ?_, ?_⟩
  · intro β
    exact (AronowAudit.P002.corrected_I1_I2 (toCovPopulation P) S Y D β h1rank h0rank).2.1
  · intro α hα hrank
    exact fixed_confidence_finite_intervals h1 h2 h3 h4 P Y D S α hv hS hα hrank
  · intro hd α hα
    exact (AronowAudit.P002.adjusted_wald_in_set (toCovPopulation P) Y D S α
      h1rank h0rank hd hα).2
  · intro hcross hinst
    have H := h5 P Y D S hv hS hx h1rank h0rank hcross hinst
    refine ⟨H, ?_⟩
    intro hd
    change ivCoefficients P Y D S (.inl 0) = adjustedTau P Y S / adjustedTau P D S
    apply (eq_div_iff hd).mpr
    simpa only [mul_comm] using H

/-- Summing the four-root bound over the M^2 ordered pairs proves the printed
bound for every complete increasing crossing list. Identical curves contribute
the empty set rather than all real numbers. -/
theorem crossing_list_length_bound {M : ℕ}
    (Qg : Fin M → QuadraticAR) (hg : ∀ m, ARRegular (Qg m))
    (J : List ℝ) (hJ : IntersectionList (fun m => arFunction (Qg m)) J) :
    J.length ≤ 4*M^2 := by
  let roots : (Fin M × Fin M) → Finset ℝ := fun p =>
    if h : arFunction (Qg p.1) ≠ arFunction (Qg p.2) then
      (quadratic_intersections_bound (Qg p.1) (Qg p.2) (hg p.1) (hg p.2) h).choose else ∅
  have hr (p : Fin M × Fin M) : (roots p).card ≤ 4 ∧
      ∀ β, β ∈ roots p ↔
        arFunction (Qg p.1) ≠ arFunction (Qg p.2) ∧
          arFunction (Qg p.1) β = arFunction (Qg p.2) β := by
    dsimp only [roots]
    split_ifs with h
    · have H := (quadratic_intersections_bound (Qg p.1) (Qg p.2) (hg p.1) (hg p.2) h).choose_spec
      exact ⟨H.2, fun β => ⟨fun hβ => ⟨h, (H.1 β).mp hβ⟩,
        fun hβ => (H.1 β).mpr hβ.2⟩⟩
    · simp [h]
  let C := Finset.univ.biUnion roots
  have heq : J.toFinset = C := by
    ext β
    simp only [List.mem_toFinset, hJ.2, C, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨s, t, hne, he⟩
      exact ⟨(s,t), (hr (s,t)).2 β |>.mpr ⟨hne, he⟩⟩
    · rintro ⟨⟨s,t⟩, hβ⟩
      exact ⟨s, t, ((hr (s,t)).2 β).mp hβ⟩
  have hn : J.Nodup := hJ.1.imp (fun h => ne_of_lt h)
  rw [← List.toFinset_card_of_nodup hn, heq]
  calc
    C.card ≤ ∑ p : Fin M × Fin M, (roots p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p : Fin M × Fin M, 4 := Finset.sum_le_sum (fun p _ => (hr p).1)
    _ = 4*M^2 := by simp [pow_two]; omega

/-- The retained corrected theorem is separate from the refuted printed target.
The former root-count leaf is now proved; only T22's policy leaf remains here. -/
theorem T28_corrected_assembly (h1 : T22_L1) : T28CorrectedStatement := by
  have h22 := T22_assembly h1
  refine ⟨h22, ?_⟩
  intro M Qf Qg α hM hα hf hg
  dsimp only
  let f := arFunction Qf
  let g := fun m => arFunction (Qg m)
  have hreg := AronowAudit.P002.arFamily_regular (fun m => toQuadratic (Qg m)) hg
  have hn : ∀ m β, 0 ≤ g m β := hreg.2.1
  have hf' : ∀ β, 0 ≤ f β := fun β => div_nonneg (hf.2 β) (hf.1 β).le
  have hall : ∀ β, (mcIndices g α β).Nonempty := fun β =>
    (AronowAudit.P002.Wave1.AlgorithmSupport.n1_proof M g α β hM hα (fun m => hn m β)).1
  have h22' := h22 M Qf Qg α hM hα hf hg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨J, hJ⟩ := AronowAudit.P002.Wave1.AlgorithmSupport.n8_proof M g hreg
    exact ⟨J, hJ, crossing_list_length_bound Qg hg J hJ⟩
  · intro J hJ
    obtain ⟨ps, hps⟩ := AronowAudit.P002.Wave1.AlgorithmSupport.n9_proof M g α J hJ hall
    refine ⟨ps.map fromPiece, (algorithm1Run_map g α J _).mp ?_⟩
    simpa only [List.map_map, Function.comp_def, to_fromPiece, List.map_id'] using hps
  · intro J ps hps
    constructor
    · have H := congrArg List.length hps.2.1
      simpa [gapEndpoints, List.length_zip, Nat.add_comm] using H
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
    let choose : List (RecordedPiece M) → ℝ → Fin M :=
      fun _ β => (hall β).choose
    have hadm : AdmissibleIndexPolicy g α choose := fun _ β => (hall β).choose_spec
    obtain ⟨ps, hps, _⟩ := (h22' J hJ hne).1 choose hadm
    exact ⟨ps, hps.1⟩
  · intro J ps hps
    exact ((h22' J hps.1 hps.2.1).2 ps hps).2.2.2.2.2.2
  · intro J hJ hnil
    refine ⟨hall, ?_⟩
    have hnc : ∀ β, ¬ crossing g β := by
      intro β hc
      have H := (hJ.2 β).mpr hc
      simp only [hnil, List.not_mem_nil] at H
    have constIndex : ∀ β m, m ∈ mcIndices g α β → ∀ x, m ∈ mcIndices g α x := by
      intro β m hm x
      have H := AronowAudit.P002.Wave1.AlgorithmSupport.n3_proof M g α m ⊥ ⊤ β
        hM hα hreg.1 hn ⟨EReal.bot_lt_coe β, EReal.coe_lt_top β⟩
        (fun s hs y _ he => hnc y ⟨s, m, hs, he⟩) hm
      apply H x ⟨EReal.bot_lt_coe x, EReal.coe_lt_top x⟩
    intro β m hm
    ext x
    have hcrit : Real.sqrt (g m x) = mcCritical g α x :=
      (Finset.mem_filter.mp (constIndex β m hm x)).2
    change f x ≤ g m x ↔ Real.sqrt (f x) ≤ mcCritical g α x
    rw [← hcrit]
    exact (Real.sqrt_le_sqrt_iff (hn m x)).symm

/-- A proved finite common-data counterexample refutes the printed indexing.
It requires no new writer leaf and leaves the corrected theorem separate. -/
theorem T28_assembly : T28WholeStatement := printed_index_refutation

end
end SAP.P002b.WH.W1
