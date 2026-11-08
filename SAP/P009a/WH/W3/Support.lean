import SAP.P009a.Defs.WholeW3
import SAP.P009a.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SAP.P009a.WH.W3

open Filter SAP.P009a.Bridge
open scoped BigOperators Topology Classical

noncomputable section

theorem regularity_of_uniform_bound {n : ℕ} (E : FiniteExperiment n) (k B q s : ℝ)
    (hk : AssignmentBounds E k) (hb : ∀ i z, |E.outcome i z| ≤ B)
    (hq : 2 ≤ q) (hs : 1 ≤ s) : Regularity E (max k B) q s := by
  have hK : 0 < max k B := lt_of_lt_of_le hk.1 (le_max_left _ _)
  have hinv : (max k B)⁻¹ ≤ k⁻¹ :=
    (inv_le_inv₀ hK hk.1).2 (le_max_left _ _)
  refine ⟨hK, hq, hs, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hinv.trans (hk.2 i).1, (hk.2 i).2.trans (by linarith)⟩
  · intro i
    apply AronowAudit.P009.SparseCompletion.mean_le_constant
      (toProjectDistribution E.design)
    intro z
    exact Real.rpow_le_rpow (abs_nonneg _) ((hb i z).trans (le_max_right _ _))
      (by linarith)
  · intro i b
    apply AronowAudit.P009.SparseCompletion.mean_le_constant
      (toProjectDistribution E.design)
    intro z
    exact Real.rpow_le_rpow (abs_nonneg _)
      ((hb i (Function.update z i b)).trans (le_max_right _ _)) (by linarith)

theorem fair_all_orders (n : ℕ) (y : Fin n → TreatmentVector n → ℝ)
    (hy : ∀ i z, |y i z| ≤ 2) (q s : ℝ) (hq : 2 ≤ q) (hs : 1 ≤ s) :
    Regularity (fairPopulation n y) 2 q s := by
  have hp : AssignmentBounds (fairPopulation n y) 2 := by
    refine ⟨by norm_num, ?_⟩
    intro i
    change (2 : ℝ)⁻¹ ≤ AronowAudit.P009.marginal
      (AronowAudit.P009.fairExperiment n y) i true ∧
      AronowAudit.P009.marginal (AronowAudit.P009.fairExperiment n y) i true ≤ 1 - (2 : ℝ)⁻¹
    rw [AronowAudit.P009.SparseCompletion.fair_marginal]
    norm_num
  simpa only [max_self] using regularity_of_uniform_bound
    (fairPopulation n y) 2 2 q s hp hy hq hs

theorem no_spillovers_indicators {n : ℕ} (E : FiniteExperiment n) (h : NoSpillovers E) :
    (∀ i j, interferenceIndicator E i j = if i = j then 1 else 0) ∧
    (∀ i j, dependenceIndicator E i j = if i = j then 1 else 0) := by
  constructor
  · intro i j
    change (if AronowAudit.P009.Interferes (toProjectExperiment E) i j then
      (1 : ℝ) else 0) = _
    rw [AronowAudit.P009.SparseCompletion.noI_interferes (toProjectExperiment E) h]
    simp
  · exact AronowAudit.P009.SparseCompletion.noI_d (toProjectExperiment E) h

theorem density_bounds (S : ExperimentSequence) (t : ℕ) :
    0 ≤ interferenceDensity S t ∧ interferenceDensity S t ≤ 1 := by
  have hn : (0 : ℝ) < S.N t := by exact_mod_cast S.positive t
  have hd (i j : Fin (S.N t)) : 0 ≤ dependenceIndicator (S.experiment t) i j ∧
      dependenceIndicator (S.experiment t) i j ≤ 1 := by
    unfold dependenceIndicator
    split_ifs <;> norm_num
  have hsum : (∑ i, ∑ j, dependenceIndicator (S.experiment t) i j) ≤
      (S.N t : ℝ) * S.N t := by
    calc
      _ ≤ ∑ _i : Fin (S.N t), ∑ _j : Fin (S.N t), (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => (hd i j).2))
      _ = _ := by simp
  unfold interferenceDensity averageDependence dependenceDegree sampleSize
  constructor
  · exact div_nonneg (div_nonneg
      (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (hd i j).1))) hn.le) hn.le
  · apply (div_le_iff₀ hn).2
    apply (div_le_iff₀ hn).2
    simpa using hsum

/-- Remove the irrelevant reference-outcome moment assumptions before using the finite donor. -/
theorem finite_limsup_construction {n : ℕ} (hn : 0 < n) (E : FiniteExperiment n)
    (k L : ℝ) (hk : AssignmentBounds E k) (hL : 0 < L ∧ L ≤ 1) :
    LimsupFiniteFacts hn E k L := by
  let E0 : FiniteExperiment n := { E with outcome := fun _ _ => 0 }
  have hReg : Regularity E0 k 2 1 := by
    refine ⟨hk.1, by norm_num, by norm_num, hk.2, ?_, ?_⟩
    · intro i
      simp only [E0, expectation, abs_zero, Real.rpow_eq_pow, Real.rpow_two, mul_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero]
      positivity
    · intro i b
      simp only [potentialResponse, E0, expectation, abs_zero, Real.rpow_eq_pow, Real.rpow_one,
        mul_zero, Finset.sum_const_zero]
      exact hk.1.le
  obtain ⟨hg, hl, hb, he, ht, _⟩ :=
    AronowAudit.P009.Wave1.construction_p1_proof hn (toProjectExperiment E0)
      k 2 1 L hReg hL
  refine ⟨hg, hl, hb, he, ?_⟩
  intro z
  refine ⟨(ht z).1, ?_, (ht z).2⟩
  change |htEstimate (limsupPopulation hn E L) z - expectedATE _| = _
  rw [show htEstimate (limsupPopulation hn E L) z = _ from (ht z).1,
    show expectedATE (limsupPopulation hn E L) = _ from he]
  rfl

theorem coordinate_alpha (n : ℕ) (i j : Fin n) :
    mixingCoefficient (fairDistribution n) (fun z => z i) (fun z => z j) =
      if i = j then 1/4 else 0 := by
  change AronowAudit.P009.alpha (AronowAudit.P009.fairLaw n) _ _ = _
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    apply le_antisymm (AronowAudit.P009.Wave1.t9_alpha_le_quarter _ _ _)
    have h := AronowAudit.P009.MixingBasics.covariance_indicator_le_alpha
      (AronowAudit.P009.fairLaw n) (fun z => z i) (fun z => z i) {true} {true}
    have hc : AronowAudit.P009.cov (AronowAudit.P009.fairLaw n)
        (fun z => AronowAudit.P009.bit (z i)) (fun z => AronowAudit.P009.bit (z i)) ≤
        AronowAudit.P009.alpha (AronowAudit.P009.fairLaw n) (fun z => z i) (fun z => z i) := by
      convert h using 2 <;> ext z <;> cases hz : z i <;> simp [AronowAudit.P009.bit, hz]
    simpa [AronowAudit.P009.DiagonalCompletion.coordinate_covariance] using hc
  · rw [if_neg hij]
    apply AronowAudit.P009.DiagonalCompletion.alpha_zero_of_block_functions
      (AronowAudit.P009.identityExperiment n)
      (AronowAudit.P009.SparseCompletion.fair_BER n _) _ _ ({i} : Set (Fin n))
    · intro z w h
      exact h i (Set.mem_singleton i)
    · intro z w h
      exact h j (by simpa using Ne.symm hij)

theorem assignment_covariance_eq {n : ℕ} (E : FiniteExperiment n) (i j : Fin n) :
    assignmentCovariance E i j = covariance E.design
      (fun z => treatmentValue (z i)) (fun z => treatmentValue (z j)) := by
  rw [covariance_correspondence, AronowAudit.P009.BernoulliCompletion.covariance_product_formula]
  change probability E.design (fun z => z i = true ∧ z j = true) -
      probability E.design (fun z => z i = true) * probability E.design (fun z => z j = true) =
    expectation E.design (fun z => treatmentValue (z i) * treatmentValue (z j)) -
      expectation E.design (fun z => treatmentValue (z i)) *
        expectation E.design (fun z => treatmentValue (z j))
  simp only [probability]
  congr 1
  · apply congrArg (expectation E.design)
    funext z
    by_cases hi : z i = true <;> by_cases hj : z j = true <;> simp [treatmentValue, hi, hj]
  · apply congrArg₂ (fun a b : ℝ => a*b)
    · apply congrArg (expectation E.design)
      funext z
      by_cases h : z i = true <;> simp [treatmentValue, h]
    · apply congrArg (expectation E.design)
      funext z
      by_cases h : z j = true <;> simp [treatmentValue, h]

end
end SAP.P009a.WH.W3
