import SAP.P002a.WH.W2.Details

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace SAP.P002a.WH.W2
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
open SAP.P002a.Bridge
attribute [local instance] Classical.propDecidable

theorem t4_ranks : W2T4Ranks := by
  intro n P hP
  have hn := hP.1.1
  have ht := hP.1.2.1
  have htn := hP.1.2.2
  have htR : (0 : ℝ) < P.pop.n1 := by exact_mod_cast ht
  have htnR : (P.pop.n1 : ℝ) < n := by exact_mod_cast htn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hcR : 0 < controlSize P.pop := by unfold controlSize; linarith
  have hd : 0 < (n : ℝ)-1 := by linarith
  have hQ : 1/4 ≤ mean (fun i => P.x i 0^2) := by
    have H := hP.2.2.2.2.2.2.2.2.2 (fun _ => 1)
    simpa [normSq, dotProduct, Fin.sum_univ_succ] using H
  have hfirst :
      probability P.pop (fun S => (gram P.x S).det = 0) ≤
        258*controlSize P.pop/((P.pop.n1 : ℝ)*((n : ℝ)-1)) ∧
      probability P.pop (fun S => (gram P.x Sᶜ).det = 0) ≤
        258*(P.pop.n1 : ℝ)/(controlSize P.pop*((n : ℝ)-1)) := by
    by_cases hlarge : 2 ≤ P.pop.n1 ∧ 2 ≤ n-P.pop.n1
    · have H := AronowAudit.P002.Wave1.T4SC_single_arm_failure n (toCovPopulation P)
        (hP.2.2.2.2.2.2.2.1 0) hQ (hP.2.2.2.2.2.2.2.2.1 0) hlarge.1 hlarge.2
      simp only [probability_eq, gram_eq]
      simpa only [toCovPopulation, toPopulation, controlSize, mul_div_assoc] using H
    · have hsmall : n ≤ 4 := by
        have hl := hP.2.2.2.1
        have hu := hP.2.2.2.2.1
        by_cases ht2 : 2 ≤ P.pop.n1
        · have hc1 : n-P.pop.n1 = 1 := by omega
          have hEq : n = P.pop.n1+1 := by omega
          have hEqR : (n : ℝ) = (P.pop.n1 : ℝ)+1 := by exact_mod_cast hEq
          have hn4 : (n : ℝ) ≤ 4 := by linarith
          exact_mod_cast hn4
        · have ht1 : P.pop.n1 = 1 := by omega
          rw [ht1] at hl
          have hn4 : (n : ℝ) ≤ 4 := by norm_num at hl; linarith
          exact_mod_cast hn4
      have hbounds := AronowAudit.P002.Wave1.PrintedTheorem2.n11_proof n (toPopulation P.pop)
      constructor
      · apply (hbounds.1 _).2.trans
        generalize heq : P.pop.n1 = t at *
        unfold controlSize
        rw [heq]
        interval_cases n <;> interval_cases t <;> norm_num at *
      · apply (hbounds.1 _).2.trans
        generalize heq : P.pop.n1 = t at *
        unfold controlSize
        rw [heq]
        interval_cases n <;> interval_cases t <;> norm_num at *
  have hb1 : 258*controlSize P.pop/(P.pop.n1 : ℝ) ≤ 774 := by
    apply (div_le_iff₀ htR).mpr
    have hl := hP.2.2.2.1
    unfold controlSize
    linarith
  have hb0 : 258*(P.pop.n1 : ℝ)/controlSize P.pop ≤ 774 := by
    apply (div_le_iff₀ hcR).mpr
    have hu := hP.2.2.2.2.1
    unfold controlSize
    linarith
  refine ⟨hfirst.1, hfirst.2, ?_, ?_, ?_⟩
  · simpa only [div_div] using div_le_div_of_nonneg_right hb1 hd.le
  · simpa only [div_div] using div_le_div_of_nonneg_right hb0 hd.le
  · have H := AronowAudit.P002.Wave1.T4SC_class_failure n (toCovPopulation P) hn hP
    simp only [W2FullRank, not_and_or, ne_eq, not_not, probability_eq, gram_eq]
    exact H

theorem t4_inf_bounds : W2T4InfBounds := by
  intro α hα n hn
  have hclass := restrictedT4.2.2.2 α hα
  constructor
  · unfold infCoverageXi
    refine le_iInf fun β => le_iInf fun P => ?_
    apply ENNReal.ofReal_le_ofReal
    simpa only [P.property.2] using hclass.2.1 n hn P.val P.property.1
  · let P := degenerateCovModel n 0
    have hP := (hclass.1 n hn 0).1
    have hle : infCoverageXi n 1 0 (1/4) 4 (1/2) (1/4) α ≤
        ENNReal.ofReal (adjustedCoverage P (late P.pop) α) := by
      unfold infCoverageXi
      exact iInf_le_of_le (late P.pop) (iInf_le_of_le ⟨P, hP, rfl⟩ le_rfl)
    apply hle.trans
    apply ENNReal.ofReal_le_one.mpr
    exact ((AronowAudit.P002.Wave1.PrintedTheorem2.n11_proof n (toPopulation P.pop)).1
      (adjustedAccepted P (late P.pop) α)).2

/-- Constant effects make the response fixed; use the existing generic quantile theorem. -/
theorem adjusted_nominal_of_cdf
    (sizes : ℕ → ℕ) (k : ℕ) (P : ∀ j, CovPopulation (sizes j) k)
    (δ e A B r α : ℝ) (hα : 0 < α ∧ α < 1) (hP : ∀ j, Xi (P j) δ e A B r)
    (hconstant : ∀ j, ∃ β : ℝ, ∀ i, (P j).pop.y i true = (P j).pop.y i false+β)
    (hCDF : ∀ t : ℝ, 0 < t → Tendsto (fun j => probability (P j).pop (fun S =>
      adjustedAR (P j) (fun i => (P j).pop.y i false) S ≤ ENNReal.ofReal t))
      atTop (nhds (W2AbsNormalCDF t))) :
    Tendsto (fun j => ENNReal.ofReal (adjustedCoverage (P j) (late (P j).pop) α))
      atTop (nhds (ENNReal.ofReal (1-α))) := by
  have H := AronowAudit.P002.Wave1.GP0022B2b_SH_nominal_of_cdf_limits sizes
    (fun j => toPopulation (P j).pop)
    (fun j => adjustedAR (P j) (fun i => (P j).pop.y i false))
    (fun j => (hP j).1) α hα W2AbsNormalCDF hCDF
    (fun ε hε => AronowAudit.P002.Wave1.GP0022B2b_SH_normal_bracket α hα ε hε)
  have ho (j : ℕ) (S : Finset (Fin (sizes j))) :
      observedW (P j).pop (late (P j).pop) S = fun i => (P j).pop.y i false :=
    AronowAudit.P002.Wave1.GP0022B2b_SH_observedW_baseline
      (toPopulation (P j).pop) (hP j).2.2.1 (hconstant j) S
  apply ENNReal.tendsto_ofReal
  change Tendsto (fun j => probability (P j).pop (fun S =>
    adjustedAR (P j) (observedW (P j).pop (late (P j).pop) S) S ≤
      quantile (P j).pop (adjustedAR (P j) (observedW (P j).pop (late (P j).pop) S)) α))
    atTop (nhds (1-α))
  simp_rw [ho]
  simpa only [← probability_eq, ← quantile_eq] using H

/-- A finite nominal liminf guarantees that at least one class is inhabited. -/
theorem exists_xi_of_nominal (k : ℕ) (δ e A B r α : ℝ)
    (h : Filter.liminf (fun n => infCoverageXi n k δ e A B r α)
      (atTop ⊓ Filter.principal (xiSizes k δ e A B r)) = ENNReal.ofReal (1-α)) :
    ∃ n, ∃ P : CovPopulation n k, Xi P δ e A B r := by
  by_contra hnone
  have hs : xiSizes k δ e A B r = ∅ := by
    ext n
    simp only [xiSizes, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hh => hnone ⟨n, hh⟩
  rw [hs] at h
  simp only [Filter.principal_empty, inf_bot_eq, Filter.liminf_bot] at h
  exact ENNReal.ofReal_ne_top h.symm

end
end SAP.P002a.WH.W2
