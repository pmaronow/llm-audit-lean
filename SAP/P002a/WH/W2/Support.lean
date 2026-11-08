import SAP.P002a.Defs.WholeW2
import SAP.P002a.Bridge
import AronowAudit.P002.Wave1.Gap.GLP0021B1
import AronowAudit.P002.Wave1.Gap.GP0021B1
import AronowAudit.P002.Wave1.Gap.GP0021B2
import AronowAudit.P002.Wave1.Gap.GLP0022B1
import AronowAudit.P002.Wave1.Gap.GLP0022B2
import AronowAudit.P002.Wave1.Gap.GP0022B2b
import AronowAudit.P002.Wave1.Gap.Theorem2
import AronowAudit.P002.Wave1.Gap.DecisionLemma12

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

theorem restrictedT1 : SAP.P002a.T1Statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact AronowAudit.P002.negative_delta_counterexample
  · intro m hm
    exact AronowAudit.P002.Wave1.negative_delta_sequence_proof m hm
  · exact AronowAudit.P002.negative_delta_AMGM_failure
  · exact AronowAudit.P002.negative_delta_population_ols

theorem restrictedT2 : SAP.P002a.T2Statement := by
  constructor
  · intro n P δ r A hδ hr hA hP
    exact AronowAudit.P002.Wave1.corrected_lemma5_proof (toPopulation P) δ r A hδ hr hA hP
  · intro n k P δ e A B r hk hδ he hA hB hr hP
    exact AronowAudit.P002.Wave1.corrected_E10_proof (toCovPopulation P)
      δ e A B r hk hδ he hA hB hr hP

theorem restrictedT4 : SAP.P002a.T4Statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact @AronowAudit.P002.half_moment_collapse
  · intro n P hP
    exact AronowAudit.P002.theta_half_moment_constant (toPopulation P) hP
  · intro α hα
    have h := AronowAudit.P002.theorem1_sharpness_counterexample α hα
    refine ⟨h.1, ?_, ?_, ?_, ?_⟩
    · intro n hn P hP
      exact h.2.1 n hn (toPopulation P) hP
    · simpa only [infCoverageTheta_eq] using h.2.2.1
    · simpa only [infCoverageTheta_eq] using h.2.2.2.1
    · simpa only [infCoverageTheta_eq] using h.2.2.2.2
  · intro α hα
    have h := AronowAudit.P002.Wave1.theorem2_sharpness_counterexample_proof α hα
    refine ⟨h.1, ?_, ?_, ?_⟩
    · intro n hn P hP
      exact h.2.1 n hn (toCovPopulation P) hP
    · simpa only [infCoverageXi_eq] using h.2.2.1
    · simpa only [infCoverageXi_eq] using h.2.2.2

theorem restrictedT5 : SAP.P002a.T5Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro δ r A α hδ hr hA hα _hclasses
    have h := AronowAudit.P002.Wave1.corrected_theorem1_proof δ r A α hδ hr hA hα
    simpa only [← infCoverageTheta_eq, ← thetaSizes_eq, thetaSizes] using h
  · intro k δ e A B r α hk hδ he hA hB hr hα _hclasses
    have h := AronowAudit.P002.Wave1.corrected_theorem2_proof k δ e A B r α
      hk hδ he hA hB hr hα
    simpa only [← infCoverageXi_eq, ← xiSizes_eq, xiSizes] using h
  · intro sizes hsizes P δ r A α hδ hr hA hα hP hconstant hnondegenerate
    have h := AronowAudit.P002.Wave1.corrected_remark3_sharpness_proof sizes hsizes
      (fun n => toPopulation (P n)) δ r A α hδ hr hA hα hP hconstant hnondegenerate
    constructor
    · simpa only [← coverage_eq, ← late_eq] using h.1
    · simpa only [← infCoverageTheta_eq, ← thetaSizes_eq, thetaSizes] using h.2

theorem restrictedT14 : T14Statement := by
  exact AronowAudit.P002.Wave1.missing_square_counterexample_proof

/-- All omitted twelve-unit calculations are finite sums and elementary design algebra. -/
theorem t1_details : W2T1Details := by
  let P := negativeDeltaModel 1
  have heps (a : Bool) : residual P a 0 = fun i => P.pop.y i false := by
    funext i
    have hp : psi P a 0 = 0 := AronowAudit.P002.negative_delta_population_ols a
    simp only [residual, hp, dotProduct_zero, sub_zero]
    simp [w, P, negativeDeltaModel]
  have hv (a : Bool) : w P.pop a 0 = fun i => P.pop.y i false := by
    funext i
    simp [w, P, negativeDeltaModel]
  have hvar : popVar (fun i => P.pop.y i false) = 12/11 := by
    norm_num [popVar, mean, P, negativeDeltaModel, Fin.sum_univ_succ]
  have hfour : fourthNorm (fun i => P.pop.y i false) = 1 := by
    norm_num [fourthNorm, mean, P, negativeDeltaModel, Fin.sum_univ_succ]
  have hS (a : Bool) : S2 P.pop 0 a = 25/1188 := by
    rw [S2, hv, hvar]
    norm_num [fraction, P, negativeDeltaModel]
  have hcard : (assignments P.pop).card = 66 := restrictedT1.1.2.2.2.1
  have hray : leastRayleigh P.x = 1 := by
    have hset : {t : ℝ | ∃ b : Fin 1 → ℝ, normSq b = 1 ∧
        mean (fun i => dotProduct (P.x i) b ^ 2) = t} = {1} := by
      ext t
      constructor
      · rintro ⟨b, hb, ht⟩
        have hm : mean (fun i => dotProduct (P.x i) b ^ 2) = normSq b := by
          norm_num [mean, dotProduct, normSq, P, negativeDeltaModel, Fin.sum_univ_succ]
        simp [← ht, hm, hb]
      · intro ht
        have ht1 : t = 1 := Set.mem_singleton_iff.mp ht
        subst t
        refine ⟨fun _ => 1, ?_, ?_⟩
        · norm_num [normSq, Fin.sum_univ_succ]
        · norm_num [mean, dotProduct, P, negativeDeltaModel, Fin.sum_univ_succ]
    unfold leastRayleigh
    rw [hset]
    exact csInf_singleton 1
  change (∀ i, P.pop.d i false = false ∧ P.pop.d i true = true) ∧
  (∀ a, w P.pop a 0 = fun i => P.pop.y i false) ∧
  (∀ a, mean (w P.pop a 0) = 0 ∧ fourthNorm (w P.pop a 0) = 1) ∧
  groupCov (compliers P.pop) (w P.pop true 0) (w P.pop false 0) = 12/11 ∧
  (∀ a, groupVar (compliers P.pop) (w P.pop a 0) = 12/11) ∧
  (1 : ℝ) ≤ 2*Real.sqrt (12/11) ∧
  (∑ i, P.x i 0) = 0 ∧ (∑ i, P.pop.y i false) = 0 ∧
  (∑ i, P.x i 0*P.pop.y i false) = 0 ∧ (∑ i, P.x i 0^2) = 12 ∧
  mean (fun i => P.x i 0^4) = 1 ∧ leastRayleigh P.x = 1 ∧
  (∀ a, residual P a 0 = fun i => P.pop.y i false) ∧
  popCov (residual P true 0) (residual P false 0) = 12/11 ∧
  (∀ a, popVar (residual P a 0) = 12/11 ∧ fourthNorm (residual P a 0) = 1) ∧
  Sdiff2 P.pop 0 = 0 ∧ popVar (fun i => residual P true 0 i-residual P false 0 i) = 0 ∧
  (1-(-1/2 : ℝ))*(controlSize P.pop/(12*2)*S2 P.pop 0 true +
    2/(12*controlSize P.pop)*S2 P.pop 0 false) = 65/4752 ∧
  (1-(-1/2 : ℝ))*(controlSize P.pop/(12*2)*popVar (residual P true 0) +
    2/(12*controlSize P.pop)*popVar (residual P false 0)) = 39/55 ∧
  (∀ S ∈ assignments P.pop,
    probability P.pop (fun T => T = S) = 1/66 ∧
    oracleTau P 0 S = (1/2)*∑ i ∈ S, P.pop.y i false -
      (1/10)*∑ i ∈ Sᶜ, P.pop.y i false)
  refine ⟨?_, hv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hray, heps, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; simp [P, negativeDeltaModel]
  · intro a; rw [hv, hfour]
    norm_num [mean, P, negativeDeltaModel, Fin.sum_univ_succ]
  · rw [hv true, hv false]
    norm_num [groupCov, groupMean, compliers, P, negativeDeltaModel, Fin.sum_univ_succ]
  · intro a; rw [hv a]
    norm_num [groupVar, groupCov, groupMean, compliers, P, negativeDeltaModel, Fin.sum_univ_succ]
  · have hh : 1 ≤ Real.sqrt (12/11 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
    linarith
  · norm_num [P, negativeDeltaModel, Fin.sum_univ_succ]
  · norm_num [P, negativeDeltaModel, Fin.sum_univ_succ]
  · norm_num [P, negativeDeltaModel, Fin.sum_univ_succ]
  · norm_num [P, negativeDeltaModel, Fin.sum_univ_succ]
  · norm_num [mean, P, negativeDeltaModel, Fin.sum_univ_succ]
  · rw [heps true, heps false]
    simpa only [popCov, popVar, pow_two] using hvar
  · intro a; rw [heps a]; exact ⟨hvar, hfour⟩
  · have he : v P.pop true 0 = v P.pop false 0 := by
      funext i; simp only [v, hv]
    simp [Sdiff2, he]
  · simp only [heps, sub_self]; norm_num [popVar, mean]
  · rw [hS true, hS false]; norm_num [controlSize, P, negativeDeltaModel]
  · rw [heps true, heps false, hvar]; norm_num [controlSize, P, negativeDeltaModel]
  · intro S hS
    have hsz : S.card = 2 := (Finset.mem_powersetCard.mp hS).2
    have hcomp : Sᶜ.card = 10 := by rw [Finset.card_compl, Fintype.card_fin, hsz]
    constructor
    · unfold probability
      rw [hcard]
      norm_num
      apply Finset.card_eq_one.mpr
      refine ⟨S, ?_⟩
      ext T
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · intro h; subst T; exact ⟨hS, rfl⟩
    · have hp (a : Bool) : psi P a 0 = 0 := AronowAudit.P002.negative_delta_population_ols a
      have ho : observedW P.pop 0 S = fun i => P.pop.y i false := by
        funext i; simp [observedW, observedY, observedD, P, negativeDeltaModel]
      simp only [oracleTau, adjustedWith, hp, slopeDot, Pi.zero_apply, mul_zero,
        Finset.sum_const_zero, sub_zero, ho, groupMean, hsz, hcomp]
      ring

end
end SAP.P002a.WH.W2
