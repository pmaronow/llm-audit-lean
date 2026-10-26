import AronowAudit.P002.Wave1.Theorem2.PooledObserved
import AronowAudit.P002.Wave1.Theorem2.ResidualCLT

namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def T2C_responsePopulation {n} (D : Population n) (q : Bool → Fin n → ℝ) : Population n where
  y i a := q a i
  d _ a := a
  n1 := D.n1

lemma T2C_response_compliers {n} (D : Population n) (q : Bool → Fin n → ℝ) :
    compliers (T2C_responsePopulation D q) = Finset.univ := by
  ext i
  simp [compliers, T2C_responsePopulation]

lemma T2C_response_late {n} (D : Population n) (q : Bool → Fin n → ℝ)
    (hq : mean (q true) = mean (q false)) : late (T2C_responsePopulation D q) = 0 := by
  unfold late
  rw [T2C_response_compliers]
  change groupMean Finset.univ (fun i => q true i-q false i) = 0
  have hmean : groupMean Finset.univ (fun i => q true i-q false i) =
      mean (fun i => q true i-q false i) := by simp [groupMean, mean]
  rw [hmean, T2C_mean_sub, hq, sub_self]

lemma T2C_response_w {n} (D : Population n) (q : Bool → Fin n → ℝ) (a : Bool) :
    w (T2C_responsePopulation D q) a 0 = q a := by
  funext i
  simp [w, T2C_responsePopulation]

lemma T2C_groupCov_univ {n} (hn : 2 ≤ n) (q t : Fin n → ℝ) :
    groupCov Finset.univ q t = popCov q t := by
  simp only [groupCov, Finset.card_univ, Fintype.card_fin, if_pos hn,
    groupMean, popCov, mean]

def T2C_residualPopulation {n k} (P : CovPopulation n k) : Population n :=
  T2C_responsePopulation P.pop (fun a => residual P a (late P.pop))

lemma T2C_residual_late {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hP : Xi P δ e A B r) : late (T2C_residualPopulation P) = 0 := by
  apply T2C_response_late
  rw [T2C_residual_centered P.x _ (T2C_Xi_residual_score P δ e A B r he hP true),
    T2C_residual_centered P.x _ (T2C_Xi_residual_score P δ e A B r he hP false)]

lemma T2C_residual_w {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hP : Xi P δ e A B r) (a : Bool) :
    w (T2C_residualPopulation P) a (late (T2C_residualPopulation P)) =
      residual P a (late P.pop) := by
  rw [T2C_residual_late P δ e A B r he hP]
  exact T2C_response_w _ _ a

lemma T2C_residual_Theta {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hP : Xi P δ e A B r) : Theta (T2C_residualPopulation P) δ r B := by
  have hn : 0 < n := by have := hP.1.1; omega
  have hcomp : compliers (T2C_residualPopulation P) = Finset.univ :=
    T2C_response_compliers P.pop (fun a => residual P a (late P.pop))
  have hmean (a : Bool) := T2C_residual_centered P.x _
    (T2C_Xi_residual_score P δ e A B r he hP a)
  have hw (a : Bool) := T2C_residual_w P δ e A B r he hP a
  refine ⟨hP.1, ?_, ?_, hP.2.2.2.1, hP.2.2.2.2.1, ?_, ?_⟩
  · intro i hi
    change (false : Bool) = true at hi
    contradiction
  · rw [hcomp]
    exact Finset.univ_nonempty_iff.mpr ⟨⟨0,hn⟩⟩
  · rw [hcomp, T2C_groupCov_univ hP.1.1]
    simp only [groupVar, T2C_groupCov_univ hP.1.1]
    simp only [hw]
    have hself (q : Fin n → ℝ) : popCov q q = popVar q := by
      simp only [popCov, popVar, pow_two]
    simpa only [hself] using hP.2.2.2.2.2.1
  · intro a
    have hv : v (T2C_residualPopulation P) a (late (T2C_residualPopulation P)) =
        residual P a (late P.pop) := by
      unfold v
      simp only [hw, hmean, sub_zero]
    rw [hv, hw]
    exact hP.2.2.2.2.2.2.1 a

lemma T2C_mix_oracle {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hP : Xi P δ e A B r) (S : Finset (Fin n)) (hS : S ∈ assignments P.pop) :
    rawTau (T2C_residualPopulation P) (T2C_D_mix (T2C_residualPopulation P)) S =
      (fraction P.pop*(1-fraction P.pop))*oracleTau P (late P.pop) S := by
  have hΘ := T2C_residual_Theta P δ e A B r he hP
  have hm := T2C_D_mix_tau (T2C_residualPopulation P) hΘ.1 hΘ.2.1 hΘ.2.2.1 S hS
  rw [NDS_tau_as_contrast (T2C_residualPopulation P) hΘ.1 _ S hS] at hm
  rw [T2C_residual_w P δ e A B r he hP true, T2C_residual_w P δ e A B r he hP false] at hm
  have hx := T2C_Xi_covariates P δ e A B r hP
  have hg := T2C_population_det P.x e A (by have := hP.1.1; omega) he hx
  have ho := (corrected_oracle_expansion P hP.1 hP.2.1 hP.2.2.1 hx.1 hg S hS).2
  rw [ho]
  exact hm

lemma T2C_mix_oracle_variance {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hP : Xi P δ e A B r) :
    designVariance (T2C_residualPopulation P)
        (rawTau (T2C_residualPopulation P) (T2C_D_mix (T2C_residualPopulation P))) =
      (fraction P.pop*(1-fraction P.pop))^2*designVariance P.pop (oracleTau P (late P.pop)) := by
  change designVariance P.pop _ = _
  calc
    _ = designVariance P.pop (fun S => (fraction P.pop*(1-fraction P.pop))*
        oracleTau P (late P.pop) S) :=
      NDS_variance_congr P.pop (T2C_mix_oracle P δ e A B r he hP)
    _ = _ := by
      simpa only [sub_zero] using NDS_variance_affine P.pop hP.1
        (oracleTau P (late P.pop)) (fraction P.pop*(1-fraction P.pop)) 0

/-- The adjusted oracle contrast obeys the same scalar finite-population CLT. -/
theorem T2C_oracle_abs_cdf (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ j, CovPopulation (sizes j) k) (δ e A B r : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1/2) (hP : ∀ j, Xi (P j) δ e A B r)
    (hH : ∀ j, 0 < T2C_totalH (P j)) (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun j => probability (P j).pop (fun S =>
      |oracleTau (P j) (late (P j).pop) S/
        Real.sqrt (designVariance (P j).pop (oracleTau (P j) (late (P j).pop)))| ≤ t))
      atTop (nhds (SH_absNormalCDF t)) := by
  let Q := fun j => T2C_residualPopulation (P j)
  have hΘ (j) : Theta (Q j) δ r B := T2C_residual_Theta (P j) δ e A B r he (hP j)
  have hQtotal (j) : 0 < T2C_D_total (Q j) := by
    change 0 < popVar (w (Q j) true (late (Q j)))+popVar (w (Q j) false (late (Q j)))
    rw [T2C_residual_w (P j) δ e A B r he (hP j) true,
      T2C_residual_w (P j) δ e A B r he (hP j) false]
    have hvar (a : Bool) := T2C_second_le_popVar (hP j).1.1
      (residual (P j) a (late (P j).pop)) (T2C_residual_centered (P j).x _
        (T2C_Xi_residual_score (P j) δ e A B r he (hP j) a))
    have hh : 0 < T2C_residualH (P j) true+T2C_residualH (P j) false := hH j
    dsimp only [T2C_residualH] at hh
    linarith [hvar true, hvar false]
  have hlim := (T2C_D_mix_CLT sizes hsizes Q δ r B hδ hr hB hΘ hQtotal).2 t ht
  apply hlim.congr'
  apply Eventually.of_forall
  intro j
  apply T2C_probability_congr (P j).pop
  intro S hS
  have hp : 0 < fraction (P j).pop ∧ fraction (P j).pop < 1 := by
    have hm : (0 : ℝ) < (P j).pop.n1 := by exact_mod_cast (hP j).1.2.1
    have hmn : ((P j).pop.n1 : ℝ) < sizes j := by exact_mod_cast (hP j).1.2.2
    exact ⟨div_pos hm (hm.trans hmn), (div_lt_one (hm.trans hmn)).mpr hmn⟩
  have ha : 0 < fraction (P j).pop*(1-fraction (P j).pop) := mul_pos hp.1 (sub_pos.mpr hp.2)
  have hn : (0 : ℝ) < sizes j := by exact_mod_cast (by have := (hP j).1.1; omega : 0 < sizes j)
  have hbase : 0 < ((1-max δ 0)*r)*T2C_totalH (P j)/sizes j :=
    div_pos (mul_pos (mul_pos (sub_pos.mpr (max_lt hδ zero_lt_one)) hr.1) (hH j)) hn
  have hV := hbase.trans_le (T2C_observed_variance_lower (P j) δ e A B r hk hδ he hA hB hr (hP j))
  have hnorm : rawTau (Q j) (T2C_D_mix (Q j)) S/
      Real.sqrt (designVariance (Q j) (rawTau (Q j) (T2C_D_mix (Q j)))) =
    oracleTau (P j) (late (P j).pop) S/
      Real.sqrt (designVariance (P j).pop (oracleTau (P j) (late (P j).pop))) := by
    rw [T2C_mix_oracle (P j) δ e A B r he (hP j) S hS,
      T2C_mix_oracle_variance (P j) δ e A B r he (hP j),
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ha.le]
    exact mul_div_mul_left _ _ ha.ne'
  rw [hnorm]

end
end AronowAudit.P002.Wave1
