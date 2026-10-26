import AronowAudit.P002.Wave1.Theorem2.PooledXi

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

lemma T2C_pooled_affine {n k} (x : Fin n → Fin k → ℝ) (q : Fin n → ℝ)
    (b : Option (Fin k) → ℝ) (hg : (gram x Finset.univ).det ≠ 0) :
    T2C_pooledResidual x (fun i => q i+dotProduct (augmented x i) b) = T2C_pooledResidual x q := by
  have h := ols_error x Finset.univ (fun i => q i+dotProduct (augmented x i) b) b hg
  have hfun : (fun i => q i+dotProduct (augmented x i) b-dotProduct (augmented x i) b) = q := by
    funext i
    ring
  rw [hfun] at h
  have hols : ols x Finset.univ (fun i => q i+dotProduct (augmented x i) b)-b =
      ols x Finset.univ q := by simpa only [ols, if_pos hg] using h
  have heq := sub_eq_iff_eq_add.mp hols
  funext i
  dsimp only [T2C_pooledResidual]
  rw [heq, dotProduct_add]
  ring

lemma T2C_observed_pooledResidual {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hP : Xi P δ e A B r) (S : Finset (Fin n)) (hS : S ∈ assignments P.pop) :
    T2C_pooledResidual P.x (observedW P.pop (late P.pop) S) =
      T2C_pooledResidual P.x (T2C_frozen (T2C_R P) S) := by
  let p := fraction P.pop
  let b : Option (Fin k) → ℝ := fun s => s.elim (psi P false (late P.pop) none)
    (fun t => p*psi P true (late P.pop) (some t)+(1-p)*psi P false (late P.pop) (some t))
  have hcov := T2C_Xi_covariates P δ e A B r hP
  have hg := T2C_population_det P.x e A (by have := hP.1.1; omega) he hcov
  have hint := (corrected_oracle_expansion P hP.1 hP.2.1 hP.2.2.1 hcov.1 hg S hS).1
  have hell (i : Fin n) : T2C_ell P i =
      slopeDot (P.x i) (psi P true (late P.pop))-slopeDot (P.x i) (psi P false (late P.pop)) := by
    simp only [T2C_ell, T2C_slopeDifference, slopeDot, dotProduct, mul_sub, Finset.sum_sub_distrib]
  have hres (a : Bool) (i : Fin n) : residual P a (late P.pop) i =
      w P.pop a (late P.pop) i-psi P a (late P.pop) none-
        slopeDot (P.x i) (psi P a (late P.pop)) := by
    simp only [residual, dotProduct, Fintype.sum_option, augmented, one_mul, slopeDot]
    ring
  have hpred (i : Fin n) : dotProduct (augmented P.x i) b = psi P false (late P.pop) none+
      p*slopeDot (P.x i) (psi P true (late P.pop))+
        (1-p)*slopeDot (P.x i) (psi P false (late P.pop)) := by
    simp only [dotProduct, Fintype.sum_option, augmented, one_mul]
    change psi P false (late P.pop) none+
      (∑ s, P.x i s*(p*psi P true (late P.pop) (some s)+
        (1-p)*psi P false (late P.pop) (some s))) = _
    have hpoint (s : Fin k) : P.x i s*(p*psi P true (late P.pop) (some s)+
        (1-p)*psi P false (late P.pop) (some s)) =
      p*(P.x i s*psi P true (late P.pop) (some s))+
        (1-p)*(P.x i s*psi P false (late P.pop) (some s)) := by ring
    simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]
    dsimp [slopeDot]
    ring
  have hfun : observedW P.pop (late P.pop) S =
      fun i => T2C_frozen (T2C_R P) S i+dotProduct (augmented P.x i) b := by
    funext i
    by_cases hi : i ∈ S
    · rw [observedW_treated P.pop (late P.pop) S i hi]
      simp only [T2C_frozen, if_pos hi, T2C_R, binary, ite_true]
      rw [hres true i, hpred i, hell i, hint]
      dsimp [p]
      ring
    · rw [observedW_control P.pop (late P.pop) S i (Finset.mem_compl.mpr hi)]
      simp only [T2C_frozen, if_neg hi, T2C_R, binary, Bool.false_eq_true, ite_false]
      rw [hres false i, hpred i, hell i]
      dsimp [p]
      ring
  rw [hfun]
  exact T2C_pooled_affine P.x _ b hg

lemma T2C_observed_pooledH {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hP : Xi P δ e A B r) (S : Finset (Fin n)) (hS : S ∈ assignments P.pop) :
    T2C_pooledH P.x (observedW P.pop (late P.pop) S) =
      T2C_pooledH P.x (T2C_frozen (T2C_R P) S) := by
  unfold T2C_pooledH
  rw [T2C_observed_pooledResidual P δ e A B r he hP S hS]

/-- Pooled-residual kurtosis control from the Xi assumptions with no response-scale bound. -/
theorem T2C_observed_pooled_limit (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ j, CovPopulation (sizes j) k) (δ e A B r : ℝ)
    (he : 0 < e) (hr : 0 < r) (hP : ∀ j, Xi (P j) δ e A B r)
    (hH : ∀ j, 0 < T2C_totalH (P j)) :
    Tendsto (fun j => probability (P j).pop (fun S =>
      ¬ (0 < T2C_pooledH (P j).x (observedW (P j).pop (late (P j).pop) S) ∧
        mean (fun i => T2C_pooledResidual (P j).x (observedW (P j).pop (late (P j).pop) S) i^4) ≤
          T2C_pooledK k e A (T2C_RK k e A B r)*
            (T2C_pooledH (P j).x (observedW (P j).pop (late (P j).pop) S))^2)))
      atTop (nhds 0) := by
  have hD (j) := (hP j).1
  have hl (j) := (hP j).2.2.2.1
  have hu (j) := (hP j).2.2.2.2.1
  have hcov (j) := T2C_Xi_covariates (P j) δ e A B r (hP j)
  have hL (j) : 0 < T2C_energy (P j) :=
    (T2C_energy_lower (P j) δ e A B r hr (hP j)).2.2 (hH j)
  have h := T2C_frozen_pooled_limit sizes hsizes k P e A r (T2C_RK k e A B r) he hr
    (by dsimp [T2C_RK]; positivity) hD hl hu hcov (fun j => T2C_R (P j))
    (fun j => T2C_energy (P j)) hL
    (fun j => T2C_R_score_zero (P j) δ e A B r he (hP j))
    (fun j => T2C_R_energy (P j) δ e A B r he (hP j))
    (fun j => T2C_R_fourth (P j) δ e A B r he hr (hP j))
  apply h.congr'
  apply Eventually.of_forall
  intro j
  apply T2C_probability_congr
  intro S hS
  rw [T2C_observed_pooledH (P j) δ e A B r he (hP j) S hS,
    T2C_observed_pooledResidual (P j) δ e A B r he (hP j) S hS]

end
end AronowAudit.P002.Wave1
