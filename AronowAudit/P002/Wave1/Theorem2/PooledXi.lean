import AronowAudit.P002.Wave1.Theorem2.Pooled

/-! The Xi-specific residual/slope decomposition for pooled moment bounds. -/

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

def T2C_slopeDifference {n k} (P : CovPopulation n k) (s : Fin k) : ℝ :=
  psi P true (late P.pop) (some s)-psi P false (late P.pop) (some s)

def T2C_ell {n k} (P : CovPopulation n k) (i : Fin n) : ℝ :=
  dotProduct (P.x i) (T2C_slopeDifference P)

def T2C_R {n k} (P : CovPopulation n k) (a : Bool) (i : Fin n) : ℝ :=
  (binary a-fraction P.pop)*T2C_ell P i+residual P a (late P.pop) i

def T2C_energy {n k} (P : CovPopulation n k) : ℝ :=
  fraction P.pop*(1-fraction P.pop)*mean (fun i => T2C_ell P i^2)+
    fraction P.pop*T2C_residualH P true+(1-fraction P.pop)*T2C_residualH P false

lemma T2C_mean_dot_product {n} {ι : Type*} [Fintype ι]
    (u : Fin n → ι → ℝ) (b : ι → ℝ) (q : Fin n → ℝ) :
    mean (fun i => dotProduct (u i) b*q i) =
      dotProduct (fun s => mean (fun i => u i s*q i)) b := by
  simp only [mean, dotProduct, Finset.sum_mul, Finset.sum_div, div_mul_eq_mul_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma T2C_ell_orthogonal {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hP : Xi P δ e A B r) (a : Bool) :
    mean (fun i => T2C_ell P i*residual P a (late P.pop) i) = 0 := by
  have h := T2C_mean_dot_product P.x (T2C_slopeDifference P) (residual P a (late P.pop))
  have hzero (s : Fin k) : mean (fun i => P.x i s*residual P a (late P.pop) i) = 0 :=
    T2C_score_centered P.x _ (T2C_Xi_residual_score P δ e A B r he hP a) (some s)
  simp_rw [hzero] at h
  simpa only [T2C_ell, dotProduct, zero_mul, Finset.sum_const_zero] using h

lemma T2C_R_score_zero {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hP : Xi P δ e A B r) (s : Option (Fin k)) :
    T2C_frozenMean P.pop (fun a i => augmented P.x i s*T2C_R P a i) = 0 := by
  have hmean (a : Bool) : mean (fun i => augmented P.x i s*T2C_R P a i) =
      (binary a-fraction P.pop)*mean (fun i => augmented P.x i s*T2C_ell P i) := by
    have hpoint : (fun i => augmented P.x i s*T2C_R P a i) =
        fun i => (binary a-fraction P.pop)*(augmented P.x i s*T2C_ell P i)+
          augmented P.x i s*residual P a (late P.pop) i := by
      funext i
      dsimp only [T2C_R]
      ring
    rw [hpoint, T2C_mean_add, T2C_mean_mul,
      T2C_score_centered P.x _ (T2C_Xi_residual_score P δ e A B r he hP a) s, add_zero]
  unfold T2C_frozenMean
  rw [hmean true, hmean false]
  simp only [binary, Bool.false_eq_true, ite_true, ite_false]
  ring

lemma T2C_R_second {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hP : Xi P δ e A B r) (a : Bool) :
    mean (fun i => T2C_R P a i^2) =
      (binary a-fraction P.pop)^2*mean (fun i => T2C_ell P i^2)+T2C_residualH P a := by
  have hpoint (i : Fin n) : T2C_R P a i^2 =
      (binary a-fraction P.pop)^2*T2C_ell P i^2+
        (2*(binary a-fraction P.pop))*(T2C_ell P i*residual P a (late P.pop) i)+
          residual P a (late P.pop) i^2 := by dsimp only [T2C_R]; ring
  simp_rw [hpoint, T2C_mean_add, T2C_mean_mul, T2C_ell_orthogonal P δ e A B r he hP a,
    mul_zero, add_zero]
  rfl

lemma T2C_R_energy {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hP : Xi P δ e A B r) :
    T2C_frozenMean P.pop (fun a i => T2C_R P a i^2) = T2C_energy P := by
  unfold T2C_frozenMean
  rw [T2C_R_second P δ e A B r he hP true, T2C_R_second P δ e A B r he hP false]
  simp only [binary, Bool.false_eq_true, ite_true, ite_false]
  unfold T2C_energy
  ring

lemma T2C_fraction_allocation {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (hP : Xi P δ e A B r) : r ≤ fraction P.pop ∧ r ≤ 1-fraction P.pop := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hP.1.1; omega : 0 < n)
  constructor
  · exact (le_div_iff₀ hn).mpr hP.2.2.2.1
  · have hu : fraction P.pop ≤ 1-r := (div_le_iff₀ hn).mpr hP.2.2.2.2.1
    linarith

lemma T2C_energy_lower {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (hr : 0 < r) (hP : Xi P δ e A B r) :
    r^2*mean (fun i => T2C_ell P i^2) ≤ T2C_energy P ∧
      (∀ a, r*T2C_residualH P a ≤ T2C_energy P) ∧
      (0 < T2C_totalH P → 0 < T2C_energy P) := by
  have hp := T2C_fraction_allocation P δ e A B r hP
  have hpn := T2C_fraction_bounds P.pop hP.1
  have hell := T2C_mean_nonneg (fun i => T2C_ell P i^2) (fun i => sq_nonneg _)
  have h1 := T2C_residualH_nonneg P true
  have h0 := T2C_residualH_nonneg P false
  have hprod : r^2 ≤ fraction P.pop*(1-fraction P.pop) := by
    have hh := mul_le_mul hp.1 hp.2 hr.le hpn.1
    nlinarith
  have hc1 := mul_le_mul_of_nonneg_right hp.1 h1
  have hc0 := mul_le_mul_of_nonneg_right hp.2 h0
  have hcell := mul_le_mul_of_nonneg_right hprod hell
  have hsum : r^2*mean (fun i => T2C_ell P i^2)+r*T2C_totalH P ≤ T2C_energy P := by
    dsimp [T2C_energy, T2C_totalH]
    nlinarith
  have ht : 0 ≤ T2C_totalH P := add_nonneg h1 h0
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · intro a
    have ha := T2C_residualH_le_total P a
    have hm := mul_le_mul_of_nonneg_left ha hr.le
    nlinarith [sq_nonneg r]
  · intro htotal
    have hh := mul_pos hr htotal
    nlinarith [sq_nonneg r]

def T2C_RK (k : ℕ) (e A B r : ℝ) : ℝ :=
  8*(((k : ℝ)+1)^2*max 1 A/(e^2*r^4)+4*B^4/r^2)

/-- Unbounded slope differences are controlled by the energy, using the Rayleigh bound. -/
lemma T2C_ell_fourth {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hr : 0 < r) (hP : Xi P δ e A B r) :
    mean (fun i => T2C_ell P i^4) ≤
      (((k : ℝ)+1)^2*max 1 A/(e^2*r^4))*(T2C_energy P)^2 := by
  let b : Option (Fin k) → ℝ := fun s => s.elim 0 (T2C_slopeDifference P)
  have hdot (i : Fin n) : dotProduct (augmented P.x i) b = T2C_ell P i := by
    simp [b, T2C_ell, augmented, dotProduct, Fintype.sum_option]
  have hnorm : normSq b = normSq (T2C_slopeDifference P) := by
    simp [b, normSq, Fintype.sum_option]
  have hpred := T2C_predictor_fourth P.x (by have := hP.1.1; omega) A
    (T2C_Xi_covariates P δ e A B r hP).2.1 b
  simp_rw [hdot, hnorm] at hpred
  have hray := (T2C_Xi_covariates P δ e A B r hP).2.2 (T2C_slopeDifference P)
  have henergy := (T2C_energy_lower P δ e A B r hr hP).1
  have hn : normSq (T2C_slopeDifference P) ≤ T2C_energy P/(e*r^2) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < e*r^2)).mpr
    have hh := mul_le_mul_of_nonneg_left hray (sq_nonneg r)
    change r^2*mean (fun i => (dotProduct (P.x i) (T2C_slopeDifference P))^2) ≤ _ at henergy
    nlinarith
  have hn2 : (normSq (T2C_slopeDifference P))^2 ≤ (T2C_energy P)^2/(e^2*r^4) := by
    have hh := pow_le_pow_left₀ (T2C_normSq_nonneg _) hn 2
    convert hh using 1 <;> ring
  apply hpred.trans
  have hh := mul_le_mul_of_nonneg_left hn2 (by positivity : 0 ≤ ((k : ℝ)+1)^2*max 1 A)
  convert hh using 1 <;> ring

lemma T2C_residual_energy_fourth {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hr : 0 < r) (hP : Xi P δ e A B r) (a : Bool) :
    mean (fun i => residual P a (late P.pop) i^4) ≤
      (4*B^4/r^2)*(T2C_energy P)^2 := by
  have hh := (T2C_energy_lower P δ e A B r hr hP).2.1 a
  have hH : T2C_residualH P a ≤ T2C_energy P/r :=
    (le_div_iff₀ hr).mpr (by nlinarith)
  have hH2 : (T2C_residualH P a)^2 ≤ (T2C_energy P)^2/r^2 := by
    have hpow := pow_le_pow_left₀ (T2C_residualH_nonneg P a) hH 2
    convert hpow using 1 <;> ring
  apply (T2C_Xi_residual_fourth P δ e A B r he hP a).trans
  have hm := mul_le_mul_of_nonneg_left hH2 (by positivity : 0 ≤ 4*B^4)
  convert hm using 1 <;> ring

lemma T2C_R_fourth {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hr : 0 < r) (hP : Xi P δ e A B r) (a : Bool) :
    mean (fun i => T2C_R P a i^4) ≤ T2C_RK k e A B r*(T2C_energy P)^2 := by
  have hp := T2C_fraction_bounds P.pop hP.1
  have hcoef2 : (binary a-fraction P.pop)^2 ≤ 1 := by
    cases a <;> simp only [binary, Bool.false_eq_true, ite_false, ite_true] <;> nlinarith
  have hcoef4 : (binary a-fraction P.pop)^4 ≤ 1 := by
    have h := pow_le_pow_left₀ (sq_nonneg (binary a-fraction P.pop)) hcoef2 2
    convert h using 1 <;> ring
  have hell := T2C_mean_nonneg (fun i => T2C_ell P i^4) (fun i => by positivity)
  have hcoef := mul_le_mul_of_nonneg_right hcoef4 hell
  have hR : mean (fun i => T2C_R P a i^4) ≤
      8*(mean (fun i => T2C_ell P i^4)+mean (fun i => residual P a (late P.pop) i^4)) := by
    calc
      _ ≤ mean (fun i => 8*((binary a-fraction P.pop)^4*T2C_ell P i^4+
          residual P a (late P.pop) i^4)) := by
        apply T2C_mean_mono
        intro i
        have h := T2C_fourth_sub ((binary a-fraction P.pop)*T2C_ell P i)
          (-residual P a (late P.pop) i)
        change ((binary a-fraction P.pop)*T2C_ell P i+residual P a (late P.pop) i)^4 ≤ _
        convert h using 1 <;> ring
      _ = 8*((binary a-fraction P.pop)^4*mean (fun i => T2C_ell P i^4)+
          mean (fun i => residual P a (late P.pop) i^4)) := by
        rw [T2C_mean_mul, T2C_mean_add, T2C_mean_mul]
      _ ≤ _ := by nlinarith
  have h1 := T2C_ell_fourth P δ e A B r he hr hP
  have h0 := T2C_residual_energy_fourth P δ e A B r he hr hP a
  apply hR.trans
  dsimp [T2C_RK]
  nlinarith

end
end AronowAudit.P002.Wave1
