import AronowAudit.P002.P002_Audit
import AronowAudit.External.Causalean.Experimentation.FinitePopulationMoments

/-! Repeated-block counterexample and corrected complier variance bound. -/
namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

/- The finite-design bridge and contrast variance below are adapted from
this repository's `GP0022B2.lean`. -/
private theorem NDS_mem_assignments {n} (P : Population n) (S : Finset (Fin n)) :
    S ∈ assignments P ↔ S.card = P.n1 := by
  simp only [assignments, Finset.mem_powersetCard, Finset.subset_univ, true_and]

/-- This equality is independent of the validity/nonemptiness of the design. -/
theorem NDS_sum_carrier {n} (P : Population n) (f : Finset (Fin n) → ℝ) :
    (∑ S ∈ assignments P, f S) =
      ∑ S : {S : Finset (Fin n) // S.card = P.n1}, f S.val := by
  exact Finset.sum_subtype (assignments P) (NDS_mem_assignments P) f

/-- Uniform finite averages on the two representations of the assignment space. -/
theorem NDS_expectation_carrier {n} (P : Population n) (h : ValidDesign P)
    (f : Finset (Fin n) → ℝ) :
    expectation P f =
      (Causalean.Experimentation.DesignBased.completeRandomization (V := Fin n) P.n1
        (by simpa only [Fintype.card_fin] using Nat.le_of_lt h.2.2)).E
        (fun S => f S.val) := by
  have hcard : (assignments P).card =
      Fintype.card {S : Finset (Fin n) // S.card = P.n1} := by
    rw [Causalean.Experimentation.DesignBased.completeRandomization_card]
    simp only [assignments, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  unfold expectation Causalean.Experimentation.DesignBased.FiniteDesign.E
  rw [hcard, NDS_sum_carrier]
  simp only [Causalean.Experimentation.DesignBased.completeRandomization,
    ← Finset.mul_sum, one_div]
  ring

/-- Transport of the actual centered finite variance, not a formula-defined variance. -/
theorem NDS_variance_carrier {n} (P : Population n) (h : ValidDesign P)
    (f : Finset (Fin n) → ℝ) :
    designVariance P f =
      (Causalean.Experimentation.DesignBased.completeRandomization (V := Fin n) P.n1
        (by simpa only [Fintype.card_fin] using Nat.le_of_lt h.2.2)).Var
        (fun S => f S.val) := by
  unfold designVariance Causalean.Experimentation.DesignBased.FiniteDesign.Var
  rw [NDS_expectation_carrier P h f, NDS_expectation_carrier P h]

private theorem NDS_expectation_congr {n} (P : Population n)
    {f g : Finset (Fin n) → ℝ} (hfg : ∀ S ∈ assignments P, f S = g S) :
    expectation P f = expectation P g := by
  unfold expectation
  congr 1
  exact Finset.sum_congr rfl hfg

/-- Equality is needed only on the actual finite support. -/
theorem NDS_variance_congr {n} (P : Population n)
    {f g : Finset (Fin n) → ℝ} (hfg : ∀ S ∈ assignments P, f S = g S) :
    designVariance P f = designVariance P g := by
  have he : expectation P f = expectation P g := NDS_expectation_congr P hfg
  unfold designVariance
  rw [he]
  apply NDS_expectation_congr
  intro S hS
  rw [hfg S hS]

/-- Both zero scales and nonzero intercept shifts are included. -/
theorem NDS_variance_affine {n} (P : Population n) (h : ValidDesign P)
    (f : Finset (Fin n) → ℝ) (c d : ℝ) :
    designVariance P (fun S => c * f S - d) = c ^ 2 * designVariance P f := by
  have he : expectation P (fun S => c * f S - d) = c * expectation P f - d := by
    rw [expectation_sub, expectation_mul, expectation_const P h]
  unfold designVariance
  rw [he]
  calc
    expectation P (fun S => (c * f S - d - (c * expectation P f - d)) ^ 2) =
        expectation P (fun S => c ^ 2 * (f S - expectation P f) ^ 2) := by
      apply NDS_expectation_congr
      intro S hS
      ring
    _ = c ^ 2 * expectation P (fun S => (f S - expectation P f) ^ 2) :=
      expectation_mul P _ _

/-- The vendored SRS result, transported to P002's finite assignment average. -/
theorem NDS_groupMean_variance {n} (P : Population n) (h : ValidDesign P)
    (q : Fin n → ℝ) :
    designVariance P (fun S => groupMean S q) =
      (1 / (P.n1 : ℝ) - 1 / (n : ℝ)) * popVar q := by
  rw [NDS_variance_carrier P h]
  have hfun :
      (fun S : {S : Finset (Fin n) // S.card = P.n1} => groupMean S.val q) =
      Causalean.Experimentation.FinitePopulationMoments.sampleMean P.n1 q := by
    funext S
    simp only [groupMean, S.property,
      Causalean.Experimentation.FinitePopulationMoments.sampleMean]
    congr 1
    simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hfun]
  have hv := Causalean.Experimentation.FinitePopulationMoments.Var_sampleMean
    (U := Fin n) P.n1
    (by simpa only [Fintype.card_fin] using Nat.le_of_lt h.2.2)
    h.2.1 (by simpa only [Fintype.card_fin] using h.1) q
  simpa only [Causalean.Experimentation.FinitePopulationMoments.popVar,
    Causalean.Experimentation.FinitePopulationMoments.popMean,
    Fintype.card_fin, popVar, mean] using hv

/-! The remaining identities are finite-sum algebra over arbitrary potential vectors. -/

private theorem NDS_mean_add_mul {n} (a b : Fin n → ℝ) (t : ℝ) :
    mean (fun i => a i + t * b i) = mean a + t * mean b := by
  simp only [mean, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private theorem NDS_mean_sub {n} (a b : Fin n → ℝ) :
    mean (fun i => a i - b i) = mean a - mean b := by
  simp only [mean, Finset.sum_sub_distrib, sub_div]

/-- Population variance with its exact P002 divisor n-1. -/
theorem NDS_popVar_add_mul {n} (a b : Fin n → ℝ) (t : ℝ) :
    popVar (fun i => a i + t * b i) =
      popVar a + 2 * t * popCov a b + t ^ 2 * popVar b := by
  have hpoint (i : Fin n) :
      (a i + t * b i - (mean a + t * mean b)) ^ 2 =
      (a i - mean a) ^ 2 + 2 * t * ((a i - mean a) * (b i - mean b)) +
        t ^ 2 * (b i - mean b) ^ 2 := by ring
  unfold popVar
  rw [NDS_mean_add_mul]
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, popCov]
  ring

private theorem NDS_popVar_sub {n} (a b : Fin n → ℝ) :
    popVar (fun i => a i - b i) = popVar a + popVar b - 2 * popCov a b := by
  have hf : (fun i => a i - b i) = (fun i => a i + (-1 : ℝ) * b i) := by
    funext i
    ring
  rw [hf, NDS_popVar_add_mul]
  ring

/-- A two-potential-response contrast as an affine SRS mean, on the support. -/
theorem NDS_contrast_as_mean {n} (P : Population n) (h : ValidDesign P)
    (a b : Fin n → ℝ) (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    groupMean S a - groupMean Sᶜ b =
      groupMean S (fun i => a i + (P.n1 : ℝ) / controlSize P * b i) -
        (n : ℝ) / controlSize P * mean b := by
  have hScard : S.card = P.n1 := (NDS_mem_assignments P S).mp hS
  have hCcard : ((Sᶜ).card : ℝ) = controlSize P := by
    simp only [Finset.card_compl, Fintype.card_fin, hScard]
    rw [Nat.cast_sub (Nat.le_of_lt h.2.2)]
    rfl
  have hm : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h.2.1)
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (show 0 < n by have := h.1; omega))
  have hc : controlSize P ≠ 0 := by
    have hmn : (P.n1 : ℝ) < n := by exact_mod_cast h.2.2
    unfold controlSize
    linarith
  have hsplit : (∑ i ∈ S, b i) + (∑ i ∈ Sᶜ, b i) = ∑ i, b i :=
    Finset.sum_add_sum_compl S b
  have hcomp : (∑ i ∈ Sᶜ, b i) = (∑ i, b i) - ∑ i ∈ S, b i := by
    linarith only [hsplit]
  unfold groupMean mean
  rw [hScard, hCcard]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hcomp]
  field_simp [hm, hc, hn]
  <;> ring

/-- Generic Neyman identity; reusable for oracle statistics with fixed coefficients. -/
theorem NDS_contrast_variance {n} (P : Population n) (h : ValidDesign P)
    (a b : Fin n → ℝ) :
    designVariance P (fun S => groupMean S a - groupMean Sᶜ b) =
      popVar a / (P.n1 : ℝ) + popVar b / controlSize P -
        popVar (fun i => a i - b i) / (n : ℝ) := by
  have hm : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h.2.1)
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (show 0 < n by have := h.1; omega))
  have hc : controlSize P ≠ 0 := by
    have hmn : (P.n1 : ℝ) < n := by exact_mod_cast h.2.2
    unfold controlSize
    linarith
  calc
    designVariance P (fun S => groupMean S a - groupMean Sᶜ b) =
        designVariance P (fun S =>
          (1 : ℝ) * groupMean S (fun i => a i + (P.n1 : ℝ) / controlSize P * b i) -
            (n : ℝ) / controlSize P * mean b) := by
      apply NDS_variance_congr
      intro S hS
      simpa only [one_mul] using NDS_contrast_as_mean P h a b S hS
    _ = designVariance P
        (fun S => groupMean S (fun i => a i + (P.n1 : ℝ) / controlSize P * b i)) := by
      rw [NDS_variance_affine P h]
      simp only [one_pow, one_mul]
    _ = _ := by
      rw [NDS_groupMean_variance P h, NDS_popVar_add_mul, NDS_popVar_sub]
      unfold controlSize at *
      field_simp [hm, hn, hc]
      <;> ring

private def NDS_y (i : ℕ) : ℝ := if i % 2 = 0 then -1 else 1
private def NDS_x (i : ℕ) : ℝ := if i % 4 < 2 then -1 else 1

private lemma NDS_block_sum (m : ℕ) (f : ℕ → ℝ)
    (hf : ∀ i j, f (12 * i + j) = f j) :
    (∑ i : Fin (12*m), f i.val) = (m : ℝ) * ∑ j : Fin 12, f j.val := by
  simp only [Fin.sum_univ_eq_sum_range]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have ht : (∑ j ∈ Finset.range 12, f (12*m+j)) =
        ∑ j ∈ Finset.range 12, f j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hf m j
    rw [ht]
    push_cast
    ring

private lemma NDS_sum_y (m : ℕ) : (∑ i : Fin (12*m), NDS_y i.val) = 0 := by
  rw [NDS_block_sum m NDS_y (by intro i j; simp [NDS_y, Nat.add_mod, Nat.mul_mod])]
  norm_num [NDS_y, Fin.sum_univ_succ]

private lemma NDS_sum_x (m : ℕ) : (∑ i : Fin (12*m), NDS_x i.val) = 0 := by
  rw [NDS_block_sum m NDS_x (by intro i j; simp [NDS_x, Nat.add_mod, Nat.mul_mod])]
  norm_num [NDS_x, Fin.sum_univ_succ]

private lemma NDS_sum_xy (m : ℕ) :
    (∑ i : Fin (12*m), NDS_x i.val * NDS_y i.val) = 0 := by
  rw [NDS_block_sum m (fun j => NDS_x j * NDS_y j)
    (by intro i j; simp [NDS_x, NDS_y, Nat.add_mod, Nat.mul_mod])]
  norm_num [NDS_x, NDS_y, Fin.sum_univ_succ]

private lemma NDS_y_sq (i : ℕ) : NDS_y i ^ 2 = 1 := by
  unfold NDS_y
  split <;> norm_num

private lemma NDS_x_sq (i : ℕ) : NDS_x i ^ 2 = 1 := by
  unfold NDS_x
  split <;> norm_num

private lemma NDS_y_four (i : ℕ) : NDS_y i ^ 4 = 1 := by
  rw [show 4 = 2*2 from rfl, pow_mul, NDS_y_sq, one_pow]

private lemma NDS_x_four (i : ℕ) : NDS_x i ^ 4 = 1 := by
  rw [show 4 = 2*2 from rfl, pow_mul, NDS_x_sq, one_pow]

private lemma NDS_valid (m : ℕ) (hm : 1 ≤ m) :
    ValidDesign (negativeDeltaModel m).pop := by
  simp only [ValidDesign, negativeDeltaModel]
  omega

private lemma NDS_n_ne (m : ℕ) (hm : 1 ≤ m) : ((12*m : ℕ) : ℝ) ≠ 0 := by
  exact_mod_cast (show 12*m ≠ 0 by omega)

private lemma NDS_compliers (m : ℕ) :
    compliers (negativeDeltaModel m).pop = Finset.univ := by
  simp [compliers, negativeDeltaModel]

private lemma NDS_late (m : ℕ) : late (negativeDeltaModel m).pop = 0 := by
  simp [late, NDS_compliers, groupMean, negativeDeltaModel]

private lemma NDS_w (m : ℕ) (a : Bool) :
    w (negativeDeltaModel m).pop a 0 = fun i => NDS_y i.val := by
  funext i
  simp [w, negativeDeltaModel, NDS_y]

private lemma NDS_mean_y (m : ℕ) : mean (fun i : Fin (12*m) => NDS_y i.val) = 0 := by
  simp [mean, NDS_sum_y]

private lemma NDS_v (m : ℕ) (a : Bool) :
    v (negativeDeltaModel m).pop a 0 = fun i => NDS_y i.val := by
  funext i
  simp [v, NDS_w, NDS_mean_y]

private lemma NDS_fraction (m : ℕ) (hm : 1 ≤ m) :
    fraction (negativeDeltaModel m).pop = 1/6 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  simp only [fraction, negativeDeltaModel, Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  <;> ring

private lemma NDS_control (m : ℕ) :
    controlSize (negativeDeltaModel m).pop = 10 * (m : ℝ) := by
  simp only [controlSize, negativeDeltaModel, Nat.cast_mul, Nat.cast_ofNat]
  ring

private lemma NDS_popVar (m : ℕ) :
    popVar (fun i : Fin (12*m) => NDS_y i.val) =
      ((12*m : ℕ) : ℝ) / (((12*m : ℕ) : ℝ)-1) := by
  simp [popVar, NDS_mean_y, NDS_y_sq]

private lemma NDS_popCov (m : ℕ) :
    popCov (fun i : Fin (12*m) => NDS_y i.val) (fun i => NDS_y i.val) =
      ((12*m : ℕ) : ℝ) / (((12*m : ℕ) : ℝ)-1) := by
  simpa only [popCov, popVar, pow_two] using NDS_popVar m

private lemma NDS_groupCov (m : ℕ) (hm : 1 ≤ m) :
    groupCov (compliers (negativeDeltaModel m).pop)
      (fun i => NDS_y i.val) (fun i => NDS_y i.val) =
      ((12*m : ℕ) : ℝ) / (((12*m : ℕ) : ℝ)-1) := by
  have hn : 2 ≤ 12*m := by omega
  simp only [NDS_compliers, groupCov, Finset.card_univ, Fintype.card_fin, if_pos hn]
  simpa only [popCov, groupMean, mean, Finset.card_univ, Fintype.card_fin]
    using NDS_popCov m

private lemma NDS_fourth (m : ℕ) (hm : 1 ≤ m) :
    fourthNorm (fun i : Fin (12*m) => NDS_y i.val) = 1 := by
  simp [fourthNorm, mean, NDS_y_four, show m ≠ 0 by omega]

private lemma NDS_gram (m : ℕ) (hm : 1 ≤ m) :
    gram (negativeDeltaModel m).x Finset.univ = 1 := by
  have hn := NDS_n_ne m hm
  ext s t
  rcases s with _ | s <;> rcases t with _ | t
  · simp [gram, groupMean, augmented, Matrix.one_apply, hn, show m ≠ 0 by omega]
  · fin_cases t
    change (∑ i : Fin (12*m), 1 * NDS_x i.val) / _ = 0
    simp [NDS_sum_x]
  · fin_cases s
    change (∑ i : Fin (12*m), NDS_x i.val * 1) / _ = 0
    simp [NDS_sum_x]
  · fin_cases s
    fin_cases t
    change (∑ i : Fin (12*m), NDS_x i.val * NDS_x i.val) / _ = 1
    simp [← pow_two, NDS_x_sq, hn, show m ≠ 0 by omega]

private lemma NDS_score (m : ℕ) (a : Bool) :
    score (negativeDeltaModel m).x Finset.univ
      (w (negativeDeltaModel m).pop a 0) = 0 := by
  rw [NDS_w]
  ext s
  rcases s with _ | s
  · change (∑ i : Fin (12*m), 1 * NDS_y i.val) / _ = 0
    simp [NDS_sum_y]
  · fin_cases s
    change (∑ i : Fin (12*m), NDS_x i.val * NDS_y i.val) / _ = 0
    simp [NDS_sum_xy]

private lemma NDS_psi (m : ℕ) (hm : 1 ≤ m) (a : Bool) :
    psi (negativeDeltaModel m) a 0 = 0 := by
  simp [psi, ols, NDS_gram m hm, NDS_score]

private lemma NDS_residual (m : ℕ) (hm : 1 ≤ m) (a : Bool) :
    residual (negativeDeltaModel m) a 0 = fun i => NDS_y i.val := by
  funext i
  simp [residual, NDS_psi m hm, NDS_w]

private lemma NDS_admissible (m : ℕ) (hm : 1 ≤ m) :
    Theta (negativeDeltaModel m).pop (-1/2) (1/6) 2 ∧
      Xi (negativeDeltaModel m) (-1/2) (1/2) 2 2 (1/6) := by
  have hn : (1 : ℝ) < ((12*m : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < 12*m by omega)
  have hden : 0 < ((12*m : ℕ) : ℝ)-1 := by linarith
  have hV : 1 ≤ ((12*m : ℕ) : ℝ) / (((12*m : ℕ) : ℝ)-1) := by
    apply (le_div_iff₀ hden).mpr
    linarith
  have hV0 : 0 ≤ ((12*m : ℕ) : ℝ) / (((12*m : ℕ) : ℝ)-1) := by linarith
  have hroot := Real.one_le_sqrt.mpr hV
  have hsq := Real.sq_sqrt hV0
  have hcov : -(-(1/2) : ℝ) *
      Real.sqrt (((12*m : ℕ) : ℝ) / (((12*m : ℕ) : ℝ)-1)) *
      Real.sqrt (((12*m : ℕ) : ℝ) / (((12*m : ℕ) : ℝ)-1)) ≤
      ((12*m : ℕ) : ℝ) / (((12*m : ℕ) : ℝ)-1) := by nlinarith
  have hmono : MonotoneReceipt (negativeDeltaModel m).pop := by
    intro i hi
    rfl
  have hc : (compliers (negativeDeltaModel m).pop).Nonempty := by
    rw [NDS_compliers]
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hb1 : (1/6 : ℝ) * ((12*m : ℕ) : ℝ) ≤
      ((negativeDeltaModel m).pop.n1 : ℝ) := by
    simp only [negativeDeltaModel, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hb0 : ((negativeDeltaModel m).pop.n1 : ℝ) ≤
      (1-(1/6 : ℝ)) * ((12*m : ℕ) : ℝ) := by
    simp only [negativeDeltaModel, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  constructor
  · refine ⟨NDS_valid m hm, hmono, hc, hb1, hb0, ?_, ?_⟩
    · simpa only [NDS_late, NDS_w, groupVar, NDS_groupCov m hm, neg_div] using hcov
    · intro a
      simp only [NDS_late, NDS_v, NDS_w, NDS_fourth m hm, NDS_popVar]
      nlinarith
  · refine ⟨NDS_valid m hm, hmono, hc, hb1, hb0, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [NDS_late, NDS_residual m hm, NDS_popCov, NDS_popVar, neg_div] using hcov
    · intro a
      simp only [NDS_late, NDS_residual m hm, NDS_fourth m hm, NDS_popVar]
      nlinarith
    · intro s
      change (∑ i : Fin (12*m), NDS_x i.val) = 0
      exact NDS_sum_x m
    · intro s
      change mean (fun i : Fin (12*m) => NDS_x i.val ^ 4) ≤ 2
      simp [mean, NDS_x_four, show m ≠ 0 by omega]
    · intro b
      simp only [normSq, dotProduct, Fin.sum_univ_one]
      change (1/2 : ℝ) * b 0 ^ 2 ≤ mean (fun i : Fin (12*m) => (NDS_x i.val * b 0)^2)
      simp only [mean, mul_pow, NDS_x_sq, one_mul, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_div_cancel_left₀ _ (NDS_n_ne m hm)]
      nlinarith [sq_nonneg (b 0)]

/-- Convert the observed-outcome statistic to the potential-response contrast. -/
theorem NDS_tau_as_contrast {n} (P : Population n) (h : ValidDesign P)
    (β : ℝ) (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    tau P β S = fraction P * (1 - fraction P) *
      (groupMean S (w P true β) - groupMean Sᶜ (w P false β)) := by
  have hScard : S.card = P.n1 := (NDS_mem_assignments P S).mp hS
  have hCcard : ((Sᶜ).card : ℝ) = controlSize P := by
    simp only [Finset.card_compl, Fintype.card_fin, hScard]
    rw [Nat.cast_sub (Nat.le_of_lt h.2.2)]
    rfl
  have hm : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h.2.1)
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (show 0 < n by have := h.1; omega))
  have hc : controlSize P ≠ 0 := by
    have hmn : (P.n1 : ℝ) < n := by exact_mod_cast h.2.2
    unfold controlSize
    linarith
  have hpoint (i : Fin n) :
      observedW P β S i * ((if i ∈ S then 1 else 0) - fraction P) =
        (if i ∈ S then (1 - fraction P) * w P true β i else 0) +
          (if i ∈ Sᶜ then -fraction P * w P false β i else 0) := by
    by_cases hi : i ∈ S
    · simp [observedW, observedY, observedD, w, hi]
      <;> ring
    · simp [observedW, observedY, observedD, w, hi]
      <;> ring
  unfold tau rawTau
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
    ← Finset.mul_sum]
  unfold groupMean
  rw [hScard, hCcard]
  unfold fraction controlSize at *
  field_simp [hm, hn, hc]
  <;> ring

/-- Supporting variance identity for P002-T29: Supplement Lemma 2. -/
theorem NDS_neyman_variance {n} (P : Population n) (h : ValidDesign P) (β : ℝ) :
    designVariance P (tau P β) = S2 P β true / (P.n1 : ℝ) +
      S2 P β false / controlSize P - Sdiff2 P β / (n : ℝ) := by
  have hscaled : designVariance P (tau P β) =
      (fraction P * (1 - fraction P)) ^ 2 *
        designVariance P (fun S => groupMean S (w P true β) -
          groupMean Sᶜ (w P false β)) := by
    calc
      _ = designVariance P (fun S =>
          (fraction P * (1 - fraction P)) *
            (groupMean S (w P true β) - groupMean Sᶜ (w P false β)) - 0) := by
        apply NDS_variance_congr
        intro S hS
        simpa only [sub_zero] using NDS_tau_as_contrast P h β S hS
      _ = _ := NDS_variance_affine P h _ _ 0
  have hdiff : popVar (fun i => w P true β i - w P false β i) =
      (∑ i, (v P true β i - v P false β i) ^ 2) / ((n : ℝ) - 1) := by
    unfold popVar
    rw [NDS_mean_sub]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    unfold v
    ring
  rw [hscaled, NDS_contrast_variance P h, hdiff]
  unfold S2 Sdiff2
  ring

private lemma NDS_observed (m : ℕ) (S : Finset (Fin (12*m))) :
    observedW (negativeDeltaModel m).pop 0 S = fun i => NDS_y i.val := by
  funext i
  simp [observedW, observedY, observedD, negativeDeltaModel, NDS_y]

private lemma NDS_oracle (m : ℕ) (hm : 1 ≤ m) :
    oracleTau (negativeDeltaModel m) 0 = fun S =>
      groupMean S (fun i => NDS_y i.val) - groupMean Sᶜ (fun i => NDS_y i.val) := by
  funext S
  simp [oracleTau, adjustedWith, NDS_psi m hm, slopeDot, NDS_observed]

private lemma NDS_variances (m : ℕ) (hm : 1 ≤ m) :
    designVariance (negativeDeltaModel m).pop (tau (negativeDeltaModel m).pop 0) =
        5/(36*(((12*m : ℕ) : ℝ)-1)) ∧
    designVariance (negativeDeltaModel m).pop (oracleTau (negativeDeltaModel m) 0) =
        36/(5*((12*m : ℕ) : ℝ)-5) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hd : 12*(m : ℝ)-1 ≠ 0 := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  constructor
  · rw [NDS_neyman_variance _ (NDS_valid m hm)]
    simp only [S2, Sdiff2, NDS_fraction m hm, NDS_w, NDS_v, NDS_popVar,
      sub_self, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, mul_zero,
      zero_div, sub_zero, NDS_control]
    simp only [negativeDeltaModel, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hm0, hd]
    <;> ring
  · rw [NDS_oracle m hm, NDS_contrast_variance _ (NDS_valid m hm)]
    have hz : popVar (fun i : Fin (12*m) => NDS_y i.val - NDS_y i.val) = 0 := by
      simp [popVar, mean]
    rw [NDS_popVar, hz, NDS_control]
    simp only [negativeDeltaModel, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hm0, hd]
    <;> ring

/-- The repeated-block negative-delta example, with actual design variances. -/
theorem negative_delta_sequence_proof (m : ℕ) (hm : 1 ≤ m) :
    let P := negativeDeltaModel m
    Theta P.pop (-1/2) (1/6) 2 ∧ Xi P (-1/2) (1/2) 2 2 (1/6) ∧
    late P.pop = 0 ∧
    designVariance P.pop (tau P.pop 0) = 5/(36*(((12*m : ℕ) : ℝ)-1)) ∧
    designVariance P.pop (oracleTau P 0) = 36/(5*((12*m : ℕ) : ℝ)-5) ∧
    (1-(-1/2 : ℝ))*(controlSize P.pop/(((12*m : ℕ) : ℝ)*(P.pop.n1 : ℝ))*
        S2 P.pop 0 true +
      (P.pop.n1 : ℝ)/(((12*m : ℕ) : ℝ)*controlSize P.pop)*S2 P.pop 0 false) =
      (13/12)*designVariance P.pop (tau P.pop 0) ∧
    (1-(-1/2 : ℝ))*(controlSize P.pop/(((12*m : ℕ) : ℝ)*(P.pop.n1 : ℝ))*
        popVar (residual P true 0) +
      (P.pop.n1 : ℝ)/(((12*m : ℕ) : ℝ)*controlSize P.pop)*popVar (residual P false 0)) =
      (13/12)*designVariance P.pop (oracleTau P 0) := by
  dsimp only
  obtain ⟨ht, hx⟩ := NDS_admissible m hm
  obtain ⟨hv, ho⟩ := NDS_variances m hm
  refine ⟨ht, hx, NDS_late m, hv, ho, ?_, ?_⟩
  all_goals
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hd : 12*(m : ℝ)-1 ≠ 0 := by
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    simp only [hv, ho, S2, NDS_w, NDS_fraction m hm, NDS_residual m hm,
      NDS_popVar, NDS_control]
    simp only [negativeDeltaModel, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hm0, hd]
    <;> ring

/-! Corrected Lemma 5: transfer from the complier covariance to population squares. -/

private lemma CL5_groupVar_nonneg {n} (S : Finset (Fin n)) (q : Fin n → ℝ) :
    0 ≤ groupVar S q := by
  unfold groupVar groupCov
  split_ifs with hS
  · apply div_nonneg
    · exact Finset.sum_nonneg fun i hi => mul_self_nonneg _
    · have hh : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
      linarith
  · exact le_rfl

private lemma CL5_difference_algebra (c t A B C δ : ℝ)
    (hc : 0 < c) (ht : 0 < t) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : -δ * Real.sqrt A * Real.sqrt B ≤ C) :
    A+B-2*C ≤ (1+max δ 0*c/t)*A + (1+max δ 0*t/c)*B := by
  have h := corrected_variance_algebra c t (Real.sqrt A) (Real.sqrt B) C δ
    hc ht (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hC
  rw [Real.sq_sqrt hA, Real.sq_sqrt hB] at h
  have hg := mul_nonneg (le_of_lt (add_pos hc ht)) (sub_nonneg.mpr h)
  have he : (c+t) *
      (A/t+B/c-(A+B-2*C)/(c+t) -
        (1-max δ 0)*(c/((c+t)*t)*A+t/((c+t)*c)*B)) =
      (1+max δ 0*c/t)*A+(1+max δ 0*t/c)*B-(A+B-2*C) := by
    field_simp [hc.ne', ht.ne', (add_pos hc ht).ne']
    <;> ring
  rw [he] at hg
  exact sub_nonneg.mp hg

private lemma CL5_group_bound {n} (S : Finset (Fin n)) (u v : Fin n → ℝ)
    (μ c t δ : ℝ) (hS : S.Nonempty) (hc : 0 < c) (ht : 0 < t)
    (hmean : groupMean S u = groupMean S v)
    (hcov : -δ * Real.sqrt (groupVar S u) * Real.sqrt (groupVar S v) ≤
      groupCov S u v) :
    (∑ i ∈ S, (u i-v i)^2) ≤
      (1+max δ 0*c/t) * (∑ i ∈ S, (u i-μ)^2) +
      (1+max δ 0*t/c) * (∑ i ∈ S, (v i-μ)^2) := by
  have hd : 0 ≤ max δ 0 := le_max_right _ _
  have hcoef1 : 0 ≤ 1+max δ 0*c/t := by positivity
  have hcoef0 : 0 ≤ 1+max δ 0*t/c := by positivity
  by_cases htwo : 2 ≤ S.card
  · have hden : 0 < (S.card : ℝ)-1 := by
      have hh : (2 : ℝ) ≤ S.card := by exact_mod_cast htwo
      linarith
    have hb := CL5_difference_algebra c t (groupVar S u) (groupVar S v)
      (groupCov S u v) δ hc ht (CL5_groupVar_nonneg S u)
      (CL5_groupVar_nonneg S v) hcov
    have hp1 : ((S.card : ℝ)-1)*groupVar S u ≤ ∑ i ∈ S, (u i-μ)^2 := by
      have H := (le_div_iff₀ hden).mp (group_variance_second_moment S u μ htwo)
      simpa only [mul_comm] using H
    have hp0 : ((S.card : ℝ)-1)*groupVar S v ≤ ∑ i ∈ S, (v i-μ)^2 := by
      have H := (le_div_iff₀ hden).mp (group_variance_second_moment S v μ htwo)
      simpa only [mul_comm] using H
    have hpoint (i : Fin n) : (u i-v i)^2 =
        (u i-groupMean S u)^2+(v i-groupMean S v)^2 -
          2*((u i-groupMean S u)*(v i-groupMean S v)) := by
      rw [hmean]
      ring
    have hid : (∑ i ∈ S, (u i-v i)^2) =
        ((S.card : ℝ)-1)*(groupVar S u+groupVar S v-2*groupCov S u v) := by
      simp_rw [hpoint]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        groupVar, groupCov, if_pos htwo, ← pow_two]
      field_simp [hden.ne']
      <;> ring
    calc
      _ = ((S.card : ℝ)-1)*(groupVar S u+groupVar S v-2*groupCov S u v) := hid
      _ ≤ ((S.card : ℝ)-1)*
          ((1+max δ 0*c/t)*groupVar S u+(1+max δ 0*t/c)*groupVar S v) :=
        mul_le_mul_of_nonneg_left hb hden.le
      _ = (1+max δ 0*c/t)*(((S.card : ℝ)-1)*groupVar S u) +
          (1+max δ 0*t/c)*(((S.card : ℝ)-1)*groupVar S v) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hp1 hcoef1)
        (mul_le_mul_of_nonneg_left hp0 hcoef0)
  · have hcard : S.card = 1 := by have := Finset.card_pos.mpr hS; omega
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hcard
    have huv : u j = v j := by simpa [groupMean] using hmean
    simp only [Finset.sum_singleton, huv, sub_self, zero_pow (by decide : 2 ≠ 0)]
    exact add_nonneg (mul_nonneg hcoef1 (sq_nonneg _))
      (mul_nonneg hcoef0 (sq_nonneg _))

private lemma CL5_group_means {n} (P : Population n) (hm : MonotoneReceipt P)
    (hc : (compliers P).Nonempty) :
    groupMean (compliers P) (w P true (late P)) =
      groupMean (compliers P) (w P false (late P)) := by
  have hs : (∑ i ∈ compliers P, (w P true (late P) i-w P false (late P) i)) =
      ∑ i : Fin n, (w P true (late P) i-w P false (late P) i) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hin
    rw [w_difference_compliers P hm, if_neg hin]
  have hz := sum_w_difference P hm hc (late P)
  rw [← hs] at hz
  simp only [sub_self, mul_zero, Finset.sum_sub_distrib, sub_eq_zero] at hz
  simp only [groupMean, hz]

private lemma CL5_v_difference {n} (P : Population n) (hm : MonotoneReceipt P)
    (hc : (compliers P).Nonempty) (i : Fin n) :
    v P true (late P) i-v P false (late P) i =
      w P true (late P) i-w P false (late P) i := by
  simp only [v, mean_w_equal_at_late P hm hc]
  ring

private lemma CL5_difference_bound {n} (P : Population n) (δ r A : ℝ)
    (hP : Theta P δ r A) :
    (∑ i, (v P true (late P) i-v P false (late P) i)^2) ≤
      (1+max δ 0*controlSize P/(P.n1 : ℝ)) * (∑ i, v P true (late P) i^2) +
      (1+max δ 0*(P.n1 : ℝ)/controlSize P) * (∑ i, v P false (late P) i^2) := by
  rcases hP with ⟨hv, hm, hc, hb1, hb0, hcov, hfour⟩
  have ht : (0 : ℝ) < P.n1 := by exact_mod_cast hv.2.1
  have hct : (P.n1 : ℝ) < n := by exact_mod_cast hv.2.2
  have hcontrol : 0 < controlSize P := by unfold controlSize; linarith
  have hd : 0 ≤ max δ 0 := le_max_right _ _
  have hcoef1 : 0 ≤ 1+max δ 0*controlSize P/(P.n1 : ℝ) := by positivity
  have hcoef0 : 0 ≤ 1+max δ 0*(P.n1 : ℝ)/controlSize P := by positivity
  have hrestrict : (∑ i, (v P true (late P) i-v P false (late P) i)^2) =
      ∑ i ∈ compliers P, (w P true (late P) i-w P false (late P) i)^2 := by
    simp_rw [CL5_v_difference P hm hc]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hin
    rw [w_difference_compliers P hm, if_neg hin]
    norm_num
  have hg := CL5_group_bound (compliers P) (w P true (late P)) (w P false (late P))
    (mean (w P false (late P))) (controlSize P) (P.n1 : ℝ) δ hc hcontrol ht
    (CL5_group_means P hm hc) hcov
  have hsub (a : Bool) : (∑ i ∈ compliers P, v P a (late P) i^2) ≤
      ∑ i, v P a (late P) i^2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro i hi hin
    exact sq_nonneg _
  calc
    _ = ∑ i ∈ compliers P, (w P true (late P) i-w P false (late P) i)^2 := hrestrict
    _ ≤ (1+max δ 0*controlSize P/(P.n1 : ℝ)) *
          (∑ i ∈ compliers P, (w P true (late P) i-mean (w P false (late P)))^2) +
        (1+max δ 0*(P.n1 : ℝ)/controlSize P) *
          (∑ i ∈ compliers P, (w P false (late P) i-mean (w P false (late P)))^2) := hg
    _ = (1+max δ 0*controlSize P/(P.n1 : ℝ)) *
          (∑ i ∈ compliers P, v P true (late P) i^2) +
        (1+max δ 0*(P.n1 : ℝ)/controlSize P) *
          (∑ i ∈ compliers P, v P false (late P) i^2) := by
      simp only [v, mean_w_equal_at_late P hm hc]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hsub true) hcoef1)
      (mul_le_mul_of_nonneg_left (hsub false) hcoef0)

private lemma CL5_scaled_bound {n} (P : Population n) (δ r A : ℝ)
    (hP : Theta P δ r A) :
    Sdiff2 P (late P) ≤
      (1+max δ 0*controlSize P/(P.n1 : ℝ))*S2 P (late P) true +
      (1+max δ 0*(P.n1 : ℝ)/controlSize P)*S2 P (late P) false := by
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast hP.1.1
  have hbound := CL5_difference_bound P δ r A hP
  have hdiv := div_le_div_of_nonneg_right hbound (show 0 ≤ (n : ℝ)-1 by linarith)
  have hmul := mul_le_mul_of_nonneg_left hdiv
    (mul_nonneg (sq_nonneg (fraction P)) (sq_nonneg (1-fraction P)))
  convert hmul using 1 <;> simp only [Sdiff2, S2, popVar, v] <;> ring

/-- Corrected Lemma 5 with its original complier covariance hypothesis. -/
theorem corrected_lemma5_proof {n} (P : Population n) (δ r A : ℝ)
    (hδ : δ < 1) (hr : 0 < r ∧ r ≤ 1/2) (hA : 0 < A) (hP : Theta P δ r A) :
    (1-max δ 0) * (controlSize P/((n : ℝ)*(P.n1 : ℝ))*S2 P (late P) true +
      (P.n1 : ℝ)/((n : ℝ)*controlSize P)*S2 P (late P) false) ≤
      designVariance P (tau P (late P)) := by
  have ht : (0 : ℝ) < P.n1 := by exact_mod_cast hP.1.2.1
  have hnt : (P.n1 : ℝ) < n := by exact_mod_cast hP.1.2.2
  have hn : (0 : ℝ) < n := lt_trans ht hnt
  have hc : 0 < controlSize P := by unfold controlSize; linarith
  have hbound := div_le_div_of_nonneg_right (CL5_scaled_bound P δ r A hP) hn.le
  rw [NDS_neyman_variance P hP.1 (late P)]
  calc
    _ = S2 P (late P) true/(P.n1 : ℝ)+S2 P (late P) false/controlSize P -
        ((1+max δ 0*controlSize P/(P.n1 : ℝ))*S2 P (late P) true +
          (1+max δ 0*(P.n1 : ℝ)/controlSize P)*S2 P (late P) false)/(n : ℝ) := by
      unfold controlSize at *
      field_simp [hn.ne', ht.ne', hc.ne']
      <;> ring
    _ ≤ _ := sub_le_sub_left hbound _

end
end AronowAudit.P002.Wave1
