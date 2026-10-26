import AronowAudit.P002.P002_Audit
import AronowAudit.External.Causalean.Experimentation.FinitePopulationMoments
import Mathlib.Algebra.BigOperators.Fin

/-!
P002-T14 and P002-T2: the balanced-sign counterexample and corrected (E.10).
The finite-sampling results use the Causalean development.
-/
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

open Causalean.Experimentation.DesignBased

/-! ## The balanced-sign counterexample -/

private theorem missing_square_expectation_congr {n} (P : Population n)
    {f g : Finset (Fin n) → ℝ}
    (hfg : ∀ S ∈ assignments P, f S = g S) : expectation P f = expectation P g := by
  unfold expectation
  congr 1
  exact Finset.sum_congr rfl hfg

private theorem missing_square_variance_congr {n} (P : Population n)
    {f g : Finset (Fin n) → ℝ}
    (hfg : ∀ S ∈ assignments P, f S = g S) :
    designVariance P f = designVariance P g := by
  have hm := missing_square_expectation_congr P hfg
  unfold designVariance
  rw [hm]
  apply missing_square_expectation_congr P
  intro S hS
  rw [hfg S hS]

private theorem missing_square_expectation_add {n} (P : Population n)
    (f g : Finset (Fin n) → ℝ) :
    expectation P (fun S => f S + g S) = expectation P f + expectation P g := by
  simp only [expectation, Finset.sum_add_distrib, add_div]

private theorem missing_square_variance_affine {n} (P : Population n)
    (hP : ValidDesign P) (f g : Finset (Fin n) → ℝ) (a b : ℝ)
    (hfg : ∀ S ∈ assignments P, f S = a * g S + b) :
    designVariance P f = a ^ 2 * designVariance P g := by
  have hm : expectation P f = a * expectation P g + b := by
    rw [missing_square_expectation_congr P hfg,
      missing_square_expectation_add, expectation_mul, expectation_const P hP]
  unfold designVariance
  rw [hm, ← expectation_mul P (a ^ 2)]
  apply missing_square_expectation_congr P
  intro S hS
  rw [hfg S hS]
  ring

/-- Reindex the actual assignment finset by the fixed-cardinality subtype.
The bijection also identifies the two normalizing cardinalities. -/
private theorem missing_square_design_bridge {n} (P : Population n)
    (hP : ValidDesign P) (f : Finset (Fin n) → ℝ) :
    expectation P f =
      (completeRandomization P.n1 (by simpa using Nat.le_of_lt hP.2.2)).E
        (fun S => f S.val) := by
  have hsum (g : Finset (Fin n) → ℝ) :
      (∑ S ∈ assignments P, g S) =
        ∑ S : {S : Finset (Fin n) // S.card = P.n1}, g S.val := by
    refine Finset.sum_bij
      (fun S hS => (⟨S, (Finset.mem_powersetCard.mp hS).2⟩ :
        {S : Finset (Fin n) // S.card = P.n1})) ?_ ?_ ?_ ?_
    · intro S hS
      exact Finset.mem_univ _
    · intro S hS T hT heq
      exact congrArg Subtype.val heq
    · intro S hS
      have hmem : S.val ∈ assignments P := by
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, S.property⟩
      exact ⟨S.val, hmem, Subtype.ext rfl⟩
    · intro S hS
      rfl
  have hcard : ((assignments P).card : ℝ) =
      (Fintype.card {S : Finset (Fin n) // S.card = P.n1} : ℝ) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ] using
      hsum (fun _ => 1)
  rw [expectation, hsum, hcard]
  simp only [FiniteDesign.E, completeRandomization, ← Finset.mul_sum]
  ring

private theorem missing_square_sample_moments {n} (P : Population n)
    (hP : ValidDesign P) (q : Fin n → ℝ) :
    expectation P (fun S => groupMean S q) = mean q ∧
    designVariance P (fun S => groupMean S q) =
      (1 / (P.n1 : ℝ) - 1 / (n : ℝ)) * popVar q := by
  let D := completeRandomization P.n1
    (show P.n1 ≤ Fintype.card (Fin n) by simpa using Nat.le_of_lt hP.2.2)
  let sm := Causalean.Experimentation.FinitePopulationMoments.sampleMean P.n1 q
  have hsm (S : {S : Finset (Fin n) // S.card = P.n1}) :
      groupMean S.val q = sm S := by
    dsimp [groupMean, sm,
      Causalean.Experimentation.FinitePopulationMoments.sampleMean]
    rw [S.property]
    congr 1
    exact (Finset.sum_ite_mem_eq S.val q).symm
  have hmean : expectation P (fun S => groupMean S q) = mean q := by
    rw [missing_square_design_bridge P hP]
    simp_rw [hsm]
    simpa only [Causalean.Experimentation.FinitePopulationMoments.popMean,
      Fintype.card_fin, mean] using
      Causalean.Experimentation.FinitePopulationMoments.E_sampleMean
        P.n1 (show P.n1 ≤ Fintype.card (Fin n) by simpa using Nat.le_of_lt hP.2.2)
        hP.2.1 q
  refine ⟨hmean, ?_⟩
  have hv : designVariance P (fun S => groupMean S q) = D.Var sm := by
    unfold designVariance FiniteDesign.Var
    rw [missing_square_design_bridge P hP]
    have hE : D.E sm = expectation P (fun S => groupMean S q) := by
      rw [missing_square_design_bridge P hP]
      exact D.E_congr (fun S => (hsm S).symm)
    rw [hE]
    exact D.E_congr (fun S => by simpa only [hsm])
  rw [hv]
  simpa only [Causalean.Experimentation.FinitePopulationMoments.popVar,
    Causalean.Experimentation.FinitePopulationMoments.popMean,
    Fintype.card_fin, popVar, mean, D, sm] using
    Causalean.Experimentation.FinitePopulationMoments.Var_sampleMean P.n1
      (show P.n1 ≤ Fintype.card (Fin n) by simpa using Nat.le_of_lt hP.2.2)
      hP.2.1 (by simpa using hP.1) q

private theorem missing_square_probability_one {n} (P : Population n)
    (hP : ValidDesign P) (E : Finset (Fin n) → Prop)
    (hE : ∀ S ∈ assignments P, E S) : probability P E = 1 := by
  have hcard : ((assignments P).card : ℝ) ≠ 0 := by
    have hne : (assignments P).Nonempty := by
      apply Finset.powersetCard_nonempty.mpr
      simpa using Nat.le_of_lt hP.2.2
    exact_mod_cast Finset.card_ne_zero.mpr hne
  have hf : (assignments P).filter E = assignments P := by
    ext S
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.1, fun h => ⟨h, hE S h⟩⟩
  simp only [probability, hf, div_self hcard]

private theorem missing_square_markov {n} (P : Population n)
    (X : Finset (Fin n) → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hX : ∀ S ∈ assignments P, 0 ≤ X S) :
    probability P (fun S => κ ≤ X S) ≤ expectation P X / κ := by
  have hind : expectation P (fun S => if κ ≤ X S then (1 : ℝ) else 0) =
      probability P (fun S => κ ≤ X S) := by
    simp [expectation, probability, Finset.sum_ite]
  have hle : expectation P (fun S => κ * (if κ ≤ X S then (1 : ℝ) else 0)) ≤
      expectation P X := by
    unfold expectation
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro S hS
    by_cases he : κ ≤ X S
    · simpa only [if_pos he, mul_one] using he
    · simpa only [if_neg he, mul_zero] using hX S hS
  rw [expectation_mul, hind] at hle
  exact (le_div_iff₀ hκ).mpr (by simpa only [mul_comm] using hle)

private def missing_square_y (m : ℕ) : Fin (2*m) → ℝ :=
  fun i => (signModel m).y i false

private theorem missing_square_y_sq (m : ℕ) (i : Fin (2*m)) :
    missing_square_y m i ^ 2 = 1 := by
  dsimp [missing_square_y, signModel]
  split_ifs <;> norm_num

private theorem missing_square_y_sum (m : ℕ) : ∑ i, missing_square_y m i = 0 := by
  have h : (∑ i : Fin (m+m), if i.val < m then (-1 : ℝ) else 1) = 0 := by
    rw [Fin.sum_univ_add]
    have hl (i : Fin m) : (Fin.castAdd m i).val < m := i.isLt
    have hr (i : Fin m) : ¬ (Fin.natAdd m i).val < m := by
      change ¬ m + i.val < m
      omega
    simp only [hl, hr, if_true, if_false, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  let f (N : ℕ) : ℝ := ∑ i : Fin N, if i.val < m then -1 else 1
  change f (2*m) = 0
  rw [two_mul]
  exact h

private theorem missing_square_design (m : ℕ) (hm : 2 ≤ m) :
    ValidDesign (signModel m) := by
  dsimp [ValidDesign, signModel]
  omega

private theorem missing_square_population (m : ℕ) (hm : 2 ≤ m) :
    Theta (signModel m) 0 (1/2) 1 ∧ late (signModel m) = 0 := by
  have hN : (0 : ℝ) < (2*m : ℕ) := by exact_mod_cast (show 0 < 2*m by omega)
  have hN1 : 0 < ((2*m : ℕ) : ℝ) - 1 := by
    have : (4 : ℝ) ≤ (2*m : ℕ) := by exact_mod_cast (show 4 ≤ 2*m by omega)
    linarith
  have hC : compliers (signModel m) = Finset.univ := by
    ext i
    simp [compliers, signModel]
  have hlate : late (signModel m) = 0 := by
    simp [late, signModel, groupMean]
  have hw (a : Bool) : w (signModel m) a (late (signModel m)) = missing_square_y m := by
    funext i
    rw [hlate]
    simp [w, signModel, missing_square_y]
  have hmean : mean (missing_square_y m) = 0 := by
    rw [mean, missing_square_y_sum, zero_div]
  have hv (a : Bool) : v (signModel m) a (late (signModel m)) = missing_square_y m := by
    funext i
    change w (signModel m) a (late (signModel m)) i - mean (w (signModel m) a (late (signModel m))) = _
    rw [hw, hmean, sub_zero]
  have hvar : popVar (missing_square_y m) = ((2*m : ℕ) : ℝ) / (((2*m : ℕ) : ℝ)-1) := by
    simp only [popVar, hmean, sub_zero, missing_square_y_sq, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hgvar : groupVar Finset.univ (missing_square_y m) = popVar (missing_square_y m) := by
    simp only [groupVar, groupCov, Finset.card_univ, Fintype.card_fin,
      if_pos (show 2 ≤ 2*m by omega), groupMean, mean, popVar, ← pow_two]
  have hgcov : groupCov Finset.univ (missing_square_y m) (missing_square_y m) =
      popVar (missing_square_y m) := hgvar
  have hfourth : fourthNorm (missing_square_y m) = 1 := by
    have h4 (i : Fin (2*m)) : missing_square_y m i ^ 4 = 1 := by
      rw [show missing_square_y m i ^ 4 = (missing_square_y m i ^ 2)^2 by ring,
        missing_square_y_sq]
      norm_num
    simp only [fourthNorm, mean, h4, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, div_self (ne_of_gt hN), Real.sqrt_one]
  have hvar1 : 1 ≤ popVar (missing_square_y m) := by
    rw [hvar]
    apply (le_div_iff₀ hN1).mpr
    linarith
  have hsqrt : 1 ≤ Real.sqrt (popVar (missing_square_y m)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hvar1
  refine ⟨?_, hlate⟩
  refine ⟨missing_square_design m hm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rfl
  · rw [hC]
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  · dsimp [signModel]
    push_cast
    linarith
  · dsimp [signModel]
    push_cast
    linarith
  · rw [hC, hw true, hw false, hgcov]
    simpa only [neg_zero, zero_mul] using le_trans (by norm_num : (0 : ℝ) ≤ 1) hvar1
  · intro a
    rw [hv, hw, hfourth, one_mul]
    exact hsqrt

private theorem missing_square_observed (m : ℕ) (S : Finset (Fin (2*m))) :
    observedW (signModel m) 0 S = missing_square_y m := by
  funext i
  simp [observedW, observedY, observedD, signModel, missing_square_y]

private theorem missing_square_mean_zero (m : ℕ) : mean (missing_square_y m) = 0 := by
  rw [mean, missing_square_y_sum, zero_div]

private theorem missing_square_variance (m : ℕ) (hm : 2 ≤ m) :
    designVariance (signModel m) (rawTau (signModel m) (missing_square_y m)) =
      1/(4*(((2*m : ℕ) : ℝ)-1)) := by
  have hP := missing_square_design m hm
  have hM : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hN1 : 2*(m : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hf (S) (hS : S ∈ assignments (signModel m)) :
      rawTau (signModel m) (missing_square_y m) S =
        (1/2 : ℝ) * groupMean S (missing_square_y m) + 0 := by
    have hc : S.card = m := (Finset.mem_powersetCard.mp hS).2
    rw [rawTau_sum, missing_square_y_sum]
    simp only [mul_zero, sub_zero, groupMean, hc]
    push_cast
    field_simp [hM]
    <;> ring
  rw [missing_square_variance_affine _ hP _ _ (1/2) 0 hf,
    (missing_square_sample_moments _ hP _).2]
  simp only [popVar, missing_square_mean_zero, sub_zero, missing_square_y_sq,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    signModel]
  push_cast
  field_simp [hM, hN1]
  <;> ring

private theorem missing_square_sample_second (m : ℕ) (hm : 2 ≤ m) :
    expectation (signModel m) (fun T => (groupMean T (missing_square_y m))^2) =
      1/(((2*m : ℕ) : ℝ)-1) := by
  have hP := missing_square_design m hm
  have hM : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hN1 : 2*(m : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have H := (missing_square_sample_moments (signModel m) hP (missing_square_y m)).2
  rw [designVariance, (missing_square_sample_moments _ hP _).1,
    missing_square_mean_zero] at H
  simp only [sub_zero] at H
  rw [H]
  simp only [popVar, missing_square_mean_zero, sub_zero, missing_square_y_sq,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    signModel]
  push_cast
  field_simp [hM, hN1]
  <;> ring

/-- All assignment-wise algebra is kept separate from the sampling moment.
Here K counts negative signs; using positive signs gives the same squared mean. -/
private theorem missing_square_assignment_formulas (m : ℕ) (hm : 2 ≤ m)
    (T : Finset (Fin (2*m))) (hT : T ∈ assignments (signModel m)) :
    let K := (T.filter (fun i => i.val < m)).card
    let a := groupMean T (missing_square_y m)
    K ≤ m ∧ a = ((m : ℝ)-2*(K : ℝ))/(m : ℝ) ∧ a^2 ≤ 1 ∧
      rawSigma2 (signModel m) (missing_square_y m) T = (1-a^2)/(8*(m : ℝ)) := by
  dsimp only
  let y := missing_square_y m
  let K := (T.filter (fun i => i.val < m)).card
  let a := groupMean T y
  have hM : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hcard : T.card = m := (Finset.mem_powersetCard.mp hT).2
  have hcomp : (Tᶜ).card = m := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
    omega
  have hne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hcne : (Tᶜ).Nonempty := Finset.card_pos.mp (by omega)
  have hK : K ≤ m := by
    dsimp [K]
    exact (Finset.card_filter_le _ _).trans hcard.le
  have hcount : (K : ℝ) + ((T.filter (fun i => ¬ i.val < m)).card : ℝ) = (m : ℝ) := by
    have H := T.card_filter_add_card_filter_not (fun i => i.val < m)
    rw [hcard] at H
    exact_mod_cast H
  have hsum : (∑ i ∈ T, y i) = (m : ℝ)-2*(K : ℝ) := by
    dsimp [y, missing_square_y, signModel]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul]
    change (K : ℝ) * (-1) + ((T.filter (fun i => ¬ i.val < m)).card : ℝ) * 1 = _
    linarith
  have ha : a = ((m : ℝ)-2*(K : ℝ))/(m : ℝ) := by
    dsimp [a, groupMean]
    rw [hcard, hsum]
  have habs : a^2 ≤ 1 := by
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hKM : (K : ℝ) ≤ m := by exact_mod_cast hK
    have hlo : -1 ≤ a := by
      rw [ha]
      apply (le_div_iff₀ hM).mpr
      linarith
    have hhi : a ≤ 1 := by
      rw [ha]
      apply (div_le_iff₀ hM).mpr
      linarith
    have H := mul_nonneg (show 0 ≤ a+1 by linarith)
      (show 0 ≤ 1-a by linarith)
    nlinarith only [H]
  have hcsum : (∑ i ∈ Tᶜ, y i) = -(∑ i ∈ T, y i) := by
    have H := Finset.sum_add_sum_compl T y
    rw [missing_square_y_sum] at H
    linarith
  have hcm : groupMean Tᶜ y = -a := by
    dsimp [groupMean, a]
    rw [hcomp, hcard, hcsum]
    ring
  have hsqmean (U : Finset (Fin (2*m))) (hU : U.card = m) :
      groupMean U (fun i => y i ^ 2) = 1 := by
    simp only [groupMean, missing_square_y_sq, y, Finset.sum_const, nsmul_eq_mul,
      hU, mul_one, div_self (ne_of_gt hM)]
  have hss : (∑ i ∈ T, (y i-a)^2) = (m : ℝ)*(1-a^2) := by
    have H := square_centering T y 0 hne
    simp only [sub_zero] at H
    rw [hsqmean T hcard] at H
    change (∑ i ∈ T, (y i-a)^2)/(T.card : ℝ) = 1-a^2 at H
    rw [hcard] at H
    exact (div_eq_iff (ne_of_gt hM)).mp H |>.trans (by ring)
  have hcss : (∑ i ∈ Tᶜ, (y i-(-a))^2) = (m : ℝ)*(1-a^2) := by
    have H := square_centering Tᶜ y 0 hcne
    simp only [sub_zero] at H
    rw [hsqmean Tᶜ hcomp, hcm] at H
    change (∑ i ∈ Tᶜ, (y i-(-a))^2)/((Tᶜ).card : ℝ) = 1-(-a)^2 at H
    rw [hcomp] at H
    have H' := (div_eq_iff (ne_of_gt hM)).mp H
    nlinarith only [H']
  refine ⟨hK, ha, habs, ?_⟩
  change rawSigma2 (signModel m) y T = _
  simp only [rawSigma2, armMean, if_true, Bool.false_eq_true, if_false, hcm]
  change (fraction (signModel m))^2 * (1-fraction (signModel m))^2 *
    ((∑ i ∈ T, (y i-a)^2)/(m : ℝ)^2 +
      (∑ i ∈ Tᶜ, (y i-(-a))^2)/(controlSize (signModel m))^2) = _
  rw [hss, hcss]
  simp only [fraction, controlSize, signModel, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [ne_of_gt hM]
  <;> ring

/-- The printed square-root/variance ratio has support in {0} union [3,infinity).
The count argument works at the boundary m=2 as well. -/
private theorem missing_square_ratio_support (m : ℕ) (hm : 2 ≤ m)
    (T : Finset (Fin (2*m))) (hT : T ∈ assignments (signModel m)) :
    |Real.sqrt (rawSigma2 (signModel m) (missing_square_y m) T) /
      (1/(4*(((2*m : ℕ) : ℝ)-1)))-1| ≥ 1/2 := by
  let M : ℝ := m
  let K : ℕ := (T.filter (fun i => i.val < m)).card
  let a := groupMean T (missing_square_y m)
  let V : ℝ := 1/(4*(2*M-1))
  let s := rawSigma2 (signModel m) (missing_square_y m) T
  have hM : 2 ≤ M := by dsimp [M]; exact_mod_cast hm
  have hMp : 0 < M := by linarith
  have hD : 0 < 2*M-1 := by linarith
  have hV : 0 < V := by dsimp [V]; positivity
  obtain ⟨hK, ha, ha2, hs⟩ := missing_square_assignment_formulas m hm T hT
  change K ≤ m at hK
  change a = (M-2*(K : ℝ))/M at ha
  change s = (1-a^2)/(8*M) at hs
  have hs0 : 0 ≤ s := by
    rw [hs]
    exact div_nonneg (sub_nonneg.mpr ha2) (by positivity)
  have htarget : |Real.sqrt s / V - 1| ≥ 1/2 := by
    by_cases he : K = 0 ∨ K = m
    · have haext : a^2 = 1 := by
        rcases he with he | he
        · rw [ha, he]
          simp [ne_of_gt hMp]
        · have hKM : (K : ℝ) = M := by dsimp [M]; rw [he]
          rw [ha, hKM]
          field_simp [ne_of_gt hMp]
          <;> ring
      have hz : s = 0 := by rw [hs, haext]; ring
      norm_num [hz]
    · have hKn : 1 ≤ K ∧ K+1 ≤ m := by omega
      have hKlo : (1 : ℝ) ≤ K := by exact_mod_cast hKn.1
      have hKhi : (K : ℝ)+1 ≤ M := by dsimp [M]; exact_mod_cast hKn.2
      have hcount : M-1 ≤ (K : ℝ)*(M-(K : ℝ)) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hKlo)
          (show 0 ≤ M-(K : ℝ)-1 by linarith)]
      have hDsq : (9/4 : ℝ)*M^2 ≤ (2*M-1)^2 := by
        have H := mul_nonneg (show 0 ≤ 2*M-1-(3/2)*M by linarith)
          (show 0 ≤ 2*M-1+(3/2)*M by linarith)
        nlinarith only [H]
      have hpoly1 : (9/8 : ℝ)*M^3 ≤ (2*M-1)^2*(M-1) := by
        calc
          (9/8 : ℝ)*M^3 = ((9/4 : ℝ)*M^2)*(M/2) := by ring
          _ ≤ (2*M-1)^2*(M-1) :=
            mul_le_mul hDsq (by linarith) (by positivity) (sq_nonneg _)
      have hpoly2 : (2*M-1)^2*(M-1) ≤ (2*M-1)^2*((K : ℝ)*(M-(K : ℝ))) :=
        mul_le_mul_of_nonneg_left hcount (sq_nonneg _)
      have hpoly : 9*M^3 ≤ 8*(2*M-1)^2*((K : ℝ)*(M-(K : ℝ))) := by
        linarith
      have hsK : s = ((K : ℝ)*(M-(K : ℝ)))/(2*M^3) := by
        rw [hs, ha]
        field_simp [ne_of_gt hMp]
        <;> ring
      have hsquared : (3*V)^2 ≤ s := by
        calc
          (3*V)^2 = 9/(16*(2*M-1)^2) := by
            dsimp [V]
            field_simp [ne_of_gt hD]
            <;> ring
          _ ≤ ((K : ℝ)*(M-(K : ℝ)))/(2*M^3) := by
            apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
            nlinarith only [hpoly]
          _ = s := hsK.symm
      have hsqrt : 3*V ≤ Real.sqrt s := by
        have H := Real.sqrt_le_sqrt hsquared
        simpa only [Real.sqrt_sq (show 0 ≤ 3*V by positivity)] using H
      have hratio : 3 ≤ Real.sqrt s / V := (le_div_iff₀ hV).mpr hsqrt
      rw [abs_of_nonneg (by linarith : 0 ≤ Real.sqrt s / V - 1)]
      linarith
  simpa only [s, V, M, Nat.cast_mul, Nat.cast_ofNat] using htarget

private theorem missing_square_ratio_mean_error (m : ℕ) (hm : 2 ≤ m) :
    expectation (signModel m) (fun T =>
      |rawSigma2 (signModel m) (missing_square_y m) T /
        (1/(4*(((2*m : ℕ) : ℝ)-1)))-1|) = 2/((2*m : ℕ) : ℝ) := by
  let N : ℝ := (2*m : ℕ)
  let a := fun T => groupMean T (missing_square_y m)
  have hM : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hN : 0 < N := by dsimp [N]; positivity
  have hD : 0 < N-1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    dsimp [N]
    push_cast
    linarith
  have hf (T) (hT : T ∈ assignments (signModel m)) :
      |rawSigma2 (signModel m) (missing_square_y m) T /(1/(4*(N-1)))-1| =
        1/N + ((N-1)/N) * (a T)^2 := by
    obtain ⟨_, _, ha2, hs⟩ := missing_square_assignment_formulas m hm T hT
    have hDm : 2*(m : ℝ)-1 ≠ 0 := by
      have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have hR : rawSigma2 (signModel m) (missing_square_y m) T /(1/(4*(N-1))) =
        (N-1)*(1-(a T)^2)/N := by
      rw [hs]
      dsimp [N, a]
      push_cast
      field_simp [ne_of_gt hM, hDm]
      <;> ring
    rw [hR]
    have hle : (N-1)*(1-(a T)^2)/N ≤ 1 := by
      apply (div_le_iff₀ hN).mpr
      have H := mul_nonneg (le_of_lt hD) (sq_nonneg (a T))
      nlinarith only [H]
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    field_simp [ne_of_gt hN]
    <;> ring
  change expectation (signModel m) (fun T =>
    |rawSigma2 (signModel m) (missing_square_y m) T /(1/(4*(N-1)))-1|) = 2/N
  rw [missing_square_expectation_congr _ hf, missing_square_expectation_add,
    expectation_const _ (missing_square_design m hm), expectation_mul,
    missing_square_sample_second m hm]
  change 1/N + (N-1)/N * (1/(N-1)) = 2/N
  field_simp [ne_of_gt hN, ne_of_gt hD]
  <;> ring

private theorem missing_square_probabilities (m : ℕ) (hm : 2 ≤ m) :
    probability (signModel m) (fun T =>
      |Real.sqrt (rawSigma2 (signModel m) (missing_square_y m) T) /
        designVariance (signModel m) (rawTau (signModel m) (missing_square_y m))-1| ≥ 1/2) = 1 ∧
    (∀ κ : ℝ, 0 < κ → probability (signModel m) (fun T =>
      |rawSigma2 (signModel m) (missing_square_y m) T /
        designVariance (signModel m) (rawTau (signModel m) (missing_square_y m))-1| ≥ κ) ≤
        2/(((2*m : ℕ) : ℝ)*κ)) := by
  rw [missing_square_variance m hm]
  constructor
  · apply missing_square_probability_one _ (missing_square_design m hm)
    exact missing_square_ratio_support m hm
  · intro κ hκ
    have H := missing_square_markov (signModel m)
      (fun T => |rawSigma2 (signModel m) (missing_square_y m) T /
        (1/(4*(((2*m : ℕ) : ℝ)-1)))-1|) κ hκ (fun _ _ => abs_nonneg _)
    rw [missing_square_ratio_mean_error m hm] at H
    simpa only [div_div] using H

/-- Statement of P002-T14. -/
theorem missing_square_counterexample_proof :
    (∀ m, 2 ≤ m →
      let P := signModel m
      Theta P 0 (1/2) 1 ∧ late P = 0 ∧
      (∀ S ∈ assignments P,
        let q := observedW P 0 S
        designVariance P (rawTau P q) = 1/(4*(((2*m : ℕ) : ℝ)-1)) ∧
        probability P (fun T => |Real.sqrt (rawSigma2 P q T) /
          designVariance P (rawTau P q)-1| ≥ 1/2) = 1 ∧
        (∀ κ : ℝ, 0 < κ → probability P (fun T => |rawSigma2 P q T /
          designVariance P (rawTau P q)-1| ≥ κ) ≤ 2/(((2*m : ℕ) : ℝ)*κ)))) ∧
    Tendsto (fun j =>
      let P := signModel (j+2)
      probability P (fun T => |Real.sqrt (rawSigma2 P (fun i => P.y i false) T) /
        designVariance P (rawTau P (fun i => P.y i false))-1| ≥ 1/2)) atTop (nhds 1) := by
  constructor
  · intro m hm
    dsimp only
    obtain ⟨hTheta, hlate⟩ := missing_square_population m hm
    refine ⟨hTheta, hlate, ?_⟩
    intro S hS
    rw [missing_square_observed]
    exact ⟨missing_square_variance m hm, missing_square_probabilities m hm⟩
  · have hf (j : ℕ) :
        (let P := signModel (j+2)
        probability P (fun T => |Real.sqrt (rawSigma2 P (fun i => P.y i false) T) /
          designVariance P (rawTau P (fun i => P.y i false))-1| ≥ 1/2)) = 1 := by
      exact (missing_square_probabilities (j+2) (by omega)).1
    simp_rw [hf]
    exact tendsto_const_nhds

/-! ## Corrected (E.10) -/

private theorem corrected_E10_mean_add_mul {n} (u v : Fin n → ℝ) (a : ℝ) :
    mean (fun i => u i + a*v i) = mean u + a*mean v := by
  simp only [mean, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private theorem corrected_E10_popVar_add_mul {n} (u v : Fin n → ℝ) (a : ℝ) :
    popVar (fun i => u i + a*v i) =
      popVar u + a^2*popVar v + 2*a*popCov u v := by
  have hp (i : Fin n) :
      (u i+a*v i-(mean u+a*mean v))^2 =
        (u i-mean u)^2 + a^2*(v i-mean v)^2 +
          (2*a)*((u i-mean u)*(v i-mean v)) := by ring
  unfold popVar
  rw [corrected_E10_mean_add_mul]
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, popCov]
  ring

private theorem corrected_E10_popVar_sub {n} (u v : Fin n → ℝ) :
    popVar (fun i => u i-v i) = popVar u + popVar v - 2*popCov u v := by
  have hf : (fun i => u i-v i) = (fun i => u i+(-1 : ℝ)*v i) := by
    funext i
    ring
  rw [hf, corrected_E10_popVar_add_mul]
  ring

/-- The actual finite two-arm variance.  Expressing the contrast as a treated
sample mean plus a constant reduces it to the sample moment.
This also covers either population variance being zero. -/
private theorem corrected_E10_two_arm_variance {n} (P : Population n)
    (hP : ValidDesign P) (u v : Fin n → ℝ) :
    designVariance P (fun S => groupMean S u-groupMean Sᶜ v) =
      popVar u/(P.n1 : ℝ) + popVar v/controlSize P -
        popVar (fun i => u i-v i)/(n : ℝ) := by
  let t : ℝ := P.n1
  let c : ℝ := controlSize P
  let q : Fin n → ℝ := fun i => u i + (t/c)*v i
  let b : ℝ := -(∑ i, v i)/c
  have ht : 0 < t := by dsimp [t]; exact_mod_cast hP.2.1
  have hc : 0 < c := by
    dsimp [c, controlSize]
    exact sub_pos.mpr (by exact_mod_cast hP.2.2)
  have hN : (n : ℝ) = c+t := by dsimp [c, t, controlSize]; ring
  have hf (S : Finset (Fin n)) (hS : S ∈ assignments P) :
      groupMean S u-groupMean Sᶜ v = 1*groupMean S q+b := by
    have hcard : (S.card : ℝ) = t := by
      change (S.card : ℝ) = (P.n1 : ℝ)
      exact_mod_cast (Finset.mem_powersetCard.mp hS).2
    have hcomp : ((Sᶜ).card : ℝ) = c := by
      have hnat : S.card = P.n1 := (Finset.mem_powersetCard.mp hS).2
      simp only [Finset.card_compl, Fintype.card_fin, hnat,
        Nat.cast_sub (Nat.le_of_lt hP.2.2), c, controlSize]
    have hcsum : (∑ i ∈ Sᶜ, v i) = (∑ i, v i)-(∑ i ∈ S, v i) := by
      have H := Finset.sum_add_sum_compl S v
      linarith
    simp only [groupMean, hcard, hcomp, hcsum, q,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    dsimp [b]
    field_simp [ne_of_gt ht, ne_of_gt hc]
    <;> ring
  have hv := missing_square_variance_affine P hP
    (fun S => groupMean S u-groupMean Sᶜ v) (fun S => groupMean S q) 1 b hf
  simp only [one_pow, one_mul] at hv
  rw [hv, (missing_square_sample_moments P hP q).2]
  change (1/t-1/(n : ℝ))*popVar q =
    popVar u/t + popVar v/c - popVar (fun i => u i-v i)/(n : ℝ)
  have hq : popVar q = popVar u + (t/c)^2*popVar v + 2*(t/c)*popCov u v :=
    corrected_E10_popVar_add_mul u v (t/c)
  rw [hq, corrected_E10_popVar_sub, hN]
  have hct : c+t ≠ 0 := ne_of_gt (add_pos hc ht)
  field_simp [ne_of_gt ht, ne_of_gt hc, hct]
  <;> ring

/-- Positive augmented-Gram coercivity gives a trivial kernel, hence a nonzero
finite-dimensional determinant. -/
private theorem corrected_E10_population_full_rank {n k}
    (P : CovPopulation n k) (hn : 0 < n) (e : ℝ) (he : 0 < e)
    (hx : ∀ s, ∑ i, P.x i s = 0)
    (hRayleigh : ∀ b : Fin k → ℝ,
      e*normSq b ≤ mean (fun i => (dotProduct (P.x i) b)^2)) :
    (gram P.x Finset.univ).det ≠ 0 := by
  let G := gram P.x Finset.univ
  have hco := (corrected_augmented_gram P.x hn e hx hRayleigh).2.2.2
  have hminpos : 0 < min (1 : ℝ) e := lt_min (by norm_num) he
  have hker (b : Option (Fin k) → ℝ) (hb : G *ᵥ b = 0) : b = 0 := by
    have H := hco b
    have hq : mean (fun i => (dotProduct (augmented P.x i) b)^2) =
        dotProduct b (G *ᵥ b) := by
      simpa only [G, groupMean, mean, Finset.card_univ, Fintype.card_fin] using
        (gram_quadratic P.x Finset.univ b).symm
    rw [hq, hb] at H
    have hnrm : 0 ≤ normSq b := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hz : normSq b = 0 := by
      simp only [dotProduct_zero] at H
      exact le_antisymm (nonpos_of_mul_nonpos_right H hminpos) hnrm
    funext i
    have hi : b i ^ 2 ≤ normSq b := by
      exact Finset.single_le_sum (fun j _ => sq_nonneg (b j)) (Finset.mem_univ i)
    rw [hz] at hi
    change b i = 0
    exact (sq_nonpos_iff (b i)).mp hi
  have hinj : Function.Injective G.mulVec := by
    intro b d hbd
    have hz : G *ᵥ (b-d) = 0 := by rw [Matrix.mulVec_sub, hbd]; simp
    exact sub_eq_zero.mp (hker (b-d) hz)
  have hunit : IsUnit G := Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det G).mp hunit)

private theorem corrected_E10_popVar_nonneg {n} (hn : 2 ≤ n) (u : Fin n → ℝ) :
    0 ≤ popVar u := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by linarith)

/-- Corrected (E.10). -/
theorem corrected_E10_proof {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1/2) (hP : Xi P δ e A B r) :
    (1-max δ 0) * (controlSize P.pop/((n : ℝ)*(P.pop.n1 : ℝ))*
      popVar (residual P true (late P.pop)) +
      (P.pop.n1 : ℝ)/((n : ℝ)*controlSize P.pop)*popVar (residual P false (late P.pop))) ≤
      designVariance P.pop (oracleTau P (late P.pop)) := by
  rcases hP with ⟨hD, hm, hc, hlo, hhi, hcov, hfour, hx, hx4, hRayleigh⟩
  have hn : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hD.1
  have hg := corrected_E10_population_full_rank P hn e he hx hRayleigh
  have horacle : designVariance P.pop (oracleTau P (late P.pop)) =
      designVariance P.pop (fun S =>
        groupMean S (residual P true (late P.pop)) -
          groupMean Sᶜ (residual P false (late P.pop))) := by
    apply missing_square_variance_congr P.pop
    intro S hS
    exact (corrected_oracle_expansion P hD hm hc hx hg S hS).2
  have ht : (0 : ℝ) < P.pop.n1 := by exact_mod_cast hD.2.1
  have hcpos : 0 < controlSize P.pop := by
    unfold controlSize
    exact sub_pos.mpr (by exact_mod_cast hD.2.2)
  have hsum : controlSize P.pop + (P.pop.n1 : ℝ) = (n : ℝ) := by
    unfold controlSize
    ring
  have hV1 := corrected_E10_popVar_nonneg hD.1 (residual P true (late P.pop))
  have hV0 := corrected_E10_popVar_nonneg hD.1 (residual P false (late P.pop))
  have H := corrected_variance_algebra (controlSize P.pop) (P.pop.n1 : ℝ)
    (Real.sqrt (popVar (residual P true (late P.pop))))
    (Real.sqrt (popVar (residual P false (late P.pop))))
    (popCov (residual P true (late P.pop)) (residual P false (late P.pop))) δ
    hcpos ht (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hcov
  rw [Real.sq_sqrt hV1, Real.sq_sqrt hV0, hsum] at H
  rw [horacle, corrected_E10_two_arm_variance P.pop hD,
    corrected_E10_popVar_sub]
  exact H

end
end AronowAudit.P002.Wave1
