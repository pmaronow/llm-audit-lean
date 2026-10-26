import AronowAudit.P004.Wave1.ObservationalCoverageBlueprint
import AronowAudit.P004.Wave1.ObservationalCoverage.O2
import AronowAudit.P004.Wave1.ObservationalCoverage.O4

/-! Exact finite-sample identities for O6, with elementary helpers shared by O5, O7,
and O8. -/

namespace AronowAudit.P004.Wave1.ObservationalCoverage

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators Classical

theorem activeTable_eq_sign (N : ℕ) (i : Fin N) (z : Assignment N) :
    activeTable N i z = activeSign N i * bit (z i) := rfl

theorem activeSign_of_not_group {N : ℕ} (i : Fin N) (hi : ¬ activeGroup N i) :
    activeSign N i = 0 := by
  have h0 : i.val % 8 ≠ 0 := by unfold activeGroup at hi; omega
  have h1 : i.val % 8 ≠ 1 := by unfold activeGroup at hi; omega
  simp only [activeSign, if_neg h0, if_neg h1]

theorem activeSign_sq (N : ℕ) (i : Fin N) :
    (activeSign N i)^2 = if activeGroup N i then 1 else 0 := by
  unfold activeSign activeGroup
  by_cases h0 : i.val % 8 = 0
  · simp [h0]
  · by_cases h1 : i.val % 8 = 1
    · simp [h0, h1]
    · have h2 : ¬ i.val % 8 < 2 := by omega
      simp [h0, h1, h2]

theorem activeSign_abs_le (N : ℕ) (i : Fin N) : |activeSign N i| ≤ 1 := by
  unfold activeSign
  split_ifs <;> norm_num

theorem sum_active_const (N : ℕ) (c : ℝ) :
    (∑ i : Fin N, if activeGroup N i then c else 0) = nH N * c := by
  have hcount : (∑ i : Fin N, if activeGroup N i then (1 : ℝ) else 0) = nH N := by
    simpa only [nH] using
      (Finset.sum_boole (fun i : Fin N => activeGroup N i) Finset.univ)
  calc
    _ = (∑ i : Fin N, if activeGroup N i then (1 : ℝ) else 0) * c := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ = _ := by rw [hcount]

theorem sum_inactive_const (N : ℕ) (c : ℝ) :
    (∑ i : Fin N, if activeGroup N i then 0 else c) = nL N * c := by
  have hcount : (∑ i : Fin N, if activeGroup N i then (0 : ℝ) else 1) = nL N := by
    simpa only [nL, ite_not] using
      (Finset.sum_boole (fun i : Fin N => ¬ activeGroup N i) Finset.univ)
  calc
    _ = (∑ i : Fin N, if activeGroup N i then (0 : ℝ) else 1) * c := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ = _ := by rw [hcount]

theorem sum_activeSign_sq (N : ℕ) : (∑ i : Fin N, (activeSign N i)^2) = nH N := by
  simp_rw [activeSign_sq]
  simpa using sum_active_const N 1

private theorem active_count_sum (N : ℕ) :
    (∑ i : Fin N, if i.val % 8 < 2 then (1 : ℕ) else 0) = 2 * (N / 8) + min (N % 8) 2 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    have hm : N % 8 < 8 := Nat.mod_lt N (by decide)
    have hd : N % 8 + 8 * (N / 8) = N := Nat.mod_add_div N 8
    have hm' : (N + 1) % 8 < 8 := Nat.mod_lt (N + 1) (by decide)
    have hd' : (N + 1) % 8 + 8 * ((N + 1) / 8) = N + 1 :=
      Nat.mod_add_div (N + 1) 8
    split_ifs <;> omega

/-- This natural-number identity includes every partial last block. -/
theorem active_count_formula (N : ℕ) :
    (Finset.univ.filter (fun i : Fin N => activeGroup N i)).card =
      2 * (N / 8) + min (N % 8) 2 := by
  have hsum : (Finset.univ.filter (fun i : Fin N => activeGroup N i)).card =
      ∑ i : Fin N, if i.val % 8 < 2 then (1 : ℕ) else 0 := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : i.val % 8 < 2 <;> simp [activeGroup, h]
  rw [hsum]
  exact active_count_sum N

theorem sAct_formula (N : ℕ) : sAct N = if N % 8 = 1 then 1 else 0 := by
  induction N with
  | zero => simp [sAct]
  | succ N ih =>
    have hstep : sAct (N + 1) = sAct N +
        (if N % 8 = 0 then 1 else if N % 8 = 1 then -1 else 0) := by
      unfold sAct
      rw [Fin.sum_univ_castSucc]
      rfl
    rw [hstep, ih]
    have hnext : (N + 1) % 8 = 1 ↔ N % 8 = 0 := by omega
    simp only [hnext]
    by_cases h0 : N % 8 = 0
    · have h1 : N % 8 ≠ 1 := by omega
      simp [h0, h1]
    · by_cases h1 : N % 8 = 1 <;> simp [h0, h1]

theorem sAct_sq_le_one (N : ℕ) : (sAct N)^2 ≤ 1 := by
  rw [sAct_formula]
  split_ifs <;> norm_num

theorem nH_ge_quarter (N : ℕ) : (N : ℝ) / 4 ≤ nH N := by
  have hnat : N ≤ 4 * (Finset.univ.filter (fun i : Fin N => activeGroup N i)).card := by
    rw [active_count_formula]
    have hm : N % 8 < 8 := Nat.mod_lt N (by decide)
    have hd : N % 8 + 8 * (N / 8) = N := Nat.mod_add_div N 8
    omega
  have hr : (N : ℝ) ≤ 4 *
      ((Finset.univ.filter (fun i : Fin N => activeGroup N i)).card : ℝ) := by
    exact_mod_cast hnat
  change (N : ℝ) ≤ 4 * nH N at hr
  linarith

theorem nH_pos {N : ℕ} (hN : 0 < N) : 0 < nH N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hh := nH_ge_quarter N
  linarith

theorem nL_pos {N : ℕ} (hN : 3 ≤ N) : 0 < nL N := by
  let i : Fin N := ⟨2, by omega⟩
  have hi : i ∈ Finset.univ.filter (fun j : Fin N => ¬ activeGroup N j) := by
    norm_num [i, activeGroup]
  have hc : 0 < (Finset.univ.filter (fun j : Fin N => ¬ activeGroup N j)).card :=
    Finset.card_pos.mpr ⟨i, hi⟩
  change 0 < ((Finset.univ.filter (fun j : Fin N => ¬ activeGroup N j)).card : ℝ)
  exact_mod_cast hc

theorem clip_bounds (q : ℝ) : (1 : ℝ) / 20 ≤ clip q ∧ clip q ≤ 19 / 20 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem pHatH_mem (N : ℕ) (z : Assignment N) : 0 < pHatH N z ∧ pHatH N z < 1 := by
  have hh := clip_bounds (KAct N z / nH N)
  change (1 : ℝ) / 20 ≤ pHatH N z ∧ pHatH N z ≤ 19 / 20 at hh
  constructor <;> linarith

theorem pHatL_mem (N : ℕ) (z : Assignment N) : 0 < pHatL N z ∧ pHatL N z < 1 := by
  have hh := clip_bounds (JAct N z / nL N)
  change (1 : ℝ) / 20 ≤ pHatL N z ∧ pHatL N z ≤ 19 / 20 at hh
  constructor <;> linarith

theorem active_true_admissible (N : ℕ) :
    ∀ i, 0 < propensities (activeO N) activeTheta i ∧
      propensities (activeO N) activeTheta i < 1 := by
  intro i
  rw [o4_proof N]
  dsimp only
  split_ifs <;> norm_num

theorem active_fitted_propensity_high {N : ℕ} (hN : 0 < N) (z : Assignment N)
    (i : Fin N) (hi : activeGroup N i) :
    propensities (activeO N) (activeMLE N z) i = pHatH N z := by
  have hn : nH N ≠ 0 := (nH_pos hN).ne'
  simp only [propensities, activeO, if_pos hi, dot, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, zero_mul, add_zero]
  simp only [activeMLE, Matrix.cons_val_zero, if_neg hn]
  exact o2_proof.2.1 (KAct N z / nH N)

theorem active_fitted_propensities {N : ℕ} (hN : 3 ≤ N) (z : Assignment N) :
    propensities (activeO N) (activeMLE N z) =
      fun i => if activeGroup N i then pHatH N z else pHatL N z := by
  have hnH : nH N ≠ 0 := (nH_pos (by omega : 0 < N)).ne'
  have hnL : nL N ≠ 0 := (nL_pos hN).ne'
  funext i
  by_cases hi : activeGroup N i
  · simpa only [if_pos hi] using active_fitted_propensity_high (by omega) z i hi
  · simp only [propensities, activeO, if_neg hi, dot, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, one_mul, zero_add,
      activeMLE, if_neg hnL]
    exact o2_proof.2.1 (JAct N z / nL N)

theorem active_marginal {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (i : Fin N) (a : Bool) :
    marginal p (activeTable N) i a = activeSign N i * bit a := by
  rw [marginal_is_marginalization p (activeTable N) i a hp]
  have hfun : (fun z => activeTable N i (Function.update z i a)) =
      fun _ : Assignment N => activeSign N i * bit a := by
    funext z
    simp only [activeTable_eq_sign, Function.update_self]
  rw [hfun, expect_const]

/-- An arbitrary function of one coin, under the actual heterogeneous product law.
No positivity assumption is needed for this finite algebra identity. -/
theorem own_expect {N : ℕ} (p : Fin N → ℝ) (i : Fin N) (f : Bool → ℝ) :
    expect p (fun z => f (z i)) = (1 - p i) * f false + p i * f true := by
  have hc : (∑ u : {j : Fin N // j ≠ i} → Bool,
      ∏ j : {j : Fin N // j ≠ i}, coin (p j) (u j)) = 1 := by
    have h := GraphCompletion.cube_normalized (fun j : {j : Fin N // j ≠ i} => p j)
    simp only [GraphCompletion.cubeWeight] at h
    convert h
  rw [expect_split p i]
  have hj (a : Bool) (u : {j : Fin N // j ≠ i} → Bool) :
      f (joinAssignment i a u i) = f a := by simp [joinAssignment]
  simp_rw [hj, ← Finset.sum_mul, hc]
  simp [Fintype.sum_bool, coin, add_comm]

theorem own_variance {N : ℕ} (p : Fin N → ℝ) (i : Fin N) (f : Bool → ℝ) :
    variance p (fun z => f (z i)) = p i * (1 - p i) * (f true - f false)^2 := by
  unfold variance cov
  rw [own_expect p i (fun a => f a * f a), own_expect p i f]
  ring

theorem own_cov_of_ne {N : ℕ} (p : Fin N → ℝ) (i j : Fin N) (hij : i ≠ j)
    (f g : Bool → ℝ) : cov p (fun z => f (z i)) (fun z => g (z j)) = 0 := by
  have hF : DependsOn (fun z : Assignment N => f (z i)) ({i} : Set (Fin N)) := by
    intro x y hxy
    exact congrArg f (hxy i (by simp))
  have hG : DependsOn (fun z : Assignment N => g (z j)) (({i} : Set (Fin N))ᶜ) := by
    intro x y hxy
    exact congrArg g (hxy j (by simpa using hij.symm))
  unfold cov
  rw [GraphCompletion.expect_mul_of_disjoint_depends p {i} _ _ hF hG]
  ring

theorem own_sum_variance {N : ℕ} (p : Fin N → ℝ) (f : Fin N → Bool → ℝ) :
    variance p (fun z => ∑ i, f i (z i)) =
      ∑ i, p i * (1 - p i) * (f i true - f i false)^2 := by
  rw [variance_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j, cov p (fun z => f i (z i)) (fun z => f j (z j))) =
        cov p (fun z => f i (z i)) (fun z => f i (z i)) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact own_cov_of_ne p i j hji.symm (f i) (f j)
      · simp
    _ = p i * (1 - p i) * (f i true - f i false)^2 := own_variance p i (f i)

theorem o6_proof : O6 := by
  constructor
  · intro N hN z
    have hrow (i : Fin N) :
        bit (z i) * activeTable N i z /
            propensities (activeO N) (activeMLE N z) i -
          (1 - bit (z i)) * activeTable N i z /
            (1 - propensities (activeO N) (activeMLE N z) i) =
        activeSign N i * bit (z i) / pHatH N z := by
      by_cases hi : activeGroup N i
      · rw [active_fitted_propensity_high hN z i hi]
        cases hz : z i <;> simp [activeTable_eq_sign, bit, hz]
      · simp [activeTable_eq_sign, activeSign_of_not_group i hi]
    change (∑ i, _) / (N : ℝ) = _
    simp_rw [hrow]
    rw [← Finset.sum_div]
    change (SAct N z / pHatH N z) / (N : ℝ) = SAct N z / (N * pHatH N z)
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · intro N
    unfold ame nodeEffect
    simp_rw [active_marginal _ (active_true_admissible N)]
    simp [bit, sAct]

end
end AronowAudit.P004.Wave1.ObservationalCoverage
