import AronowAudit.P019.P019_Audit

namespace AronowAudit.P019.Wave1

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory
noncomputable section
open Classical

/-- Computable copies of the model coordinates, related to the originals below. -/
private def GP019B5b_suffix (ω : Fin 128) (j : ℕ) : ℤ :=
  ∏ i ∈ Finset.Ico (j+1) 5, integerSign (fairBit ω (i+2))

private def GP019B5b_W (j : Fin 5) (ω : Fin 128) : ℕ :=
  if integerSign (fairBit ω 1) * integerPrefix ω j.val = 1 then 2 else 1

private def GP019B5b_Y (j : Fin 5) (ω : Fin 128) : Bool :=
  fairBit ω 0 && decide (GP019B5b_suffix ω j.val = 1)

private def GP019B5b_V (j : Fin 5) (ω : Fin 128) : ℕ :=
  GP019B5b_W j ω + if fairBit ω 0 && fairBit ω (j.val+2) then 1 else 0

private theorem GP019B5b_sign_cast (b : Bool) : (integerSign b : ℝ) = bitSign b := by
  cases b <;> norm_num [integerSign, bitSign]

private theorem GP019B5b_suffix_cast (ω : Fin 128) (j : ℕ) :
    (GP019B5b_suffix ω j : ℝ) = suffixSign ω j := by
  simp [GP019B5b_suffix, suffixSign, GP019B5b_sign_cast]

private theorem GP019B5b_W_eq (j : Fin 5) (ω : Fin 128) :
    (sequentialStudy j).W ω = GP019B5b_W j ω := by
  have h : bitSign (fairBit ω 1) * prefixSign ω j.val = 1 ↔
      integerSign (fairBit ω 1) * integerPrefix ω j.val = 1 := by
    rw [← GP019B5b_sign_cast, ← prefix_integer_cast, ← Int.cast_mul, ← Int.cast_one]
    exact Int.cast_inj
  simp only [sequentialStudy, GP019B5b_W, h]

private theorem GP019B5b_Y_eq (j : Fin 5) (ω : Fin 128) :
    (sequentialStudy j).Y ω = GP019B5b_Y j ω := by
  have h : suffixSign ω j.val = 1 ↔ GP019B5b_suffix ω j.val = 1 := by
    rw [← GP019B5b_suffix_cast, ← Int.cast_one]
    exact Int.cast_inj
  simp only [sequentialStudy, GP019B5b_Y, h]

private theorem GP019B5b_V_eq (j : Fin 5) (ω : Fin 128) :
    (sequentialStudy j).V ω = GP019B5b_V j ω := by
  change (sequentialStudy j).W ω + _ = _
  rw [GP019B5b_W_eq]
  rfl

private theorem GP019B5b_law_eq (j : Fin 5) :
    (sequentialStudy j).law = uniformFin 128 (by norm_num) := rfl

private theorem GP019B5b_Z_eq (j : Fin 5) (ω : Fin 128) :
    (sequentialStudy j).Z ω = fairBit ω (j.val+2) := rfl

private theorem GP019B5b_mean_int (f : Fin 128 → ℤ) :
    (uniformFin 128 (by norm_num)).mean (fun ω => (f ω : ℝ)) =
      ((∑ ω, f ω : ℤ) : ℝ) / 128 := by
  simp only [FiniteLaw.mean, uniformFin, Int.cast_sum]
  rw [← Finset.mul_sum]
  norm_num only [Nat.cast_ofNat]
  ring

private def GP019B5b_flip (j : Fin 5) (ω : Fin 128) : Fin 128 :=
  ⟨(ω.val ^^^ 2^(j.val+2)) % 128, Nat.mod_lt _ (by decide)⟩

private theorem GP019B5b_flip_table : ∀ j : Fin 5, ∀ ω : Fin 128,
    GP019B5b_flip j (GP019B5b_flip j ω) = ω ∧
    GP019B5b_W j (GP019B5b_flip j ω) = GP019B5b_W j ω ∧
    fairBit (GP019B5b_flip j ω) 0 = fairBit ω 0 ∧
    GP019B5b_Y j (GP019B5b_flip j ω) = GP019B5b_Y j ω ∧
    fairBit (GP019B5b_flip j ω) (j.val+2) = !(fairBit ω (j.val+2)) := by
  decide

private theorem GP019B5b_treatment_count : ∀ j : Fin 5, ∀ z : Bool,
    (∑ ω : Fin 128, (if fairBit ω (j.val+2) = z then 1 else 0 : ℤ)) = 64 := by
  decide

private theorem GP019B5b_treatment_mass (j : Fin 5) (z : Bool) :
    (sequentialStudy j).law.prob (fun ω => (sequentialStudy j).Z ω = z) = 1/2 := by
  change (uniformFin 128 (by norm_num)).mean
    (fun ω => if fairBit ω (j.val+2) = z then 1 else 0) = _
  have h := GP019B5b_mean_int (fun ω => if fairBit ω (j.val+2) = z then 1 else 0)
  norm_num only [Int.cast_ite, Int.cast_one, Int.cast_zero, GP019B5b_treatment_count,
    Int.cast_ofNat] at h
  exact h

private theorem GP019B5b_own_factorization (j : Fin 5) :
    (sequentialStudy j).treatmentIndependent := by
  intro f z
  rw [GP019B5b_treatment_mass]
  let g : Fin 128 → ℝ := fun ω => f (GP019B5b_W j ω) (fairBit ω 0) (GP019B5b_Y j ω)
  let e : Fin 128 ≃ Fin 128 :=
    ⟨GP019B5b_flip j, GP019B5b_flip j,
      fun ω => (GP019B5b_flip_table j ω).1,
      fun ω => (GP019B5b_flip_table j ω).1⟩
  have he : ∀ ω, g (e ω) = g ω := by
    intro ω
    simp only [g, e, Equiv.coe_fn_mk,
      (GP019B5b_flip_table j ω).2.1, (GP019B5b_flip_table j ω).2.2.1,
      (GP019B5b_flip_table j ω).2.2.2.1]
  have hs : (∑ ω, if fairBit ω (j.val+2) = z then g ω else 0) =
      ∑ ω, if fairBit ω (j.val+2) = z then 0 else g ω := by
    calc
      _ = ∑ ω, if fairBit (e ω) (j.val+2) = z then g (e ω) else 0 :=
        (Equiv.sum_comp e _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro ω _
        rw [he]
        change (if fairBit (GP019B5b_flip j ω) (j.val+2) = z then g ω else 0) = _
        rw [(GP019B5b_flip_table j ω).2.2.2.2]
        cases fairBit ω (j.val+2) <;> cases z <;> rfl
  have ht : (∑ ω, if fairBit ω (j.val+2) = z then g ω else 0) +
      (∑ ω, if fairBit ω (j.val+2) = z then 0 else g ω) = ∑ ω, g ω := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> simp
  change (uniformFin 128 (by norm_num)).mean (fun ω =>
      if fairBit ω (j.val+2) = z then
        f ((sequentialStudy j).W ω) (fairBit ω 0) ((sequentialStudy j).Y ω) else 0) =
    1/2 * (uniformFin 128 (by norm_num)).mean (fun ω =>
      f ((sequentialStudy j).W ω) (fairBit ω 0) ((sequentialStudy j).Y ω))
  simp only [GP019B5b_W_eq, GP019B5b_Y_eq, FiniteLaw.mean, uniformFin, one_div]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  norm_num only [Nat.cast_ofNat]
  dsimp only [g] at hs ht
  linarith

/-- Cell count, response sum and squared-response sum on the actual 128 atoms. -/
private def GP019B5b_cellNum (j : Fin 5) (z y : Bool) (n : Fin 3) : ℤ :=
  if j.val < 4 then
    if y then
      if z then (![16, 40, 104] : Fin 3 → ℤ) n else (![16, 24, 40] : Fin 3 → ℤ) n
    else
      if z then (![48, 88, 184] : Fin 3 → ℤ) n else (![48, 72, 120] : Fin 3 → ℤ) n
  else
    if z && y then (![32, 80, 208] : Fin 3 → ℤ) n
    else (![32, 48, 80] : Fin 3 → ℤ) n

private theorem GP019B5b_cell_table : ∀ (j : Fin 5) (z y : Bool) (n : Fin 3),
    (∑ ω : Fin 128, if fairBit ω (j.val+2) = z ∧ GP019B5b_Y j ω = y
      then (GP019B5b_V j ω : ℤ)^n.val else 0) = GP019B5b_cellNum j z y n := by
  decide

private theorem GP019B5b_cell_moment (j : Fin 5) (z y : Bool) (n : Fin 3) :
    (sequentialStudy j).law.mean (fun ω => if (sequentialStudy j).cell z y ω
      then ((sequentialStudy j).V ω : ℝ)^n.val else 0) =
        (GP019B5b_cellNum j z y n : ℝ) / 128 := by
  have h := GP019B5b_mean_int (fun ω =>
    if fairBit ω (j.val+2) = z ∧ GP019B5b_Y j ω = y
      then (GP019B5b_V j ω : ℤ)^n.val else 0)
  rw [GP019B5b_cell_table] at h
  simpa only [Study.cell, GP019B5b_Y_eq, GP019B5b_V_eq,
    GP019B5b_Z_eq, GP019B5b_law_eq,
    Int.cast_ite, Int.cast_pow, Int.cast_natCast, Int.cast_zero] using h

private theorem GP019B5b_cell_mass (j : Fin 5) (z y : Bool) :
    (sequentialStudy j).law.prob ((sequentialStudy j).cell z y) =
      if j.val < 4 then (if y then 1/8 else 3/8) else 1/4 := by
  have h := GP019B5b_cell_moment j z y 0
  simp only [Fin.val_zero, pow_zero] at h
  change (sequentialStudy j).law.mean _ = _
  rw [h]
  fin_cases j <;> cases z <;> cases y <;> norm_num [GP019B5b_cellNum]

private theorem GP019B5b_cell_variance (j : Fin 5) (z y : Bool) :
    (sequentialStudy j).law.cv (fun ω => ((sequentialStudy j).V ω : ℝ))
        ((sequentialStudy j).cell z y) =
      if j.val < 4 ∧ z = true ∧ y = false then 17/36 else 1/4 := by
  unfold FiniteLaw.cv FiniteLaw.ce
  rw [GP019B5b_cell_mass]
  have h1 := GP019B5b_cell_moment j z y 1
  have h2 := GP019B5b_cell_moment j z y 2
  simp only [Fin.val_one, pow_one] at h1
  change (sequentialStudy j).law.mean (fun ω => if (sequentialStudy j).cell z y ω
      then ((sequentialStudy j).V ω : ℝ)^2 else 0) = _ at h2
  rw [h1, h2]
  fin_cases j <;> cases z <;> cases y <;> norm_num [GP019B5b_cellNum]

private theorem GP019B5b_binary_table : ∀ j : Fin 5,
    (∑ ω : Fin 128, (if GP019B5b_Y j ω then 1 else 0 : ℤ)) =
      (if j.val < 4 then 32 else 64) := by
  decide

private theorem GP019B5b_Y_mass (j : Fin 5) :
    (sequentialStudy j).law.prob (fun ω => (sequentialStudy j).Y ω = true) =
      if j.val < 4 then 1/4 else 1/2 := by
  have h := GP019B5b_mean_int (fun ω => if GP019B5b_Y j ω then 1 else 0)
  rw [GP019B5b_binary_table] at h
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero] at h
  change (uniformFin 128 (by norm_num)).mean _ = _
  simp only [GP019B5b_Y_eq]
  rw [h]
  split_ifs <;> norm_num

private theorem GP019B5b_bool_variance (P : FiniteLaw (Fin 128)) (b : Fin 128 → Bool) :
    P.variance (fun ω => bitVal (b ω)) =
      P.prob (fun ω => b ω = true) - (P.prob (fun ω => b ω = true))^2 := by
  unfold FiniteLaw.variance FiniteLaw.prob
  congr 1
  · congr 1
    funext ω
    cases b ω <;> norm_num [bitVal]

private theorem GP019B5b_nondegenerate (j : Fin 5) :
    (sequentialStudy j).nondegenerate := by
  refine ⟨?_, ?_, ?_⟩
  · intro z y
    rw [GP019B5b_cell_mass, GP019B5b_cell_variance]
    by_cases hj : j.val < 4 <;> cases z <;> cases y <;> norm_num [hj]
  · rw [GP019B5b_bool_variance, GP019B5b_treatment_mass]
    norm_num
  · rw [GP019B5b_bool_variance, GP019B5b_Y_mass]
    split_ifs <;> norm_num

private theorem GP019B5b_monotone (j : Fin 5) :
    (sequentialStudy j).monotone := by
  intro ω _ hY
  change (fairBit ω 0 && decide (suffixSign ω j.val = 1)) = true at hY
  exact (Bool.and_eq_true_iff.mp hY).1

private theorem GP019B5b_response (j : Fin 5) :
    (sequentialStudy j).noLiarsDesign := by
  intro ω _
  change (((sequentialStudy j).W ω +
    (if fairBit ω 0 && fairBit ω (j.val+2) then 1 else 0) : ℕ) : ℝ) = _
  rw [Nat.cast_add]
  change _ = ((sequentialStudy j).W ω : ℝ) +
    bitVal (fairBit ω 0) * bitVal (fairBit ω (j.val+2))
  cases fairBit ω 0 <;> cases fairBit ω (j.val+2) <;> norm_num [bitVal]

private theorem GP019B5b_standing (j : Fin 5) : (sequentialStudy j).standing := by
  exact ⟨GP019B5b_monotone j, GP019B5b_response j,
    GP019B5b_own_factorization j, GP019B5b_nondegenerate j⟩

private theorem GP019B5b_affirmative_W_table : ∀ j : Fin 5,
    (∑ ω : Fin 128, if GP019B5b_Y j ω = true then (GP019B5b_W j ω : ℤ) else 0) =
      (if j.val < 4 then 48 else 96) := by
  decide

private theorem GP019B5b_affirmative_W (j : Fin 5) :
    (sequentialStudy j).law.ce (fun ω => ((sequentialStudy j).W ω : ℝ))
      (fun ω => (sequentialStudy j).Y ω = true) = 3/2 := by
  unfold FiniteLaw.ce
  rw [GP019B5b_Y_mass]
  have h := GP019B5b_mean_int (fun ω =>
    if GP019B5b_Y j ω = true then (GP019B5b_W j ω : ℤ) else 0)
  rw [GP019B5b_affirmative_W_table] at h
  simp only [Int.cast_ite, Int.cast_natCast, Int.cast_zero] at h
  simp only [GP019B5b_W_eq, GP019B5b_Y_eq, GP019B5b_law_eq]
  rw [h]
  split_ifs <;> norm_num

private theorem GP019B5b_influence_table : ∀ (j : Fin 5) (ω : Fin 128),
    (if j.val < 4 then (4 : ℤ) else 2) *
      (if GP019B5b_Y j ω then 1 else 0) *
      (2 * (if fairBit ω (j.val+2) then 1 else 0) - 1) *
      (2 * (GP019B5b_W j ω : ℤ) - 3) = integerSequentialPsi j ω := by
  decide

private theorem GP019B5b_influence (j : Fin 5) (ω : Fin 128) :
    (sequentialStudy j).betaPsi ω = sequentialPsi j ω := by
  rw [← sequential_psi_integer_cast, ← GP019B5b_influence_table]
  unfold Study.betaPsi
  rw [show (sequentialStudy j).gamma = 1/2 from GP019B5b_treatment_mass j true,
    GP019B5b_Y_mass, GP019B5b_affirmative_W]
  simp only [GP019B5b_W_eq, GP019B5b_Y_eq, GP019B5b_Z_eq]
  push_cast
  by_cases hj : j.val < 4 <;> cases GP019B5b_Y j ω <;>
    cases fairBit ω (j.val+2) <;> simp [hj, bitVal] <;> ring

private theorem GP019B5b_assignment_table : ∀ a : Fin 5 → Bool,
    (∑ ω : Fin 128, (if ∀ j, fairBit ω (j.val+2) = a j then 1 else 0 : ℤ)) = 4 := by
  decide

private theorem GP019B5b_assignment_mass (a : Fin 5 → Bool) :
    (uniformFin 128 (by norm_num)).prob
      (fun ω => ∀ j, (sequentialStudy j).Z ω = a j) = 1/32 := by
  have h := GP019B5b_mean_int (fun ω =>
    if ∀ j, fairBit ω (j.val+2) = a j then 1 else 0)
  rw [GP019B5b_assignment_table] at h
  norm_num only [Int.cast_ite, Int.cast_one, Int.cast_zero, Int.cast_ofNat] at h
  exact h.trans (by norm_num)

private theorem GP019B5b_beta (j : Fin 5) : (sequentialStudy j).beta = 1 := by
  have hs := GP019B5b_standing j
  exact placebo_one_identity (sequentialStudy j) hs.1 hs.2.1 hs.2.2.1
    (ne_of_gt (hs.2.2.2.1 false true).1) (ne_of_gt (hs.2.2.2.1 true true).1)

theorem fisher_sequential_finite_proof :
    (∀ j : Fin 5, (sequentialStudy j).standing ∧ (sequentialStudy j).beta = 1) ∧
    (∀ a : Fin 5 → Bool,
      (uniformFin 128 (by norm_num)).prob
        (fun ω => ∀ j, (sequentialStudy j).Z ω = a j) = 1/32) ∧
    (∀ j ω, (sequentialStudy j).betaPsi ω = sequentialPsi j ω) ∧
    (∀ j, (uniformFin 128 (by norm_num)).mean (sequentialPsi j) = 0) ∧
    (∀ j k, (uniformFin 128 (by norm_num)).mean
      (fun ω => sequentialPsi j ω * sequentialPsi k ω) =
        if j = k then (if j.val < 4 then 4 else 2) else 2) := by
  exact ⟨fun j => ⟨GP019B5b_standing j, GP019B5b_beta j⟩,
    GP019B5b_assignment_mass, GP019B5b_influence,
    sequential_influence_centered, sequential_influence_matrix⟩

theorem sequential_own_independence_proof (j : Fin 5) : (sequentialStudy j).treatmentIndependent := by
  exact GP019B5b_own_factorization j

theorem sequential_standing_proof (j : Fin 5) : (sequentialStudy j).standing := by
  exact GP019B5b_standing j

end
end AronowAudit.P019.Wave1
