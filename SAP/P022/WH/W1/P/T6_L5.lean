import SAP.P022.WH.W1.Leaves
import AronowAudit.P022.Wave1.Gap.GP022B2b

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T6_L5

open SAP.P022 AronowAudit.P022.Wave1 MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

lemma lower_joint {n : ℕ} [NeZero n] (A B : Fin n → ℝ)
    (hA : Monotone A) (hB : Antitone B) (x y : ℝ) :
    finiteMean (fun i => if A i ≤ x ∧ B i ≤ y then (1 : ℝ) else 0) =
      max 0 (empiricalCDF A x + empiricalCDF B y - 1) := by
  classical
  let P : Fin n → Prop := fun i => A i ≤ x
  let Q : Fin n → Prop := fun i => B i ≤ y
  by_cases hover : ∃ i, P i ∧ Q i
  · obtain ⟨i, hiP, hiQ⟩ := hover
    have hcover : ∀ j, P j ∨ Q j := by
      intro j
      by_cases hji : j ≤ i
      · left
        exact (hA hji).trans hiP
      · right
        have hij : i ≤ j := le_of_not_ge hji
        exact (hB hij).trans hiQ
    have hpoint (j : Fin n) :
        (if P j then (1 : ℝ) else 0) + (if Q j then 1 else 0) =
          1 + (if P j ∧ Q j then 1 else 0) := by
      rcases hcover j with hp | hq
      · by_cases hq' : Q j <;> simp [hp, hq']
      · by_cases hp' : P j <;> simp [hp', hq]
    have hsum :
        finiteMean (fun j => if P j then (1 : ℝ) else 0) +
            finiteMean (fun j => if Q j then 1 else 0) =
          1 + finiteMean (fun j => if P j ∧ Q j then 1 else 0) := by
      calc
        _ = finiteMean (fun j =>
            (if P j then (1 : ℝ) else 0) + (if Q j then 1 else 0)) := by
          simp only [finiteMean, Finset.expect_add_distrib]
        _ = finiteMean (fun j => 1 + (if P j ∧ Q j then 1 else 0)) := by
          unfold finiteMean
          apply Finset.expect_congr rfl
          intro j hj
          exact hpoint j
        _ = _ := by
          simp only [finiteMean, Finset.expect_add_distrib,
            Finset.expect_const Finset.univ_nonempty]
    have hnonneg : 0 ≤ finiteMean (fun j => if P j ∧ Q j then (1 : ℝ) else 0) := by
      rw [← (show finiteMean (fun _ : Fin n => (0 : ℝ)) = 0 by simp [finiteMean])]
      unfold finiteMean
      apply Finset.expect_le_expect
      intro j hj
      by_cases h : P j ∧ Q j <;> simp [h]
    change finiteMean (fun i => if P i ∧ Q i then (1 : ℝ) else 0) =
      max 0 (finiteMean (fun i => if P i then (1 : ℝ) else 0) +
        finiteMean (fun i => if Q i then (1 : ℝ) else 0) - 1)
    rw [show finiteMean (fun i => if P i then (1 : ℝ) else 0) +
          finiteMean (fun i => if Q i then (1 : ℝ) else 0) - 1 =
        finiteMean (fun i => if P i ∧ Q i then (1 : ℝ) else 0) by linarith [hsum]]
    exact (max_eq_right hnonneg).symm
  · have hnone : ∀ i, ¬ (P i ∧ Q i) := by
      intro i hi
      exact hover ⟨i, hi⟩
    have hinter : finiteMean (fun i => if P i ∧ Q i then (1 : ℝ) else 0) = 0 := by
      calc
        _ = finiteMean (fun _ : Fin n => (0 : ℝ)) := by
          unfold finiteMean
          apply Finset.expect_congr rfl
          intro i hi
          simp [hnone i]
        _ = 0 := by simp [finiteMean]
    have hpoint (j : Fin n) :
        (if P j then (1 : ℝ) else 0) + (if Q j then 1 else 0) ≤ 1 := by
      by_cases hp : P j <;> by_cases hq : Q j
      · exact (hnone j ⟨hp, hq⟩).elim
      · simp [hp, hq]
      · simp [hp, hq]
      · simp [hp, hq]
    have hsum :
        finiteMean (fun j => if P j then (1 : ℝ) else 0) +
            finiteMean (fun j => if Q j then 1 else 0) ≤ 1 := by
      calc
        _ = finiteMean (fun j =>
            (if P j then (1 : ℝ) else 0) + (if Q j then 1 else 0)) := by
          simp only [finiteMean, Finset.expect_add_distrib]
        _ ≤ finiteMean (fun _ : Fin n => (1 : ℝ)) := by
          unfold finiteMean
          apply Finset.expect_le_expect
          intro j hj
          exact hpoint j
        _ = 1 := by simp [finiteMean]
    change finiteMean (fun i => if P i ∧ Q i then (1 : ℝ) else 0) =
      max 0 (finiteMean (fun i => if P i then (1 : ℝ) else 0) +
        finiteMean (fun i => if Q i then (1 : ℝ) else 0) - 1)
    rw [hinter, max_eq_left (by linarith [hsum])]

end SAP.P022.WH.W1.P.T6_L5

open SAP.P022 AronowAudit.P022.Wave1 MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

theorem SAP.P022.WH.W1.T6_L5_proof : SAP.P022.WH.W1.T6_L5 := by
  intro m k hm hk a b C hC ha hb
  classical
  letI : NeZero (m * k) := ⟨Nat.ne_of_gt (Nat.mul_pos hm hk)⟩
  let A : Fin (m * k) → ℝ := fun j => AronowAudit.P022.sortedValues a
    ⟨j.val / k, (Nat.div_lt_iff_lt_mul hk).mpr j.isLt⟩
  let B₀ : Fin (m * k) → ℝ := fun j => AronowAudit.P022.sortedValues b
    ⟨j.val / m, (Nat.div_lt_iff_lt_mul hm).mpr (by simpa [Nat.mul_comm] using j.isLt)⟩
  let B : Fin (m * k) → ℝ := fun j => B₀ j.rev
  have hA (f : ℝ → ℝ) :
      finiteMean (fun j => f (A j)) = finiteMean (fun i => f (a i)) :=
    AronowAudit.P022.Wave1.GP022B2b_lift_mean hm hk a f
  have hB₀ (f : ℝ → ℝ) :
      finiteMean (fun j => f (B₀ j)) = finiteMean (fun i => f (b i)) := by
    calc
      _ = finiteMean (fun j : Fin (k * m) => f (sortedValues b
          ⟨j.val / m, (Nat.div_lt_iff_lt_mul hm).mpr j.isLt⟩)) := by
        exact Fintype.expect_equiv (finCongr (Nat.mul_comm m k)) _ _ (fun _ => rfl)
      _ = _ := AronowAudit.P022.Wave1.GP022B2b_lift_mean hk hm b f
  have hB (f : ℝ → ℝ) :
      finiteMean (fun j => f (B j)) = finiteMean (fun i => f (b i)) := by
    calc
      _ = finiteMean (fun j => f (B₀ j)) := by
        exact Fintype.expect_equiv Fin.revPerm _ _ (fun _ => rfl)
      _ = _ := hB₀ f
  have hmonoA : Monotone A := by
    intro i j hij
    exact (AronowAudit.P022.Wave1.SharpBounds.n2_proof a).2.2
      (Nat.div_le_div_right hij)
  have hmonoB₀ : Monotone B₀ := by
    intro i j hij
    exact (AronowAudit.P022.Wave1.SharpBounds.n2_proof b).2.2
      (Nat.div_le_div_right hij)
  have hantiB : Antitone B := by
    intro i j hij
    exact hmonoB₀ (Fin.rev_le_rev.mpr hij)
  have hAb : ∀ j, |A j| ≤ C := by
    intro j
    have hj : A j ∈ List.ofFn a := (AronowAudit.P022.Wave1.SharpBounds.n2_proof a).1.mem_iff.mp
      (List.mem_ofFn.mpr ⟨_, rfl⟩)
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hj
    simpa only [hi] using ha i
  have hBb : ∀ j, |B j| ≤ C := by
    intro j
    have hj : B j ∈ List.ofFn b := (AronowAudit.P022.Wave1.SharpBounds.n2_proof b).1.mem_iff.mp
      (List.mem_ofFn.mpr ⟨_, rfl⟩)
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hj
    simpa only [hi] using hb i
  have hprod :
      (∫ u in (0 : ℝ)..1, empiricalQuantile a u * empiricalQuantile b (1 - u)) =
        finiteMean (fun j => A j * B j) := by
    apply AronowAudit.P022.Wave1.SharpBounds.n4_proof
    intro j u hl hu
    have hqa := AronowAudit.P022.Wave1.GP022B2b_common_cell hm hk a j u
      (by exact_mod_cast hl) (by exact_mod_cast hu)
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hN : (0 : ℝ) < (m : ℝ) * k := mul_pos hmR hkR
    have hrevval : j.rev.val + j.val + 1 = m * k := by
      simp only [Fin.val_rev]
      omega
    have hrevvalR : (j.rev : ℝ) + (j : ℝ) + 1 = (m * k : ℝ) := by
      exact_mod_cast hrevval
    have hl' := (div_lt_iff₀ hN).mp (by simpa only [Nat.cast_mul] using hl)
    have hu' := (lt_div_iff₀ hN).mp (by simpa only [Nat.cast_mul] using hu)
    have hcell :
        (j.rev : ℝ) / (m * k) < 1 - u ∧
          1 - u < ((j.rev : ℝ) + 1) / (m * k) := by
      constructor
      · have hn : (j.rev : ℝ) < (1 - u) * ((m : ℝ) * k) := by
          calc
            (j.rev : ℝ) < (m : ℝ) * k - u * ((m : ℝ) * k) := by
              linarith [hrevvalR, hu']
            _ = (1 - u) * ((m : ℝ) * k) := by ring
        exact (div_lt_iff₀ hN).2 (by simpa only [Nat.cast_mul] using hn)
      · have hn : (1 - u) * ((m : ℝ) * k) < (j.rev : ℝ) + 1 := by
          calc
            (1 - u) * ((m : ℝ) * k) =
                (m : ℝ) * k - u * ((m : ℝ) * k) := by ring
            _ < (j.rev : ℝ) + 1 := by linarith [hrevvalR, hl']
        exact (lt_div_iff₀ hN).2 (by simpa only [Nat.cast_mul] using hn)
    let l : Fin (k * m) := Fin.cast (Nat.mul_comm m k) j.rev
    have hlb : (l : ℝ) / (k * m) < 1 - u := by
      have hv : (l : ℝ) = (j.rev : ℝ) := by simp [l]
      have hd : (k * m : ℝ) = (m * k : ℝ) := by exact_mod_cast Nat.mul_comm k m
      rw [hv, hd]
      exact hcell.1
    have hub : 1 - u < ((l : ℝ) + 1) / (k * m) := by
      have hv : (l : ℝ) = (j.rev : ℝ) := by simp [l]
      have hd : (k * m : ℝ) = (m * k : ℝ) := by exact_mod_cast Nat.mul_comm k m
      rw [hv, hd]
      exact hcell.2
    have hqb := AronowAudit.P022.Wave1.GP022B2b_common_cell hk hm b l (1 - u)
      hlb hub
    have hqb' : empiricalQuantile b (1 - u) = B j := by
      change AronowAudit.P022.empiricalQuantile b (1 - u) = B j
      simpa [B, B₀, l] using hqb
    exact congrArg₂ (· * ·) hqa hqb'
  have hcdf (x y : ℝ) :
      frechetCDF (empiricalCDF a) (empiricalCDF b) .L x y =
        finiteMean (fun i => if A i ≤ x ∧ B i ≤ y then (1 : ℝ) else 0) := by
    have hj := SAP.P022.WH.W1.P.T6_L5.lower_joint A B hmonoA hantiB x y
    have hca : empiricalCDF A x = empiricalCDF a x := by
      unfold empiricalCDF
      exact hA (fun z => if z ≤ x then (1 : ℝ) else 0)
    have hcb : empiricalCDF B y = empiricalCDF b y := by
      unfold empiricalCDF
      exact hB (fun z => if z ≤ y then (1 : ℝ) else 0)
    simpa [frechetCDF, hca, hcb] using hj.symm
  simp_rw [hcdf]
  have hpair := AronowAudit.P022.Wave1.GP022B2b_pair_integral A B C hAb hBb
  have hpair' :
      (∫ x in (-C)..C, ∫ y in (-C)..C,
        SAP.P022.finiteMean (fun i => if A i ≤ x ∧ B i ≤ y then (1 : ℝ) else 0)) =
        SAP.P022.finiteMean (fun i => (C - A i) * (C - B i)) := by
    simpa only [SAP.P022.finiteMean, AronowAudit.P022.finiteMean] using hpair
  conv_rhs =>
    arg 2
    rw [hpair']
  rw [hprod]
  have hexpand :
      finiteMean (fun i => (C - A i) * (C - B i)) =
        C ^ 2 - C * (finiteMean a + finiteMean b) +
          finiteMean (fun i => A i * B i) := by
    have heq : (fun i => (C - A i) * (C - B i)) =
        (fun i => C ^ 2 - C * (A i + B i) + A i * B i) := by
      funext i
      ring
    rw [heq]
    simp only [finiteMean, Finset.expect_add_distrib, Finset.expect_sub_distrib,
      ← Finset.mul_expect, Finset.expect_const Finset.univ_nonempty]
    change C ^ 2 - C * (finiteMean A + finiteMean B) + _ = _
    have hAm : finiteMean A = finiteMean a := by simpa using hA id
    have hBm : finiteMean B = finiteMean b := by simpa using hB id
    rw [hAm, hBm]
    rfl
  rw [hexpand]
  ring

