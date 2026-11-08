import SAP.P061a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a.WH.W1.P.T5_L1

open scoped BigOperators Classical

lemma fair_coordinate_sum (n : ℕ) (j : Fin n) (b : Fin 2) :
    (∑ w : Fin n → Fin 2, if w j = b then (1/2 : ℝ)^n else 0) = 1/2 := by
  have h := AronowAudit.P061.coordinate_probability n
    (fun _ : Fin n => AronowAudit.P061.uniformDesign (Fin 2)) j (fun a => a = b)
  simpa [AronowAudit.P061.probability, AronowAudit.P061.productDesign,
    AronowAudit.P061.uniformDesign, tsum_fintype] using h

lemma boundary_bit_probability (n : ℕ) (i : Fin (n+2)) (b : Fin 2) :
    eventProbability (boundaryDesignW1 n) (fun z => z i = b) = 1/2 := by
  unfold eventProbability
  rw [tsum_fintype, AronowAudit.P061.sum_vector_succ (n+1)]
  simp only [AronowAudit.P061.sum_vector_succ n]
  simp_rw [boundaryDesignW1]
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    simp [Finset.sum_const, nsmul_eq_mul, Fin.sum_univ_two]
    have hn : (2 : ℝ)^n ≠ 0 := by positivity
    field_simp
    fin_cases b <;> norm_num
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    simp [Finset.sum_const, nsmul_eq_mul, Fin.sum_univ_two]
    have hn : (2 : ℝ)^n ≠ 0 := by positivity
    field_simp
    fin_cases b <;> norm_num
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
    have hs (x a : Fin 2) :
        (∑ w : Fin n → Fin 2,
          if w j = b then (if x = a then (3/8 : ℝ) else 1/8) * (1/2 : ℝ)^n else 0) =
        (if x = a then (3/8 : ℝ) else 1/8) *
          (∑ w : Fin n → Fin 2, if w j = b then (1/2 : ℝ)^n else 0) := by
      calc
        _ = ∑ w : Fin n → Fin 2,
            (if x = a then (3/8 : ℝ) else 1/8) *
              (if w j = b then (1/2 : ℝ)^n else 0) := by
          apply Finset.sum_congr rfl
          intro w hw
          by_cases hwj : w j = b <;> simp [hwj]
        _ = _ := by rw [Finset.mul_sum]
    calc
      _ = ∑ x : Fin 2, ∑ a : Fin 2,
          (if x = a then (3/8 : ℝ) else 1/8) *
            (∑ w : Fin n → Fin 2, if w j = b then (1/2 : ℝ)^n else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro a ha
        exact hs x a
      _ = ∑ x : Fin 2, ∑ a : Fin 2,
          (if x = a then (3/8 : ℝ) else 1/8) * (1/2 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro a ha
        rw [fair_coordinate_sum]
      _ = 1/2 := by norm_num [Fin.sum_univ_two]

end SAP.P061a.WH.W1.P.T5_L1

theorem SAP.P061a.WH.W1.T5_L1_proof : SAP.P061a.WH.W1.T5_L1 := by
  intro n D hD
  constructor
  · intro z
    change 0 < D.mass z
    rw [hD z]
    split_ifs <;> positivity
  · intro i
    have hprob (P : BoundarySpaceW1 n → Prop) :
        eventProbability D P = eventProbability (boundaryDesignW1 n) P := by
      unfold eventProbability
      rw [tsum_fintype, tsum_fintype]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hP : P z <;> simp [hP, hD z, boundaryDesignW1]
    have hbit1 (c : Fin 2) : ((c.val : ℝ) = 1) ↔ c = 1 := by
      fin_cases c <;> norm_num
    have hbit0 (c : Fin 2) : ((c.val : ℝ) = 0) ↔ c = 0 := by
      fin_cases c <;> norm_num
    constructor
    · have h := SAP.P061a.WH.W1.P.T5_L1.boundary_bit_probability n i 1
      simpa [exposureProbability, boundaryExposureW1, hbit1] using (hprob (fun z => z i = 1)).trans h
    · have h := SAP.P061a.WH.W1.P.T5_L1.boundary_bit_probability n i 0
      simpa [exposureProbability, boundaryExposureW1, hbit0] using (hprob (fun z => z i = 0)).trans h
