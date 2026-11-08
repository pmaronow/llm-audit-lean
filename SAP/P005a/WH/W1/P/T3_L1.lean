import SAP.P005a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace SAP.P005a.WH.W1.P.T3_L1

open Finset SAP.P005a
open scoped BigOperators

def D (S : Finset (Fin 16)) (i : Fin 16) : ℝ := AronowAudit.P005.indicator S i

lemma probability_as_expectation (E : Finset (Fin 16) → Prop) [DecidablePred E] :
    probability 8 E = expectation 8 (fun S => if E S then 1 else 0) := by
  classical
  unfold SAP.P005a.probability SAP.P005a.expectation
  rw [Finset.sum_boole]
  apply congrArg (fun k : ℕ => (k : ℝ) / (design 16 8).card)
  congr 1
  ext S
  simp

lemma expectation_add (f g : Finset (Fin 16) → ℝ) :
    expectation 8 (fun S => f S + g S) = expectation 8 f + expectation 8 g := by
  simp only [SAP.P005a.expectation, Finset.sum_add_distrib, add_div]

lemma expectation_sub (f g : Finset (Fin 16) → ℝ) :
    expectation 8 (fun S => f S - g S) = expectation 8 f - expectation 8 g := by
  simp only [SAP.P005a.expectation, Finset.sum_sub_distrib, sub_div]

lemma expectation_mul_const (f : Finset (Fin 16) → ℝ) (c : ℝ) :
    expectation 8 (fun S => c * f S) = c * expectation 8 f := by
  unfold SAP.P005a.expectation
  rw [← Finset.mul_sum]
  ring

lemma expectation_const (c : ℝ) : expectation 8 (fun _ : Finset (Fin 16) => c) = c := by
  change AronowAudit.P005.expectation 8 (fun _ : Finset (Fin 16) => c) = c
  exact AronowAudit.P005.Wave1.GP005B4b_T3_expectation_const c

lemma indicator_zero_identity (S : Finset (Fin 16)) :
    (if W1HighCount S = 0 then 1 else 0) =
      (1 - D S 0 - D S 1) + D S 0 * D S 1 := by
  classical
  by_cases h0 : (0 : Fin 16) ∈ S <;> by_cases h1 : (1 : Fin 16) ∈ S <;>
    simp [W1HighCount, D, AronowAudit.P005.indicator, h0, h1]

lemma indicator_one_identity (S : Finset (Fin 16)) :
    (if W1HighCount S = 1 then 1 else 0) =
      (D S 0 + D S 1) - 2 * (D S 0 * D S 1) := by
  classical
  by_cases h0 : (0 : Fin 16) ∈ S <;> by_cases h1 : (1 : Fin 16) ∈ S <;>
    simp [W1HighCount, D, AronowAudit.P005.indicator, h0, h1] <;> norm_num

lemma indicator_two_identity (S : Finset (Fin 16)) :
    (if W1HighCount S = 2 then 1 else 0) = D S 0 * D S 1 := by
  classical
  by_cases h0 : (0 : Fin 16) ∈ S <;> by_cases h1 : (1 : Fin 16) ∈ S <;>
    simp [W1HighCount, D, AronowAudit.P005.indicator, h0, h1]

lemma single_zero_mean : expectation 8 (fun S => D S 0) = (1/2 : ℝ) := by
  change AronowAudit.P005.expectation 8 (fun S => AronowAudit.P005.indicator S 0) = (1/2 : ℝ)
  calc
    _ = (8 : ℝ)/16 := AronowAudit.P005.indicator_expectation (n := 16) (m := 8)
      (by norm_num) (by norm_num) (by norm_num) (0 : Fin 16)
    _ = 1/2 := by norm_num

lemma single_one_mean : expectation 8 (fun S => D S 1) = (1/2 : ℝ) := by
  change AronowAudit.P005.expectation 8 (fun S => AronowAudit.P005.indicator S 1) = (1/2 : ℝ)
  calc
    _ = (8 : ℝ)/16 := AronowAudit.P005.indicator_expectation (n := 16) (m := 8)
      (by norm_num) (by norm_num) (by norm_num) (1 : Fin 16)
    _ = 1/2 := by norm_num

lemma pair_mean : expectation 8 (fun S => D S 0 * D S 1) = (7/30 : ℝ) := by
  change AronowAudit.P005.expectation 8
    (fun S => AronowAudit.P005.indicator S 0 * AronowAudit.P005.indicator S 1) = (7/30 : ℝ)
  exact AronowAudit.P005.Wave1.GP005B4b_T3_pair_inclusion

lemma probability_zero : probability 8 (fun S => W1HighCount S = 0) = (7/30 : ℝ) := by
  classical
  calc
    probability 8 (fun S => W1HighCount S = 0) =
        expectation 8 (fun S => if W1HighCount S = 0 then (1 : ℝ) else 0) :=
      probability_as_expectation _
    _ = expectation 8 (fun S => (1 - D S 0 - D S 1) + D S 0 * D S 1) := by
      apply congrArg
      funext S
      exact indicator_zero_identity S
    _ = (7/30 : ℝ) := by
      rw [expectation_add, expectation_sub, expectation_sub, expectation_const,
        single_zero_mean, single_one_mean, pair_mean]
      norm_num

lemma probability_one : probability 8 (fun S => W1HighCount S = 1) = (8/15 : ℝ) := by
  classical
  calc
    probability 8 (fun S => W1HighCount S = 1) =
        expectation 8 (fun S => if W1HighCount S = 1 then (1 : ℝ) else 0) :=
      probability_as_expectation _
    _ = expectation 8 (fun S => (D S 0 + D S 1) - 2 * (D S 0 * D S 1)) := by
      apply congrArg
      funext S
      exact indicator_one_identity S
    _ = (8/15 : ℝ) := by
      rw [expectation_sub, expectation_add, expectation_mul_const,
        single_zero_mean, single_one_mean, pair_mean]
      norm_num

lemma probability_two : probability 8 (fun S => W1HighCount S = 2) = (7/30 : ℝ) := by
  classical
  calc
    probability 8 (fun S => W1HighCount S = 2) =
        expectation 8 (fun S => if W1HighCount S = 2 then (1 : ℝ) else 0) :=
      probability_as_expectation _
    _ = expectation 8 (fun S => D S 0 * D S 1) := by
      apply congrArg
      funext S
      exact indicator_two_identity S
    _ = (7/30 : ℝ) := pair_mean

end SAP.P005a.WH.W1.P.T3_L1

theorem SAP.P005a.WH.W1.T3_L1_proof : SAP.P005a.WH.W1.T3_L1 := by
  exact ⟨SAP.P005a.WH.W1.P.T3_L1.probability_zero,
    SAP.P005a.WH.W1.P.T3_L1.probability_one,
    SAP.P005a.WH.W1.P.T3_L1.probability_two⟩
