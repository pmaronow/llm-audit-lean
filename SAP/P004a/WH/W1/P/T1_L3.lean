import SAP.P004a.WH.W1.Leaves
import AronowAudit.P004.Wave1.FiniteConditioning.FC7

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W1.P.T1_L3

open AronowAudit.P004
open scoped BigOperators

end SAP.P004a.WH.W1.P.T1_L3

theorem SAP.P004a.WH.W1.T1_L3_proof : SAP.P004a.WH.W1.T1_L3 := by
  classical
  intro N p X a b hp ha hb hsecond hfourth
  let E : Assignment N → Prop := fun z => a / 2 < (X z)^2
  let I : Assignment N → ℝ := fun z => if E z then 1 else 0
  let A : Assignment N → ℝ := fun z => if E z then (X z)^2 else 0
  let C : Assignment N → ℝ := fun z => if E z then 0 else (X z)^2
  have hsplit : AronowAudit.P004.expect p (fun z => (X z)^2) =
      AronowAudit.P004.expect p (fun z => A z + C z) := by
    congr 1
    funext z
    by_cases h : E z <;> simp [A, C, h]
  have hsplit' : a = AronowAudit.P004.expect p A + AronowAudit.P004.expect p C := by
    calc
      a = AronowAudit.P004.expect p (fun z => (X z)^2) := hsecond.symm
      _ = AronowAudit.P004.expect p (fun z => A z + C z) := hsplit
      _ = AronowAudit.P004.expect p A + AronowAudit.P004.expect p C := AronowAudit.P004.expect_add p A C
  have hC : AronowAudit.P004.expect p C ≤ a / 2 := by
    have ht := AronowAudit.P004.expect_mono p hp C (fun _ => a / 2) (by
      intro z
      by_cases h : E z
      · simp [C, h]
        linarith
      · simp [C, h, E]
        exact le_of_not_gt h)
    simpa only [AronowAudit.P004.expect_const] using ht
  have hAlower : a / 2 ≤ AronowAudit.P004.expect p A := by linarith [hsplit']
  have hAnonneg : 0 ≤ AronowAudit.P004.expect p A := by
    have ht := AronowAudit.P004.expect_mono p hp (fun _ => 0) A (by
      intro z
      by_cases h : E z <;> simp [A, h]
      exact sq_nonneg (X z))
    simpa only [AronowAudit.P004.expect_const] using ht
  have hInonneg : 0 ≤ AronowAudit.P004.expect p I := by
    have ht := AronowAudit.P004.expect_mono p hp (fun _ => 0) I (by
      intro z
      simp [I]
      split_ifs <;> norm_num)
    simpa only [AronowAudit.P004.expect_const] using ht
  have hfourthNonneg : 0 ≤ AronowAudit.P004.expect p (fun z => (X z)^4) := by
    have ht := AronowAudit.P004.expect_mono p hp (fun _ => 0)
        (fun z => (X z)^4) (by
      intro z
      nlinarith [sq_nonneg ((X z)^2)])
    simpa only [AronowAudit.P004.expect_const] using ht
  have hI2 : AronowAudit.P004.expect p (fun z => (I z)^2) = prob p E := by
    unfold prob
    congr 1
    funext z
    by_cases h : E z <;> simp [I, h]
  have hAprod : AronowAudit.P004.expect p (fun z => I z * (X z)^2) = AronowAudit.P004.expect p A := by
    congr 1
    funext z
    by_cases h : E z <;> simp [I, A, h]
  have hX4 : AronowAudit.P004.expect p (fun z => ((X z)^2)^2) = AronowAudit.P004.expect p (fun z => (X z)^4) := by
    congr 1
    funext z
    ring
  have hcs0 : |AronowAudit.P004.expect p (fun z => I z * (X z)^2)| ≤
      Real.sqrt (AronowAudit.P004.expect p (fun z => (I z)^2)) *
        Real.sqrt (AronowAudit.P004.expect p (fun z => ((X z)^2)^2)) := by
    rcases AronowAudit.P004.Wave1.FiniteConditioning.fc7_proof p hp with
      ⟨_, _, _, _, _, _, _, hcs, _, _⟩
    simpa only [AronowAudit.P004.l2Norm] using
      hcs I (fun z => (X z)^2)
  have hcs : |AronowAudit.P004.expect p A| ≤
      Real.sqrt (prob p E) * Real.sqrt (AronowAudit.P004.expect p (fun z => (X z)^4)) := by
    rw [hAprod, hI2, hX4] at hcs0
    exact hcs0
  have hprobNonneg : 0 ≤ prob p E := by
    change 0 ≤ AronowAudit.P004.expect p I
    exact hInonneg
  have hcsSq : (AronowAudit.P004.expect p A)^2 ≤ prob p E * AronowAudit.P004.expect p (fun z => (X z)^4) := by
    have hroot : 0 ≤ Real.sqrt (prob p E) *
        Real.sqrt (AronowAudit.P004.expect p (fun z => (X z)^4)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have habsSq : (|AronowAudit.P004.expect p A|)^2 ≤
        (Real.sqrt (prob p E) * Real.sqrt (AronowAudit.P004.expect p (fun z => (X z)^4)))^2 := by
      nlinarith [sq_nonneg (|AronowAudit.P004.expect p A| -
        Real.sqrt (prob p E) * Real.sqrt (AronowAudit.P004.expect p (fun z => (X z)^4))),
        abs_nonneg (AronowAudit.P004.expect p A)]
    calc
      (AronowAudit.P004.expect p A)^2 = (|AronowAudit.P004.expect p A|)^2 := (sq_abs _).symm
      _ ≤ (Real.sqrt (prob p E) *
          Real.sqrt (AronowAudit.P004.expect p (fun z => (X z)^4)))^2 := habsSq
      _ = prob p E * AronowAudit.P004.expect p (fun z => (X z)^4) := by
        rw [mul_pow, Real.sq_sqrt hprobNonneg, Real.sq_sqrt hfourthNonneg]
  have hmain : a^2 / 4 ≤ prob p E * b := by
    have hAlowerSq : a^2 / 4 ≤ (AronowAudit.P004.expect p A)^2 := by
      nlinarith [sq_nonneg (a / 2 - AronowAudit.P004.expect p A)]
    calc
      a^2 / 4 ≤ (AronowAudit.P004.expect p A)^2 := hAlowerSq
      _ ≤ prob p E * AronowAudit.P004.expect p (fun z => (X z)^4) := hcsSq
      _ ≤ prob p E * b := mul_le_mul_of_nonneg_left hfourth hprobNonneg
  change a^2 / (4*b) ≤ prob p E
  apply (div_le_iff₀ (by positivity : 0 < 4*b)).2
  nlinarith [hmain]
