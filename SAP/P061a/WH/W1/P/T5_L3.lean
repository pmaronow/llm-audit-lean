import SAP.P061a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Topology Classical BoundedContinuousFunction ENNReal
open Filter MeasureTheory
open SAP.P061a SAP.P061a.WH.W1

namespace SAP.P061a.WH.W1.P.T5_L3


lemma fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  have hv : x.val = 0 ∨ x.val = 1 := by have hx := x.isLt; omega
  rcases hv with hv | hv
  · left
    apply Fin.ext
    simpa using hv
  · right
    apply Fin.ext
    simpa using hv

lemma fin2_val_zero_iff (x : Fin 2) : ((x.val : ℝ) = 0) ↔ x = 0 := by
  constructor
  · intro h
    apply Fin.ext
    have hn : x.val = 0 := by exact_mod_cast h
    exact hn
  · intro h
    simp [h]

lemma fin2_val_one_iff (x : Fin 2) : ((x.val : ℝ) = 1) ↔ x = 1 := by
  constructor
  · intro h
    apply Fin.ext
    have hn : x.val = 1 := by exact_mod_cast h
    exact hn
  · intro h
    simp [h]

lemma first_bit_probability (n : ℕ) (D : AtomicDesign (BoundarySpaceW1 n))
    (hm : BoundaryMarginsW1 n D) (b : Fin 2) :
    eventProbability D (fun z => z 0 = b) = 1/2 := by
  have h1 : exposureProbability D (boundaryExposureW1 n) 0 1 = 1/2 := (hm.2 0).1
  have h0 : exposureProbability D (boundaryExposureW1 n) 0 0 = 1/2 := (hm.2 0).2
  have hp1 : eventProbability D (fun (z : BoundarySpaceW1 n) => z 0 = (1 : Fin 2)) = 1/2 := by
    change eventProbability D (fun (z : BoundarySpaceW1 n) => ((z 0).val : ℝ) = 1) = 1/2 at h1
    have he : (fun (z : BoundarySpaceW1 n) => ((z 0).val : ℝ) = 1) = fun (z : BoundarySpaceW1 n) => z 0 = (1 : Fin 2) := by
      funext z
      exact propext (fin2_val_one_iff (z 0))
    rw [he] at h1
    exact h1
  have hp0 : eventProbability D (fun (z : BoundarySpaceW1 n) => z 0 = (0 : Fin 2)) = 1/2 := by
    change eventProbability D (fun (z : BoundarySpaceW1 n) => ((z 0).val : ℝ) = 0) = 1/2 at h0
    have he : (fun (z : BoundarySpaceW1 n) => ((z 0).val : ℝ) = 0) = fun (z : BoundarySpaceW1 n) => z 0 = (0 : Fin 2) := by
      funext z
      exact propext (fin2_val_zero_iff (z 0))
    rw [he] at h0
    exact h0
  fin_cases b
  · exact hp0
  · exact hp1

/-- Means of first-bit statistics are determined by its fair marginal alone. -/
lemma mean_first_bit (n : ℕ) (D : AtomicDesign (BoundarySpaceW1 n))
    (hm : BoundaryMarginsW1 n D) (f : Fin 2 → ℝ) :
    mean D (fun z => f (z 0)) = (f 0 + f 1) / 2 := by
  let P := Bridge.toProject D
  have hf : AronowAudit.P061.Integrable P (fun z => f (z 0)) := by
    unfold AronowAudit.P061.Integrable
    exact Summable.of_finite
  have hfib := AronowAudit.P061.expectation_fibers P (fun _ => True)
    (fun z => z 0) f (by simpa only [if_true] using hf)
  have hsum : AronowAudit.P061.expectation P (fun z => f (z 0)) =
      ∑ b : Fin 2, AronowAudit.P061.probability P (fun z => z 0 = b) * f b := by
    simpa only [if_true, true_and, tsum_fintype] using hfib
  rw [Bridge.mean_correspondence]
  rw [hsum]
  have hprob : ∀ b : Fin 2,
      AronowAudit.P061.probability P (fun z => z 0 = b) = 1/2 := by
    intro b
    rw [← Bridge.probability_correspondence]
    exact SAP.P061a.WH.W1.P.T5_L3.first_bit_probability n D hm b
  simp_rw [hprob]
  simp only [Fin.sum_univ_two]
  ring

end SAP.P061a.WH.W1.P.T5_L3

theorem SAP.P061a.WH.W1.T5_L3_proof : SAP.P061a.WH.W1.T5_L3 := by
  intro n D hm
  have hp0 := SAP.P061a.WH.W1.P.T5_L3.first_bit_probability n D hm (0 : Fin 2)
  have hp1 := SAP.P061a.WH.W1.P.T5_L3.first_bit_probability n D hm (1 : Fin 2)
  have hs : 0 < boundaryScaleW1 n := boundary_scale_posW1 n
  have hsle : boundaryScaleW1 n ≤ (1/2 : ℝ) := by
    have hn : (2 : ℝ) ≤ (n : ℝ) + 2 := by
      exact_mod_cast (show 2 ≤ n + 2 by omega)
    unfold boundaryScaleW1
    exact one_div_le_one_div_of_le (by norm_num) hn
  have htarget : boundaryTargetW1 n = (boundaryScaleW1 n)^2 := by
    unfold boundaryTargetW1 boundaryScaleW1
    field_simp
  have hcenter (z : BoundarySpaceW1 n) :
      boundaryEstimatorW1 n z - boundaryTargetW1 n =
        boundaryScaleW1 n * boundarySignW1 n z := by
    simp [boundaryEstimatorW1]
  have hraw (z : BoundarySpaceW1 n) :
      boundaryEstimatorW1 n z = (boundaryScaleW1 n)^2 +
        boundaryScaleW1 n * boundarySignW1 n z := by
    rw [boundaryEstimatorW1, htarget]
  have hsignsq (z : BoundarySpaceW1 n) : (boundarySignW1 n z)^2 = 1 := by
    have hcases := SAP.P061a.WH.W1.P.T5_L3.fin2_cases (z 0)
    rcases hcases with hz | hz
    · rw [boundarySignW1, hz]
      norm_num
    · rw [boundarySignW1, hz]
      norm_num
  have hformEstimator : (fun z => boundaryEstimatorW1 n z) = fun z =>
      boundaryTargetW1 n + boundaryScaleW1 n * (2 * (z 0).val - 1) := by
    funext z
    simp [boundaryEstimatorW1, boundarySignW1]
  have hmean : mean D (boundaryEstimatorW1 n) = boundaryTargetW1 n := by
    change mean D (fun z => boundaryEstimatorW1 n z) = boundaryTargetW1 n
    rw [hformEstimator]
    have hmfirst := SAP.P061a.WH.W1.P.T5_L3.mean_first_bit n D hm (fun b =>
      boundaryTargetW1 n + boundaryScaleW1 n * (2 * (b.val : ℝ) - 1))
    calc
      mean D (fun z => boundaryTargetW1 n + boundaryScaleW1 n * (2 * (z 0).val - 1)) =
          ((boundaryTargetW1 n + boundaryScaleW1 n * (2 * (0 : ℝ) - 1)) +
            (boundaryTargetW1 n + boundaryScaleW1 n * (2 * (1 : ℝ) - 1))) / 2 := by
        norm_num at hmfirst ⊢
        exact hmfirst
      _ = boundaryTargetW1 n := by norm_num; ring
  refine ⟨hmean, ?_, ?_, ?_, ?_⟩
  · rw [designVariance, hmean]
    have hvar := SAP.P061a.WH.W1.P.T5_L3.mean_first_bit n D hm (fun b =>
      (boundaryScaleW1 n * (2 * (b.val : ℝ) - 1))^2)
    have hform : (fun z => (boundaryEstimatorW1 n z - boundaryTargetW1 n)^2) =
        fun z => (boundaryScaleW1 n * (2 * (z 0).val - 1))^2 := by
      funext z
      rw [hcenter]
      rfl
    rw [hform]
    calc
      mean D (fun z => (boundaryScaleW1 n * (2 * (z 0).val - 1))^2) =
          ((boundaryScaleW1 n * (2 * ((0 : Fin 2).val : ℝ) - 1))^2 +
            (boundaryScaleW1 n * (2 * ((1 : Fin 2).val : ℝ) - 1))^2) / 2 := by
        norm_num at hvar ⊢
        exact hvar
      _ = (boundaryScaleW1 n)^2 := by norm_num
  · intro f
    have htest := SAP.P061a.WH.W1.P.T5_L3.mean_first_bit n D hm (fun b => f (2 * (b.val : ℝ) - 1))
    have hscore (z : BoundarySpaceW1 n) :
        (boundaryEstimatorW1 n z - boundaryTargetW1 n) / boundaryScaleW1 n =
          2 * (z 0).val - 1 := by
      rw [hcenter]
      have hn : boundaryScaleW1 n ≠ 0 := ne_of_gt hs
      field_simp [hn]
      unfold boundarySignW1
      ring
    have hform : (fun z => f ((boundaryEstimatorW1 n z - boundaryTargetW1 n) /
        boundaryScaleW1 n)) = fun z => f (2 * (z 0).val - 1) := by
      funext z
      rw [hscore]
    rw [hform]
    norm_num at htest ⊢
    exact htest
  · have hcover (z : BoundarySpaceW1 n) :
        |boundaryEstimatorW1 n z - boundaryTargetW1 n| ≤ boundaryScaleW1 n := by
      rw [hcenter, abs_mul, abs_of_pos hs]
      have hsign : |boundarySignW1 n z| = 1 := by
        have hcases := SAP.P061a.WH.W1.P.T5_L3.fin2_cases (z 0)
        rcases hcases with hz | hz
        · rw [boundarySignW1, hz]
          norm_num
        · rw [boundarySignW1, hz]
          norm_num
      rw [hsign, mul_one]
    have hevent : (fun z => |boundaryEstimatorW1 n z - boundaryTargetW1 n| ≤
        boundaryScaleW1 n) = fun _ : BoundarySpaceW1 n => True := by
      funext z
      simp [hcover z]
    rw [hevent]
    simp only [eventProbability, if_true]
    exact D.mass_total
  · have hs2le : (boundaryScaleW1 n)^2 ≤ boundaryScaleW1 n := by
      nlinarith [sq_nonneg (boundaryScaleW1 n), hs, hsle]
    have hleft : ∀ z, z 0 = 0 →
        |boundaryEstimatorW1 n z| ≤ boundaryScaleW1 n := by
      intro z hz
      have hsign : boundarySignW1 n z = -1 := by
        unfold boundarySignW1
        rw [hz]
        norm_num
      rw [hraw z, hsign]
      have hred : (boundaryScaleW1 n)^2 + boundaryScaleW1 n * (-1) =
          (boundaryScaleW1 n)^2 - boundaryScaleW1 n := by ring
      rw [hred]
      have hnonpos : (boundaryScaleW1 n)^2 - boundaryScaleW1 n ≤ 0 := by linarith
      rw [abs_of_nonpos hnonpos]
      nlinarith [sq_nonneg (boundaryScaleW1 n)]
    have hright : ∀ z, z 0 = 1 →
        boundaryScaleW1 n < |boundaryEstimatorW1 n z| := by
      intro z hz
      have hsign : boundarySignW1 n z = 1 := by
        unfold boundarySignW1
        rw [hz]
        norm_num
      rw [hraw z, hsign]
      have hred : (boundaryScaleW1 n)^2 + boundaryScaleW1 n * 1 =
          (boundaryScaleW1 n)^2 + boundaryScaleW1 n := by ring
      rw [hred, abs_of_pos (by positivity)]
      nlinarith [sq_pos_of_pos hs]
    have hevent : (fun z => |boundaryEstimatorW1 n z| ≤ boundaryScaleW1 n) =
        fun z => z 0 = 0 := by
      funext z
      apply propext
      by_cases hz : z 0 = 0
      · constructor
        · intro _
          exact hz
        · intro _
          exact hleft z hz
      · have hz1 : z 0 = 1 := by
          have hcases := SAP.P061a.WH.W1.P.T5_L3.fin2_cases (z 0)
          rcases hcases with hzero | hone
          · exact False.elim (hz hzero)
          · exact hone
        constructor
        · intro h
          exact False.elim ((not_lt_of_ge h) (hright z hz1))
        · intro hzero
          exact False.elim (hz hzero)
    rw [hevent]
    exact hp0

