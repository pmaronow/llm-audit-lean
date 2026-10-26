import AronowAudit.P044.Wave1.UnbiasednessBlueprint

namespace AronowAudit.P044.Wave1.Unbiasedness

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

/-- Transfer the rational star witness to the actual real assignment design. -/
theorem n2_proof : N2 := by
  classical
  intro h1
  let p : Fin 6 → ℚ := fun _ => 1 / 6
  let f : Fin 6 → Fin 4 → Exposure := fun r => exposure starAdj (starAssignments r)
  let w : Fin 4 → Exposure → ℚ := marginal p f
  let T : Fin 6 → ℚ := htContrast f starA w .d11 .d00

  -- Put the pushforward identity into the form needed by the rational-to-real adapters.
  have hpush (F : Assignment 4 → ℝ) :
      expect starMass F =
        expect (fun r : Fin 6 => (p r : ℝ)) (fun r => F (starAssignments r)) := by
    calc
      expect starMass F = (∑ r : Fin 6, F (starAssignments r)) / 6 := h1.2.2 F
      _ = expect (fun r : Fin 6 => (p r : ℝ))
          (fun r => F (starAssignments r)) := by
        simp only [expect, p, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
          ← Finset.mul_sum]
        ring

  -- Indicator instances identify all true marginals, including structural zeros.
  have hmarg (i : Fin 4) (a : Exposure) :
      marginal starMass (fun z => exposure starAdj z) i a = ((w i a : ℚ) : ℝ) := by
    calc
      marginal starMass (fun z => exposure starAdj z) i a =
          expect starMass (fun z => if exposure starAdj z i = a then 1 else 0) := by
        simp only [marginal, expect, mul_ite, mul_one, mul_zero]
      _ = expect (fun r : Fin 6 => (p r : ℝ))
          (fun r => if f r i = a then 1 else 0) :=
        hpush (fun z => if exposure starAdj z i = a then 1 else 0)
      _ = marginal (fun r : Fin 6 => (p r : ℝ)) f i a := by
        simp only [expect, marginal, mul_ite, mul_one, mul_zero]
      _ = ((w i a : ℚ) : ℝ) := ratCast_marginal p f i a
  have hweights :
      marginal starMass (fun z => exposure starAdj z) =
        fun i a => ((w i a : ℚ) : ℝ) := by
    funext i a
    exact hmarg i a

  have hcenter : w (0 : Fin 4) .d11 = (1 / 2 : ℚ) := by
    simpa [w, p, f] using star_counterexample.2.2.1 (0 : Fin 4) Exposure.d11
  have hleaf : w (1 : Fin 4) .d00 = (1 / 6 : ℚ) := by
    simpa [w, p, f] using star_counterexample.2.2.1 (1 : Fin 4) Exposure.d00
  have hT : expect p T = (1 / 4 : ℚ) := by
    simpa [T, w, p, f] using
      (star_counterexample.2.2.2.2.2.2 true).2.2.1

  have hstat (r : Fin 6) :
      htContrast (fun z => exposure starAdj z) yStar
        (marginal starMass (fun z => exposure starAdj z)) .d11 .d00
        (starAssignments r) = ((T r : ℚ) : ℝ) := by
    rw [hweights]
    change htContrast f (fun i a => ((starA i a : ℚ) : ℝ))
      (fun i a => ((w i a : ℚ) : ℝ)) .d11 .d00 r =
        ((htContrast f starA w .d11 .d00 r : ℚ) : ℝ)
    exact ratCast_htContrast f starA w .d11 .d00 r

  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨(0 : Fin 4), ?_⟩
    rw [hmarg, hcenter]
    norm_num
  · refine ⟨(1 : Fin 4), ?_⟩
    rw [hmarg, hleaf]
    norm_num
  · calc
      expect starMass (htContrast (fun z => exposure starAdj z) yStar
          (marginal starMass (fun z => exposure starAdj z)) .d11 .d00) =
          expect (fun r : Fin 6 => (p r : ℝ)) (fun r => ((T r : ℚ) : ℝ)) := by
        rw [hpush]
        unfold expect
        apply Finset.sum_congr rfl
        intro r _
        exact congrArg (fun v : ℝ => (p r : ℝ) * v) (hstat r)
      _ = ((expect p T : ℚ) : ℝ) := ratCast_expect p T
      _ = 1 / 4 := by rw [hT]; norm_num
  · calc
      tau yStar .d11 .d00 = ((tau starA .d11 .d00 : ℚ) : ℝ) :=
        ratCast_tau starA .d11 .d00
      _ = 0 := by rw [star_counterexample.2.2.2.2.1]; norm_num

end

end AronowAudit.P044.Wave1.Unbiasedness
