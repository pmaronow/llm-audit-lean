import AronowAudit.P001.Wave1.SieveRateBlueprint
import AronowAudit.P001.Wave1.SieveRate.N17

/-!
# Integrating the fixed-design Gaussian bound

All probability comparisons before the final line take place in ENNReal. Thus the
Fubini step is a nonnegative integral and requires no inverse-Gram integrability.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

theorem n19_proof : N19 := by
  classical
  intro hN1 hN18 hN16 hN17 hfixed t ht
  letI : IsProbabilityMeasure sieveMu := hN1.1
  letI : IsProbabilityMeasure (unifVec (t ^ 4)) := by unfold unifVec; infer_instance
  letI : IsProbabilityMeasure (gaussVec (t ^ 4)) := by unfold gaussVec; infer_instance
  have hn : 2 ≤ t ^ 4 := by
    have hpow : (2 : ℕ) ^ 4 ≤ t ^ 4 := Nat.pow_le_pow_left (by omega : 2 ≤ t) 4
    norm_num at hpow
    omega
  have hfirst : Measurable (firstN (t ^ 4)) := by
    apply Measurable.prodMk
    · exact Measurable.of_eval fun i : Fin (t ^ 4) =>
        measurable_fst.comp (measurable_pi_apply (i : ℕ))
    · exact Measurable.of_eval fun i : Fin (t ^ 4) =>
        measurable_snd.comp (measurable_pi_apply (i : ℕ))
  have hmap : sieveMu (firstN (t ^ 4) ⁻¹' badSet t) =
      ((unifVec (t ^ 4)).prod (gaussVec (t ^ 4))) (badSet t) := by
    rw [← Measure.map_apply hfirst (hN17 t), hN18 hN1 (t ^ 4)]
  have hsection (x : Fin (t ^ 4) → ℝ) (hx : x ∈ designSet (t ^ 4)) :
      Prod.mk x ⁻¹' badSet t =
        {y | 1 < regionInt (olsPoly (t ^ 3) x y) (olsPoly (t ^ 3) x y)} := by
    ext y
    simp only [Set.mem_preimage, badSet, Set.mem_setOf_eq, hx, true_and]
  have hpoint (x : Fin (t ^ 4) → ℝ) (hx : x ∈ designSet (t ^ 4)) :
      ENNReal.ofReal ((1 : ℝ) / 12) ≤
        (gaussVec (t ^ 4)) (Prod.mk x ⁻¹' badSet t) := by
    apply (ENNReal.ofReal_le_iff_le_toReal
      (measure_ne_top (gaussVec (t ^ 4)) _)).2
    rw [hsection x hx]
    exact hfixed t ht x hx
  have hint :
      (∫⁻ x, (designSet (t ^ 4)).indicator
        (fun _ => ENNReal.ofReal ((1 : ℝ) / 12)) x ∂(unifVec (t ^ 4))) ≤
      ∫⁻ x, (gaussVec (t ^ 4)) (Prod.mk x ⁻¹' badSet t) ∂(unifVec (t ^ 4)) := by
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ designSet (t ^ 4)
    · rw [Set.indicator_of_mem hx]
      exact hpoint x hx
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  have hfubini : ENNReal.ofReal ((1 : ℝ) / 12) *
      (unifVec (t ^ 4)) (designSet (t ^ 4)) ≤
      ((unifVec (t ^ 4)).prod (gaussVec (t ^ 4))) (badSet t) := by
    rw [Measure.prod_apply (hN17 t)]
    calc
      ENNReal.ofReal ((1 : ℝ) / 12) * (unifVec (t ^ 4)) (designSet (t ^ 4)) =
          ∫⁻ x, (designSet (t ^ 4)).indicator
            (fun _ => ENNReal.ofReal ((1 : ℝ) / 12)) x ∂(unifVec (t ^ 4)) :=
        (lintegral_indicator_const (measurableSet_designSet (t ^ 4)) _).symm
      _ ≤ ∫⁻ x, (gaussVec (t ^ 4)) (Prod.mk x ⁻¹' badSet t) ∂(unifVec (t ^ 4)) := hint
  have hdesign : ENNReal.ofReal ((1 : ℝ) / 6) ≤
      (unifVec (t ^ 4)) (designSet (t ^ 4)) :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top (unifVec (t ^ 4)) _)).2 (hN16 _ hn)
  have hconst : ENNReal.ofReal ((1 : ℝ) / 72) =
      ENNReal.ofReal ((1 : ℝ) / 12) * ENNReal.ofReal ((1 : ℝ) / 6) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 12)]
    congr 1
    norm_num
  have hlower : ENNReal.ofReal ((1 : ℝ) / 72) ≤
      ((unifVec (t ^ 4)).prod (gaussVec (t ^ 4))) (badSet t) := by
    calc
      ENNReal.ofReal ((1 : ℝ) / 72) =
          ENNReal.ofReal ((1 : ℝ) / 12) * ENNReal.ofReal ((1 : ℝ) / 6) := hconst
      _ ≤ ENNReal.ofReal ((1 : ℝ) / 12) * (unifVec (t ^ 4)) (designSet (t ^ 4)) :=
        by gcongr
      _ ≤ ((unifVec (t ^ 4)).prod (gaussVec (t ^ 4))) (badSet t) := hfubini
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top sieveMu _)).1
  rw [hmap]
  exact hlower

end

end AronowAudit.P001.Wave1.SieveRate
