import AronowAudit.P029.Wave1.LateIdentityBlueprint
import Mathlib.MeasureTheory.Measure.Real

namespace AronowAudit.P029.Wave1.LateIdentity

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

universe u v

noncomputable section

/-- Positive arm means agree with the independent fixed-response means. -/
theorem n3_proof : N3.{u, v} := by
  intro h1 h2 Ω X _ _ μ _ U Z hiv z
  have hreg := h2 μ U Z hiv
  obtain ⟨-, -, -, -, -, hZ, -, -, -, he0, he1, -, -⟩ := hiv
  have hcompl : {ω | Z ω = false} = {ω | Z ω = true}ᶜ := by
    ext ω
    cases hz : Z ω <;> simp [hz]
  have hfalse : mP μ {ω | Z ω = false} = 1 - mP μ {ω | Z ω = true} := by
    change μ.real {ω | Z ω = false} = 1 - μ.real {ω | Z ω = true}
    rw [hcompl, probReal_compl_eq_one_sub (hreg.1 true).2.2.2.2]
  have hzpos : 0 < mP μ {ω | Z ω = z} := by
    cases z with
    | false => rw [hfalse]; linarith
    | true => exact he0
  have hB : MeasurableSet {ω | Z ω = z} := (hreg.1 z).2.2.2.2
  have hDint :
      (∫ ω in {ω | Z ω = z}, bit ((U ω).receipt (Z ω)) ∂μ) =
        ∫ ω in {ω | Z ω = z}, bit ((U ω).receipt z) ∂μ := by
    apply setIntegral_congr_fun hB
    intro ω hω
    change Z ω = z at hω
    simp only [hω]
  have hYint :
      (∫ ω in {ω | Z ω = z}, (U ω).outcome (Z ω) ∂μ) =
        ∫ ω in {ω | Z ω = z}, (U ω).outcome z ∂μ := by
    apply setIntegral_congr_fun hB
    intro ω hω
    change Z ω = z at hω
    simp only [hω]
  refine ⟨?_, ?_, ?_⟩
  · calc
      mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = z} =
          mCE μ (fun ω => bit ((U ω).receipt z)) {ω | Z ω = z} := by
        simp only [mCE, hDint]
      _ = ∫ ω, bit ((U ω).receipt z) ∂μ :=
        h1 μ Z (fun ω => bit ((U ω).receipt z)) hZ (hreg.1 z).1
          (hreg.1 z).2.2.1 z hzpos
  · calc
      mCE μ (fun ω => (U ω).outcome (Z ω)) {ω | Z ω = z} =
          mCE μ (fun ω => (U ω).outcome z) {ω | Z ω = z} := by
        simp only [mCE, hYint]
      _ = ∫ ω, (U ω).outcome z ∂μ :=
        h1 μ Z (fun ω => (U ω).outcome z) hZ (hreg.1 z).2.1
          (hreg.1 z).2.2.2.1 z hzpos
  · have hconst : (∫ _ in {ω | Z ω = z}, (1 : ℝ) ∂μ) =
        mP μ {ω | Z ω = z} := by
      simpa only [smul_eq_mul, mul_one, mP, measureReal_def] using
        (setIntegral_const (μ := μ) (s := {ω | Z ω = z}) (1 : ℝ))
    unfold mCE
    rw [hconst, div_self (ne_of_gt hzpos)]

end

end AronowAudit.P029.Wave1.LateIdentity
