import AronowAudit.P031.Wave1.LargeSampleRefutationBlueprint
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! The iid CLT on the auxiliary infinite fair-coin product space.
The two moment calculations take place on `Fin 2`, before pulling them back
by a coordinate projection. No finite-population CLT is used. -/

namespace AronowAudit.P031.Wave1.LargeSampleRefutation
noncomputable section
open scoped BigOperators Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

theorem n6_proof : N6 := by
  let μ₂ : Measure (Fin 2) := (PMF.uniformOfFintype (Fin 2)).toMeasure
  let X : ℕ → (ℕ → Fin 2) → ℝ := fun j ω => sgn2 (ω j)
  have hsgn : Measurable sgn2 := measurable_of_finite _
  have hsgnSq : Measurable (fun d : Fin 2 => sgn2 d ^ 2) :=
    measurable_of_finite _
  have hcoord (j : ℕ) :
      coinMeasure.map (fun ω : ℕ → Fin 2 => ω j) = μ₂ := by
    exact Measure.infinitePi_map_eval
      (fun _ : ℕ => (PMF.uniformOfFintype (Fin 2)).toMeasure) j

  have hμ₀ : (∫ d : Fin 2, sgn2 d ∂μ₂) = 0 := by
    dsimp only [μ₂]
    rw [PMF.integral_eq_sum]
    norm_num [Fin.sum_univ_two, sgn2, PMF.uniformOfFintype_apply, smul_eq_mul]
  have hμ₁ : (∫ d : Fin 2, sgn2 d ^ 2 ∂μ₂) = 1 := by
    dsimp only [μ₂]
    rw [PMF.integral_eq_sum]
    norm_num [Fin.sum_univ_two, sgn2, PMF.uniformOfFintype_apply, smul_eq_mul]

  have h₀ : (∫ ω, X 0 ω ∂coinMeasure) = 0 := by
    calc
      (∫ ω, X 0 ω ∂coinMeasure) =
          ∫ d : Fin 2, sgn2 d ∂(coinMeasure.map (fun ω : ℕ → Fin 2 => ω 0)) := by
        exact
          (integral_map (μ := coinMeasure) (φ := fun ω : ℕ → Fin 2 => ω 0)
            (measurable_pi_apply 0).aemeasurable
            hsgn.aestronglyMeasurable).symm
      _ = ∫ d : Fin 2, sgn2 d ∂μ₂ := by rw [hcoord 0]
      _ = 0 := hμ₀
  have h₁ : (∫ ω, (X 0 ^ 2) ω ∂coinMeasure) = 1 := by
    calc
      (∫ ω, (X 0 ^ 2) ω ∂coinMeasure) =
          ∫ d : Fin 2, sgn2 d ^ 2
            ∂(coinMeasure.map (fun ω : ℕ → Fin 2 => ω 0)) := by
        exact
          (integral_map (μ := coinMeasure) (φ := fun ω : ℕ → Fin 2 => ω 0)
            (measurable_pi_apply 0).aemeasurable
            hsgnSq.aestronglyMeasurable).symm
      _ = ∫ d : Fin 2, sgn2 d ^ 2 ∂μ₂ := by rw [hcoord 0]
      _ = 1 := hμ₁

  have hindep : ProbabilityTheory.iIndepFun X coinMeasure := by
    exact ProbabilityTheory.iIndepFun_infinitePi
      (P := fun _ : ℕ => (PMF.uniformOfFintype (Fin 2)).toMeasure)
      (X := fun _ : ℕ => sgn2) (fun _ => hsgn)
  have hident (j : ℕ) :
      ProbabilityTheory.IdentDistrib (X j) (X 0) coinMeasure coinMeasure := by
    have hproj : ProbabilityTheory.IdentDistrib
        (fun ω : ℕ → Fin 2 => ω j) (fun ω : ℕ → Fin 2 => ω 0)
        coinMeasure coinMeasure :=
      { aemeasurable_fst := (measurable_pi_apply j).aemeasurable
        aemeasurable_snd := (measurable_pi_apply 0).aemeasurable
        map_eq := (hcoord j).trans (hcoord 0).symm }
    exact hproj.comp hsgn
  have hY : ProbabilityTheory.HasLaw (fun z : ℝ => z)
      (ProbabilityTheory.gaussianReal 0 1) (ProbabilityTheory.gaussianReal 0 1) :=
    ProbabilityTheory.HasLaw.id
  exact ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum
    hY h₀ h₁ hindep hident

end
end AronowAudit.P031.Wave1.LargeSampleRefutation
