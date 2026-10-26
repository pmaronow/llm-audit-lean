import AronowAudit.P018.Wave1.WeightedConsistency.M0

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

theorem m2_proof : M2.{u} := by
  intro g1 U _ k R X Y dir v C H hS hK N d t
  letI instUnitProbability : IsProbabilityMeasure R.μ := hS.1.1
  let i := if dir N d t then secondUnit d else firstUnit d
  let j := if dir N d t then firstUnit d else secondUnit d
  have hij : i ≠ j := by
    dsimp [i, j]
    split_ifs
    · exact (firstUnit_ne_secondUnit d).symm
    · exact firstUnit_ne_secondUnit d
  have hlaw := g1 R.μ i j hij
  have hx (ω : Fin N → U) : repeatedX R ω d t = X (ω i) (ω j) := by
    have hh := (hS.2.2.1 N d t (ω (firstUnit d)) (ω (secondUnit d))).1
    cases hd : dir N d t <;> simpa only [repeatedX, i, j, hd, Bool.false_eq_true, ↓reduceIte] using hh
  have hy (ω : Fin N → U) : repeatedY R ω d t = Y (ω i) (ω j) := by
    have hh := (hS.2.2.1 N d t (ω (firstUnit d)) (ω (secondUnit d))).2
    cases hd : dir N d t <;> simpa only [repeatedY, i, j, hd, Bool.false_eq_true, ↓reduceIte] using hh
  have hm : Measurable (fun ω : Fin N → U => (ω i, ω j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  constructor
  · ext a b
    change (∫ ω, repeatedX R ω d t a * repeatedX R ω d t b ∂repeatedLaw R N) = _
    simp_rw [hx]
    change _ = ∫ uv : U × U, X uv.1 uv.2 a * X uv.1 uv.2 b ∂R.μ.prod R.μ
    rw [← hlaw]
    exact (integral_map_of_stronglyMeasurable hm
      (((measurable_pi_apply a).comp hK.1).mul
        ((measurable_pi_apply b).comp hK.1)).stronglyMeasurable).symm
  · ext a
    change (∫ ω, repeatedY R ω d t * repeatedX R ω d t a ∂repeatedLaw R N) = _
    simp_rw [hx, hy]
    change _ = ∫ uv : U × U, Y uv.1 uv.2 * X uv.1 uv.2 a ∂R.μ.prod R.μ
    rw [← hlaw]
    exact (integral_map_of_stronglyMeasurable hm
      (hK.2.1.mul ((measurable_pi_apply a).comp hK.1)).stronglyMeasurable).symm

end
end AronowAudit.P018.Wave1.WeightedConsistency
