import AronowAudit.P001.Wave1.SieveRateBlueprint
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Polynomial

/-! # SieveRate N7: integral Cauchy–Schwarz on the fixed region -/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

theorem n7_proof : N7 := by
  intro p r hr
  let lam : ℝ := regionInt p r / regionInt r r
  have hpp : IntegrableOn (fun z : ℝ => p.eval z * p.eval z)
      (Set.Icc (0 : ℝ) (1 / 2)) :=
    (p.continuous.mul p.continuous).integrableOn_Icc
  have hpr : IntegrableOn (fun z : ℝ => p.eval z * r.eval z)
      (Set.Icc (0 : ℝ) (1 / 2)) :=
    (p.continuous.mul r.continuous).integrableOn_Icc
  have hrr : IntegrableOn (fun z : ℝ => r.eval z * r.eval z)
      (Set.Icc (0 : ℝ) (1 / 2)) :=
    (r.continuous.mul r.continuous).integrableOn_Icc

  have hexpand :
      (∫ z in Set.Icc (0 : ℝ) (1 / 2), (p.eval z - lam * r.eval z) ^ 2) =
        regionInt p p - (2 * lam) * regionInt p r + lam ^ 2 * regionInt r r := by
    calc
      (∫ z in Set.Icc (0 : ℝ) (1 / 2), (p.eval z - lam * r.eval z) ^ 2) =
          ∫ z in Set.Icc (0 : ℝ) (1 / 2),
            (p.eval z * p.eval z - (2 * lam) * (p.eval z * r.eval z)) +
              lam ^ 2 * (r.eval z * r.eval z) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z => by ring)
      _ = _ := by
        have hsub : IntegrableOn (fun z : ℝ => p.eval z * p.eval z -
            (2 * lam) * (p.eval z * r.eval z)) (Set.Icc (0 : ℝ) (1 / 2)) :=
          hpp.sub (hpr.const_mul (2 * lam))
        rw [integral_add hsub
          (hrr.const_mul (lam ^ 2)),
          integral_sub hpp (hpr.const_mul (2 * lam)),
          integral_const_mul, integral_const_mul]
        rfl

  have hnonneg :
      0 ≤ ∫ z in Set.Icc (0 : ℝ) (1 / 2), (p.eval z - lam * r.eval z) ^ 2 :=
    setIntegral_nonneg measurableSet_Icc (fun z _ => sq_nonneg _)
  have halgebra :
      regionInt p p - (2 * lam) * regionInt p r + lam ^ 2 * regionInt r r =
        regionInt p p - regionInt p r ^ 2 / regionInt r r := by
    dsimp only [lam]
    field_simp [ne_of_gt hr] <;> ring
  rw [hexpand, halgebra] at hnonneg
  exact sub_nonneg.mp hnonneg

end

end AronowAudit.P001.Wave1.SieveRate
