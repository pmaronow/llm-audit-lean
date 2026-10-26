import AronowAudit.P004.Wave1.AreaSumBlueprint
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Measurability and binary values of the actual angular-sector outcome field. -/

namespace AronowAudit.P004.Wave1.AreaSum

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- The coordinate map to the complex plane is continuous; only its argument needs the
Borel (rather than continuous) argument-map theorem. -/
theorem angularFraction_measurable (c : EuclideanSpace ℝ (Fin 2)) :
    Measurable (angularFraction c) := by
  classical
  have hcoord (k : Fin 2) :
      Measurable (fun x : EuclideanSpace ℝ (Fin 2) => x k) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) k).measurable
  have hre : Measurable (fun x : EuclideanSpace ℝ (Fin 2) =>
      ((x 0 - c 0 : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp ((hcoord 0).sub_const (c 0))
  have him : Measurable (fun x : EuclideanSpace ℝ (Fin 2) =>
      ((x 1 - c 1 : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp ((hcoord 1).sub_const (c 1))
  have harg : Measurable (fun x : EuclideanSpace ℝ (Fin 2) =>
      Complex.arg (((x 0 - c 0 : ℝ) : ℂ) +
        ((x 1 - c 1 : ℝ) : ℂ) * Complex.I)) :=
    Complex.measurable_arg.comp (hre.add (him.mul_const Complex.I))
  have hneg : MeasurableSet {x : EuclideanSpace ℝ (Fin 2) |
      Complex.arg (((x 0 - c 0 : ℝ) : ℂ) +
        ((x 1 - c 1 : ℝ) : ℂ) * Complex.I) < 0} :=
    measurableSet_lt harg measurable_const
  unfold angularFraction
  dsimp only
  refine Measurable.div_const ?_ (2 * Real.pi)
  exact Measurable.ite hneg (harg.add_const (2 * Real.pi)) harg

/-- The radial branch of the share is measurable for each fixed own treatment. -/
theorem areaBinaryShare_measurable (c : EuclideanSpace ℝ (Fin 2)) (a : Bool) :
    Measurable (fun x => areaBinaryShare c x a) := by
  classical
  cases a with
  | false =>
      change Measurable (fun _ : EuclideanSpace ℝ (Fin 2) => (1 / 10 : ℝ))
      exact measurable_const
  | true =>
      change Measurable (fun x : EuclideanSpace ℝ (Fin 2) =>
        if dist x c ≤ 1 then (1 / 50 : ℝ) else 273 / 2500)
      exact Measurable.ite
        (measurableSet_le (measurable_id.dist measurable_const) measurable_const)
        measurable_const measurable_const

/-- Borel measurability of the closed central disk and half-open outer annuli. -/
theorem measurableSet_bin (c : EuclideanSpace ℝ (Fin 2)) (j : ℕ) :
    MeasurableSet (bin c j) := by
  classical
  unfold bin
  split_ifs
  · exact measurableSet_closedBall
  · exact (measurableSet_lt measurable_const
      (measurable_id.dist measurable_const)).inter
      (measurableSet_le (measurable_id.dist measurable_const) measurable_const)

theorem a6_proof : A6 := by
  classical
  refine ⟨?_, ?_, angularFraction_measurable⟩
  · intro x z
    dsimp only [areaBinaryPopulation]
    split_ifs <;> norm_num
  · intro z
    have hsector (c : EuclideanSpace ℝ (Fin 2)) (a : Bool) :
        Measurable (fun x =>
          if angularFraction c x < areaBinaryShare c x a then (1 : ℝ) else 0) :=
      Measurable.ite
        (measurableSet_lt (angularFraction_measurable c)
          (areaBinaryShare_measurable c a)) measurable_const measurable_const
    dsimp only [areaBinaryPopulation]
    exact Measurable.ite
      (measurableSet_le (measurable_id.dist measurable_const) measurable_const)
      (hsector (areaBinaryCenter 0) (z 0))
      (Measurable.ite
        (measurableSet_le (measurable_id.dist measurable_const) measurable_const)
        (hsector (areaBinaryCenter 1) (z 1)) measurable_const)

end
end AronowAudit.P004.Wave1.AreaSum
