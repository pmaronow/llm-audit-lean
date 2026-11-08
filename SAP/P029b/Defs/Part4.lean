import Mathlib
import SAP.P029b.Defs.Part1
import SAP.P029b.Defs.Part2
import SAP.P029b.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b

universe u v

set_option linter.unusedVariables false
set_option warn.classDefReducibility false

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

def T25Statement : Prop :=
  
  (∀ {Ω : Type u} {X : Type v}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool)
    (hiv : IVAssumptions μ U Z),
    mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = true} -
      mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = false} =
        mP μ {ω | (U ω).complier} ∧
    mCE μ (fun ω => (U ω).outcome (Z ω)) {ω | Z ω = true} -
      mCE μ (fun ω => (U ω).outcome (Z ω)) {ω | Z ω = false} =
        (∫ ω, if (U ω).complier then (U ω).tau else 0 ∂μ) ∧
    (∫ ω, if (U ω).complier then (U ω).tau else 0 ∂μ) =
      mP μ {ω | (U ω).complier} * mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} ∧
    mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} = mWald μ U Z (fun _ => 1) ∧
    mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} =
      (mCE μ (fun ω => (U ω).outcome (Z ω)) {ω | Z ω = true} -
        mCE μ (fun ω => (U ω).outcome (Z ω)) {ω | Z ω = false}) /
      (mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = true} -
        mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = false})) ∧
  (∀ {n : ℕ} (Y : Fin n → ℝ) (D Z : Fin n → Bool)
    (hn1 : 0 < ∑ i, bit (Z i)) (hn0 : (∑ i, bit (Z i)) < (n : ℝ))
    (hstage : sampleArm (fun _ => 1) (fun i => bit (D i)) Z true -
      sampleArm (fun _ => 1) (fun i => bit (D i)) Z false ≠ 0),
    sampleWald (fun _ => 1) Y D Z = sampleCross Z Y / sampleCross Z (fun i => bit (D i))) ∧
  (((1/2*0 + 1/2*1)/(1/2+1/2) : ℝ) = 1/2 ∧
    ((1/2*(3/4)*0 + 1/2*(1/10)*1)/(1/2*(3/4)+1/2*(1/10)) : ℝ) = 2/17 ∧
    (115/1000 : ℝ) ≤ 2/17 ∧ (2/17 : ℝ) < 125/1000 ∧
    ((1/2*(3/4)*(1/(3/4))*0 + 1/2*(1/10)*(1/(1/10))*1)/
      (1/2*(3/4)*(1/(3/4)) + 1/2*(1/10)*(1/(1/10))) : ℝ) = 1/2)


def T26Statement : Prop :=
  
  (∀ {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → PotentialUnit X) (Z : Ω → Bool) (hiv : IVAssumptions μ U Z)
    (c m : X → ℝ) (hv : ScoreVersions μ U c m)
    (ε : ℝ) (he : 0 < ε) (hpos : ∀ᵐ ω ∂μ, ε < c (U ω).x ∧ c (U ω).x ≤ 1),
    mP μ {ω | (U ω).complier} * mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} =
      (∫ ω, c (U ω).x * m (U ω).x ∂μ) ∧
    mP μ {ω | (U ω).complier} = (∫ ω, c (U ω).x ∂μ) ∧
    (mArm μ Z (fun ω => 1/c (U ω).x) (fun ω => (U ω).outcome (Z ω)) true -
      mArm μ Z (fun ω => 1/c (U ω).x) (fun ω => (U ω).outcome (Z ω)) false) =
        (∫ ω, m (U ω).x ∂μ)/(∫ ω, 1/c (U ω).x ∂μ) ∧
    (mArm μ Z (fun ω => 1/c (U ω).x) (fun ω => bit ((U ω).receipt (Z ω))) true -
      mArm μ Z (fun ω => 1/c (U ω).x) (fun ω => bit ((U ω).receipt (Z ω))) false) =
        1/(∫ ω, 1/c (U ω).x ∂μ) ∧
    mWald μ U Z (fun ω => 1/c (U ω).x) = (∫ ω, m (U ω).x ∂μ) ∧
    (A1Versions μ U m → mWald μ U Z (fun ω => 1/c (U ω).x) = (∫ ω, (U ω).tau ∂μ))) ∧
  (∀ {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [TopologicalSpace X] [SecondCountableTopology X] [BorelSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ℕ → Ω → PotentialUnit X)
    (Z : ℕ → Ω → Bool) (c m : X → ℝ) (s : ℕ → ℕ → Ω → ℝ)
    (h : ICSWConditions μ U Z c m s) (a : X → ℝ)
    (ha : Measurable a)
    (haVersion : ∀ i, (fun ω => a (U i ω).x) =ᵐ[μ]
      condExp (covariateSigma (U i)) μ (fun ω => (U i ω).tau))
    (hA1 : ∀ x ∈ (Measure.map (fun ω => (U 0 ω).x) μ).support, m x = a x)
    (hA3 : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ (Measure.map (fun ω => (U 0 ω).x) μ).support,
      ε < c x ∧ c x ≤ 1)  (_ : RatiosEventuallyDefined μ U Z (fun n i ω => 1/s n i ω)),
    TendstoInMeasure μ (icswSequence U Z s) atTop (fun _ => ∫ ω, (U 0 ω).tau ∂μ))


def T27Statement : Prop :=
  
  (∀ {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool)
    (hiv : IVAssumptions μ U Z) (c m : X → ℝ) (hversions : ScoreVersions μ U c m)
    (hc : 0 < mP μ {ω | (U ω).complier}),
    complierCovariateLaw μ U =
      (Measure.map (fun ω => (U ω).x) μ).withDensity
        (fun x => ENNReal.ofReal (c x / mP μ {ω | (U ω).complier})) ∧
    mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} =
      ∫ x, m x ∂complierCovariateLaw μ U) ∧
  (∀ {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [TopologicalSpace X] [SecondCountableTopology X] [BorelSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ℕ → Ω → PotentialUnit X)
    (Z : ℕ → Ω → Bool) (c m : X → ℝ) (s : ℕ → ℕ → Ω → ℝ)
    (h : ICSWConditions μ U Z c m s)
    (hA3 : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ (Measure.map (fun ω => (U 0 ω).x) μ).support,
      ε < c x ∧ c x ≤ 1)  (_ : RatiosEventuallyDefined μ U Z (fun n i ω => 1/s n i ω)),
    TendstoInMeasure μ (icswSequence U Z s) atTop (fun _ => ∫ ω, m (U 0 ω).x ∂μ)) ∧
  (∀ {n : ℕ} (Y : Fin n → ℝ) (D Z : Fin n → Bool) (p : ℝ),
    0 < p → SampleDefined (fun _ => 1/p) D Z → SampleDefined (fun _ => 1) D Z →
    sampleWald (fun _ => 1/p) Y D Z = sampleWald (fun _ => 1) Y D Z)

end
end SAP.P029b
