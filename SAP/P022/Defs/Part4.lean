import Mathlib
import SAP.P022.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022
open scoped BigOperators Topology ENNReal NNReal
open Filter MeasureTheory
noncomputable section

-- SAP version of AronowAudit/P022/P022_Variance.lean:termRateCoefficient
def termRateCoefficient (θ ρ : ℝ) : Fin 8 → ℝ := fun i => match i.val with
  | 0 => (1 - θ * ρ) ^ 3 / (θ ^ 3 * ρ ^ 3)
  | 1 => 4 * (1 - θ * ρ) ^ 3 / (θ ^ 3 * ρ ^ 3)
  | 2 => (1 - θ * (1 - ρ)) ^ 3 / (θ ^ 3 * (1 - ρ) ^ 3)
  | 3 => 4 * (1 - θ * (1 - ρ)) ^ 3 / (θ ^ 3 * (1 - ρ) ^ 3)
  | 4 => 4 * (1 - θ * ρ) / (θ * ρ)
  | 5 => 4 * (1 - θ * (1 - ρ)) / (θ * (1 - ρ))
  | 6 => 4 * (1 - θ * ρ) / (θ * ρ)
  | _ => 4 * (1 - θ * (1 - ρ)) / (θ * (1 - ρ))

-- SAP version of AronowAudit/P022/P022_Variance.lean:cornerWitness
def cornerWitness : ExperimentSequence :=
  { reciprocalWitness with
    y1 := fun i => if i % 4 < 2 then 0 else 1
    y0 := fun i => if i % 2 = 0 then 0 else 1 }

-- SAP version of AronowAudit/P022/P022_Variance.lean:cornerLaw
def cornerLaw : JointLaw := ⟨
  (1 / 4 : ℝ≥0∞) • Measure.dirac (0, 0) +
  (1 / 4 : ℝ≥0∞) • Measure.dirac (0, 1) +
  (1 / 4 : ℝ≥0∞) • Measure.dirac (1, 0) +
  (1 / 4 : ℝ≥0∞) • Measure.dirac (1, 1), by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem,
      Set.mem_univ, smul_eq_mul, mul_one]
    have hq : (1 / 4 : ℝ≥0∞) = ((1 / 4 : ℝ≥0) : ℝ≥0∞) := by
      simpa using (ENNReal.coe_div (p := (1 : ℝ≥0)) (r := 4) (by norm_num)).symm
    rw [hq]
    norm_cast
    norm_num⟩

-- SAP version of AronowAudit/P022/P022_Variance.lean:zeroWitness
def zeroWitness : ExperimentSequence :=
  { reciprocalWitness with y1 := fun _ => 0, y0 := fun _ => 0 }

-- SAP version of AronowAudit/P022/P022_Variance.lean:empiricalCompatibleLaws
def empiricalCompatibleLaws {N : ℕ} (y1 y0 : Fin N → ℝ) : Set JointLaw :=
  {H | ∀ x, lawCDF H true x = empiricalCDF y1 x ∧
    lawCDF H false x = empiricalCDF y0 x}

/-- Existence conditions for the actual integrals and covariance extrema used in limiting formulas. -/
def LawFunctionalsDefined (H : JointLaw) : Prop :=
  (∀ J ∈ compatibleLaws H,
    (∀ t : Bool,
      Integrable (fun p : ℝ × ℝ => if t then p.1 else p.2) (J : Measure (ℝ × ℝ)) ∧
      Integrable (fun p : ℝ × ℝ => (if t then p.1 else p.2) ^ 2) (J : Measure (ℝ × ℝ)) ∧
      Integrable (fun p : ℝ × ℝ => ((if t then p.1 else p.2) - lawMean J t) ^ 2)
        (J : Measure (ℝ × ℝ))) ∧
    Integrable (fun p : ℝ × ℝ => (p.1 - lawMean J true) * (p.2 - lawMean J false))
      (J : Measure (ℝ × ℝ))) ∧
  (lawCovariance '' compatibleLaws H).Nonempty ∧
  BddAbove (lawCovariance '' compatibleLaws H) ∧
  BddBelow (lawCovariance '' compatibleLaws H)

/-- The real infimum defining the normal critical value is over a nonempty lower-bounded set. -/
def NormalCriticalDefined (α : ℝ) : Prop :=
  {x : ℝ | 1 - α / 2 ≤ normalCDF x}.Nonempty ∧
  BddBelow {x : ℝ | 1 - α / 2 ≤ normalCDF x}

end
end SAP.P022
