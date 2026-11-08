import Mathlib
import SAP.P028.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

universe u

/-- Section 2's monotone, randomized, exclusion model, without moments for unused
counterfactual outcomes. The three strata encode exactly the three monotone
binary treatment pairs. Finiteness of the four means used in Corollary 1 is
specified separately by `T9FiniteCells`. -/
structure T9Model (Ω : Type u) [MeasurableSpace Ω] where
  μ : Measure Ω
  probability : IsProbabilityMeasure μ
  S : Ω → Fin 3
  Y : Bool → Ω → ℝ
  Z : Ω → Bool
  measurableS : Measurable S
  measurableY : ∀ d, Measurable (Y d)
  measurableZ : Measurable Z
  randomAssignment : IndepFun (fun ω => (S ω, Y false ω, Y true ω)) Z μ
  armPositive : ∀ z, 0 < μ.real {ω | Z ω = z}
  nonzeroFirstStage : (∫ ω, realBit (treatment (S ω) true) -
    realBit (treatment (S ω) false) ∂μ) ≠ 0

attribute [instance] T9Model.probability

namespace T9Model

variable {Ω : Type u} [MeasurableSpace Ω]

def complierEvent (M : T9Model Ω) : Set Ω := {ω | M.S ω = 2}
def alwaysEvent (M : T9Model Ω) : Set Ω := {ω | M.S ω = 0}
def neverEvent (M : T9Model Ω) : Set Ω := {ω | M.S ω = 1}
def noncomplierEvent (M : T9Model Ω) : Set Ω := M.complierEventᶜ
def armEvent (M : T9Model Ω) (z : Bool) : Set Ω := {ω | M.Z ω = z}
def observedD (M : T9Model Ω) (ω : Ω) : Bool := treatment (M.S ω) (M.Z ω)
def observedY (M : T9Model Ω) (ω : Ω) : ℝ := M.Y (M.observedD ω) ω
def cellEvent (M : T9Model Ω) (d z : Bool) : Set Ω :=
  {ω | M.observedD ω = d ∧ M.Z ω = z}
def complierProbability (M : T9Model Ω) : ℝ := M.μ.real M.complierEvent
def armMean (M : T9Model Ω) (z : Bool) : ℝ :=
  eventMean M.μ M.observedY (M.armEvent z)
def complierMean (M : T9Model Ω) (d : Bool) : ℝ :=
  eventMean M.μ (M.Y d) M.complierEvent
def noncomplierMean (M : T9Model Ω) : ℝ :=
  eventMean M.μ M.observedY M.noncomplierEvent
def cellProbability (M : T9Model Ω) (d z : Bool) : ℝ :=
  M.μ.real (M.cellEvent d z) / M.μ.real (M.armEvent z)
def cellMean (M : T9Model Ω) (d z : Bool) : ℝ :=
  eventMean M.μ M.observedY (M.cellEvent d z)

end T9Model

/-- The four ordinary finite means in the corollary's premise exist. Positivity
guards their denominators; integrability is required only on observed cells. -/
def T9FiniteCells {Ω : Type u} [MeasurableSpace Ω] (M : T9Model Ω) : Prop :=
  ∀ d z, 0 < M.μ.real (M.cellEvent d z) ∧
    IntegrableOn M.observedY (M.cellEvent d z) M.μ

/-- Reconstruct an assignment-arm mean from its two observed cell summaries. -/
def t9ArmFromCells (π m : Bool → Bool → ℝ) (z : Bool) : ℝ :=
  ∑ d : Bool, π d z * m d z

/-- The observable treatment first stage. Its positivity is proved below. -/
def t9MassFromCells (π : Bool → Bool → ℝ) : ℝ := π true true - π true false

/-- The displayed complier-mean formula as a function of the eight known cell
numbers alone. The whole statement proves its denominator positive. -/
def t9MeanFromCells (π m : Bool → Bool → ℝ) (d : Bool) : ℝ :=
  (t9ArmFromCells π m d - π true false * m true false -
    π false true * m false true) / t9MassFromCells π

/-- All probabilistic identities and existence assertions used in the corollary
and its printed substitution argument. No unused counterfactual moment occurs. -/
structure T9Conclusions {Ω : Type u} [MeasurableSpace Ω] (M : T9Model Ω) : Prop where
  observed_integrable : Integrable M.observedY M.μ
  complier_integrable : ∀ d, IntegrableOn (M.Y d) M.complierEvent M.μ
  always_integrable : IntegrableOn (M.Y true) M.alwaysEvent M.μ
  never_integrable : IntegrableOn (M.Y false) M.neverEvent M.μ
  noncomplier_integrable : IntegrableOn M.observedY M.noncomplierEvent M.μ
  complier_positive : 0 < M.complierProbability
  always_positive : 0 < M.μ.real M.alwaysEvent
  never_positive : 0 < M.μ.real M.neverEvent
  noncomplier_positive : 0 < M.μ.real M.noncomplierEvent
  pure_sum_positive : 0 < M.cellProbability true false + M.cellProbability false true
  arm_reconstruction : ∀ z,
    M.armMean z = t9ArmFromCells M.cellProbability M.cellMean z
  always_probability : M.cellProbability true false = M.μ.real M.alwaysEvent
  never_probability : M.cellProbability false true = M.μ.real M.neverEvent
  complier_probability :
    M.complierProbability = 1 - M.cellProbability true false - M.cellProbability false true
  noncomplier_probability :
    M.μ.real M.noncomplierEvent = M.cellProbability true false + M.cellProbability false true
  observable_first_stage : M.complierProbability = t9MassFromCells M.cellProbability
  always_mean : M.cellMean true false = eventMean M.μ (M.Y true) M.alwaysEvent
  never_mean : M.cellMean false true = eventMean M.μ (M.Y false) M.neverEvent
  noncomplier_mean : M.noncomplierMean =
    (M.cellProbability true false * M.cellMean true false +
      M.cellProbability false true * M.cellMean false true) /
    (M.cellProbability true false + M.cellProbability false true)
  mixture : ∀ z, M.complierProbability * M.complierMean z +
    (1 - M.complierProbability) * M.noncomplierMean = M.armMean z
  control_mean : M.complierMean false =
    (M.armMean false - M.cellProbability true false * M.cellMean true false -
      M.cellProbability false true * M.cellMean false true) / M.complierProbability
  treated_shift : M.complierMean true = M.complierMean false +
    (M.armMean true - M.armMean false) / M.complierProbability
  treated_mean : M.complierMean true =
    (M.armMean true - M.cellProbability true false * M.cellMean true false -
      M.cellProbability false true * M.cellMean false true) / M.complierProbability
  identified_mean : ∀ d,
    M.complierMean d = t9MeanFromCells M.cellProbability M.cellMean d

/-- P028-T9; Corollary 1, Section 3, p. 678 (PDF p. 2), and its proof,
p. 679 (PDF p. 3), under the Section 2 assumptions.
The four ordinary finite treatment-assignment cell means and probabilities
determine both complier average potential outcomes. They reconstruct the arm
means and positive complier probability, the pure-stratum means and masses,
the printed noncomplier ratio, both mixture equations, and both displayed
complier formulas. Any two models with the same eight cell summaries have the
same complier means. The usual measure-theoretic conditions are assumed;
only observed cell moments are required, with no moment condition on unused
counterfactual outcomes. Positive conditioning events express existence of the
ordinary means in the premise. -/
def T9WholeStatement : Prop :=
  (∀ (Ω : Type u) [MeasurableSpace Ω] (M : T9Model Ω),
    T9FiniteCells M → T9Conclusions M) ∧
  (∀ (Ω Ξ : Type u) [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (M : T9Model Ω) (N : T9Model Ξ), T9FiniteCells M → T9FiniteCells N →
    (∀ d z, M.cellProbability d z = N.cellProbability d z) →
    (∀ d z, M.cellMean d z = N.cellMean d z) →
    ∀ d, M.complierMean d = N.complierMean d)

end

end SAP.P028
