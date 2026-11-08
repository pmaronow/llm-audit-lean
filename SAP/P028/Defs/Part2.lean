import SAP.P028.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
open Classical

def treatment (s : Fin 3) (z : Bool) : Bool :=
  if s = 0 then true else if s = 1 then false else z

def realBit (b : Bool) : ℝ := if b then 1 else 0

structure CausalModel (Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  probability : IsProbabilityMeasure μ
  S : Ω → Fin 3
  Y : Bool → Ω → ℝ
  Z : Ω → Bool
  measurableS : Measurable S
  measurableY : ∀ d, Measurable (Y d)
  integrableY : ∀ d, Integrable (Y d) μ
  measurableZ : Measurable Z
  randomAssignment : IndepFun (fun ω => (S ω, Y false ω, Y true ω)) Z μ
  armPositive : ∀ z, 0 < μ.real {ω | Z ω = z}
  nonzeroFirstStage : (∫ ω, realBit (treatment (S ω) true) -
    realBit (treatment (S ω) false) ∂μ) ≠ 0

attribute [instance] CausalModel.probability

variable {Ω : Type*} [MeasurableSpace Ω]

def complierEvent (M : CausalModel Ω) : Set Ω := {ω | M.S ω = 2}

def alwaysEvent (M : CausalModel Ω) : Set Ω := {ω | M.S ω = 0}

def neverEvent (M : CausalModel Ω) : Set Ω := {ω | M.S ω = 1}

def noncomplierEvent (M : CausalModel Ω) : Set Ω := (complierEvent M)ᶜ

def armEvent (M : CausalModel Ω) (z : Bool) : Set Ω := {ω | M.Z ω = z}

def observedD (M : CausalModel Ω) (ω : Ω) : Bool := treatment (M.S ω) (M.Z ω)

def observedY (M : CausalModel Ω) (ω : Ω) : ℝ := M.Y (observedD M ω) ω

def eventMean (μ : Measure Ω) (f : Ω → ℝ) (E : Set Ω) : ℝ :=
  (∫ ω in E, f ω ∂μ) / μ.real E

def complierProbability (M : CausalModel Ω) : ℝ := M.μ.real (complierEvent M)

def armMean (M : CausalModel Ω) (z : Bool) : ℝ :=
  eventMean M.μ (observedY M) (armEvent M z)

def complierMean (M : CausalModel Ω) (d : Bool) : ℝ :=
  eventMean M.μ (M.Y d) (complierEvent M)

def noncomplierMean (M : CausalModel Ω) : ℝ :=
  eventMean M.μ (observedY M) (noncomplierEvent M)

def cace (M : CausalModel Ω) : ℝ :=
  eventMean M.μ (fun ω => M.Y true ω - M.Y false ω) (complierEvent M)

def boundedOutcomes (M : CausalModel Ω) : Prop :=
  ∀ d ω, 0 ≤ M.Y d ω ∧ M.Y d ω ≤ 1

def noncomplierContribution (M : CausalModel Ω) : ℝ :=
  (∫ ω in alwaysEvent M, M.Y true ω ∂M.μ) +
  (∫ ω in neverEvent M, M.Y false ω ∂M.μ)

def cellEvent (M : CausalModel Ω) (d z : Bool) : Set Ω :=
  {ω | observedD M ω = d ∧ M.Z ω = z}

def cellProbability (M : CausalModel Ω) (d z : Bool) : ℝ :=
  M.μ.real (cellEvent M d z) / M.μ.real (armEvent M z)

def cellMean (M : CausalModel Ω) (d z : Bool) : ℝ :=
  eventMean M.μ (observedY M) (cellEvent M d z)

def jointOutcomeMoment (M : CausalModel Ω) (d z : Bool) : ℝ :=
  eventMean M.μ (fun ω => if observedD M ω = d then observedY M ω else 0)
    (armEvent M z)

end
end SAP.P028
