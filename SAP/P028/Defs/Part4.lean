import SAP.P028.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
open Classical

structure Response (Ω : Type*) [MeasurableSpace Ω] where
  R : Ω → Bool
  measurableR : Measurable R

variable {Ω : Type*} [MeasurableSpace Ω]

def responseEvent (T : Response Ω) : Set Ω := {ω | T.R ω = true}

def responseArmMean (M : CausalModel Ω) (T : Response Ω) (z : Bool) : ℝ :=
  eventMean M.μ (observedY M) (armEvent M z ∩ responseEvent T)

def responseCellMean (M : CausalModel Ω) (T : Response Ω) (d z : Bool) : ℝ :=
  eventMean M.μ (observedY M) (cellEvent M d z ∩ responseEvent T)

def mixedMeanEqualities (M : CausalModel Ω) (T : Response Ω) : Prop :=
  (∀ z, responseArmMean M T z = armMean M z) ∧
  responseCellMean M T true false = cellMean M true false ∧
  responseCellMean M T false true = cellMean M false true

def mixedResponsePositive (M : CausalModel Ω) (T : Response Ω) : Prop :=
  (∀ z, 0 < M.μ.real (armEvent M z ∩ responseEvent T)) ∧
  0 < M.μ.real (cellEvent M true false ∩ responseEvent T) ∧
  0 < M.μ.real (cellEvent M false true ∩ responseEvent T)

def assignmentConditionalLaw (M : CausalModel Ω) (z : Bool) : Measure Ω :=
  (M.μ (armEvent M z))⁻¹ • M.μ.restrict (armEvent M z)

def reweightedCellMoment (M : CausalModel Ω) (T : Response Ω) (d z : Bool) : ℝ :=
  if 0 < cellProbability M d z then cellProbability M d z*responseCellMean M T d z else 0

def recordedOutcomeMoment (M : CausalModel Ω) (T : Response Ω) (d z : Bool) : ℝ :=
  eventMean M.μ (fun ω => realBit (T.R ω) *
    (if observedD M ω = d then observedY M ω else 0)) (armEvent M z)

def missingOutcomeProbability (M : CausalModel Ω) (T : Response Ω) (d z : Bool) : ℝ :=
  M.μ.real {ω | T.R ω = false ∧ observedD M ω = d ∧ M.Z ω = z} / M.μ.real (armEvent M z)

end
end SAP.P028
