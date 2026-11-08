import SAP.P028.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
open Classical

variable {Ω : Type*} [MeasurableSpace Ω]

def mixedIdentification (M : CausalModel Ω) (T : Response Ω) : Prop :=
  complierMean M false =
    (responseArmMean M T false-cellProbability M true false*responseCellMean M T true false-
     cellProbability M false true*responseCellMean M T false true)/complierProbability M ∧
  complierMean M true = complierMean M false +
    (responseArmMean M T true-responseArmMean M T false)/complierProbability M

def cellReweighting (M : CausalModel Ω) (T : Response Ω) : Prop :=
  (∀ z, armMean M z = ∑ d : Bool, reweightedCellMoment M T d z) ∧
  complierMean M false =
    (reweightedCellMoment M T false false-reweightedCellMoment M T false true)/complierProbability M ∧
  complierMean M true =
    (reweightedCellMoment M T true true-reweightedCellMoment M T true false)/complierProbability M

def sensitivityBounds (M : CausalModel Ω) (T : Response Ω) : Prop :=
  (recordedOutcomeMoment M T false false-recordedOutcomeMoment M T false true-
    missingOutcomeProbability M T false true)/complierProbability M ≤ complierMean M false ∧
  complierMean M false ≤
    (recordedOutcomeMoment M T false false+missingOutcomeProbability M T false false-
     recordedOutcomeMoment M T false true)/complierProbability M ∧
  (recordedOutcomeMoment M T true true-recordedOutcomeMoment M T true false-
    missingOutcomeProbability M T true false)/complierProbability M ≤ complierMean M true ∧
  complierMean M true ≤
    (recordedOutcomeMoment M T true true+missingOutcomeProbability M T true true-
     recordedOutcomeMoment M T true false)/complierProbability M

def sourceTableCalculations : Prop :=
  ((167/495-130/505-26/505)/(2047/9999) : ℝ) = 1423/10235 ∧
  ((167/495+36/495-130/505)/(2047/9999) : ℝ) = 7633/10235 ∧
  ((110/505-40/495-1/495)/(2047/9999) : ℝ) = 6749/10235 ∧
  ((110/505+8/505-40/495)/(2047/9999) : ℝ) = 7642/10235 ∧
  ((207/458-(16/99)*(40/79)-(64/101)*(130/294))/(2047/9999) : ℝ) = 1594452863/3629163146 ∧
  ((207/458-(16/99)*(40/79)-(64/101)*(130/294))/(2047/9999)+(240/471-207/458)/(2047/9999) : ℝ) = 896530960/1244058109 ∧
  (((415/495)*(167/379)-(320/505)*(130/294))/(2047/9999) : ℝ) = 16568969/38014837 ∧
  (((185/505)*(110/177)-(80/495)*(40/79))/(2047/9999) : ℝ) = 295510/414829

def T2Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  (∀ (M : CausalModel Ω) (T : Response Ω), boundedOutcomes M →
    0 < complierProbability M ∧
    complierProbability M = 1-cellProbability M true false-cellProbability M false true ∧
    (complierProbability M*complierMean M false = jointOutcomeMoment M false false-jointOutcomeMoment M false true ∧
     complierProbability M*complierMean M true = jointOutcomeMoment M true true-jointOutcomeMoment M true false) ∧
    (0 < cellProbability M true false → 0 < cellProbability M false true →
      mixedResponsePositive M T → mixedMeanEqualities M T → mixedIdentification M T) ∧
    ((∀ z, 0 < M.μ.real (armEvent M z ∩ responseEvent T)) →
      (∀ z, IndepFun T.R (fun ω => (observedY M ω, observedD M ω)) (assignmentConditionalLaw M z)) →
      (∀ z, responseArmMean M T z = armMean M z) ∧
      (0 < cellProbability M true false → 0 < cellProbability M false true →
        mixedMeanEqualities M T ∧ mixedResponsePositive M T ∧ mixedIdentification M T)) ∧
    ((∀ d z, 0 < cellProbability M d z →
      0 < M.μ.real (cellEvent M d z ∩ responseEvent T) ∧
      responseCellMean M T d z = cellMean M d z) → cellReweighting M T) ∧
    sensitivityBounds M T) ∧ sourceTableCalculations

end
end SAP.P028
