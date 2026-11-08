import SAP.P028.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
open Classical

def missingAssumptions : Prop :=
  finiteValid lowerLaw ∧ finiteValid upperLaw ∧
    fpc lowerLaw = 2047/9999 ∧ fpc upperLaw = 2047/9999 ∧
    assignmentMass false = 99/200 ∧ assignmentMass true = 101/200 ∧
    0 < assignmentMass false ∧ 0 < assignmentMass true

def missingCells : Prop :=
  (∀ z d v, recordedCell lowerLaw z d v = recordedCount z d v / armCount z ∧
                recordedCell upperLaw z d v = recordedCount z d v / armCount z) ∧
    (∀ z d, missingCell lowerLaw z d = missingCount z d / armCount z ∧
              missingCell upperLaw z d = missingCount z d / armCount z)

def missingCounterexample : Prop :=
  finiteValid lowerLaw ∧ finiteValid upperLaw ∧
    observedLaw lowerLaw = observedLaw upperLaw ∧
    fcy lowerLaw false = 1423/10235 ∧ fcy lowerLaw true = 6749/10235 ∧
    fcy upperLaw false = 7633/10235 ∧ fcy upperLaw true = 7642/10235 ∧
    fcy lowerLaw false ≠ fcy upperLaw false ∧ fcy lowerLaw true ≠ fcy upperLaw true

def missingMoments : Prop :=
  (∀ M ∈ [lowerLaw, upperLaw],
      ftakeup M true false = 16/99 ∧ ftakeup M false true = 64/101 ∧
      respondentArmMean M false = 207/458 ∧ respondentArmMean M true = 240/471 ∧
      respondentCellMean M true false = 40/79 ∧ respondentCellMean M false true = 130/294) ∧
    fey lowerLaw false = 208/495 ∧ fey lowerLaw true = 266/505 ∧
    fey upperLaw false = 27/55 ∧ fey upperLaw true = 248/505

def missingCorollaryComparison : Prop :=
  fullCorollary lowerLaw = (1423/10235,6749/10235) ∧
    fullCorollary upperLaw = (7633/10235,7642/10235) ∧
    respondentCorollary lowerLaw = (1594452863/3629163146,896530960/1244058109) ∧
    respondentCorollary upperLaw = (1594452863/3629163146,896530960/1244058109) ∧
    respondentCorollary lowerLaw ≠ (fcy lowerLaw false,fcy lowerLaw true) ∧
    respondentCorollary upperLaw ≠ (fcy upperLaw false,fcy upperLaw true)

def missingJointProbability : Prop :=
  (∑ i : Fin 17, ∑ z : Bool, jointMass lowerLaw i z) = 1 ∧
    (∑ i : Fin 17, ∑ z : Bool, jointMass upperLaw i z) = 1 ∧
    (∀ i z, 0 < jointMass lowerLaw i z) ∧ (∀ i z, 0 < jointMass upperLaw i z)

def finiteMeanDomain (M : BinaryLaw) : Prop :=
  (∀ z, 0 < fprob M (fun i => fr (M.atom i) z = true)) ∧
  (∀ d z, 0 < fprob M (fun i => fd (M.atom i) z = d)) ∧
  (∀ d z, 0 < fprob M (fun i => fd (M.atom i) z = d ∧ fr (M.atom i) z = true))

def T1Statement : Prop :=
  missingAssumptions ∧ missingJointProbability ∧
  (∀ M ∈ [lowerLaw, upperLaw], finiteMeanDomain M) ∧
  (∀ M ∈ [lowerLaw, upperLaw], ∀ (E : Fin 17 → Prop) (z : Bool),
    (∑ i, if E i then jointMass M i z else 0) = fprob M E * assignmentMass z) ∧
  missingCells ∧ missingCounterexample ∧ missingMoments ∧ missingCorollaryComparison ∧
  (∀ d, ¬ ∃ F : (Bool × Bool × Bool × Bool → ℚ) → ℚ,
    ∀ M : BinaryLaw, finiteValid M → F (observedLaw M) = fcy M d)

end
end SAP.P028
