import Mathlib
import SAP.P026b.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026b
open Finset
open scoped BigOperators
noncomputable section

def logitEstimate : (Fin 6 × Fin 15) → ℝ :=
  ht realTableDesign 16 tableLogitResidual tableLogitResidual

def logitVarianceEstimate : (Fin 6 × Fin 15) → ℝ :=
  printedVariance realTableDesign 16 tableLogitResidual tableLogitResidual

/-- The ten rows of the Logit column; RMSE is the square root of mean squared error. -/
def logitColumn : Fin 10 → ℝ :=
  let Δ := ate 16 (fun i : Fin 16 => (tableY i : ℝ)) (fun i => (tableY i : ℝ))
  let μ := expectation realTableDesign logitEstimate
  let v := variance realTableDesign logitEstimate
  let e := expectation realTableDesign logitVarianceEstimate
  ![Δ, μ, μ-Δ, Real.sqrt v,
    Real.sqrt (expectation realTableDesign (fun w => (logitEstimate w-Δ)^2)),
    v, e, e-v, Real.sqrt (variance realTableDesign logitVarianceEstimate),
    Real.sqrt (expectation realTableDesign (fun w => (logitVarianceEstimate w-v)^2))]

def roundsTo (x r : ℝ) : Prop := r-1/2000 ≤ x ∧ x < r+1/2000

def correctedLogitColumn : Fin 10 → ℝ := ![0,0,0,247/1000,247/1000,61/1000,61/1000,0,13/1000,13/1000]
def printedLogitColumn : Fin 10 → ℝ := ![0,0,0,170/1000,170/1000,29/1000,29/1000,0,7/1000,7/1000]

def logitCoreFacts : Prop :=
  (∃! β, logitMaximizer false β) ∧ (∃! β, logitMaximizer true β) ∧
  |(logitCoefficients true).1-(-11201076/10000000)| ≤ 5/10000000 ∧
  |(logitCoefficients true).2-(5657586/10000000)| ≤ 5/10000000 ∧
  |(logitCoefficients false).1-(10843223/10000000)| ≤ 5/10000000 ∧
  |(logitCoefficients false).2-(2280259/10000000)| ≤ 5/10000000 ∧
  expectation realTableDesign logitEstimate = 0 ∧
  (247090/1000000 : ℝ) ≤ Real.sqrt (variance realTableDesign logitEstimate) ∧
  Real.sqrt (variance realTableDesign logitEstimate) ≤ 247093/1000000 ∧
  (605/10000 : ℝ) ≤ variance realTableDesign logitEstimate ∧
  variance realTableDesign logitEstimate < 615/10000 ∧
  expectation realTableDesign logitVarianceEstimate = variance realTableDesign logitEstimate ∧
  (125/10000 : ℝ) ≤ Real.sqrt (variance realTableDesign logitVarianceEstimate) ∧
  Real.sqrt (variance realTableDesign logitVarianceEstimate) < 135/10000

def T14Statement : Prop :=
  logitCoreFacts ∧
  (∀ b, logitMaximizer b (logitCoefficients b)) ∧
  (∀ a b : ℝ,
    (0 ≤ a → 0 ≤ a+4*b → a+2*b ≤ 0 → a=0 ∧ b=0) ∧
    (0 ≤ a+b → 0 ≤ a+4*b → a+2*b ≤ 0 → a=0 ∧ b=0)) ∧
  (∀ j, roundsTo (logitColumn j) (correctedLogitColumn j)) ∧
  (∀ j : Fin 10, j ∈ ({3,4,5,6,8,9} : Finset (Fin 10)) →
    ¬ roundsTo (logitColumn j) (printedLogitColumn j))

/-- Refutation of universal support/conservativeness, and of footnote 9 separately. -/
def T17Statement : Prop :=
  (¬ (∀ (D : Design (Fin 3) (Fin 2) ℝ), probabilityDesign D → positiveMarginals D →
    (∀ i j, i ≠ j → 0 < disagreement D i j) →
    (∀ x z : Fin 2 → ℝ, crossSupport D ∧
      variance D (ht D 2 x z) ≤ expectation D (printedVariance D 2 x z)))) ∧
  probabilityDesign realAsymmetricTwo ∧ positiveMarginals realAsymmetricTwo ∧
  (∀ i j : Fin 2, i ≠ j → 0 < disagreement realAsymmetricTwo i j ∧
    0 < joint realAsymmetricTwo true true i j ∧ 0 < joint realAsymmetricTwo false false i j) ∧
  expectation realAsymmetricTwo (printedVariance realAsymmetricTwo 2 (fun _ => 1) (fun _ => 1)) ≠
    variance realAsymmetricTwo (generalized realAsymmetricTwo 2 (fun _ => 1) (fun _ => 1)
      (fun _ _ => 0))

/-- A deterministic fit of individually independent inputs has nonzero covariance. -/
def T18Statement : Prop :=
  probabilityDesign realXorThree ∧ positiveMarginals realXorThree ∧
  (∀ j ∈ xorFittingSet, independent realXorThree
    (fun w => realXorThree.treatment w 0) (fun w => realXorThree.treatment w j)) ∧
  covariance realXorThree (fun w => indicator realXorThree true w 0)
    (fun w => xorFit (fittingOutcomes realXorThree xorFittingSet (fun _ => 1) (fun _ => 0) w)) ≠ 0

/-- The selected printed FE, Linear and Logit moment assertions cannot all hold. -/
def T19Statement : Prop :=
  (∀ w : Fin 6 × Fin 15, 0 < ∑ i, (feTreatmentResidual w i)^2) ∧
  (∃! β, logitMaximizer false β) ∧ (∃! β, logitMaximizer true β) ∧
  ¬ (
(∃! β, logitMaximizer false β) ∧ (∃! β, logitMaximizer true β) ∧
    rounded3 (expectation tableDesign feEstimate) (-12/1000) ∧
    rounded3 (variance tableDesign feEstimate) (36/1000) ∧
    roundedSD3 (variance tableDesign feEstimate) (191/1000) ∧
    roundedSD3 (variance tableDesign feEstimate+(expectation tableDesign feEstimate)^2) (191/1000) ∧
    roundedSD3 (variance tableDesign (ht tableDesign 16 tableLinearResidual tableLinearResidual)) (162/1000) ∧
    rounded3 (variance tableDesign (ht tableDesign 16 tableLinearResidual tableLinearResidual)) (26/1000) ∧
    rounded3 (expectation tableDesign (printedVariance tableDesign 16 tableLinearResidual tableLinearResidual)) (26/1000) ∧
    roundedSD3 (variance tableDesign (printedVariance tableDesign 16 tableLinearResidual tableLinearResidual)) (7/1000) ∧
    |Real.sqrt (variance realTableDesign (ht realTableDesign 16 tableLogitResidual tableLogitResidual))-170/1000| ≤ 1/2000 ∧
    |variance realTableDesign (ht realTableDesign 16 tableLogitResidual tableLogitResidual)-29/1000| ≤ 1/2000 ∧
    |expectation realTableDesign (printedVariance realTableDesign 16 tableLogitResidual tableLogitResidual)-29/1000| ≤ 1/2000 ∧
    |Real.sqrt (variance realTableDesign (printedVariance realTableDesign 16 tableLogitResidual tableLogitResidual))-7/1000| ≤ 1/2000)

end
end SAP.P026b
