import Mathlib
import SAP.P015b.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P015b

universe u v

noncomputable section
open Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal NNReal
attribute [local instance] Classical.propDecidable

def sigmoidTaylor (N : ℕ) (c a : ℝ) : ℝ := taylorWithinEval sigmoidMean N Set.univ c a

def twoCellLogLikelihood (θ : Fin 2 → ℝ) : ℝ :=
  binomialLogLikelihoodSAP sigmoidMean 100 1 (θ 0)+binomialLogLikelihoodSAP sigmoidMean 100 99 (θ 0+θ 1)

def TaylorFailure : Prop :=
  (let L := Real.log 99;
    (∀ θ : Fin 2 → ℝ, twoCellLogLikelihood θ  ≤  twoCellLogLikelihood ![-L,2*L]) ∧
    (∀ θ : Fin 2 → ℝ, twoCellLogLikelihood θ = twoCellLogLikelihood ![-L,2*L] → θ = ![-L,2*L]) ∧
    sigmoidMean (-L) = 1/100 ∧ sigmoidMean L = 99/100 ∧
    logOdds ((1+99)/200) = 0 ∧ 9/2  <  L ∧ Real.pi  <  9/2 ∧
    (∀ N : ℕ, 49/100  ≤  |sigmoidTaylor N 0 L-sigmoidMean L| ∧
      49/100  ≤  |sigmoidTaylor N 0 (-L)-sigmoidMean (-L)| ∧
      49  ≤  |100*(99/100-sigmoidTaylor N 0 L)|)) ∧
  (∃ s : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun z : ℂ => (1+Complex.exp (-z))⁻¹) s 0 ∧
      s.radius=ENNReal.ofReal Real.pi) ∧
  (let W : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;1,1]
    let L := Real.log 99;
    ((100 : ℝ) • (W.transpose*W)).det=10000 ∧
    (0:ℝ) < 1 ∧ (1:ℝ) < 100 ∧ (0:ℝ) < 99 ∧ (99:ℝ) < 100 ∧
    residualEquation W (fun _ => 100) ![1,99] sigmoidMean ![-L,2*L]=0) ∧
  (sigmoidMean (Real.log 99) = 99/100 ∧ sigmoidMean (-Real.log 99) = 1/100 ∧
    logOdds ((1+99)/200) = 0 ∧ Real.pi  <  9/2 ∧
    |sigmoidTaylor 0 0 (Real.log 99)-sigmoidMean (Real.log 99)| = 49/100) ∧
  (9/2  <  Real.log 99)

/-- Predictors, sample mean, and the treatment equation for the two repeated rows. -/
def TaylorDataIdentities : Prop :=
  let W : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;1,1]
  let L := Real.log 99
  W.mulVec ![-L,2*L] = ![-L,L] ∧
  ((1+99 : ℝ)/200 = 1/2) ∧
  (∀ N : ℕ, residualEquation W (fun _ => 100) ![1,99]
    (fun a => sigmoidTaylor N 0 a) ![-L,2*L] 1 =
      100*(99/100-sigmoidTaylor N 0 L))

def T11Statement : Prop := TaylorFailure ∧ TaylorDataIdentities

end
end SAP.P015b
