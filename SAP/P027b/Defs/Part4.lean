import SAP.P027b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027b
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The fixed-population part C1 of the bias-ranking counterexample. -/
def T14Statement : Prop :=
  let D := strataDesign 5 (by norm_num)
  let V := fun α => variance D (htMean D (fixedStrata5 α))
  let H := fun α => expect D (fun ω => htVarianceEstimator D (fixedStrata5 α) ω / 100)
  let C := fun α => expect D (fun ω => c2Estimator D (fixedStrata5 α) ω / 100)
  let CS := fun α => expect D (collapsedEstimator (fixedStrata5 α))
  V 0 = 1/2 ∧ V 2 = 1/2 ∧
  H 0 = 2/5 ∧ C 0 = 4/5 ∧ CS 0 = 1/2 ∧ H 2 = 2 ∧ C 2 = 4 ∧ CS 2 = 9/2 ∧
  C 0 - V 0 = 3/10 ∧ CS 0 - V 0 = 0 ∧ C 2 - V 2 = 7/2 ∧ CS 2 - V 2 = 4 ∧
  CS 0 - V 0 < C 0 - V 0 ∧ C 2 - V 2 < CS 2 - V 2

/-- A finite, equally weighted independent-sign witness, rather than Gaussian errors. -/
def T16Statement : Prop :=
  let Y := fun ω => (1/2:ℝ) * pairS ω + pairE ω
  let Y' := fun ω => (1/2:ℝ) * pairS ω + pairE' ω
  expect pairLaw pairS = 0 ∧ expect pairLaw pairE = 0 ∧ expect pairLaw pairE' = 0 ∧
  variance pairLaw pairS = 1 ∧ variance pairLaw pairE = 1 ∧ variance pairLaw pairE' = 1 ∧
  expect pairLaw (fun ω => pairS ω * pairE ω) = 0 ∧
  expect pairLaw (fun ω => pairS ω * pairE' ω) = 0 ∧
  expect pairLaw (fun ω => pairE ω * pairE' ω) = 0 ∧
  expect pairLaw Y = 0 ∧ expect pairLaw Y' = 0 ∧
  variance pairLaw Y = 5/4 ∧ variance pairLaw Y' = 5/4 ∧ outcomeCov pairLaw Y Y' = 1/4 ∧
  outcomeCorr pairLaw Y Y' = 1/5 ∧ heterogeneity (1/2) = 1/3 ∧
  heterogeneity (1/2) - outcomeCorr pairLaw Y Y' = 2/15

/-- The corrected first- and second-order inclusion and covariance formulas. -/
def T18Statement : Prop :=
  (∀ (M : ℕ) (hM : 0 < M),
    let D := strataDesign M hM
    (∀ k, pi D k = 1/(M:ℝ)) ∧
    (∀ k l, joint D k l = if k = l then 1/(M:ℝ) else
      if k.2 = l.2 then 0 else 1/(M:ℝ)^2) ∧
    (∀ k l, inclusionCov D k l = if k = l then
      (1/(M:ℝ)) * (1-1/(M:ℝ)) else if k.2 = l.2 then -1/(M:ℝ)^2 else 0) ∧
    (∀ k, variance D (fun ω => indicator D ω k) = (1/(M:ℝ)) * (1-1/(M:ℝ)))) ∧
  joint (strataDesign 2 (by norm_num)) ((0:Fin 2),(0:Fin 2)) (0,0) = 1/2

end
end SAP.P027b
