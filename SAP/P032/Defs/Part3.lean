import SAP.P032.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P032

open scoped BigOperators
open Matrix MeasureTheory ProbabilityTheory Filter

noncomputable section

variable {R M P : Type*} [Fintype R] [Fintype M] [Fintype P]
  [DecidableEq R] [DecidableEq M] [DecidableEq P]

/-! Exact survival and ten-dyad OLS examples; labels start at zero. -/

structure SurvivalRecord where
  id : Fin 6
  dyad : DyadData (Fin 4)
  start : ℕ
  stop : ℕ
  x : ℝ
  status : ℕ

def survivalRecords : Fin 10 → SurvivalRecord :=
  ![⟨0,sixDyadData 0,0,1,1,1⟩, ⟨1,sixDyadData 5,0,1,-1,1⟩,
    ⟨2,sixDyadData 1,0,1,1,0⟩, ⟨2,sixDyadData 1,1,2,3,1⟩,
    ⟨3,sixDyadData 4,0,1,-1,0⟩, ⟨3,sixDyadData 4,1,2,-3,1⟩,
    ⟨4,sixDyadData 2,0,1,1,0⟩, ⟨4,sixDyadData 2,1,3,1,2⟩,
    ⟨5,sixDyadData 3,0,1,-1,0⟩, ⟨5,sixDyadData 3,1,3,-1,2⟩]

abbrev survivalAtRisk (r : Fin 10) (t : ℕ) : Prop :=
  (survivalRecords r).start < t ∧ t ≤ (survivalRecords r).stop

abbrev survivalEvent (r : Fin 10) (t : ℕ) : Prop :=
  (survivalRecords r).status = 1 ∧ (survivalRecords r).stop = t

def survivalRiskCount (t : ℕ) : ℝ := ∑ r, if survivalAtRisk r t then 1 else 0

def survivalEventCount (t : ℕ) : ℝ := ∑ r, if survivalEvent r t then 1 else 0

def survivalRiskMean (t : ℕ) : ℝ :=
  (∑ r, if survivalAtRisk r t then (survivalRecords r).x else 0) / survivalRiskCount t

def survivalLogLikelihood (β : ℝ) : ℝ := ∑ t : Fin 2,
  ((∑ r, if survivalEvent r (t.val+1) then β*(survivalRecords r).x else 0) -
  survivalEventCount (t.val+1) * Real.log
    (∑ r, if survivalAtRisk r (t.val+1) then Real.exp (β*(survivalRecords r).x) else 0))

def survivalClosedLikelihood (β : ℝ) : ℝ :=
  -2*Real.log (6*Real.cosh β) -
    2*Real.log (2*Real.cosh (3*β)+2*Real.cosh β)

def survivalEfficientScore (r : Fin 10) : ℝ := ∑ t : Fin 2,
  if survivalAtRisk r (t.val+1) then
    ((if survivalEvent r (t.val+1) then 1 else 0) - survivalEventCount (t.val+1)/survivalRiskCount (t.val+1)) *
      ((survivalRecords r).x-survivalRiskMean (t.val+1)) else 0

def survivalScores : Fin 10 → ℝ := ![2/3,-2/3,-1/3,3/2,1/3,-3/2,-1/3,-1/2,1/3,1/2]

def survivalInformation : ℝ := ∑ t : Fin 2, survivalEventCount (t.val+1) *
  ((∑ r, if survivalAtRisk r (t.val+1) then ((survivalRecords r).x)^2 else 0)/survivalRiskCount (t.val+1) -
    (survivalRiskMean (t.val+1))^2)

def survivalInfluence (r : Fin 10) : ℝ := survivalScores r / 12

def tenDyadData : Fin 10 → DyadData (Fin 5) := fun r =>
  ⟨![({0,1} : Finset (Fin 5)),{0,2},{1,2},{0,3},{1,3},
    {2,3},{0,4},{1,4},{2,4},{3,4}] r, by fin_cases r <;> decide⟩

def tenCovariate : Fin 10 → ℝ := ![3,0,2,1,-1,1,-3,-2,3,-2]

def tenResponse : Fin 10 → ℝ := ![3,-2,-2,1,1,0,0,2,1,0]

def tenDesignMatrix : Matrix (Fin 10) (Fin 2) ℝ := fun r => ![1,tenCovariate r]

def tenBreadMatrix : Matrix (Fin 2) (Fin 2) ℝ := (1/208 : ℝ) • !![21,-1;-1,5]

def tenResidualValues : Fin 10 → ℝ := fun r => ![31,-31,-33,7,9,-6,-2,23,5,-3] r / 13

def tenScoreValues (r : Fin 10) : Fin 2 → ℝ := fun i => tenResidualValues r * tenDesignMatrix r i

def tenDyadicMeat : Matrix (Fin 2) (Fin 2) ℝ := scoreCovariance (dyadicMask tenDyadData) tenScoreValues

def tenCovariance : Matrix (Fin 2) (Fin 2) ℝ := tenBreadMatrix * tenDyadicMeat * tenBreadMatrix

def tenPositiveRoot : ℝ := ((467922/3655808 : ℝ) +
  Real.sqrt ((467922/3655808 : ℝ)^2-4*(-70529/308915776)))/2

def tenNegativeRoot : ℝ := ((467922/3655808 : ℝ) -
  Real.sqrt ((467922/3655808 : ℝ)^2-4*(-70529/308915776)))/2

end
end SAP.P032
