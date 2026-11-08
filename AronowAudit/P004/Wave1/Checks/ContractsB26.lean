import AronowAudit.P004.Wave1.Gap.DecideP004T1

namespace AronowAudit.P004.Wave1.ContractsB26

open scoped BigOperators Matrix Topology
open MeasureTheory Filter AronowAudit.P004

/-- Approved statement: `~/lean-work/runs/map-decide-P004T1/map.json`, record 1 (P004-T1).
Both `ref1-decide-P004T1` and `ref2-decide-P004T1` accept this record with no fixes. -/
def approvedContract_P004_T1 : Prop :=
  
    ∃ θhat : ∀ N, Assignment N → Fin 2 → ℝ,
      LogisticConditions threeTypeONat threeTypeTheta threeTypeParameterSet θhat ∧
      threeTypeTheta ∈ interior threeTypeParameterSet ∧
      SpatialLocalConditions threeTypePopulation ∧
      Overlap (fun N => propensities (threeTypeONat N) threeTypeTheta) ∧
      (∀ N : ℕ, 0 < N → WellDefined (threeTypePopulation N) 0) ∧
      (∀ N, homophilyQ (propensities (threeTypeONat N) threeTypeTheta)
        (circleAverage (threeTypePopulation N) 0) (fun i => {i})
        (printedFits (propensities (threeTypeONat N) threeTypeTheta)
          (circleAverage (threeTypePopulation N) 0) (threeTypeONat N)) = 0) ∧
      Nondegenerate (fun N => variance (propensities (threeTypeONat N) threeTypeTheta)
        (augmented (propensities (threeTypeONat N) threeTypeTheta)
          (circleAverage (threeTypePopulation N) 0)
          (printedFits (propensities (threeTypeONat N) threeTypeTheta)
            (circleAverage (threeTypePopulation N) 0) (threeTypeONat N)))) ∧
      ¬ LittleOp (fun N => propensities (threeTypeONat N) threeTypeTheta)
        (fun N z => augmented (propensities (threeTypeONat N) threeTypeTheta)
          (circleAverage (threeTypePopulation N) 0)
          (printedFits (propensities (threeTypeONat N) threeTypeTheta)
            (circleAverage (threeTypePopulation N) 0) (threeTypeONat N)) z -
          fittedIPW (circleAverage (threeTypePopulation N) 0)
            (threeTypeONat N) (θhat N) z)
        (fun N => (Real.sqrt N)⁻¹)

example : approvedContract_P004_T1 := @AronowAudit.P004.Wave1.ipw_linearization_counterexample_nat

-- `map-decide-P004T1/map.json`, record 0: the approved definition body,
-- accepted without changes by both decide-P004T1 referees.
example : AronowAudit.P004.Wave1.threeTypeONat = fun N i => ![1, (((i.val % 3 : ℕ) : ℝ) - 1)] := rfl

end AronowAudit.P004.Wave1.ContractsB26
