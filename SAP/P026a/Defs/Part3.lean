import SAP.P026a.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a
open Finset
open scoped BigOperators
noncomputable section

variable {Ω I R : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]

def paperTwoOfSix : Fin 15 → Fin 6 → Bool := ![
  ![true,true,false,false,false,false], ![true,false,true,false,false,false],
  ![true,false,false,true,false,false], ![true,false,false,false,true,false],
  ![true,false,false,false,false,true], ![false,true,true,false,false,false],
  ![false,true,false,true,false,false], ![false,true,false,false,true,false],
  ![false,true,false,false,false,true], ![false,false,true,true,false,false],
  ![false,false,true,false,true,false], ![false,false,true,false,false,true],
  ![false,false,false,true,true,false], ![false,false,false,true,false,true],
  ![false,false,false,false,true,true]]

def paperTableDesign : AssignmentDesign (Fin 6 × Fin 15) (Fin 10) ℚ where
  weight := fun _ => 1/90
  treatment := fun w i => if h : i.val < 4 then twoOfFourLaw.treatment w.1 ⟨i.val,h⟩
    else paperTwoOfSix w.2 ⟨i.val-4, by omega⟩

def paperTableCluster : Fin 16 → Fin 10 := ![0,0,1,1,2,3,4,4,4,5,5,6,6,7,8,9]

def paperTableY : Fin 16 → ℚ := ![1,1,1,1,1,0,1,1,0,1,1,1,1,0,0,0]

def paperTableX : Fin 16 → ℚ := ![4,0,4,1,4,2,4,1,2,5,4,1,4,2,2,3]

def paperTableLinearPrediction (i : Fin 16) : ℚ :=
  if i.val < 6 then 1/4+paperTableX i/8 else 70/93+paperTableX i/31

/-- Actual cluster sums of outcomes minus the specified opposite-block linear predictions. -/
def paperTableLinearResidual (k : Fin 10) : ℚ :=
  fiberTotal paperTableCluster (fun i => paperTableY i - paperTableLinearPrediction i) k

def roundsToThree (x r : ℚ) : Prop := r-1/2000 ≤ x ∧ x < r+1/2000

def sdRoundsToThree (v r : ℚ) : Prop := (r-1/2000)^2 ≤ v ∧ v < (r+1/2000)^2

def paperTableUnitDesign : AssignmentDesign (Fin 6 × Fin 15) (Fin 16) ℚ where
  weight := paperTableDesign.weight
  treatment := fun w i => paperTableDesign.treatment w (paperTableCluster i)

def paperTableTreatmentMean (w : Fin 6 × Fin 15) (b : Bool) : ℚ :=
  (∑ i ∈ (univ : Finset (Fin 16)).filter (fun i => if b then 6 ≤ i.val else i.val < 6),
    armIndicator paperTableUnitDesign true w i) / (if b then 10 else 6)

def paperTableCenteredX (i : Fin 16) : ℚ := paperTableX i-(if i.val < 6 then 5/2 else 14/5)

def paperTableCenteredY (i : Fin 16) : ℚ := paperTableY i-(if i.val < 6 then 5/6 else 3/5)

def paperTableCenteredT (w : Fin 6 × Fin 15) (i : Fin 16) : ℚ :=
  armIndicator paperTableUnitDesign true w i-paperTableTreatmentMean w (decide (6 ≤ i.val))

def paperFeTreatmentResidual (w : Fin 6 × Fin 15) (i : Fin 16) : ℚ :=
  paperTableCenteredT w i - (∑ j, paperTableCenteredX j*paperTableCenteredT w j) /
    (∑ j, (paperTableCenteredX j)^2)*paperTableCenteredX i

def paperFeEstimate (w : Fin 6 × Fin 15) : ℚ :=
  (∑ i, paperFeTreatmentResidual w i*paperTableCenteredY i) / (∑ i, (paperFeTreatmentResidual w i)^2)

def paperFeXCoefficient (w : Fin 6 × Fin 15) : ℚ :=
  (∑ i, paperTableCenteredX i*(paperTableCenteredY i-paperFeEstimate w*paperTableCenteredT w i)) /
    (∑ i, (paperTableCenteredX i)^2)

def paperFeFitted (w : Fin 6 × Fin 15) (i : Fin 16) : ℚ :=
  (if i.val < 6 then 5/6 else 3/5) + paperFeEstimate w*paperTableCenteredT w i +
    paperFeXCoefficient w*paperTableCenteredX i

def paperTableClusterY : Fin 10 → ℚ := ![2,2,1,0,2,2,2,0,0,0]

def paperTablePriorResidual : Fin 10 → ℚ := ![1,1,1/2,-1/2,1/2,1,1,-1/2,-1/2,-1/2]

end
end SAP.P026a
