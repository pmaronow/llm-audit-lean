import Mathlib
import SAP.P026b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026b
open Finset
open scoped BigOperators
noncomputable section

def asymmetricTwo : Design (Fin 3) (Fin 2) ℚ where
  weight := fun _ => 1/3
  treatment := ![![false, false], ![false, true], ![true, true]]

def oneOfThree : Design (Fin 3) (Fin 3) ℚ where
  weight := fun _ => 1/3
  treatment := fun w i => decide (w = i)

def packageFit (w : Fin 3) (i : Fin 3) : ℚ :=
  (![5/6,1/3,-1/6] : Fin 3 → ℚ) w + (![-1/2,0,1/2] : Fin 3 → ℚ) w * i.val

def singleAsymmetric : Design (Fin 3) (Fin 1) ℚ where
  weight := asymmetricTwo.weight
  treatment := fun w _ => asymmetricTwo.treatment w 0

def unequalClusterDesign : Design (Fin 3) (Fin 4) ℚ where
  weight := fun _ => 1/3
  treatment := fun w i => decide (w = (![0,1,2,2] : Fin 4 → Fin 3) i)

def twoOfFour : Design (Fin 6) (Fin 4) ℚ where
  weight := fun _ => 1/6
  treatment := ![![true,true,false,false], ![true,false,true,false], ![true,false,false,true],
    ![false,true,true,false], ![false,true,false,true], ![false,false,true,true]]

def twoOfSix : Fin 15 → Fin 6 → Bool := ![
  ![true,true,false,false,false,false], ![true,false,true,false,false,false],
  ![true,false,false,true,false,false], ![true,false,false,false,true,false],
  ![true,false,false,false,false,true], ![false,true,true,false,false,false],
  ![false,true,false,true,false,false], ![false,true,false,false,true,false],
  ![false,true,false,false,false,true], ![false,false,true,true,false,false],
  ![false,false,true,false,true,false], ![false,false,true,false,false,true],
  ![false,false,false,true,true,false], ![false,false,false,true,false,true],
  ![false,false,false,false,true,true]]

def tableDesign : Design (Fin 6 × Fin 15) (Fin 10) ℚ where
  weight := fun _ => 1/90
  treatment := fun w i => if h : i.val < 4 then twoOfFour.treatment w.1 ⟨i.val,h⟩
    else twoOfSix w.2 ⟨i.val-4, by omega⟩

def tableCluster : Fin 16 → Fin 10 := ![0,0,1,1,2,3,4,4,4,5,5,6,6,7,8,9]

def tableY : Fin 16 → ℚ := ![1,1,1,1,1,0,1,1,0,1,1,1,1,0,0,0]

def tableX : Fin 16 → ℚ := ![4,0,4,1,4,2,4,1,2,5,4,1,4,2,2,3]

def tableLinearResidual : Fin 10 → ℚ :=
  ![1,7/8,1/4,-1/2,-15/31,19/93,1/3,-76/93,-76/93,-79/93]

def rounded3 (x r : ℚ) : Prop := r-1/2000 ≤ x ∧ x < r+1/2000

def roundedSD3 (v r : ℚ) : Prop := (r-1/2000)^2 ≤ v ∧ v < (r+1/2000)^2

def tableUnitDesign : Design (Fin 6 × Fin 15) (Fin 16) ℚ where
  weight := tableDesign.weight
  treatment := fun w i => tableDesign.treatment w (tableCluster i)

def tableTreatmentMean (w : Fin 6 × Fin 15) (b : Bool) : ℚ :=
  (∑ i ∈ (univ : Finset (Fin 16)).filter (fun i => if b then 6 ≤ i.val else i.val < 6),
    indicator tableUnitDesign true w i) / (if b then 10 else 6)

def tableCenteredX (i : Fin 16) : ℚ := tableX i-(if i.val < 6 then 5/2 else 14/5)

def tableCenteredY (i : Fin 16) : ℚ := tableY i-(if i.val < 6 then 5/6 else 3/5)

def tableCenteredT (w : Fin 6 × Fin 15) (i : Fin 16) : ℚ :=
  indicator tableUnitDesign true w i-tableTreatmentMean w (decide (6 ≤ i.val))

def feTreatmentResidual (w : Fin 6 × Fin 15) (i : Fin 16) : ℚ :=
  tableCenteredT w i - (∑ j, tableCenteredX j*tableCenteredT w j) /
    (∑ j, (tableCenteredX j)^2)*tableCenteredX i

def feEstimate (w : Fin 6 × Fin 15) : ℚ :=
  (∑ i, feTreatmentResidual w i*tableCenteredY i) / (∑ i, (feTreatmentResidual w i)^2)

def realTableDesign : Design (Fin 6 × Fin 15) (Fin 10) ℝ where
  weight := fun w => (tableDesign.weight w : ℝ)
  treatment := tableDesign.treatment

noncomputable def sigmoid (z : ℝ) : ℝ := 1-1/(1+Real.exp z)

noncomputable def logitLikelihood (b : Bool) (β : ℝ × ℝ) : ℝ :=
  ∑ i ∈ (univ : Finset (Fin 16)).filter (fun i => if b then 6 ≤ i.val else i.val < 6),
    ((tableY i : ℝ)*Real.log (sigmoid (β.1+β.2*(tableX i : ℝ))) +
      (1-(tableY i : ℝ))*Real.log (1-sigmoid (β.1+β.2*(tableX i : ℝ))))

def logitMaximizer (b : Bool) (β : ℝ × ℝ) : Prop :=
  ∀ γ : ℝ × ℝ, logitLikelihood b γ ≤ logitLikelihood b β

noncomputable def logitCoefficients (b : Bool) : ℝ × ℝ := by
  classical
  exact if h : ∃ β, logitMaximizer b β then Classical.choose h else (0,0)

noncomputable def tableLogitPrediction (i : Fin 16) : ℝ :=
  let β := logitCoefficients (decide (i.val < 6))
  sigmoid (β.1+β.2*(tableX i : ℝ))

noncomputable def tableLogitResidual : Fin 10 → ℝ :=
  clusterTotal tableCluster (fun i => (tableY i : ℝ)-tableLogitPrediction i)

def realAsymmetricTwo : Design (Fin 3) (Fin 2) ℝ where
  weight := fun _ => 1/3
  treatment := ![![false,false], ![false,true], ![true,true]]

def realXorThree : Design (Fin 4) (Fin 3) ℝ where
  weight := fun _ => 1/4
  treatment := ![![false,false,false], ![false,true,true], ![true,false,true], ![true,true,false]]

def xorFittingSet : Finset (Fin 3) := univ.erase 0

def xorFit (y : ↥xorFittingSet → ℝ) : ℝ :=
  y ⟨1, by decide⟩ + y ⟨2, by decide⟩ - 2*y ⟨1, by decide⟩*y ⟨2, by decide⟩

end
end SAP.P026b
