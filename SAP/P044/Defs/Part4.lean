import SAP.P044.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P044

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators unitInterval

noncomputable section

def T1Statement : Prop :=
  (cliqueF = (fun r => exposure cliqueAdj (cliqueAssignments r)) ∧
    (∀ z : Assignment 12, (Finset.univ.filter (fun i => z i)).card = 2 ↔ ∃ r, cliqueAssignments r = z) ∧
    (∀ i j, cliqueAdj i j = cliqueAdj j i) ∧
    Function.Injective cliqueAssignments ∧
    (∀ r, (Finset.univ.filter (fun i => cliqueAssignments r i)).card = 2) ∧
    (∀ i, cliqueAdj i i = false ∧ ∃ j, cliqueAdj i j = true) ∧
    (∀ i, marginal (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF i .d01 = 9/22 ∧
      marginal (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF i .d00 = 14/33) ∧
    (∀ t, Function.Injective (retainedAssignments t) ∧
      (∀ r, retainedAssignments t r ≠ cliqueAssignments t)) ∧
    (∀ t i, 0 < (smoothedWeight (retainedF t) i .d01 : ℚ) ∧
      0 < (smoothedWeight (retainedF t) i .d00 : ℚ)) ∧
    tau cliqueY .d01 .d00 = 0 ∧
    (let w := marginal (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF
     let q := joint (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF
     let T := htContrast cliqueF cliqueY w .d01 .d00
     expect (fun _ : Fin 66 => (1/66 : ℚ)) T = 0 ∧
     designVariance (fun _ : Fin 66 => (1/66 : ℚ)) T = 6050/11907 ∧
     expect (fun _ : Fin 66 => (1/66 : ℚ))
       (varianceEstimate cliqueF cliqueY w q .d01 .d00) = 6050/11907) ∧
    expect (cliqueJointMass false) (fun x => cliqueT x.1 x.2) = -67/53592 ∧
    designVariance (cliqueJointMass false) (fun x => cliqueT x.1 x.2) = 113448938731/232640299584 ∧
    expect (cliqueJointMass false) (fun x => cliqueV x.1 x.2) = 1040129476423/2326402995840 ∧
    expect (cliqueJointMass false) (fun x => cliqueV x.1 x.2) -
      designVariance (cliqueJointMass false) (fun x => cliqueT x.1 x.2) = -953130413/23499020160 ∧
    expect (cliqueJointMass true) (fun x => cliqueT x.1 x.2) = -67/52780 ∧
    designVariance (cliqueJointMass true) (fun x => cliqueT x.1 x.2) = 11375808887/23342482800 ∧
    expect (cliqueJointMass true) (fun x => cliqueV x.1 x.2) = 4673362763/10414338480 ∧
    expect (cliqueJointMass true) (fun x => cliqueV x.1 x.2) -
      designVariance (cliqueJointMass true) (fun x => cliqueT x.1 x.2) = -20161943/522324075 ∧
    (∀ included,
      expect (cliqueJointMass included) (fun x => cliqueV x.1 x.2) <
        designVariance (cliqueJointMass included) (fun x => cliqueT x.1 x.2) ∧
      expect (cliqueJointMass included) (fun x => cliqueV x.1 x.2) < 6050/11907) ∧
    designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT 0) = 2810528137/5767941312 ∧
    expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV 0) = 267260522663/634473544320 ∧
    designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT 3) = 937589375/1922647104 ∧
    expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV 3) = 4830430961/10574559072) ∧
  ((∀ i, exposureCount cliqueF i .d01 = 27 ∧ exposureCount cliqueF i .d00 = 28) ∧
    (∀ i j, i ≠ j →
      jointCount cliqueF i j .d01 .d01 = (if i.val / 4 = j.val / 4 then 17 else 9) ∧
      jointCount cliqueF i j .d00 .d00 = (if i.val / 4 = j.val / 4 then 28 else 6) ∧
      jointCount cliqueF i j .d01 .d00 = (if i.val / 4 = j.val / 4 then 0 else 15))) ∧
  (Function.Injective cliqueAssignments ∧
    (∀ r, (Finset.univ.filter (fun i => cliqueAssignments r i)).card = 2) ∧
    (∀ i j, cliqueAdj i j = cliqueAdj j i) ∧
    (∀ i, cliqueAdj i i = false ∧ ∃ j, cliqueAdj i j = true) ∧
    (∀ r, (Finset.univ.filter (fun i => cliqueF r i = .d01)).card =
        if (cliquePairs r).1.val / 4 = (cliquePairs r).2.val / 4 then 2 else 6) ∧
    (∀ r, (Finset.univ.filter (fun i => cliqueF r i = .d00)).card =
        if (cliquePairs r).1.val / 4 = (cliquePairs r).2.val / 4 then 8 else 4) ∧
    (Finset.univ.filter (fun r => (cliquePairs r).1.val / 4 = (cliquePairs r).2.val / 4)).card = 18 ∧
    (Finset.univ.filter (fun r => (cliquePairs r).1.val / 4 ≠ (cliquePairs r).2.val / 4)).card = 48) ∧
  (∀ t : Fin 66,
      let same := (cliquePairs t).1.val / 4 = (cliquePairs t).2.val / 4
      designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT t) =
        (if same then 2810528137/5767941312 else 937589375/1922647104) ∧
      expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV t) =
        (if same then 267260522663/634473544320 else 4830430961/10574559072) ∧
      expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV t) -
        designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT t) =
        (if same then -1551761941/23499020160 else -72513467/2349902016) ∧
      expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV t) <
        designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT t)) ∧
  (let m := marginal (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF
    ∀ r, htContrast cliqueF cliqueY m .d01 .d00 r =
      if (cliquePairs r).1.val / 4 = (cliquePairs r).2.val / 4 then -220/189 else 55/126) ∧
  ((∀ t i, cliqueWeights t i .d01 = (smoothedWeight (retainedF t) i .d01 : ℚ) ∧
      cliqueWeights t i .d00 = (smoothedWeight (retainedF t) i .d00 : ℚ)) ∧
    (∀ t i j a b, (a = Exposure.d01 ∨ a = .d00) → (b = Exposure.d01 ∨ b = .d00) →
      cliqueJoints t i j a b = (smoothedJoint (retainedF t) i j a b : ℚ))) ∧
  (∀ t : Fin 66, ∃ e : Equiv.Perm (Fin 12),
    (∀ i j, cliqueAdj (e i) (e j) = cliqueAdj i j) ∧
    (∀ i, cliqueAssignments t (e i) =
      cliqueAssignments (if (cliquePairs t).1.val / 4 = (cliquePairs t).2.val / 4 then 0 else 3) i))

end
end SAP.P044
