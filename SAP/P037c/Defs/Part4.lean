import Mathlib
import SAP.P037c.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037c
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def controlPair (z : Fin 6) : Finset (Fin 4) := ![{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}] z

noncomputable def pairReferentRate : Fin 4 → ℝ := ![1/10,1/5,3/10,2/5]

def controlExposure (z : Fin 6 × (Fin 4 → Bool)) (i : Fin 4 × Fin 2) : Fin 4 :=
  if i.1∈controlPair z.1 then
    (if (z.2 i.1)==decide (i.2=0) then 3 else 2)
  else if (z.2 i.1)==decide (i.2=0) then 0 else 1

noncomputable def controlMass (z : Fin 6 × (Fin 4 → Bool)) : ℝ :=
  (1/6)*∏ j, if j∈controlPair z.1 then
    (if z.2 j then pairReferentRate j else 1-pairReferentRate j) else 1/2

noncomputable def controlPiI (i : Fin 4 × Fin 2) : ℝ :=
  (1/2)*(if i.2=0 then pairReferentRate i.1 else 1-pairReferentRate i.1)

noncomputable def controlPi (i : Fin 4 × Fin 2) (k : Fin 4) : ℝ :=
  if k=0 ∨ k=1 then 1/4 else if k=2 then 1/2-controlPiI i else controlPiI i

def controlObserved (i : Fin 4 × Fin 2) : Fin 4 :=
  if i.1.val<2 then (if i.2=0 then 3 else 2) else if i.2=0 then 0 else 1

noncomputable def controlY (i : Fin 4 × Fin 2) : ℝ := ![![0,2],![1,0],![3,1],![2,4]] i.1 i.2

noncomputable def controlFullRow (D : (Fin 4 × Fin 2) → Fin 4) : Matrix (Fin 4 × Fin 2) (Fin 5) ℝ :=
  pooledExposureRow D (fun i => ![controlPiI i])

noncomputable def controlWeight (D : (Fin 4 × Fin 2) → Fin 4) (i : Fin 4 × Fin 2) : ℝ :=
  1/controlPi i (D i)

noncomputable def controlPoint : Fin 5 → ℝ :=
  (regressionMap (controlWeight controlObserved) (controlFullRow controlObserved)).mulVec controlY

noncomputable def controlPointMean (k : Fin 4) : ℝ := controlPoint k.castSucc+controlPoint 4/4

noncomputable def controlResidual : (Fin 4 × Fin 2) → ℝ :=
  controlY-(controlFullRow controlObserved).mulVec controlPoint

noncomputable def controlContrast (z : Fin 6 × (Fin 4 → Bool)) (full : Bool)
    (Y : (Fin 4 × Fin 2) → ℝ) : ℝ :=
  if full then
    let b := (regressionMap (controlWeight (controlExposure z)) (controlFullRow (controlExposure z))).mulVec Y
    b 3-b 2
  else
    let X : Matrix (Fin 4 × Fin 2) (Fin 4) ℝ := fun i k => if controlExposure z i=k then 1 else 0
    let b := (regressionMap (controlWeight (controlExposure z)) X).mulVec Y
    b 3-b 2

noncomputable def controlVariance (f : (Fin 6 × (Fin 4 → Bool)) → ℝ) : ℝ :=
  (∑ z, controlMass z*(f z)^2)-(∑ z, controlMass z*f z)^2

noncomputable def controlFullVarianceCertificate : ℝ :=
  1574066925743604937750798623088231315086040632174801225920729815316988109390788379330079414475192929 /
  171796363313262196427951740421954806512514436622177625713808591915692887084446808987770465290240000

noncomputable def controlCollapsedVarianceCertificate : ℝ := 1453114769225810453/621302156766720000

def CollapsedControlCertificate : Prop :=
  Fintype.card (Fin 6 × (Fin 4 → Bool))=96 ∧
    (∑ z, controlMass z)=1 ∧ (∀ z, 0<controlMass z) ∧
    (∀ z k, (Finset.univ.filter (fun i => controlExposure z i=k)).card=2) ∧
    (∀ i k, (∑ z, controlMass z*(if controlExposure z i=k then (1:ℝ) else 0))=controlPi i k) ∧
    (∀ z, Function.Injective (controlFullRow (controlExposure z)).mulVec) ∧
    controlPoint=![1/13,-2,-14/3,-23/39,180/13] ∧
    (∀ k, controlPointMean k=(![46/13,19/13,-47/39,112/39] : Fin 4 → ℝ) k) ∧
    (∀ z,
      controlContrast z true (fun i => controlY i+controlPointMean (controlExposure z i)-controlPointMean (controlObserved i))=
        controlContrast z true controlResidual+controlPointMean 3-controlPointMean 2) ∧
    controlVariance (fun z => controlContrast z true controlResidual)=controlFullVarianceCertificate ∧
    controlVariance (fun z => controlContrast z false controlResidual)=controlCollapsedVarianceCertificate ∧
    9<controlFullVarianceCertificate ∧ controlFullVarianceCertificate<37/4 ∧
    2<controlCollapsedVarianceCertificate ∧ controlCollapsedVarianceCertificate<5/2

/-- The actual full and collapsed residual-refit contrast variances are unequal. -/
def T33Statement : Prop :=
  CollapsedControlCertificate ∧
  controlVariance (fun z => controlContrast z false controlResidual) ≠
    controlVariance (fun z => controlContrast z true controlResidual) ∧
  controlResidual=(fun i =>
    (![![-4/39,17/39],![8/39,-34/39],![11/13,-24/13],![-11/13,24/13]] :
      Fin 4 → Fin 2 → ℝ) i.1 i.2) ∧
  controlVariance (fun z => controlContrast z true (fun i => controlY i+
    controlPointMean (controlExposure z i)-controlPointMean (controlObserved i)))=
    controlFullVarianceCertificate ∧
  (∀ i, controlPi i 2+controlPi i 3=1/2) ∧
  (∀ (D : (Fin 4 × Fin 2) → Fin 4) i, 0<controlWeight D i) ∧
  Function.Injective (controlFullRow controlObserved).mulVec ∧
  (∀ z, Function.Injective (Matrix.mulVec
    (fun i k => if controlExposure z i=k then (1:ℝ) else 0 :
      Matrix (Fin 4 × Fin 2) (Fin 4) ℝ)))

end SAP.P037c
