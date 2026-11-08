import SAP.P026a.Defs.Part8

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a
open Finset
open scoped BigOperators
noncomputable section


/-- Mathematical content of target P026-T5. -/
def T5Statement : Prop :=
  (∀ {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitLaw I)
    {Θ :  Type*}
    (i :  I)
    (J :  Finset I)
    (y1 y0 :  I → ℝ)
    (G :  (↥J → ℝ) → Θ)
    (P :  Θ → ℝ)
    (h :  finiteIndependent E.assignmentDesign (fun w => E.assignmentDesign.treatment w i) (fittingIndicators E.assignmentDesign J)),
    finiteIndependent E.assignmentDesign (fun w => E.assignmentDesign.treatment w i) (fun w => G (fittingResponses E.assignmentDesign J y1 y0 w)) ∧
    finiteIndependent E.assignmentDesign (fun w => E.assignmentDesign.treatment w i) (fun w => P (G (fittingResponses E.assignmentDesign J y1 y0 w))) ∧
    designCovariance E.assignmentDesign (fun w => armIndicator E.assignmentDesign true w i)
      (fun w => P (G (fittingResponses E.assignmentDesign J y1 y0 w))) = 0) ∧
  (∀ {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitLaw I)
    {Θ :  Type*}
    (i :  I)
    (J :  Finset I)
    (y1 y0 :  I → ℝ)
    (G :  (↥J → ℝ) → Θ)
    (P :  Θ → ℝ)
    (h :  finiteIndependent E.assignmentDesign (fun w => E.assignmentDesign.treatment w i) (fittingResponses E.assignmentDesign J y1 y0)),
    finiteIndependent E.assignmentDesign (fun w => E.assignmentDesign.treatment w i) (fun w => G (fittingResponses E.assignmentDesign J y1 y0 w)) ∧
    finiteIndependent E.assignmentDesign (fun w => E.assignmentDesign.treatment w i) (fun w => P (G (fittingResponses E.assignmentDesign J y1 y0 w))) ∧
    designCovariance E.assignmentDesign (fun w => armIndicator E.assignmentDesign true w i)
      (fun w => P (G (fittingResponses E.assignmentDesign J y1 y0 w))) = 0) ∧
  (∀ {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitLaw I)
    (x z :  I → ℝ)
    (J :  I → Finset I)
    (G :  ∀ i, (↥(J i) → ℝ) → ℝ)
    (h :  ∀ i, finiteIndependent E.assignmentDesign (fun w => E.assignmentDesign.treatment w i) (fittingIndicators E.assignmentDesign (J i))),
    let f : (I → Bool) → I → ℝ := fun w i => G i (fittingResponses E.assignmentDesign (J i) x z w)
    mean E.assignmentDesign (adjustedSum E.assignmentDesign true x f)=fixedTotal x ∧
    mean E.assignmentDesign (adjustedSum E.assignmentDesign false z f)=fixedTotal z ∧
    mean E.assignmentDesign (adjustedContrast E.assignmentDesign (Fintype.card I) x z f)=averageEffect (Fintype.card I) x z) ∧
  (∀ {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitLaw I)
    (i :  I)
    (J :  Finset I)
    (x z :  I → ℝ)
    (a :  ℝ)
    (b :  ↥J → ℝ)
    (h :  ∀ j : ↥J, finiteIndependent E.assignmentDesign (fun w => E.assignmentDesign.treatment w i) (fun w => E.assignmentDesign.treatment w j)),
    designCovariance E.assignmentDesign (fun w => armIndicator E.assignmentDesign true w i)
      (fun w => a+∑ j : ↥J, b j*response E.assignmentDesign x z w j) =
        ∑ j : ↥J, b j*(x j-z j)*designCovariance E.assignmentDesign
          (fun w => armIndicator E.assignmentDesign true w i) (fun w => armIndicator E.assignmentDesign true w j) ∧
    designCovariance E.assignmentDesign (fun w => armIndicator E.assignmentDesign true w i)
      (fun w => a+∑ j : ↥J, b j*response E.assignmentDesign x z w j)=0) ∧
  (∀ {I : Type*} [Fintype I] [DecidableEq I]
    (E : UnitLaw I) (h : independentAssignments E.assignmentDesign) (i : I),
    finiteIndependent E.assignmentDesign (fun w => w i) (fittingIndicators E.assignmentDesign (univ.erase i))) ∧
  (∀ {I B : Type*} [Fintype I] [DecidableEq I]
    [Fintype B] [DecidableEq B] (E : UnitLaw I) (c : I → B)
    (h : independentBlocks E.assignmentDesign c) (i : I),
    finiteIndependent E.assignmentDesign (fun w => w i)
      (fittingIndicators E.assignmentDesign (univ.filter (fun j => c j≠c i))))

end
end SAP.P026a
