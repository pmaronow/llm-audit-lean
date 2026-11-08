import SAP.P027a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a.WH.W1.P.T4_L1

noncomputable section
open scoped BigOperators
open SAP.P027a

theorem prove : SAP.P027a.WH.W1.T4_L1 := by
  intro G Ω _ _ n hn D hv hp hae y
  let Dc := SAP.P027a.wholeRepDesign n hn D
  change quadraticA D y = quadraticA (liftDesign Dc n) y ∧
    wholeC2Bias D y = wholeC2Bias (liftDesign Dc n) y
  have hvc : Valid Dc := by
    constructor
    · intro ω
      exact hv.1 ω
    · exact hv.2
  have hbridge := SAP.P027a.WH.W1.ae_preservation_core n hn D hv hp hae y
  rcases hbridge with ⟨hpc, hpi, hj, _, _, hA⟩
  have hLiftJointRep (k l : Σ g, Fin (n g)) :
      joint (liftDesign Dc n) k l = joint Dc k.1 l.1 := rfl
  have hLiftJoint (k l : Σ g, Fin (n g)) :
      joint (liftDesign Dc n) k l = joint D k l := by
    calc
      joint (liftDesign Dc n) k l = joint Dc k.1 l.1 := hLiftJointRep k l
      _ = joint D k l := (hj k.1 l.1 k.2 l.2).symm
  have hquad : quadraticA D y = quadraticA (liftDesign Dc n) y := by
    unfold quadraticA
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [hLiftJoint k l]
  have hpcAudit : AronowAudit.P027.Positive
      (SAP.P027a.Bridge.toAudit Dc hvc) := by
    intro g
    exact hpc g
  have hAlift : biasA (liftDesign Dc n) y = biasA Dc (groupTotal n y) := by
    exact AronowAudit.P027.aggregation_A_preserved
      (SAP.P027a.Bridge.toAudit Dc hvc) hpcAudit n y
  have hAeq : biasA D y = biasA (liftDesign Dc n) y := hA.trans hAlift.symm
  have hvalidLift : Valid (liftDesign Dc n) := by
    constructor
    · intro ω
      exact hvc.1 ω
    · exact hvc.2
  have hpositiveLift : Positive (liftDesign Dc n) := fun k => hpc k.1
  constructor
  · exact hquad
  · calc
      wholeC2Bias D y = biasA D y + quadraticA D y :=
        SAP.P027a.WH.W1.c2_bias_add D hv hp y
      _ = biasA (liftDesign Dc n) y + quadraticA (liftDesign Dc n) y := by
        rw [hAeq, hquad]
      _ = wholeC2Bias (liftDesign Dc n) y :=
        (SAP.P027a.WH.W1.c2_bias_add
          (liftDesign Dc n) hvalidLift hpositiveLift y).symm

end
end SAP.P027a.WH.W1.P.T4_L1

theorem SAP.P027a.WH.W1.T4_L1_proof : SAP.P027a.WH.W1.T4_L1 :=
  SAP.P027a.WH.W1.P.T4_L1.prove
