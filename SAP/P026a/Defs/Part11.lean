import SAP.P026a.Defs.Part10

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a
open Finset
open scoped BigOperators
noncomputable section


/-- Mathematical content of target P026-T7. -/
def T7Statement : Prop :=
  (0 < (∑ i, (paperTableCenteredX i)^2) ∧
    ∀ w : Fin 6 × Fin 15, 0 < (∑ i, (paperFeTreatmentResidual w i)^2)) ∧
  ((mean paperTableDesign (htContrast paperTableDesign 16 paperTableLinearResidual paperTableLinearResidual)=0 ∧
    designVariance paperTableDesign (htContrast paperTableDesign 16 paperTableLinearResidual paperTableLinearResidual)=38307/634880 ∧
    mean paperTableDesign (printedVarianceEstimate paperTableDesign 16 paperTableLinearResidual paperTableLinearResidual)=38307/634880 ∧
    designVariance paperTableDesign (printedVarianceEstimate paperTableDesign 16 paperTableLinearResidual paperTableLinearResidual)=
      2400328658503/15687787688755200)
    ∧ (sdRoundsToThree (38307/634880) (246/1000) ∧ roundsToThree (38307/634880) (60/1000) ∧
    sdRoundsToThree (2400328658503/15687787688755200) (12/1000))
    ∧ ((-145/10000 : ℚ) < mean paperTableDesign paperFeEstimate ∧
    mean paperTableDesign paperFeEstimate < -135/10000 ∧
    (775/10000 : ℚ) < designVariance paperTableDesign paperFeEstimate ∧
    designVariance paperTableDesign paperFeEstimate < 785/10000 ∧
    sdRoundsToThree (designVariance paperTableDesign paperFeEstimate) (279/1000) ∧
    sdRoundsToThree (designVariance paperTableDesign paperFeEstimate+(mean paperTableDesign paperFeEstimate)^2) (279/1000) ∧
    (38307/634880 : ℚ) < designVariance paperTableDesign paperFeEstimate+(mean paperTableDesign paperFeEstimate)^2)
    ∧ ((∀ k, fiberTotal paperTableCluster paperTableY k=paperTableClusterY k ∧
      fiberTotal paperTableCluster (fun i => paperTableY i-1/2) k=paperTablePriorResidual k) ∧
    mean paperTableDesign (htContrast paperTableDesign 16 paperTableClusterY paperTableClusterY)=0 ∧
    designVariance paperTableDesign (htContrast paperTableDesign 16 paperTableClusterY paperTableClusterY)=353/1920 ∧
    mean paperTableDesign (printedVarianceEstimate paperTableDesign 16 paperTableClusterY paperTableClusterY)=353/1920 ∧
    mean paperTableDesign (htContrast paperTableDesign 16 paperTablePriorResidual paperTablePriorResidual)=0 ∧
    designVariance paperTableDesign (htContrast paperTableDesign 16 paperTablePriorResidual paperTablePriorResidual)=233/2560 ∧
    mean paperTableDesign (printedVarianceEstimate paperTableDesign 16 paperTablePriorResidual paperTablePriorResidual)=233/2560 ∧
    roundsToThree (353/1920) (184/1000) ∧ roundsToThree (233/2560) (91/1000)))

end
end SAP.P026a
