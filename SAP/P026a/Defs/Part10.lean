import SAP.P026a.Defs.Part9

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a
open Finset
open scoped BigOperators
noncomputable section


/-- Mathematical content of target P026-T6. -/
def T6Statement : Prop :=
  (0 < (∑ i, (paperTableCenteredX i)^2) ∧
    ∀ w : Fin 6 × Fin 15, 0 < (∑ i, (paperFeTreatmentResidual w i)^2)) ∧
  (paperTableLinearResidual =
    ![1,7/8,1/4,-1/2,-15/31,19/93,1/3,-76/93,-76/93,-79/93]) ∧
  (mean paperTableDesign (htContrast paperTableDesign 16 paperTableLinearResidual paperTableLinearResidual)=0 ∧
    designVariance paperTableDesign (htContrast paperTableDesign 16 paperTableLinearResidual paperTableLinearResidual)=38307/634880 ∧
    mean paperTableDesign (printedVarianceEstimate paperTableDesign 16 paperTableLinearResidual paperTableLinearResidual)=38307/634880 ∧
    designVariance paperTableDesign (printedVarianceEstimate paperTableDesign 16 paperTableLinearResidual paperTableLinearResidual)=
      2400328658503/15687787688755200) ∧
  (designVariance paperTableDesign (htContrast paperTableDesign 16 paperTableLinearResidual paperTableLinearResidual) > 265/10000 ∧
    designVariance paperTableDesign (htContrast paperTableDesign 16 paperTableLinearResidual paperTableLinearResidual) > (1625/10000)^2 ∧
    designVariance paperTableDesign (printedVarianceEstimate paperTableDesign 16 paperTableLinearResidual paperTableLinearResidual) > (75/10000)^2) ∧
  ((-145/10000 : ℚ) < mean paperTableDesign paperFeEstimate ∧
    mean paperTableDesign paperFeEstimate < -135/10000 ∧
    (775/10000 : ℚ) < designVariance paperTableDesign paperFeEstimate ∧
    designVariance paperTableDesign paperFeEstimate < 785/10000 ∧
    sdRoundsToThree (designVariance paperTableDesign paperFeEstimate) (279/1000) ∧
    sdRoundsToThree (designVariance paperTableDesign paperFeEstimate+(mean paperTableDesign paperFeEstimate)^2) (279/1000) ∧
    (38307/634880 : ℚ) < designVariance paperTableDesign paperFeEstimate+(mean paperTableDesign paperFeEstimate)^2)

end
end SAP.P026a
