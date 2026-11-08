import SAP.P032.Defs
import AronowAudit.P032.P032_Dyadic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P032.Bridge

open scoped BigOperators
open Matrix MeasureTheory ProbabilityTheory Filter

noncomputable section

/-- Preserve the finite set and its two-member certificate. -/
def toAuditDyad {M : Type*} (d : DyadData M) : AronowAudit.P032.Dyad M :=
  ⟨d.members, d.two⟩

def fromAuditDyad {M : Type*} (d : AronowAudit.P032.Dyad M) : DyadData M :=
  ⟨d.members, d.two⟩

@[simp] theorem to_from_dyad {M : Type*} (d : AronowAudit.P032.Dyad M) :
    toAuditDyad (fromAuditDyad d) = d := by cases d; rfl

@[simp] theorem from_to_dyad {M : Type*} (d : DyadData M) :
    fromAuditDyad (toAuditDyad d) = d := by cases d; rfl

def toAuditDistribution {S : Type*} [Fintype S] (p : FiniteDistribution S) :
    AronowAudit.P032.FiniteLaw S := ⟨p.weight, p.nonneg, p.total⟩

theorem dyadicMask_eq {R M : Type*} [DecidableEq M]
    (d : R → DyadData M) (r s : R) :
    dyadicMask d r s = AronowAudit.P032.dyPattern (fun r => toAuditDyad (d r)) r s := rfl

theorem repeatedMask_eq {R M : Type*} [DecidableEq M]
    (d : R → DyadData M) (r s : R) :
    repeatedMask d r s = AronowAudit.P032.repeatPattern (fun r => toAuditDyad (d r)) r s := rfl

theorem memberMask_eq {R M : Type*} [DecidableEq R] [DecidableEq M]
    (d : R → DyadData M) (i : M) (r s : R) :
    memberMask d i r s = AronowAudit.P032.memberPattern (fun r => toAuditDyad (d r)) i r s := rfl

theorem recordMask_eq : @recordMask = @AronowAudit.P032.recordPattern := rfl

theorem scoreCovariance_eq : @scoreCovariance = @AronowAudit.P032.scoreSandwich := rfl

theorem quadForm_eq : @quadForm = @AronowAudit.P032.quadratic := rfl

theorem olsBread_eq : @olsBread = @AronowAudit.P032.bread := rfl

theorem leastSquares_eq : @leastSquares = @AronowAudit.P032.ols := rfl

theorem fitResidual_eq : @fitResidual = @AronowAudit.P032.olsResidual := rfl

theorem sandwichCovariance_eq : @sandwichCovariance = @AronowAudit.P032.sandwich := rfl

theorem plugInCovariance_eq : @plugInCovariance = @AronowAudit.P032.plugIn := rfl

theorem errorMoments_eq : @errorMoments = @AronowAudit.P032.errorCovariance := rfl

theorem clipEigenvalues_eq : @clipEigenvalues = @AronowAudit.P032.spectralClip := rfl

theorem psdPart_eq : @psdPart = @AronowAudit.P032.positivePart := rfl

theorem diagonalGate_eq : @diagonalGate = @AronowAudit.P032.gatedPart := rfl

/-- The numerical examples unfold to the same ordinary matrices and probability weights. -/
theorem tenCovariance_eq : tenCovariance = AronowAudit.P032.tenVariance := rfl

theorem fourWeights_eq : fourDistribution.weight = AronowAudit.P032.fourBlockLaw.weight := rfl

theorem sixWeights_eq : sixSignDistribution.weight = AronowAudit.P032.sixSignLaw.weight := rfl

/-- Only the structure packaging differs in these universal assertions. -/
theorem populationReading_toAudit (h : UniversalPopulationBound) :
    AronowAudit.P032.PrintedPopulationLowerBound := by
  intro n p k d X c A hr hp hd
  exact h n p k (fun r => fromAuditDyad (d r)) X c A hr hp hd

theorem strictReading_toAudit (h : UniversalStrictPopulationBound) :
    AronowAudit.P032.PrintedStrictPopulationLowerBound := by
  intro n p k d X c A hr hp hd
  exact h n p k (fun r => fromAuditDyad (d r)) X c A hr hp hd

theorem expectationReading_toAudit (h : UniversalExpectationBound) :
    AronowAudit.P032.PrintedExpectationLowerBound := by
  intro Ω mΩ μ hμ n p k d X β c u hr hu hm hd
  exact h Ω μ n p k (fun r => fromAuditDyad (d r)) X β c u hr hu hm hd

theorem limitReading_toAudit (h : UniversalLimitBound) :
    AronowAudit.P032.PrintedRatioLimitLowerBound := by
  intro Ω mΩ μ hμ p R M rows rowEq members memberEq d X β c u hsize hr hu hm hd hv L hl
  exact h Ω μ p R M (fun m r => fromAuditDyad (d m r)) X β c u hsize hr hu hm hd hv L hl

end
end SAP.P032.Bridge
