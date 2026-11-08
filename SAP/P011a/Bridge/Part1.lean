import SAP.P011a.Defs
import AronowAudit.P011.P011_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a.Bridge

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section

/-- The record adapter preserves all observed data and the probability witness. -/
def model {n : ℕ} (m : SAP.P011a.Model n) : AronowAudit.P011.Model n where
  law := m.law
  probability := m.probability
  theta := m.theta
  G := m.G
  R := m.R
  d := m.d

/-- Sample sizes, their growth witnesses, and all models are unchanged. -/
def family (F : SAP.P011a.Family) : AronowAudit.P011.Family where
  size := F.size
  positive := F.positive
  grows := F.grows
  model := fun k => model (F.model k)

theorem weighted_eq {n : ℕ} (m : SAP.P011a.Model n) :
    SAP.P011a.weighted m = AronowAudit.P011.weighted (model m) := rfl

theorem covariance_eq {n : ℕ} (m : SAP.P011a.Model n) :
    SAP.P011a.covariance m = AronowAudit.P011.covariance (model m) := rfl

theorem scaling_iff (F : SAP.P011a.Family) (c1 c2 c3 c4 : ℝ) :
    SAP.P011a.Scaling F c1 c2 c3 c4 ↔
      AronowAudit.P011.Scaling (family F) c1 c2 c3 c4 := Iff.rfl

theorem class_iff (F : SAP.P011a.Family)
    (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ) :
    SAP.P011a.CorrectedClass F V ↔ AronowAudit.P011.CorrectedClass (family F) V := Iff.rfl

theorem cycle_model_eq (a : ℝ) (b : ℕ) :
    model (SAP.P011a.cycleModel a b) = AronowAudit.P011.cycleModel a b := rfl

theorem cycle_family_eq (a : ℝ) :
    family (SAP.P011a.cycleFamily a) = AronowAudit.P011.cycleFamily a := rfl

theorem path_family_eq (t : ℝ) :
    family (SAP.P011a.pathFamily t) = AronowAudit.P011.pathFamily t := rfl

theorem alternating_family_eq :
    family SAP.P011a.alternatingFamily = AronowAudit.P011.alternatingFamily := rfl

theorem positive_part_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    SAP.P011a.positivePart M = AronowAudit.P011.positivePart M := rfl

end
end SAP.P011a.Bridge
