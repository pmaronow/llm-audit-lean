import SAP.P026b.Defs
import AronowAudit.P026.P026_PaperScope
import AronowAudit.P026.P026_CompletePaper
import AronowAudit.P026.P026_LogitCompletion
import AronowAudit.P026.P026_Refutations
import AronowAudit.P026.Wave1.Gap.FidP026

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026b.Bridge
open Finset
open scoped BigOperators
noncomputable section

/-- Preserve the weight and allocation maps without changing the sample space. -/
def toDesign {Ω I R : Type*} (D : Design Ω I R) : AronowAudit.P026.Design Ω I R :=
  ⟨D.weight, D.treatment⟩

def fromDesign {Ω I R : Type*} (D : AronowAudit.P026.Design Ω I R) : Design Ω I R :=
  ⟨D.weight, D.treatment⟩

theorem to_from {Ω I R : Type*} (D : AronowAudit.P026.Design Ω I R) :
    toDesign (fromDesign D) = D := rfl

def toUnit {I : Type*} [Fintype I] [DecidableEq I] (E : UnitExperiment I) :
    AronowAudit.P026.PaperScope.UnitExperiment I :=
  ⟨E.weight, E.nonnegative, E.normalized, E.positive⟩

def toCluster {U C : Type*} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
    (E : ClusterExperiment U C) : AronowAudit.P026.PaperScope.ClusterExperiment U C :=
  ⟨E.cluster, E.covers, toUnit E.assignment⟩

/-- All finite randomization operations agree by their identical sum definitions. -/
theorem expectation_eq {Ω I R : Type*} [Fintype Ω] [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (D : Design Ω I R) (f : Ω → R) :
    AronowAudit.P026.expectation (toDesign D) f = expectation D f := rfl

theorem unit_design_eq {I : Type*} [Fintype I] [DecidableEq I] (E : UnitExperiment I) :
    (toUnit E).design = toDesign E.design := rfl

theorem cluster_design_eq {U C : Type*} [Fintype U] [DecidableEq U]
    [Fintype C] [DecidableEq C] (E : ClusterExperiment U C) :
    (toCluster E).clusterDesign = toDesign E.clusterDesign ∧
    (toCluster E).unitDesign = toDesign E.unitDesign ∧
    (toCluster E).totals = E.totals := ⟨rfl, rfl, rfl⟩

/-- Encode any evaluated prediction array in the project's finite rule interface. -/
def encodePrediction {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → Bool) → I → ℝ) :
    AronowAudit.P026.PaperScope.PredictionRule I (Fintype.card I) (Fintype.card I) where
  covariates i j := if Fintype.equivFin I i = j then 1 else 0
  fit w _ j := f w ((Fintype.equivFin I).symm j)
  predict x θ := ∑ j, x j * θ j

theorem encoded_values {I : Type*} [Fintype I] [DecidableEq I]
    (E : UnitExperiment I) (y1 y0 : I → ℝ) (f : (I → Bool) → I → ℝ) :
    (encodePrediction f).values (toUnit E) y1 y0 = f := by
  funext w i
  simp [AronowAudit.P026.PaperScope.PredictionRule.values, encodePrediction]

/-- OLS column spaces, projections and minimization predicates are definitionally equal. -/
theorem olsFitted_eq {I : Type*} [Fintype I] (K : ℕ)
    (V : Matrix I (Fin K) ℝ) (y : I → ℝ) :
    AronowAudit.P026.Wave1.olsFitted K V y = olsFitted K V y := rfl

/-- Equation [25] followed by the existing observed/potential masking identity. -/
theorem observed_residual {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (E : UnitExperiment I) (y1 y0 : I → ℝ) (f : (I → Bool) → I → ℝ) (w : I → Bool) :
    generalized E.design (Fintype.card I) y1 y0 f w =
      residualContrast E.design (Fintype.card I) y1 y0 f w := by
  have h := AronowAudit.P026.PaperScope.generalized_residual_T16
    (toUnit E) y1 y0 _ _ (encodePrediction f) w
  rw [encoded_values] at h
  change generalized E.design (Fintype.card I) y1 y0 f w =
    ht E.design (Fintype.card I) (fun i => y1 i-f w i) (fun i => y0 i-f w i) w at h
  rw [h]
  have mask := AronowAudit.P026.observed_mask (toDesign E.design)
  change ((∑ i, indicator E.design true w i * (y1 i-f w i) / marginal E.design true i) -
    (∑ i, indicator E.design false w i * (y0 i-f w i) / marginal E.design false i)) /
      (Fintype.card I : ℝ) = _
  simp only [residualContrast, mul_sub]
  simp only [show ∀ a i, indicator E.design a w i * observed E.design y1 y0 w i =
      indicator E.design a w i * (if a then y1 i else y0 i) from fun a i => mask a y1 y0 w i,
    Bool.false_eq_true, ↓reduceIte]

end
end SAP.P026b.Bridge
