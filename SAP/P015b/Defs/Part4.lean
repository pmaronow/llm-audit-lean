import Mathlib
import SAP.P015b.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P015b

universe u v

noncomputable section
open Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal NNReal
attribute [local instance] Classical.propDecidable

def CausalOLSConvergence : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (D Y₀ τ : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (hD : ∀ i, Measurable (D i)) (hY : ∀ i, Measurable (Y₀ i))
    (hτ : ∀ i, Measurable (τ i)) (hX : ∀ i, Measurable (X i))
    (hiid : iIndepFun (fun i s => (D i s,Y₀ i s,τ i s,X i s)) P)
    (hident : ∀ i, IdentDistrib (fun s => (D i s,Y₀ i s,τ i s,X i s))
      (fun s => (D 0 s,Y₀ 0 s,τ 0 s,X 0 s)) P P)
    (hunconf : CondIndepFun (MeasurableSpace.comap (X 0) inferInstance)
      (Measurable.comap_le (hX 0)) (fun s => (Y₀ 0 s,τ 0 s)) (D 0) P)
    (ω : Fin (K+1) → ℝ)
    (hlinear : P[D 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[P]
      fun s => dotProduct (controlVector (X 0 s)) ω)
    (hreg : RegressionRegularity P D Y₀ τ X)
    (_hdefined : EventuallyDefinedRegression P D X)
    (_hDint : Integrable (D 0) P)
    (_hnum : Integrable (fun s => squaredPopulationResidual P (D 0) (X 0) s*τ 0 s) P),
    TendstoInMeasure P (treatmentEstimate D Y₀ τ X) atTop
      (fun _ => (∫ s, squaredPopulationResidual P (D 0) (X 0) s*τ 0 s ∂P)/
        (∫ s, squaredPopulationResidual P (D 0) (X 0) s ∂P))

def UnconfoundedMoments : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (D Y₀ τ : Ω → ℝ) (X : Ω → Fin K → ℝ) (hX : Measurable X)
    (hD : Measurable D) (hY : Measurable Y₀) (hτ : Measurable τ)
    (hunconf : CondIndepFun (MeasurableSpace.comap X inferInstance)
      (Measurable.comap_le hX) (fun s => (Y₀ s,τ s)) D P)
    (ω : Fin (K+1) → ℝ)
    (hlinear : P[D | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun s => dotProduct (controlVector (X s)) ω)
    (hiD : Integrable D P) (hiY : Integrable Y₀ P) (hiτ : Integrable τ P)
    (hiDY : Integrable (fun s => D s*Y₀ s) P)
    (himY : Integrable (fun s => dotProduct (controlVector (X s)) ω*Y₀ s) P)
    (hirτ : Integrable (fun s => (D s-dotProduct (controlVector (X s)) ω)*τ s) P)
    (hirmτ : Integrable (fun s => (D s-dotProduct (controlVector (X s)) ω)*
      dotProduct (controlVector (X s)) ω*τ s) P),
    (P[(fun s => D s*Y₀ s) | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun s => P[D | MeasurableSpace.comap X inferInstance] s*
        P[Y₀ | MeasurableSpace.comap X inferInstance] s) ∧
    (P[(fun s => (D s-dotProduct (controlVector (X s)) ω)*τ s) |
      MeasurableSpace.comap X inferInstance] =ᵐ[P] fun _ => 0) ∧
    ((∫ s, D s*Y₀ s ∂P)-(∫ s, dotProduct (controlVector (X s)) ω*Y₀ s ∂P)=0) ∧
    (∫ s, (D s-dotProduct (controlVector (X s)) ω)*dotProduct (controlVector (X s)) ω*τ s ∂P)=0

def T15Statement : Prop := CausalOLSConvergence.{u} ∧ UnconfoundedMoments.{u}

def T22Statement : Prop := CausalOLSConvergence.{u}

def T23Statement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (D Z : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (hD : ∀ i, Measurable (D i)) (hZ : ∀ i, Measurable (Z i)) (hX : ∀ i, Measurable (X i))
    (hiid : iIndepFun (fun i s => (D i s,Z i s,X i s)) P)
    (hident : ∀ i, IdentDistrib (fun s => (D i s,Z i s,X i s)) (fun s => (D 0 s,Z 0 s,X 0 s)) P P)
    (ω : Fin (K+1) → ℝ)
    (hlinear : P[D 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[P]
      fun s => dotProduct (controlVector (X 0 s)) ω)
    (hreg : EffectiveMeanRegularity P D Z X ω)
    (_hdefined : EventuallyDefinedEffectiveMean P D X)
    (_hDint : Integrable (D 0) P)
    (_hwint : Integrable (squaredPopulationResidual P (D 0) (X 0)) P)
    (_hnum : Integrable (fun s => squaredPopulationResidual P (D 0) (X 0) s*Z 0 s) P)
    (_hwpos : 0  <  ∫ s, squaredPopulationResidual P (D 0) (X 0) s ∂P),
    TendstoInMeasure P (fun n s =>
      (∑ i : Fin n, fittedTreatmentResidual D X n s i^2*Z i s)/(∑ i : Fin n, fittedTreatmentResidual D X n s i^2))
      atTop (fun _ => (∫ s, squaredPopulationResidual P (D 0) (X 0) s*Z 0 s ∂P)/
        (∫ s, squaredPopulationResidual P (D 0) (X 0) s ∂P))

def RandomizedOLSConvergence : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (D Y₀ τ : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (hD : ∀ i, Measurable (D i)) (hY : ∀ i, Measurable (Y₀ i))
    (hτ : ∀ i, Measurable (τ i)) (hX : ∀ i, Measurable (X i))
    (hiid : iIndepFun (fun i s => (D i s,Y₀ i s,τ i s,X i s)) P)
    (hident : ∀ i, IdentDistrib (fun s => (D i s,Y₀ i s,τ i s,X i s))
      (fun s => (D 0 s,Y₀ 0 s,τ 0 s,X 0 s)) P P)
    (hrandom : IndepFun (D 0) (fun s => (Y₀ 0 s,τ 0 s,X 0 s)) P)
    (hreg : RegressionRegularity P D Y₀ τ X)
    (_hdefined : EventuallyDefinedRegression P D X)
    (_hτint : Integrable (τ 0) P),
    TendstoInMeasure P (treatmentEstimate D Y₀ τ X) atTop (fun _ => ∫ s, τ 0 s ∂P)

def RandomizationCancellation : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (D Y₀ τ : Ω → ℝ) (X : Ω → Fin K → ℝ)
    (hD : Measurable D) (hY : Measurable Y₀) (hτ : Measurable τ) (hX : Measurable X)
    (hrandom : IndepFun D (fun s=>(Y₀ s,τ s,X s)) P)
    (h₂ : MemLp D 2 P) (hτi : Integrable τ P) (hpos : 0 < variance D P),
    (P[D|MeasurableSpace.comap X inferInstance]=ᵐ[P] fun _=>∫s,D s∂P) ∧
    (squaredPopulationResidual P D X=ᵐ[P] fun s=>(D s-(∫t,D t∂P))^2) ∧
    (∫s,squaredPopulationResidual P D X s*τ s∂P)=
      (∫s,squaredPopulationResidual P D X s∂P)*(∫s,τ s∂P) ∧
    (∫s,squaredPopulationResidual P D X s*τ s∂P)/(∫s,squaredPopulationResidual P D X s∂P)=∫s,τ s∂P

def T24Statement : Prop := RandomizedOLSConvergence.{u} ∧ RandomizationCancellation.{u}

end
end SAP.P015b
