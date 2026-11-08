import SAP.P001g.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P001g

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
universe u v w z u1 v1

def T125Statement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (h2 : MemLp (X 0) 2 μ),
  CP μ (sampleMean X) (mean μ (X 0))

def CenteredCLTStatement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (h2 : MemLp (X 0) 2 μ) (hv : 0 < var μ (X 0)),
  CD μ (fun n ω => Real.sqrt n*(sampleMean X n ω-mean μ (X 0)))
     (gaussianReal 0 ⟨var μ (X 0),le_of_lt hv⟩)

def StandardizedCLTStatement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (h2 : MemLp (X 0) 2 μ)
   (hv : 0 < var μ (X 0)),
  CD μ (standardizedMean μ X) (gaussianReal 0 1)

def StandardizationMomentsStatement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (h2 : MemLp (X 0) 2 μ)
   (hv : 0 < var μ (X 0)) (n : ℕ) (hn : 0 < n),
  Real.sqrt (var μ (sampleMean X n))=Real.sqrt (var μ (X 0))/Real.sqrt n ∧
   (∀ ω,standardizedMean μ X n ω=
     Real.sqrt n*(sampleMean X n ω-mean μ (X 0))/Real.sqrt (var μ (X 0))) ∧
   mean μ (standardizedMean μ X n)=0 ∧ var μ (standardizedMean μ X n)=1 ∧
   Real.sqrt (var μ (standardizedMean μ X n))=1

def T126Statement : Prop :=
  CenteredCLTStatement.{u} ∧ StandardizedCLTStatement.{v} ∧ StandardizationMomentsStatement.{w}

def T127Statement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (f : ℝ → ℝ) (hf : HasPDF (μ.map (X 0)) f)
   (hc : Continuous f) (h : ℕ → ℝ) (hpos : ∀ n,0 < h n)
   (hzero : Tendsto h atTop (nhds 0)) (hninf : Tendsto (fun (n : ℕ) => (n : ℝ)*h n) atTop atTop),
  ∀ x : ℝ, CP μ (fun n ω => kernelDensity rectangleKernel (h n) (firstSample X n ω) x) (f x)

def T128Statement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (that vhat : ℕ → Ω → ℝ) (hthat : ∀ n,Measurable (that n)) (hvhat : ∀ n,Measurable (vhat n))
   (hpos : ∀ n ω,0 ≤ vhat n ω) (θ φ α z : ℝ) (hφ : 0 < φ) (hα : α∈Set.Ioo (0 : ℝ) 1)
   (hz : prob (gaussianReal 0 1) (Set.Iic z)=1-α/2)
   (hAN : CD μ (fun n ω => Real.sqrt n*(that n ω-θ)) (gaussianReal 0 ⟨φ^2,sq_nonneg _⟩))
   (hVC : VarianceConsistent μ vhat (φ^2)),
  ∃ c : ℝ,1-α ≤ c ∧ Tendsto (fun (n : ℕ) => prob μ {ω | θ∈Set.Ioo
     (that n ω-z*Real.sqrt (vhat n ω)) (that n ω+z*Real.sqrt (vhat n ω))}) atTop (nhds c)

def ProductMLEConsistencyStatement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
   (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
   (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
   (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (Θ : Set (Fin τ → ℝ))
   (hc : IsCompact Θ) (θ : Fin τ → ℝ) (hθ : θ∈Θ)
   (hg : ∀ t∈Θ,Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
   (hnonneg : ∀ t∈Θ,∀ y x,0 ≤ g y x t)
   (hnorm : ∀ t∈Θ,∀ x,(∫⁻ y,ENNReal.ofReal (g y x t) ∂κ)=1)
   (htrue : μ.map (fun ω => (X 0 ω,Y 0 ω))=conditionalModelLaw νX κ g θ)
   (hlog : ∀ t∈Θ,Integrable (fun ω => Real.log (g (Y 0 ω) (X 0 ω) t)) μ)
   (hpos : ∀ t∈Θ,∀ᵐ ω ∂μ,0 < g (Y 0 ω) (X 0 ω) t)
   (hM : ContinuousOn (expectedLogLikelihood μ (X 0) (Y 0) g) Θ)
   (hunique : ∀ t∈Θ,expectedLogLikelihood μ (X 0) (Y 0) g t ≤ expectedLogLikelihood μ (X 0) (Y 0) g θ ∧
     (expectedLogLikelihood μ (X 0) (Y 0) g t=expectedLogLikelihood μ (X 0) (Y 0) g θ → t=θ))
   (that : ℕ → Ω → Fin τ → ℝ) (hmeas : ∀ n,Measurable (that n))
   (hthat : ∀ n ω,that n ω∈Θ)
   (hmax : ∀ n ω t,t∈Θ → sampleLikelihood X Y g n ω t ≤ sampleLikelihood X Y g n ω (that n ω))
   (Δ : ℕ → Ω → ℝ) (hΔ : ∀ n ω t,t∈Θ →
     |sampleLogLikelihood X Y g n ω t-expectedLogLikelihood μ (X 0) (Y 0) g t| ≤ Δ n ω)
   (hlim : CP μ Δ 0),
  CP μ that θ

def ExpectedLogMaximumStatement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K τ : ℕ} (X : Ω → Fin K → ℝ) (Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
   (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
   (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
   (Θ : Set (Fin τ → ℝ)) (θ : Fin τ → ℝ) (hθ : θ∈Θ)
   (hgmeas : ∀ t∈Θ,Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
   (hgpos : ∀ t∈Θ,∀ y x,0 ≤ g y x t)
   (hgnorm : ∀ t∈Θ,∀ x,(∫⁻ y,ENNReal.ofReal (g y x t) ∂κ)=1)
   (htrue : μ.map (fun ω => (X ω,Y ω))=conditionalModelLaw νX κ g θ)
   (hdom : ∀ t∈Θ,∀ᵐ xy ∂(νX.prod κ),0 < g xy.2 xy.1 θ → 0 < g xy.2 xy.1 t)
   (hlog : ∀ t∈Θ,Integrable (fun ω => Real.log (g (Y ω) (X ω) t)) μ),
  ∀ t∈Θ,expectedLogLikelihood μ X Y g t ≤ expectedLogLikelihood μ X Y g θ ∧
     (expectedLogLikelihood μ X Y g t=expectedLogLikelihood μ X Y g θ ↔
       (fun ω => g (Y ω) (X ω) t)=ᵐ[μ](fun ω => g (Y ω) (X ω) θ))

def T129Statement : Prop :=
  ProductMLEConsistencyStatement.{u} ∧ ExpectedLogMaximumStatement.{v}

def T130Statement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y R : ℕ → Ω → ℝ)
    (hYmeas : ∀ i, Measurable (Y i)) (hRmeas : ∀ i, Measurable (R i))
    (a b : ℝ) (hab : a ≤ b)
    (hYbound : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc a b)
    (hRbinary : ∀ i, ∀ᵐ ω ∂μ, R i ω = 0 ∨ R i ω = 1)
    (hSupportR : 0 < prob μ {ω | R 0 ω = 0} ∧ 0 < prob μ {ω | R 0 ω = 1})
    (hiid : IID μ (fun i ω => (censored (Y i ω) (R i ω), R i ω))),
  let Ys := fun i ω => censored (Y i ω) (R i ω)
    let L := fun i ω => missingEndpoint (Ys i ω) (R i ω) a
    let U := fun i ω => missingEndpoint (Ys i ω) (R i ω) b
    let lower := conditionalMeanAt μ (R 0) (Ys 0) 1 * prob μ {ω | R 0 ω = 1}
      + a * prob μ {ω | R 0 ω = 0}
    let upper := conditionalMeanAt μ (R 0) (Ys 0) 1 * prob μ {ω | R 0 ω = 1}
      + b * prob μ {ω | R 0 ω = 0}
    mean μ (L 0) = lower ∧ mean μ (U 0) = upper ∧
    (∀ n, 0 < n → mean μ (sampleMean L n) = lower ∧ mean μ (sampleMean U n) = upper) ∧
    CP μ (sampleMean L) lower ∧ CP μ (sampleMean U) upper

end

end SAP.P001g
