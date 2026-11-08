import SAP.P001a.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix

noncomputable section

universe u1 u2 u3 u4 u5 u6 u7 u8

namespace SAP.P001a.Bridge

theorem T8_correspondence : SAP.P001a.T8Statement.{u1,u2,u3} ↔
  ((∀ {Ω : Type u1} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] {K τ : ℕ}
  (X : Ω → Fin K → ℝ) (Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
  (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX]
  (κ : Measure ℝ) [SFinite κ] (f : ℝ → (Fin K → ℝ) → ℝ)
  (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (t : Fin τ → ℝ)
  (hf : Measurable (fun xy : (Fin K → ℝ) × ℝ => f xy.2 xy.1))
  (hg : Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
  (hfn : ∀ y x, 0 ≤ f y x) (hgn : ∀ y x, 0 ≤ g y x t)
  (hfnorm : ∀ x, (∫⁻ y, ENNReal.ofReal (f y x) ∂κ)=1)
  (hgnorm : ∀ x, (∫⁻ y, ENNReal.ofReal (g y x t) ∂κ)=1)
  (htrue : μ.map (fun ω => (X ω,Y ω)) =
    (νX.prod κ).withDensity (fun xy => ENNReal.ofReal (f xy.2 xy.1)))
  (hdom : ∀ᵐ xy ∂(νX.prod κ), 0 < f xy.2 xy.1 → 0 < g xy.2 xy.1 t)
  (hent : Integrable (fun xy : (Fin K → ℝ) × ℝ =>
    f xy.2 xy.1*Real.log (f xy.2 xy.1)) (νX.prod κ))
  (hcross : Integrable (fun xy : (Fin K → ℝ) × ℝ =>
    f xy.2 xy.1*Real.log (g xy.2 xy.1 t)) (νX.prod κ)),
  AronowAudit.P001.averageKLExt νX κ f g t ≠ ∞ ∧
  (AronowAudit.P001.averageKLExt νX κ f g t).toReal =
    (∫ x, ∫ y, f y x*Real.log (f y x) ∂κ ∂νX) - AronowAudit.P001.expectedLogLikelihood μ X Y g t ∧
  AronowAudit.P001.averageKL νX κ f g t = (AronowAudit.P001.averageKLExt νX κ f g t).toReal) ∧

(∀ {Ω : Type u2} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] {K τ : ℕ}
  (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
  (hiid : AronowAudit.P001.IID μ (fun i ω => (X i ω,Y i ω)))
  (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
  (f : ℝ → (Fin K → ℝ) → ℝ)
  (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
  (hf : Measurable (fun xy : (Fin K → ℝ) × ℝ => f xy.2 xy.1))
  (hfn : ∀ y x, 0 ≤ f y x) (hfnorm : ∀ x, (∫⁻ y, ENNReal.ofReal (f y x) ∂κ)=1)
  (htrue : μ.map (fun ω => (X 0 ω,Y 0 ω)) =
    (νX.prod κ).withDensity (fun xy => ENNReal.ofReal (f xy.2 xy.1)))
  (Θ : Set (Fin τ → ℝ))
  (commonS : Set ((Fin K → ℝ) × ℝ)) (hCommonS : MeasurableSet commonS)
  (hCommonSfull : (μ.map (fun ω => (X 0 ω, Y 0 ω))) commonS = 1)
  (hCommonPositive : ∀ xy ∈ commonS, ∀ t ∈ Θ, 0 < g xy.2 xy.1 t)
  (hg : ∀ t ∈ Θ, Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
  (hgn : ∀ t ∈ Θ, ∀ y x, 0 ≤ g y x t)
  (hgnorm : ∀ t ∈ Θ, ∀ x, (∫⁻ y, ENNReal.ofReal (g y x t) ∂κ)=1)
  (hdom : ∀ t ∈ Θ, ∀ᵐ xy ∂(νX.prod κ), 0 < f xy.2 xy.1 → 0 < g xy.2 xy.1 t)
  (hlog : ∀ t ∈ Θ, Integrable (fun ω => Real.log (g (Y 0 ω) (X 0 ω) t)) μ)
  (tstar : Fin τ → ℝ) (ht : tstar ∈ Θ)
  (hsep : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Θ,
    ε ≤ dist t tstar → AronowAudit.P001.expectedLogLikelihood μ (X 0) (Y 0) g t ≤
      AronowAudit.P001.expectedLogLikelihood μ (X 0) (Y 0) g tstar-δ)
  (that : ℕ → Ω → Fin τ → ℝ) (hm : ∀ n, Measurable (that n))
  (hthat : ∀ n ω, that n ω ∈ Θ)
  (e Δ : ℕ → Ω → ℝ) (hen : ∀ n ω, 0 ≤ e n ω)
  (he : AronowAudit.P001.CP μ e 0) (hΔ : AronowAudit.P001.CP μ Δ 0)
  (hbound : ∀ n ω t, t ∈ Θ →
    |AronowAudit.P001.sampleLogLikelihood X Y g n ω t-AronowAudit.P001.expectedLogLikelihood μ (X 0) (Y 0) g t| ≤ Δ n ω)
  (hmax : (∀ n ω t, t ∈ Θ →
    AronowAudit.P001.sampleLikelihood X Y g n ω t ≤ AronowAudit.P001.sampleLikelihood X Y g n ω (that n ω)) ∨
    (∀ n ω t, t ∈ Θ → AronowAudit.P001.sampleLogLikelihood X Y g n ω t-e n ω ≤
      AronowAudit.P001.sampleLogLikelihood X Y g n ω (that n ω))),
  AronowAudit.P001.CP μ that tstar ∧
  ((Integrable (fun xy : (Fin K → ℝ) × ℝ =>
      f xy.2 xy.1*Real.log (f xy.2 xy.1)) (νX.prod κ) ∧
    ∀ t ∈ Θ, Integrable (fun xy : (Fin K → ℝ) × ℝ =>
      f xy.2 xy.1*Real.log (g xy.2 xy.1 t)) (νX.prod κ)) →
    ∀ t ∈ Θ, AronowAudit.P001.averageKLExt νX κ f g tstar ≤ AronowAudit.P001.averageKLExt νX κ f g t ∧
      (AronowAudit.P001.averageKLExt νX κ f g t = AronowAudit.P001.averageKLExt νX κ f g tstar → t=tstar))) ∧

(∀ {E : Type u3} [MetricSpace E] (Θ : Set E) (hc : IsCompact Θ)
   (θ : E) (hθ : θ∈Θ) (M : E → ℝ) (hM : ContinuousOn M Θ)
   (hu : ∀ t∈Θ,M t ≤ M θ ∧ (M t=M θ → t=θ)),
  ∀ ε : ℝ,0 < ε → ∃ δ : ℝ,0 < δ ∧ ∀ t∈Θ,ε ≤ dist t θ → M t ≤ M θ-δ) ∧

(∀ {K τ : ℕ} (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX]
  (κ : Measure ℝ) [SFinite κ]
  (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
  (Θ : Set (Fin τ → ℝ)) (θ tstar : Fin τ → ℝ) (hθ : θ ∈ Θ) (ht : tstar ∈ Θ)
  (hg : ∀ t ∈ Θ, Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
  (hgn : ∀ t ∈ Θ, ∀ y x, 0 ≤ g y x t)
  (hnorm : ∀ t ∈ Θ, ∀ x, (∫⁻ y, ENNReal.ofReal (g y x t) ∂κ) = 1)
  (hunique : ∀ t ∈ Θ,
    AronowAudit.P001.averageKLExt νX κ (fun y x => g y x θ) g tstar ≤
      AronowAudit.P001.averageKLExt νX κ (fun y x => g y x θ) g t ∧
    (AronowAudit.P001.averageKLExt νX κ (fun y x => g y x θ) g t =
      AronowAudit.P001.averageKLExt νX κ (fun y x => g y x θ) g tstar → t = tstar)),
  AronowAudit.P001.averageKLExt νX κ (fun y x => g y x θ) g θ = 0 ∧
  tstar = θ ∧
  (∀ t ∈ Θ, AronowAudit.P001.averageKLExt νX κ (fun y x => g y x θ) g t = 0 ↔ t = θ))) := Iff.rfl

theorem T9_correspondence : SAP.P001a.T9Statement ↔
  ((∀ B : ℝ, ∃ σ : ℝ, 0  <  σ ∧ AronowAudit.P001.MixtureAdmissible ![1/2,1/4,1,σ,0,1,1] ∧
   B  <  AronowAudit.P001.mixtureLikelihood ![1,2,3] ![1/2,1/4,1,σ,0,1,1]) ∧
   ¬ ∃ θ : Fin 7 → ℝ, AronowAudit.P001.MixtureAdmissible θ ∧ ∀ θ', AronowAudit.P001.MixtureAdmissible θ' →
     AronowAudit.P001.mixtureLikelihood ![1,2,3] θ'  ≤  AronowAudit.P001.mixtureLikelihood ![1,2,3] θ) := Iff.rfl

theorem T10_correspondence : SAP.P001a.T10Statement ↔
  ((∀ {n : ℕ} (hn : 0  <  n) (y : Fin n → ℝ) (hy : ∀ i, 0  <  y i),
  (∀ B : ℝ, ∃ θ : Fin 7 → ℝ, AronowAudit.P001.MixtureAdmissible θ ∧ B  <  AronowAudit.P001.mixtureLikelihood y θ) ∧
  (¬ ∃ θ : Fin 7 → ℝ, AronowAudit.P001.MixtureAdmissible θ ∧ ∀ θ', AronowAudit.P001.MixtureAdmissible θ' →
     AronowAudit.P001.mixtureLikelihood y θ' ≤ AronowAudit.P001.mixtureLikelihood y θ)) ∧

(∀ {n : ℕ} (y : Fin n → ℝ) (hy : ∀ i, 0  <  y i)
   (B S δ a b : ℝ) (hδ : 0  <  δ) (ha : 0  <  a)
   (hne : (AronowAudit.P001.mixtureRestriction B S δ a b).Nonempty),
  IsCompact (AronowAudit.P001.mixtureRestriction B S δ a b) ∧
   ContinuousOn (AronowAudit.P001.mixtureLikelihood y) (AronowAudit.P001.mixtureRestriction B S δ a b) ∧
   ∃ θ ∈ AronowAudit.P001.mixtureRestriction B S δ a b, ∀ θ' ∈ AronowAudit.P001.mixtureRestriction B S δ a b,
     AronowAudit.P001.mixtureLikelihood y θ'  ≤  AronowAudit.P001.mixtureLikelihood y θ)) := Iff.rfl

theorem T11_correspondence : SAP.P001a.T11Statement ↔
  ((AronowAudit.P001.UnusedMixtureWitness ∧
  ∃ T : (n : ℕ) → (Fin n → Fin 4) → Fin 3 → ℝ,
    (∀ n (y : Fin n → Fin 4),
      T n y ∈ AronowAudit.P001.disjointMixtureParameterSet ∧
      ∀ u ∈ AronowAudit.P001.disjointMixtureParameterSet,
        AronowAudit.P001.disjointMixtureLikelihood y u ≤ AronowAudit.P001.disjointMixtureLikelihood y (T n y)) ∧
    (¬ AronowAudit.P001.FiniteMixtureConsistent T (![1, 1/3, 1/4] : Fin 3 → ℝ) ∨
     ¬ AronowAudit.P001.FiniteMixtureConsistent T (![1, 1/3, 3/4] : Fin 3 → ℝ))) ∧

(IsCompact AronowAudit.P001.disjointMixtureParameterSet ∧
   (![1,1/3,1/4] : Fin 3 → ℝ)∈AronowAudit.P001.disjointMixtureParameterSet ∧
   (![1,1/3,3/4] : Fin 3 → ℝ)∈AronowAudit.P001.disjointMixtureParameterSet ∧
   ∀ n (y : Fin n → Fin 4),Continuous (AronowAudit.P001.disjointMixtureLikelihood y) ∧
     ∃ t∈AronowAudit.P001.disjointMixtureParameterSet,∀ u∈AronowAudit.P001.disjointMixtureParameterSet,
       AronowAudit.P001.disjointMixtureLikelihood y u ≤ AronowAudit.P001.disjointMixtureLikelihood y t)) := Iff.rfl

theorem T12_correspondence : SAP.P001a.T12Statement.{u1,u2} ↔
  ((∀ {M K τ : ℕ}
  (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
  (p : (Fin τ → ℝ) → Fin M → ℝ)
  (g : Fin M → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
  (θ θ' : Fin τ → ℝ) (hθ : θ ≠ θ') (j : Fin M)
  (hp : p θ=p θ') (hpzero : p θ j=0)
  (hweight : (∀ k, 0 ≤ p θ k) ∧ (∑ k, p θ k)=1)
  (heq : ∀ k, k ≠ j → ∀ y x, g k y x θ=g k y x θ')
  (hg : ∀ t ∈ ({θ,θ'} : Set (Fin τ → ℝ)), ∀ k,
    Measurable (fun xy : (Fin K → ℝ) × ℝ => g k xy.2 xy.1 t))
  (hnonneg : ∀ t ∈ ({θ,θ'} : Set (Fin τ → ℝ)), ∀ k y x, 0 ≤ g k y x t)
  (hnorm : ∀ t ∈ ({θ,θ'} : Set (Fin τ → ℝ)), ∀ k x,
    (∫⁻ y, ENNReal.ofReal (g k y x t) ∂κ)=1)
  (hlog : Integrable (fun xy : (Fin K → ℝ) × ℝ =>
    Real.log (AronowAudit.P001.mixtureFamily p g xy.2 xy.1 θ))
    (AronowAudit.P001.conditionalModelLaw νX κ (AronowAudit.P001.mixtureFamily p g) θ)),
  (∀ y x, AronowAudit.P001.mixtureFamily p g y x θ=AronowAudit.P001.mixtureFamily p g y x θ') ∧
  AronowAudit.P001.conditionalModelLaw νX κ (AronowAudit.P001.mixtureFamily p g) θ=
    AronowAudit.P001.conditionalModelLaw νX κ (AronowAudit.P001.mixtureFamily p g) θ' ∧
  (∀ n, AronowAudit.P001.iidObservationLaw (AronowAudit.P001.conditionalModelLaw νX κ (AronowAudit.P001.mixtureFamily p g) θ) n=
    AronowAudit.P001.iidObservationLaw (AronowAudit.P001.conditionalModelLaw νX κ (AronowAudit.P001.mixtureFamily p g) θ') n) ∧
  AronowAudit.P001.mean (AronowAudit.P001.conditionalModelLaw νX κ (AronowAudit.P001.mixtureFamily p g) θ)
    (fun xy => Real.log (AronowAudit.P001.mixtureFamily p g xy.2 xy.1 θ)) =
  AronowAudit.P001.mean (AronowAudit.P001.conditionalModelLaw νX κ (AronowAudit.P001.mixtureFamily p g) θ')
    (fun xy => Real.log (AronowAudit.P001.mixtureFamily p g xy.2 xy.1 θ')) ∧
  (∀ T : (n : ℕ) → (Fin n → (Fin K → ℝ) × ℝ) → Fin τ → ℝ,
    (∀ n, Measurable (T n)) →
    ¬ (AronowAudit.P001.SampleCP (AronowAudit.P001.conditionalModelLaw νX κ (AronowAudit.P001.mixtureFamily p g) θ) T θ ∧
       AronowAudit.P001.SampleCP (AronowAudit.P001.conditionalModelLaw νX κ (AronowAudit.P001.mixtureFamily p g) θ') T θ'))) ∧

(∀ {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {M K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
   (hiid : AronowAudit.P001.IID μ (fun i ω => (X i ω,Y i ω)))
   (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
   (p : (Fin τ → ℝ) → Fin M → ℝ) (g : Fin M → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
   (Θ : Set (Fin τ → ℝ)) (hc : IsCompact Θ) (θ : Fin τ → ℝ) (hθ : θ∈Θ)
  (commonS : Set ((Fin K → ℝ) × ℝ)) (hCommonS : MeasurableSet commonS)
  (hCommonSfull : (μ.map (fun ω => (X 0 ω, Y 0 ω))) commonS = 1)
  (hCommonPositive : ∀ xy ∈ commonS, ∀ t ∈ Θ, 0 < AronowAudit.P001.mixtureFamily p g xy.2 xy.1 t)
   (hp : ∀ t∈Θ,(∀ m,0 ≤ p t m) ∧ (∑ m,p t m)=1)
   (hg : ∀ t∈Θ,∀ m,Measurable (fun xy : (Fin K → ℝ) × ℝ => g m xy.2 xy.1 t))
   (hnonneg : ∀ t∈Θ,∀ m y x,0 ≤ g m y x t)
   (hnorm : ∀ t∈Θ,∀ m x,(∫⁻ y,ENNReal.ofReal (g m y x t) ∂κ)=1)
   (htrue : μ.map (fun ω => (X 0 ω,Y 0 ω))=AronowAudit.P001.conditionalModelLaw νX κ (AronowAudit.P001.mixtureFamily p g) θ)
   (hlog : ∀ t∈Θ,Integrable
     (fun ω => Real.log (AronowAudit.P001.mixtureFamily p g (Y 0 ω) (X 0 ω) t)) μ)
   (hpositiveModel : ∀ t∈Θ,∀ᵐ ω ∂μ,0 < AronowAudit.P001.mixtureFamily p g (Y 0 ω) (X 0 ω) t)
   (hM : ContinuousOn (AronowAudit.P001.expectedLogLikelihood μ (X 0) (Y 0) (AronowAudit.P001.mixtureFamily p g)) Θ)
   (hunique : ∀ t∈Θ,AronowAudit.P001.expectedLogLikelihood μ (X 0) (Y 0) (AronowAudit.P001.mixtureFamily p g) t ≤ 
     AronowAudit.P001.expectedLogLikelihood μ (X 0) (Y 0) (AronowAudit.P001.mixtureFamily p g) θ ∧
     (AronowAudit.P001.expectedLogLikelihood μ (X 0) (Y 0) (AronowAudit.P001.mixtureFamily p g) t=
       AronowAudit.P001.expectedLogLikelihood μ (X 0) (Y 0) (AronowAudit.P001.mixtureFamily p g) θ → t=θ))
   (that : ℕ → Ω → Fin τ → ℝ) (hmeas : ∀ n,Measurable (that n))
   (hthat : ∀ n ω,that n ω∈Θ)
   (hmax : ∀ n ω t,t∈Θ → AronowAudit.P001.sampleLogLikelihood X Y (AronowAudit.P001.mixtureFamily p g) n ω t ≤ 
     AronowAudit.P001.sampleLogLikelihood X Y (AronowAudit.P001.mixtureFamily p g) n ω (that n ω))
   (Δ : ℕ → Ω → ℝ) (hΔ : ∀ n ω t,t∈Θ →
     |AronowAudit.P001.sampleLogLikelihood X Y (AronowAudit.P001.mixtureFamily p g) n ω t-
       AronowAudit.P001.expectedLogLikelihood μ (X 0) (Y 0) (AronowAudit.P001.mixtureFamily p g) t| ≤ Δ n ω)
   (hlim : AronowAudit.P001.CP μ Δ 0),
  AronowAudit.P001.CP μ that θ) ∧

(∀ {Ω : Type u2} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {M K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
   (hiid : AronowAudit.P001.IID μ (fun i ω => (X i ω,Y i ω)))
   (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
   (p : (Fin τ → ℝ) → Fin M → ℝ)
   (g : Fin M → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
   (Θ : Set (Fin τ → ℝ)) (θ : Fin τ → ℝ) (δ : ℝ) (hδ : 0 < δ)
   (hinterior : Metric.ball θ δ⊆Θ)
   (hp : ∀ t∈Θ,(∀ m,0 ≤ p t m) ∧ (∑ m,p t m)=1)
   (hg : ∀ t∈Θ,∀ m,Measurable (fun xy : (Fin K → ℝ) × ℝ => g m xy.2 xy.1 t))
   (hnonneg : ∀ t∈Θ,∀ m y x,0 ≤ g m y x t)
   (hnorm : ∀ t∈Θ,∀ m x,(∫⁻ y,ENNReal.ofReal (g m y x t) ∂κ)=1)
   (htrue : μ.map (fun ω => (X 0 ω,Y 0 ω))=AronowAudit.P001.conditionalModelLaw νX κ (AronowAudit.P001.mixtureFamily p g) θ)
   (S : Set ((Fin K → ℝ) × ℝ)) (hS : MeasurableSet S)
   (hSfull : (μ.map (fun ω => (X 0 ω,Y 0 ω))) S = 1)
   (hpositive : ∀ xy ∈ S,∀ t∈Metric.ball θ δ,
     0 < AronowAudit.P001.mixtureFamily p g xy.2 xy.1 t)
   (hdiff : ∀ xy ∈ S,ContDiffOn ℝ 2
     (fun t => Real.log (AronowAudit.P001.mixtureFamily p g xy.2 xy.1 t)) (Metric.ball θ δ))
   (hs2 : ∀ j,MemLp (fun ω => AronowAudit.P001.modelScore (AronowAudit.P001.mixtureFamily p g) (Y 0 ω) (X 0 ω) θ j) 2 μ)
   (hszero : ∀ j,AronowAudit.P001.mean μ (fun ω => AronowAudit.P001.modelScore (AronowAudit.P001.mixtureFamily p g) (Y 0 ω) (X 0 ω) θ j)=0)
   (hinfo : (AronowAudit.P001.informationMatrix μ (X 0) (Y 0) (AronowAudit.P001.mixtureFamily p g) θ).PosDef)
   (hHinfo : AronowAudit.P001.populationHessian μ (X 0) (Y 0) (AronowAudit.P001.mixtureFamily p g) θ=
     -AronowAudit.P001.informationMatrix μ (X 0) (Y 0) (AronowAudit.P001.mixtureFamily p g) θ)
   (hHcont : ContinuousAt (AronowAudit.P001.populationHessian μ (X 0) (Y 0) (AronowAudit.P001.mixtureFamily p g)) θ)
   (hHi : ∀ t∈Metric.ball θ δ,∀ j k,
     Integrable (fun ω => AronowAudit.P001.modelHessian (AronowAudit.P001.mixtureFamily p g) (Y 0 ω) (X 0 ω) t j k) μ)
   (ΔH : ℕ → Ω → ℝ) (hHbound : ∀ n ω t,t∈Metric.ball θ δ → ∀ j k,
     |AronowAudit.P001.sampleHessian X Y (AronowAudit.P001.mixtureFamily p g) n ω t j k-
       AronowAudit.P001.populationHessian μ (X 0) (Y 0) (AronowAudit.P001.mixtureFamily p g) t j k| ≤ ΔH n ω)
   (hHlim : AronowAudit.P001.CP μ ΔH 0)
   (that : ℕ → Ω → Fin τ → ℝ) (hmeas : ∀ n,Measurable (that n))
   (hthat : ∀ n ω,that n ω∈Θ)
   (hmax : ∀ n ω t,t∈Θ → AronowAudit.P001.sampleLikelihood X Y (AronowAudit.P001.mixtureFamily p g) n ω t ≤ 
     AronowAudit.P001.sampleLikelihood X Y (AronowAudit.P001.mixtureFamily p g) n ω (that n ω))
   
  (hcompact : IsCompact Θ) (hθ : θ ∈ Θ)
  (hlog : ∀ t ∈ Θ, Integrable (fun ω =>
    Real.log (AronowAudit.P001.mixtureFamily p g (Y 0 ω) (X 0 ω) t)) μ)
  (hposAll : ∀ xy ∈ S, ∀ t ∈ Θ, 0 < AronowAudit.P001.mixtureFamily p g xy.2 xy.1 t)
  (hM : ContinuousOn (AronowAudit.P001.expectedLogLikelihood μ (X 0) (Y 0) (AronowAudit.P001.mixtureFamily p g)) Θ)
  (hunique : ∀ t ∈ Θ,
    AronowAudit.P001.expectedLogLikelihood μ (X 0) (Y 0) (AronowAudit.P001.mixtureFamily p g) t ≤
      AronowAudit.P001.expectedLogLikelihood μ (X 0) (Y 0) (AronowAudit.P001.mixtureFamily p g) θ ∧
    (AronowAudit.P001.expectedLogLikelihood μ (X 0) (Y 0) (AronowAudit.P001.mixtureFamily p g) t =
      AronowAudit.P001.expectedLogLikelihood μ (X 0) (Y 0) (AronowAudit.P001.mixtureFamily p g) θ → t=θ))
  (Δ : ℕ → Ω → ℝ) (hΔ : AronowAudit.P001.CP μ Δ 0)
  (hbound : ∀ n ω t, t ∈ Θ →
    |AronowAudit.P001.sampleLogLikelihood X Y (AronowAudit.P001.mixtureFamily p g) n ω t-
      AronowAudit.P001.expectedLogLikelihood μ (X 0) (Y 0) (AronowAudit.P001.mixtureFamily p g) t| ≤ Δ n ω)
  (hqmInt : ∃ r : ℝ, 0 < r ∧ ∀ t : Fin τ → ℝ, dist t θ < r →
    Integrable (fun xy : (Fin K → ℝ) × ℝ =>
      (Real.sqrt (AronowAudit.P001.mixtureFamily p g xy.2 xy.1 t) -
       Real.sqrt (AronowAudit.P001.mixtureFamily p g xy.2 xy.1 θ) -
       (∑ j, (t j - θ j) * AronowAudit.P001.modelScore (AronowAudit.P001.mixtureFamily p g) xy.2 xy.1 θ j) *
         Real.sqrt (AronowAudit.P001.mixtureFamily p g xy.2 xy.1 θ) / 2)^2) (νX.prod κ))
  (hqm : AronowAudit.P001.QuadraticMeanModel νX κ (AronowAudit.P001.mixtureFamily p g) θ),
  AronowAudit.P001.CP μ that θ ∧ AronowAudit.P001.WeakLimit μ (fun n ω => Real.sqrt n • (that n ω-θ))
     (AronowAudit.P001.normalVectorLaw (AronowAudit.P001.informationMatrix μ (X 0) (Y 0) (AronowAudit.P001.mixtureFamily p g) θ)⁻¹) ∧
  (∀ T : (n : ℕ) → (Fin n → (Fin K → ℝ) × ℝ) → Fin τ → ℝ,
    ∀ ψ : (Fin K → ℝ) × ℝ → Fin τ → ℝ,
    AronowAudit.P001.RegularAL (AronowAudit.P001.conditionalModelLaw νX κ (AronowAudit.P001.mixtureFamily p g)) θ T ψ →
    ∀ a : Fin τ → ℝ, 0 ≤ ∑ j, ∑ k, a j*
      (AronowAudit.P001.covarianceMatrix (AronowAudit.P001.conditionalModelLaw νX κ (AronowAudit.P001.mixtureFamily p g) θ) ψ j k-
       (AronowAudit.P001.informationMatrix μ (X 0) (Y 0) (AronowAudit.P001.mixtureFamily p g) θ)⁻¹ j k)*a k))) := Iff.rfl


end SAP.P001a.Bridge
