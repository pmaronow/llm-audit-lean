import Mathlib
import SAP.P001a.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix

noncomputable section

universe u1 u2 u3 u4 u5 u6 u7 u8

namespace SAP.P001a

/-- The mathematical content packaged for target P001-T4. -/
def T4Statement : Prop :=
  ∀ {Ω : Type u1} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ}
  (X : Ω → Fin K → ℝ) (Y : Ω → ℝ) (hX : Measurable X)
  (hXi : ∀ k, Integrable (fun ω => X ω k) μ) (hY : Integrable Y μ)
  (f : (Fin K → ℝ) → ℝ) (hf : HasVectorPDF (μ.map X) f)
  (U : Set (Fin K → ℝ)) (hU : IsOpen U)
  (hmean : (fun k => mean μ (fun ω => X ω k)) ∈ U)
  (hpositive : ∀ x ∈ U, 0 < f x)
  (m m' : (Fin K → ℝ) → ℝ) (hm : IsCEF μ X Y m) (hm' : IsCEF μ X Y m')
  (hc : ContinuousOn m U) (hc' : ContinuousOn m' U)
  (k : Fin K) (a : ℝ)
  (hd : HasDerivAt (fun t => m (Function.update
    (fun j => mean μ (fun ω => X ω j)) k (mean μ (fun ω => X ω k)+t))) a 0),
  Set.EqOn m m' U ∧
  HasDerivAt (fun t => m' (Function.update
    (fun j => mean μ (fun ω => X ω j)) k (mean μ (fun ω => X ω k)+t))) a 0 ∧
  partialAt m (fun j => mean μ (fun ω => X ω j)) k =
    partialAt m' (fun j => mean μ (fun ω => X ω j)) k

/-- The mathematical content packaged for target P001-T5. -/
def T5Statement : Prop :=
  ∀ {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X Y : ℕ → Ω → ℝ) (hiid : IID μ (fun i ω => (X i ω, Y i ω)))
   (hlaw : μ.map (fun ω => (X 0 ω, Y 0 ω)) = (uniformLaw 0 1).prod (gaussianReal 0 1))
   (fit : ℕ → Ω → Polynomial ℝ)
   (hfit : IsSieveLS X Y (fun (n : ℕ) => Nat.floor ((n : ℝ)^(3/4 : ℝ))) fit),
  Tendsto (fun (n : ℕ) => Nat.floor ((n : ℝ)^(3/4 : ℝ))) atTop atTop ∧
   Tendsto (fun (n : ℕ) => (Nat.floor ((n : ℝ)^(3/4 : ℝ)) : ℝ) / n) atTop (nhds 0) ∧
   ∀ δ : ℝ, 0  <  δ → δ  ≤  1 → ∀ ε : ℝ, 0  <  ε →
     1/2  ≤  Filter.liminf (fun t : ℕ =>
       prob μ {ω | ε  <  ∫ x in Set.Icc 0 δ, ((fit (t^4) ω).eval x)^2}) atTop

/-- The mathematical content packaged for target P001-T6. -/
def T6Statement : Prop :=
  (∀ {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X Y : ℕ → Ω → ℝ) (hiid : IID μ (fun i ω => (X i ω, Y i ω)))
   (a b V : ℝ) (hab : a  <  b) (hV : 0  ≤  V) (hY2 : MemLp (Y 0) 2 μ)
   (hsupp : ∀ᵐ ω ∂μ, X 0 ω ∈ Set.Icc a b)
   (m : ℝ → ℝ) (hm : ContinuousOn m (Set.Icc a b)) (hcef : IsCEF μ (X 0) (Y 0) m)
   (hvar : ∀ A : Set ℝ, MeasurableSet A →
     (∫ ω in (X 0) ⁻¹' A, (Y 0 ω-m (X 0 ω))^2 ∂μ)  ≤  V * prob μ ((X 0) ⁻¹' A))
   (p : ℕ → Polynomial ℝ) (hdeg : ∀ k, (p k).natDegree = k)
   (horth : ∀ j k, mean μ (fun ω => (p j).eval (X 0 ω)*(p k).eval (X 0 ω)) = if j=k then 1 else 0)
   (J : ℕ → ℕ) (hJ : Tendsto J atTop atTop)
   (hrate : Tendsto (fun (n : ℕ) => ((J n+1 : ℕ) : ℝ)/n) atTop (nhds 0))
   (c : ℝ) (hc : 0  <  c)
   (hgram : Tendsto (fun (n : ℕ) => prob μ {ω | ∀ v : Fin (J n+1) → ℝ,
     c*(∑ k, (v k)^2)  ≤  (∑ i ∈ Finset.range n,
       (∑ k : Fin (J n+1), v k*(p k).eval (X i ω))^2)/(n : ℝ)}) atTop (nhds 1))
   (fit : ℕ → Ω → Polynomial ℝ) (hfit : IsSieveLS X Y J fit),
  CP μ (fun n ω => ∫ x, ((fit n ω).eval x-m x)^2 ∂(μ.map (X 0))) 0) ∧

(∀ {Ω : Type u2} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (p : ℕ → Polynomial ℝ)
   (horth : ∀ j k,mean μ (fun ω => (p j).eval (X 0 ω)*(p k).eval (X 0 ω))=if j=k then 1 else 0)
   (J : ℕ → ℕ) (zeta2 : ℕ → ℝ)
   (hrow : ∀ n,∀ᵐ ω ∂μ,(∑ k : Fin (J n+1),((p k).eval (X 0 ω))^2) ≤ zeta2 n)
   (hrate : Tendsto (fun (n : ℕ) => zeta2 n*((J n+1 : ℕ) : ℝ)/(n : ℝ)) atTop (nhds 0)),
  Tendsto (fun (n : ℕ) => prob μ {ω | ∀ v : Fin (J n+1) → ℝ,
     (1/2 : ℝ)*(∑ k,(v k)^2) ≤
       (∑ i∈Finset.range n,(∑ k : Fin (J n+1),v k*(p k).eval (X i ω))^2)/(n : ℝ)})
     atTop (nhds 1)) ∧

(∀ {Ω : Type u3} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (a b : ℝ) (hab : a < b)
   (hlaw : μ.map (X 0)=uniformLaw a b) (p : ℕ → Polynomial ℝ)
   (hdeg : ∀ k,(p k).natDegree=k)
   (horth : ∀ j k,mean μ (fun ω => (p j).eval (X 0 ω)*(p k).eval (X 0 ω))=if j=k then 1 else 0)
   (J : ℕ → ℕ)
   (hrate : Tendsto (fun (n : ℕ) => (((J n+1 : ℕ) : ℝ)^3)/(n : ℝ)) atTop (nhds 0)),
  Tendsto (fun (n : ℕ) => prob μ {ω | ∀ v : Fin (J n+1) → ℝ,
     (1/2 : ℝ)*(∑ k,(v k)^2) ≤
       (∑ i∈Finset.range n,(∑ k : Fin (J n+1),v k*(p k).eval (X i ω))^2)/(n : ℝ)})
     atTop (nhds 1)) ∧

(∀ {Ω : Type u4} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (hx : μ.map (X 0)=uniformLaw 0 1)
   (K n : ℕ) (hK : 0 < K) (hn : 0 < n) (p : Fin K → Polynomial ℝ)
   (hdeg : ∀ k,(p k).natDegree=k.val)
   (horth : ∀ j k,mean μ (fun ω => (p j).eval (X 0 ω)*(p k).eval (X 0 ω))=if j=k then 1 else 0),
  (∀ x∈Set.Icc (0 : ℝ) 1,(∑ k,((p k).eval x)^2) ≤ (K : ℝ)^2) ∧
   prob μ {ω | 1/2 < gramDeviation (sampleGram p X n ω)} ≤ 4*((K : ℝ)^3-K)/n)

/-- The mathematical content packaged for target P001-T7. -/
def T7Statement : Prop :=
  (∀ {Ω : Type u1} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → ℝ)
  (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
  (hlaw : μ.map (fun ω => (X 0 ω,Y 0 ω)) =
    (3/8 : ℝ≥0∞) • Measure.dirac (0,0) + (1/8 : ℝ≥0∞) • Measure.dirac (0,1) +
    (1/8 : ℝ≥0∞) • Measure.dirac (1,0) + (3/8 : ℝ≥0∞) • Measure.dirac (1,1)),
  (∀ p ∈ ({(1/4 : ℝ),3/4} : Set ℝ), ∀ t ∈ Set.Icc (1/10 : ℝ) (9/10),
    0 ≤ bernoulliKL p t ∧ (bernoulliKL p t=0 ↔ t=p)) ∧
  (∀ n : ℕ, 0 < n → ∀ y : Fin n → ℝ, (∀ i, y i=0 ∨ y i=1) →
    ∀ t ∈ Set.Icc (1/10 : ℝ) (9/10),
      (∏ i, if y i=1 then t else 1-t) ≤
        ∏ i, if y i=1 then clip (1/10) (9/10) (finiteSampleMean y)
          else 1-clip (1/10) (9/10) (finiteSampleMean y)) ∧
  (∀ n : ℕ, 0 < n → ∀ y : Fin n → ℝ, (∀ i, y i=0 ∨ y i=1) →
    ∀ t ∈ Set.Icc (1/10 : ℝ) (9/10),
      ((∏ i, if y i=1 then t else 1-t) =
        ∏ i, if y i=1 then clip (1/10) (9/10) (finiteSampleMean y)
          else 1-clip (1/10) (9/10) (finiteSampleMean y)) ↔
      t=clip (1/10) (9/10) (finiteSampleMean y)) ∧
  mean μ (Y 0)=1/2 ∧ var μ (Y 0)=1/4 ∧
  (∀ n : ℕ, 0 < n → ∀ ε : ℝ, 0 < ε →
    prob μ {ω | ε ≤ |clip (1/10) (9/10) (sampleMean Y n ω)-1/2|} ≤
      1/(4*(n : ℝ)*ε^2)) ∧
  (∀ n : ℕ, 0 < n →
    1-16/(n : ℝ) ≤ prob μ {ω | 1/8 < |clip (1/10) (9/10) (sampleMean Y n ω)-1/4|} ∧
    1-16/(n : ℝ) ≤ prob μ {ω | 1/8 < |clip (1/10) (9/10) (sampleMean Y n ω)-3/4|}) ∧
  CP μ (fun n ω => clip (1/10) (9/10) (sampleMean Y n ω)) (1/2) ∧
  ¬ CP μ (fun n ω => clip (1/10) (9/10) (sampleMean Y n ω)) (1/4) ∧
  ¬ CP μ (fun n ω => clip (1/10) (9/10) (sampleMean Y n ω)) (3/4) ∧
  (∀ t ∈ Set.Icc (1/10 : ℝ) (9/10),
    (bernoulliKL (1/4) (1/2)+bernoulliKL (3/4) (1/2))/2 ≤
      (bernoulliKL (1/4) t+bernoulliKL (3/4) t)/2 ∧
    ((bernoulliKL (1/4) t+bernoulliKL (3/4) t)/2 =
      (bernoulliKL (1/4) (1/2)+bernoulliKL (3/4) (1/2))/2 ↔ t=1/2))) ∧

(∀ {Ω : Type u2} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (X Y : ℕ → Ω → ℝ) (hiid : IID μ (fun i ω => (X i ω, Y i ω)))
  (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
  (hlaw : μ.map (fun ω => (X 0 ω, Y 0 ω)) =
    ENNReal.ofReal ((1-q)*3/4) • Measure.dirac (0,0) +
    ENNReal.ofReal ((1-q)/4) • Measure.dirac (0,1) +
    ENNReal.ofReal (q/4) • Measure.dirac (1,0) +
    ENNReal.ofReal (q*3/4) • Measure.dirac (1,1)),
  let T := fun n ω => clip (1/10) (9/10) (sampleMean Y n ω)
  CP μ T (1/4+q/2) ∧
  (∀ n, 0 < n → ∀ᵐ ω ∂μ,
    T n ω ∈ Set.Icc (1/10 : ℝ) (9/10) ∧
    ∀ t ∈ Set.Icc (1/10 : ℝ) (9/10),
      (∏ i : Fin n, if Y i ω = 1 then t else 1-t) ≤
        (∏ i : Fin n, if Y i ω = 1 then T n ω else 1-T n ω) ∧
      ((∏ i : Fin n, if Y i ω = 1 then t else 1-t) =
        (∏ i : Fin n, if Y i ω = 1 then T n ω else 1-T n ω) ↔ t = T n ω)) ∧
  (0 < q ∧ q < 1 →
    conditionalMeanAt μ (X 0) (Y 0) 0 = 1/4 ∧
    conditionalMeanAt μ (X 0) (Y 0) 1 = 3/4 ∧
    ¬ CP μ T (1/4) ∧ ¬ CP μ T (3/4)))

/-- The mathematical content packaged for target P001-T8. -/
def T8Statement : Prop :=
  (∀ {Ω : Type u1} [MeasurableSpace Ω]
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
  averageKLExt νX κ f g t ≠ ∞ ∧
  (averageKLExt νX κ f g t).toReal =
    (∫ x, ∫ y, f y x*Real.log (f y x) ∂κ ∂νX) - expectedLogLikelihood μ X Y g t ∧
  averageKL νX κ f g t = (averageKLExt νX κ f g t).toReal) ∧

(∀ {Ω : Type u2} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] {K τ : ℕ}
  (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
  (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
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
    ε ≤ dist t tstar → expectedLogLikelihood μ (X 0) (Y 0) g t ≤
      expectedLogLikelihood μ (X 0) (Y 0) g tstar-δ)
  (that : ℕ → Ω → Fin τ → ℝ) (hm : ∀ n, Measurable (that n))
  (hthat : ∀ n ω, that n ω ∈ Θ)
  (e Δ : ℕ → Ω → ℝ) (hen : ∀ n ω, 0 ≤ e n ω)
  (he : CP μ e 0) (hΔ : CP μ Δ 0)
  (hbound : ∀ n ω t, t ∈ Θ →
    |sampleLogLikelihood X Y g n ω t-expectedLogLikelihood μ (X 0) (Y 0) g t| ≤ Δ n ω)
  (hmax : (∀ n ω t, t ∈ Θ →
    sampleLikelihood X Y g n ω t ≤ sampleLikelihood X Y g n ω (that n ω)) ∨
    (∀ n ω t, t ∈ Θ → sampleLogLikelihood X Y g n ω t-e n ω ≤
      sampleLogLikelihood X Y g n ω (that n ω))),
  CP μ that tstar ∧
  ((Integrable (fun xy : (Fin K → ℝ) × ℝ =>
      f xy.2 xy.1*Real.log (f xy.2 xy.1)) (νX.prod κ) ∧
    ∀ t ∈ Θ, Integrable (fun xy : (Fin K → ℝ) × ℝ =>
      f xy.2 xy.1*Real.log (g xy.2 xy.1 t)) (νX.prod κ)) →
    ∀ t ∈ Θ, averageKLExt νX κ f g tstar ≤ averageKLExt νX κ f g t ∧
      (averageKLExt νX κ f g t = averageKLExt νX κ f g tstar → t=tstar))) ∧

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
    averageKLExt νX κ (fun y x => g y x θ) g tstar ≤
      averageKLExt νX κ (fun y x => g y x θ) g t ∧
    (averageKLExt νX κ (fun y x => g y x θ) g t =
      averageKLExt νX κ (fun y x => g y x θ) g tstar → t = tstar)),
  averageKLExt νX κ (fun y x => g y x θ) g θ = 0 ∧
  tstar = θ ∧
  (∀ t ∈ Θ, averageKLExt νX κ (fun y x => g y x θ) g t = 0 ↔ t = θ))

/-- The mathematical content packaged for target P001-T9. -/
def T9Statement : Prop :=
  (∀ B : ℝ, ∃ σ : ℝ, 0  <  σ ∧ MixtureAdmissible ![1/2,1/4,1,σ,0,1,1] ∧
   B  <  mixtureLikelihood ![1,2,3] ![1/2,1/4,1,σ,0,1,1]) ∧
   ¬ ∃ θ : Fin 7 → ℝ, MixtureAdmissible θ ∧ ∀ θ', MixtureAdmissible θ' →
     mixtureLikelihood ![1,2,3] θ'  ≤  mixtureLikelihood ![1,2,3] θ

/-- The mathematical content packaged for target P001-T10. -/
def T10Statement : Prop :=
  (∀ {n : ℕ} (hn : 0  <  n) (y : Fin n → ℝ) (hy : ∀ i, 0  <  y i),
  (∀ B : ℝ, ∃ θ : Fin 7 → ℝ, MixtureAdmissible θ ∧ B  <  mixtureLikelihood y θ) ∧
  (¬ ∃ θ : Fin 7 → ℝ, MixtureAdmissible θ ∧ ∀ θ', MixtureAdmissible θ' →
     mixtureLikelihood y θ' ≤ mixtureLikelihood y θ)) ∧

(∀ {n : ℕ} (y : Fin n → ℝ) (hy : ∀ i, 0  <  y i)
   (B S δ a b : ℝ) (hδ : 0  <  δ) (ha : 0  <  a)
   (hne : (mixtureRestriction B S δ a b).Nonempty),
  IsCompact (mixtureRestriction B S δ a b) ∧
   ContinuousOn (mixtureLikelihood y) (mixtureRestriction B S δ a b) ∧
   ∃ θ ∈ mixtureRestriction B S δ a b, ∀ θ' ∈ mixtureRestriction B S δ a b,
     mixtureLikelihood y θ'  ≤  mixtureLikelihood y θ)


end SAP.P001a
