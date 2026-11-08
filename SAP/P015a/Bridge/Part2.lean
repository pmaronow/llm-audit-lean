import SAP.P015a.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P015a.Bridge
open Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
attribute [local instance] Classical.propDecidable
universe u v

open AronowAudit.P015 AronowAudit.P015.Wave1

theorem T8_correspondence : SAP.P015a.T8Statement.{u,v} ↔
  ((∀ (N K : ℕ)
    (W : Matrix (Fin N) (Fin (K+2)) ℝ) (Y : Fin N → ℝ)
    (hY : ∀ i, Y i=0 ∨ Y i=1) (hW : ∀ i, W i 0=1)
    (I : Set ℝ) (hI : IsOpen I) (m : ℝ → ℝ)
    (hm : DifferentiableOn ℝ m I) (hprob : ∀ η∈I, 0 < m η ∧ m η<1)
    (θ v : Fin (K+2) → ℝ) (hθ : ∀ i, W.mulVec θ i∈I),
  HasDerivAt (fun t : ℝ => groupedLikelihood W (fun _ => 1) Y m (θ+t • v))
      (∑ i, scoreMultiplier m (W.mulVec θ i)*(Y i-m (W.mulVec θ i))*W.mulVec v i) 0) ∧
  (∀ η : ℝ, HasDerivAt logistic (logistic η*(1-logistic η)) η ∧
    scoreMultiplier logistic η = 1) ∧
  (∀ {N : Type u} {Q : Type v} [Fintype N] [Fintype Q]
    (W : Matrix N Q ℝ) (j₀ : Q) (hW : ∀ i, W i j₀=1)
    (ν : Measure ℝ) (κ : ℝ → ℝ) (s : ℝ) (carrier : ℝ → ℝ) (I support : Set ℝ)
    (hfamily : CanonicalFamily ν κ s carrier I support)
    (Y : N → ℝ) (hY : ∀ i, Y i∈support) (θ : Q → ℝ)
    (hθ : ∀ i, W.mulVec θ i∈I) (hκ : ∀ i, DifferentiableAt ℝ κ (W.mulVec θ i)),
  (∀ v : Q → ℝ, HasDerivAt
      (fun t => canonicalLikelihood W κ s (fun i => Y i) (fun i => carrier (Y i)) (fun j => θ j+t*v j))
      (s⁻¹*(∑ i, (Y i-deriv κ (W.mulVec θ i))*W.mulVec v i)) 0) ∧
    ((∀ j, s⁻¹*(∑ i, W i j*(Y i-deriv κ (W.mulVec θ i)))=0) ↔
      ∀ j, (∑ i, W i j*(Y i-deriv κ (W.mulVec θ i)))=0)) ∧
  (∀ (η : ℝ),
  (MeasureTheory.IsProbabilityMeasure
        (AronowAudit.P015.Wave1.bernoulliResponseLaw η) ∧
      MeasureTheory.Integrable (fun y : ℝ => y)
        (AronowAudit.P015.Wave1.bernoulliResponseLaw η) ∧
      (∫ y : ℝ, y ∂(AronowAudit.P015.Wave1.bernoulliResponseLaw η)) =
        AronowAudit.P015.logistic η ∧
      AronowAudit.P015.logistic η =
        deriv (fun a : ℝ => Real.log (1 + Real.exp a)) η) ∧
    (MeasureTheory.IsProbabilityMeasure
        (AronowAudit.P015.Wave1.poissonResponseLaw η) ∧
      MeasureTheory.Integrable (fun n : ℕ => (n : ℝ))
        (AronowAudit.P015.Wave1.poissonResponseLaw η) ∧
      (∫ n : ℕ, (n : ℝ) ∂(AronowAudit.P015.Wave1.poissonResponseLaw η)) =
        Real.exp η ∧
      Real.exp η = deriv Real.exp η)) ∧
  (∀ (N K : ℕ) (W : Matrix (Fin N) (Fin (K+2)) ℝ)
    (Y : Fin N → ℝ) (hY : ∀ i, Y i=0 ∨ Y i=1) (hW : ∀ i, W i 0=1)
    (θ v : Fin (K+2) → ℝ),
  HasDerivAt (fun t => groupedLikelihood W (fun _ => 1) Y normalCDF (fun j => θ j+t*v j))
      (∑ i, probitH (W.mulVec θ i)*(Y i-normalCDF (W.mulVec θ i))*W.mulVec v i) 0 ∧
    ¬ ∃ c : ℝ, ∀ η : ℝ, probitH η = c) ∧
  (normalCDF 0=1/2 ∧ deriv probitH 0=0) ∧
  (∀ (N K : ℕ)
    (W : Matrix (Fin N) (Fin (K+2)) ℝ) (Y : Fin N → ℝ)
    (hY : ∀ i, Y i=0 ∨ Y i=1) (hW : ∀ i, W i 0=1)
    (I : Set ℝ) (hI : IsOpen I) (m : ℝ → ℝ)
    (hm : DifferentiableOn ℝ m I) (hprob : ∀ η∈I, 0 < m η ∧ m η<1)
    (η₀ p₀ : ℝ) (hη : η₀∈I) (hp : 0<p₀) (hu : p₀<1) (hmean : m η₀=p₀)
    (hm₂ : DifferentiableAt ℝ (deriv m) η₀),
  let θ₀ : Fin (K+2) → ℝ := fun j => if j=0 then η₀ else 0
    let h := scoreMultiplier m
    let h₀ := h η₀
    let f₀ := deriv m η₀
    let h₁ := deriv h η₀
    let r := W.transpose.mulVec (fun i => Y i-p₀)
    let A := W.transpose*W
    let B : Matrix (Fin (K+2)) (Fin (K+2)) ℝ := fun j k => ∑ i, (Y i-p₀)*W i j*W i k
    ∀ δ : Fin (K+2) → ℝ,
      (fun j => ∑ i, W i j*firstTaylor (fun η => h η*(Y i-m η)) η₀ (W.mulVec (θ₀+δ) i)) =
        h₀ • r+((-h₀*f₀) • A+h₁ • B).mulVec δ)) := Iff.rfl

theorem T12_correspondence : SAP.P015a.T12Statement ↔
  ((∀ (p : ℝ), 0 < p → p < 1 →
    (∀ a, firstTaylor logistic (logit p) a = p+p*(1-p)*(a-logit p)) ∧
    (fun a => logistic a-(p+p*(1-p)*(a-logit p))) =O[𝓝 (logit p)]
      (fun a => (a-logit p)^2)) ∧
  (∀ (p r ρ : ℝ) (hp : 0 < p) (hu : p < 1)
    (hr : 0 ≤ r) (hrρ : r < ρ) (hρ : ρ < Real.sqrt ((logit p)^2+Real.pi^2)),
  let fc := fun z : ℂ => (1+Complex.exp (-z))⁻¹
    let M := sSup ((fun z : ℂ => ‖fc z‖) '' Metric.sphere ((logit p : ℝ) : ℂ) ρ)
    (((fun z : ℂ => ‖fc z‖) '' Metric.sphere ((logit p : ℝ) : ℂ) ρ).Nonempty →
    BddAbove ((fun z : ℂ => ‖fc z‖) '' Metric.sphere ((logit p : ℝ) : ℂ) ρ) →
    ((∃ s : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt fc s ((logit p : ℝ) : ℂ) ∧
      s.radius = ENNReal.ofReal (Real.sqrt ((logit p)^2+Real.pi^2))) ∧
    (∀ N : ℕ, ∀ a : ℝ, |a-logit p| ≤ r →
      |logistic a-logisticTaylor N (logit p) a| ≤ M*(r/ρ)^(N+1)/(1-r/ρ)) ∧
    Tendsto (fun N : ℕ => M*(r/ρ)^(N+1)/(1-r/ρ)) atTop (𝓝 0))))) := Iff.rfl

theorem T13_correspondence : SAP.P015a.T13Statement ↔
  (∀ (p : ℝ) (hp : 0 < p) (hu : p < 1),
  (∀ a, HasDerivAt logistic (Real.exp a/(1+Real.exp a)^2) a) ∧
    logistic (logit p) = p ∧
    deriv logistic (logit p) = Real.exp (logit p)/(1+Real.exp (logit p))^2 ∧
    deriv logistic (logit p) = p*(1-p) ∧
    (∀ a, firstTaylor logistic (logit p) a = p+p*(1-p)*(a-logit p) ∧
      firstTaylor logistic (logit p) a = (p-p*(1-p)*logit p)+p*(1-p)*a) ∧
    logit (1/2) = 0 ∧
    Real.exp (logit (1/2))/(1+logit (1/2))^2 = 1 ∧
    deriv logistic (logit (1/2)) = 1/4) := Iff.rfl

theorem T16_correspondence : SAP.P015a.T16Statement ↔
  ((10800420763/10000000000 < Real.exp (77/1000) ∧
    Real.exp (77/1000) < 10800420765/10000000000 ∧
    (10800420765/10000000000 : ℝ) < 6/5 ∧
    800420763/100000000 < 100*(Real.exp (77/1000)-1) ∧
    100*(Real.exp (77/1000)-1) < 800420765/100000000) ∧
  (∀ (α β d controls : ℝ),
  Real.exp (α+β*(d+1)+controls)/Real.exp (α+β*d+controls) = Real.exp β) ∧
  (let W : Matrix (Fin 4) (Fin 2) ℝ := !![1,0;1,0;1,1;1,1]
    let S : Fin 4 → ℝ := ![1,1,0,3]
    let Y := fun i => Real.log ((1+S i)/2)
    ols W Y 1=0 ∧ Real.exp (ols W Y 1)=1 ∧
    (Real.log (1/2)+Real.log 2)/2=0 ∧
    (S 0+S 1)/2=1 ∧ (S 2+S 3)/2=3/2 ∧ ((3/2:ℝ)/1-1)*100=50) ∧
  (let W : Matrix (Fin 4) (Fin 2) ℝ := !![1,0;1,0;1,1;1,1]; (W.transpose*W).det = 4)) := Iff.rfl

theorem T19_correspondence : SAP.P015a.T19Statement.{u,v} ↔
  (∀ {Ω : Type u} {B : Type v} [MeasurableSpace Ω] [MeasurableSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Ω → ℝ) (X : Ω → B),
    Measurable D → Measurable X → MemLp D 2 P →
    P[populationWeight P D X | MeasurableSpace.comap X inferInstance] = conditionalVariance P D X ∧
    ((∀ᵐ s ∂P, D s=0 ∨ D s=1) → conditionalVariance P D X =ᵐ[P]
      fun s => P[D | MeasurableSpace.comap X inferInstance] s*
        (1-P[D | MeasurableSpace.comap X inferInstance] s))) := Iff.rfl

end SAP.P015a.Bridge
