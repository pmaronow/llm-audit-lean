import SAP.P001g.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P001g

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
universe u v w z u1 v1

/-! Conditional models, actual product likelihoods, and the conventional F statistic. -/

def conditionalModelLaw {K τ : ℕ} (νX : Measure (Fin K → ℝ)) (κ : Measure ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (θ : Fin τ → ℝ) : Measure ((Fin K → ℝ) × ℝ) :=
  (νX.prod κ).withDensity (fun xy => ENNReal.ofReal (g xy.2 xy.1 θ))

def conditionalKL {K τ : ℕ} (κ : Measure ℝ) (f : ℝ → (Fin K → ℝ) → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (x : Fin K → ℝ) (t : Fin τ → ℝ) : ℝ :=
  ∫ y,f y x*Real.log (f y x/g y x t) ∂κ

def expectedLogLikelihood {Ω : Type*} [MeasurableSpace Ω] {K τ : ℕ}
    (μ : Measure Ω) (X : Ω → Fin K → ℝ) (Y : Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (t : Fin τ → ℝ) : ℝ :=
  mean μ (fun ω => Real.log (g (Y ω) (X ω) t))

def sampleLogLikelihood {Ω : Type*} {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (n : ℕ) (ω : Ω) (t : Fin τ → ℝ) : ℝ :=
  sampleMean (fun i ω => Real.log (g (Y i ω) (X i ω) t)) n ω

def sampleLikelihood {Ω : Type*} {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (n : ℕ) (ω : Ω) (t : Fin τ → ℝ) : ℝ :=
  ∏ i∈Finset.range n,g (Y i ω) (X i ω) t

def disjointMixture (p a b : ℝ) : Fin 4 → ℝ := ![p*(1-a),p*a,(1-p)*(1-b),(1-p)*b]

def olsRSS {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ) (b : Fin (K+1) → ℝ) : ℝ :=
  ∑ i,(Y i-(X.mulVec b) i)^2

def olsCoef {n K : ℕ} (X : Matrix (Fin n) (Fin K) ℝ) (Y : Fin n → ℝ) : Fin K → ℝ :=
  (X.transpose*X)⁻¹.mulVec (X.transpose.mulVec Y)

def placeboFStatistic {n K L : ℕ} (X : Fin n → Fin K → ℝ) (W : Fin n → Fin L → ℝ) (D : Fin n → ℝ) : ℝ :=
  let R : Matrix (Fin n) (Fin (K+1)) ℝ := fun i => Fin.cases 1 (X i)
  let F : Matrix (Fin n) (Fin (K+L+1)) ℝ := fun i => Fin.cases 1 (Fin.addCases (X i) (W i))
  let rr := olsRSS R D (olsCoef R D)
  let rf := olsRSS F D (olsCoef F D)
  ((rr-rf)/(L : ℝ))/(rf/((n : ℝ)-(K+L+1 : ℕ)))

def fReference (k v : ℕ) : Measure ℝ :=
  (Measure.pi (fun _ : Fin (k+v) => gaussianReal 0 1)).map (fun z =>
    ((∑ i : Fin (k+v),if i.val < k then (z i)^2 else 0)/(k : ℝ))/
      ((∑ i : Fin (k+v),if k ≤ i.val then (z i)^2 else 0)/(v : ℝ)))

def FixedCovariateKLMLEPositiveSupport : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
   (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
   (κ : Measure ℝ) [SFinite κ] (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX]
   (f : ℝ → (Fin K → ℝ) → ℝ) (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
   (hf : μ.map (fun ω => (X 0 ω,Y 0 ω))=
     (νX.prod κ).withDensity (fun xy => ENNReal.ofReal (f xy.2 xy.1)))
   (Θ : Set (Fin τ → ℝ))
   (hfpos : ∀ y x,0 ≤ f y x) (hfnorm : ∀ x,(∫⁻ y,ENNReal.ofReal (f y x) ∂κ)=1)
   (hfmeas : Measurable (fun xy : (Fin K → ℝ) × ℝ => f xy.2 xy.1))
   (hgmeas : ∀ t∈Θ,Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
   (hgpos : ∀ t∈Θ,∀ y x,0 ≤ g y x t)
   (hgnorm : ∀ t∈Θ,∀ x,(∫⁻ y,ENNReal.ofReal (g y x t) ∂κ)=1)
   (x : Fin K → ℝ) (hx : 0 < νX {x}) (tstar : Fin τ → ℝ) (ht : tstar∈Θ)
   (hdom : ∀ t∈Θ,∀ᵐ y ∂κ,0 < f y x → 0 < g y x t)
   (hKL : ∀ t∈Θ,Integrable (fun y => f y x*Real.log (f y x/g y x t)) κ)
   (hunique : ∀ t∈Θ,conditionalKL κ f g x tstar ≤ conditionalKL κ f g x t ∧
     (conditionalKL κ f g x t=conditionalKL κ f g x tstar → t=tstar))
   (that : ℕ → Ω → Fin τ → ℝ)
   (hstat : ∀ n : ℕ, ∃ h : (Fin n → ((Fin K → ℝ) × ℝ)) → (Fin τ → ℝ),
     Measurable h ∧ ∀ ω, that n ω = h (fun i : Fin n => (X i ω, Y i ω)))
   (hthat : ∀ n ω,that n ω∈Θ)
   (hmax : ∀ n ω t,t∈Θ → (∏ i ∈ Finset.range n,g (Y i ω) (X i ω) t) ≤ 
     ∏ i ∈ Finset.range n,g (Y i ω) (X i ω) (that n ω)),
    CP μ that tstar
end

end SAP.P001g
