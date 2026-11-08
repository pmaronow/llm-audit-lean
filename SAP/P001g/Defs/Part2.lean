import SAP.P001g.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P001g

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
universe u v w z u1 v1

/-! Supremum-norm CDF differentiability and the finite-moment mean functional. -/

def uniformNorm (h : ℝ → ℝ) : ℝ := sSup (Set.range (fun x => |h x|))

def IsRealCDF (F : ℝ → ℝ) : Prop :=
  (∀ x,0 ≤ F x ∧ F x ≤ 1) ∧ Monotone F ∧
  (∀ x,Tendsto F (nhdsWithin x (Set.Ici x)) (nhds (F x))) ∧
  Tendsto F atBot (nhds 0) ∧ Tendsto F atTop (nhds 1)

def CDFHadamard (T : (ℝ → ℝ) → ℝ) (F : ℝ → ℝ) : Prop :=
  ∃ L : (ℝ → ℝ) → ℝ,
    (∀ f g,L (fun x => f x+g x)=L f+L g) ∧ (∀ a f,L (fun x => a*f x)=a*L f) ∧
    (∃ C : ℝ,0 ≤ C ∧ ∀ h,BddAbove (Set.range (fun x => |h x|)) → |L h| ≤ C*uniformNorm h) ∧
    ∀ h : ℝ → ℝ,BddAbove (Set.range (fun x => |h x|)) →
      ∀ t : ℕ → ℝ,∀ hn : ℕ → ℝ → ℝ,(∀ n,0 < t n) →
        (∀ n,BddAbove (Set.range (fun x => |hn n x|))) → Tendsto t atTop (nhds 0) →
        Tendsto (fun (n : ℕ) => uniformNorm (fun x => hn n x-h x)) atTop (nhds 0) →
        (∀ n,IsRealCDF (fun x => F x+t n*hn n x)) →
        Tendsto (fun (n : ℕ) => (T (fun x => F x+t n*hn n x)-T F)/t n) atTop (nhds (L h))

def HadamardAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D H : Set E) (T : E → ℝ) (F : E) (L : E →L[ℝ] ℝ) : Prop :=
  ∀ h ∈ H, ∀ t : ℕ → ℝ, ∀ hn : ℕ → E,
    (∀ n, 0 < t n) → Tendsto t atTop (nhds 0) → Tendsto hn atTop (nhds h) →
    (∀ n, F+t n • hn n ∈ D) →
    Tendsto (fun (n : ℕ) => (T (F+t n • hn n)-T F)/t n) atTop (nhds (L h))

abbrev KolmogorovSpace := lp (fun _ : ℝ => ℝ) ∞

def kolmogorovEmbed (f : ℝ → ℝ) : KolmogorovSpace :=
  if hf : Memℓp f ∞ then ⟨f,hf⟩ else 0

def finiteSecondCDF (F : KolmogorovSpace) : Prop :=
  ∃ ν : Measure ℝ,IsProbabilityMeasure ν ∧ MemLp id 2 ν ∧ ∀ x,cdf ν id x=F x

def cdfMeanFunctional (F : KolmogorovSpace) : ℝ :=
  if h : finiteSecondCDF F then mean h.choose id else 0

def PluginPositiveNormalLimit : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ), IID μ X → ∀ T : (ℝ → ℝ) → ℝ,
    CDFHadamard T (cdf μ (X 0)) →
    ∃ φ : ℝ,0 < φ ∧ CD μ
      (fun n ω => Real.sqrt n*(T (cdf (empirical X n ω) id)-T (cdf μ (X 0))))
      (gaussianReal 0 ⟨φ^2,sq_nonneg _⟩)
end

end SAP.P001g
