import SAP.P027b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027b
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
attribute [local instance] Classical.propDecidable

variable {U Ω : Type} [Fintype U] [Fintype Ω]

def strataDesign (M : ℕ) (hM : 0 < M) : Design (Fin M × Fin 2) (Fin M × Fin M) where
  weight _ := 1/(M:ℝ)^2
  nonneg _ := by positivity
  total := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
    have hMr : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    field_simp
    <;> ring
  selected ω k := if k.2 = 0 then decide (k.1 = ω.1) else decide (k.1 = ω.2)

def stratumMeans (α : ℝ) (s : Fin 2) : ℝ := if s = 0 then α else -α

def stratumMeansVariance (α : ℝ) : ℝ :=
  (∑ s : Fin 2, (stratumMeans α s-(∑ t : Fin 2, stratumMeans α t)/2)^2)/(2-1)

def stratumOutcomes {M : ℕ} {Ξ : Type} (α : ℝ)
    (ε : (Fin M × Fin 2) → Ξ → ℝ) (ξ : Ξ) (k : Fin M × Fin 2) : ℝ :=
  stratumMeans α k.2+ε k ξ

def collapsedEstimator {M : ℕ} (y : (Fin M × Fin 2) → ℝ) (ω : Fin M × Fin M) : ℝ :=
  (y (ω.1,0)-y (ω.2,1))^2/4

def stratumVariance {M : ℕ} (y : (Fin M × Fin 2) → ℝ) (s : Fin 2) : ℝ :=
  (∑ k, y (k,s)^2)/(M:ℝ) - ((∑ k, y (k,s))/(M:ℝ))^2

def strataC2BiasFormula (M α : ℝ) : ℝ := (M-1)/(2*M)*(1+2*α^2)

def strataCSBiasFormula (M α : ℝ) : ℝ := α^2+1/(2*M)

def heterogeneity (α : ℝ) : ℝ := α^2/(α^2+1/2)

def pairCorrelationFormula (α : ℝ) : ℝ := α^2/(α^2+1)

def deviations5 : Fin 5 → ℝ := ![3/2,-3/2,1/2,-1/2,0]

def fixedStrata5 (α : ℝ) (k : Fin 5 × Fin 2) : ℝ :=
  stratumMeans α k.2+deviations5 k.1

def outcomeCov (D : Design U Ω) (f g : Ω → ℝ) : ℝ :=
  expect D (fun ω => f ω*g ω)-expect D f*expect D g

def outcomeCorr (D : Design U Ω) (f g : Ω → ℝ) : ℝ :=
  outcomeCov D f g/Real.sqrt (variance D f*variance D g)

def sign2 (s : Fin 2) : ℝ := if s = 0 then -1 else 1

def pairLaw : Design Unit (Fin 2 × Fin 2 × Fin 2) where
  weight _ := 1/8
  nonneg _ := by norm_num
  total := by norm_num [Fintype.sum_prod_type, Fin.sum_univ_two]
  selected _ _ := false

def pairS (ω : Fin 2 × Fin 2 × Fin 2) := sign2 ω.1

def pairE (ω : Fin 2 × Fin 2 × Fin 2) := sign2 ω.2.1

def pairE' (ω : Fin 2 × Fin 2 × Fin 2) := sign2 ω.2.2

def cluster3 : Design (Fin 3) (Fin 2) where
  weight _ := 1/2
  nonneg _ := by norm_num
  total := by norm_num [Fin.sum_univ_succ]
  selected g k := decide (if g.val = 0 then k.val < 2 else k.val = 2)

def allOnes3 (_ : Fin 3) : ℝ := 1

def mixed3 (k : Fin 3) : ℝ := if k = 2 then -1/4 else 1

def outcomeE {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) (f : Ξ → ℝ) : ℝ :=
  ∫ ξ, f ξ ∂μ

def NoiseMoments {Ξ K : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (ε : K → Ξ → ℝ) (σ2 : ℝ) : Prop :=
  (∀ k, Integrable (ε k) μ ∧ outcomeE μ (ε k) = 0) ∧
  ∀ k l, Integrable (fun ξ => ε k ξ * ε l ξ) μ ∧
    outcomeE μ (fun ξ => ε k ξ * ε l ξ) = if k = l then σ2 else 0

end
end SAP.P027b
