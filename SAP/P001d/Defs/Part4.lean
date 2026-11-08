import SAP.P001d.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def polynomialDesign {n : ℕ} (x : Fin n → ℝ) (J : ℕ) : Matrix (Fin n) (Fin (J+1)) ℝ :=
  fun i k => x i^k.val

def T70Statement : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ (J : ℕ) (x y : Fin n → ℝ),
    (∀ B : ℝ, ∃ b : Fin (J+1) → ℝ, (∑ i, (y i-∑ k, b k*x i^k.val)) < B) ∧
    (¬ ∃ b : Fin (J+1) → ℝ, ∀ c : Fin (J+1) → ℝ,
      (∑ i, (y i-∑ k, b k*x i^k.val)) ≤ ∑ i, (y i-∑ k, c k*x i^k.val)) ∧
    (∀ b : Fin (J+1) → ℝ,
      olsRSS (polynomialDesign x J) y b = ∑ i, (y i-∑ k, b k*x i^k.val)^2) ∧
    (IsUnit ((polynomialDesign x J).transpose*polynomialDesign x J).det →
      ∀ b : Fin (J+1) → ℝ,
        olsRSS (polynomialDesign x J) y (olsCoef (polynomialDesign x J) y) ≤
          olsRSS (polynomialDesign x J) y b ∧
        (olsRSS (polynomialDesign x J) y b =
          olsRSS (polynomialDesign x J) y (olsCoef (polynomialDesign x J) y) ↔
          b = olsCoef (polynomialDesign x J) y))

def slopePenalty {K : ℕ} (b : Fin (K+1) → ℝ) : ℝ := ∑ k : Fin K, |b k.succ|

def lassoCriterion {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ)
    (lam : ℝ) (b : Fin (K+1) → ℝ) : ℝ := olsRSS X Y b/(n : ℝ)+lam*slopePenalty b

def T71Statement : Prop :=
  ∀ {n K : ℕ}, 0 < n → ∀ (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ),
    (∀ b, lassoCriterion X Y 0 b = olsRSS X Y b/(n : ℝ)) ∧
    (∀ b, (∀ c, lassoCriterion X Y 0 b ≤ lassoCriterion X Y 0 c) ↔
      (∀ c, olsRSS X Y b ≤ olsRSS X Y c)) ∧
    (∀ b c : Fin (K+1) → ℝ, 0 ≤ slopePenalty b ∧
      (∀ a : ℝ, slopePenalty (a • b) = |a| * slopePenalty b) ∧
      slopePenalty (b+c) ≤ slopePenalty b+slopePenalty c) ∧
    slopePenalty (Pi.single 0 (1 : ℝ) : Fin (K+1) → ℝ) = 0 ∧
    (∑ j : Fin (K+1), |(Pi.single 0 (1 : ℝ) : Fin (K+1) → ℝ) j|) = 1 ∧
    (∀ lam : ℝ, 0 ≤ lam → ConvexOn ℝ Set.univ (lassoCriterion X Y lam))

def normalDensity (m s y : ℝ) : ℝ :=
  Real.exp (-(y-m)^2/(2*s^2))/(s*Real.sqrt (2*Real.pi))

def T72Statement : Prop :=
  ∀ {K : ℕ} (x b : Fin (K+1) → ℝ) (s : ℝ), 0 < s →
    (∀ y, 0 ≤ normalDensity (∑ k, x k*b k) s y) ∧
    Integrable (normalDensity (∑ k, x k*b k) s) volume ∧
    Integrable (fun y => y*normalDensity (∑ k, x k*b k) s y) volume ∧
    (∫ y, normalDensity (∑ k, x k*b k) s y) = 1 ∧
    (∫ y, y*normalDensity (∑ k, x k*b k) s y) = ∑ k, x k*b k ∧
    (∫ y, normalDensity (∑ k, x k*b k) 0 y) = 0 ∧
    (∫ y, normalDensity (∑ k, x k*b k) 0 y) ≠ 1

def heteroX : Fin 4 → ℝ := ![0,0,1,1]
def heteroY : Fin 4 → ℝ := ![1,3,0,6]
def heteroResidual (i : Fin 4) : ℝ := heteroY i-(2+heteroX i)
def finiteMean (X : Fin 4 → ℝ) : ℝ := ∑ i, (1/4 : ℝ)*X i
def finiteProb (A : Fin 4 → Prop) : ℝ := ∑ i, if A i then (1/4 : ℝ) else 0
def finiteCov (X Y : Fin 4 → ℝ) : ℝ :=
  finiteMean (fun i => (X i-finiteMean X)*(Y i-finiteMean Y))
def finiteCond (Y X : Fin 4 → ℝ) (x : ℝ) : ℝ :=
  (∑ i, if X i = x then (1/4 : ℝ)*Y i else 0)/finiteProb (fun i => X i = x)

def T73Statement : Prop :=
  finiteProb (fun i => heteroX i = 0) = 1/2 ∧
  finiteProb (fun i => heteroX i = 1) = 1/2 ∧
  finiteCond heteroY heteroX 0 = 2 ∧ finiteCond heteroY heteroX 1 = 3 ∧
  finiteMean heteroResidual = 0 ∧ finiteCov heteroX heteroResidual = 0 ∧
  finiteProb (fun i => heteroX i = 0 ∧ |heteroResidual i| = 1) = 1/2 ∧
  finiteProb (fun i => heteroX i = 0)*finiteProb (fun i => |heteroResidual i| = 1) = 1/4 ∧
  (1/2 : ℝ) ≠ 1/4

def T74Statement (Ω E : Type*) [MeasurableSpace Ω] [MeasurableSpace E] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ],
  ( (∀ (X : Ω → E), Measurable X → ∀ Y : Ω → ℝ, MemLp Y 2 μ →
      ∀ m : E → ℝ, IsCEF μ X Y m → MemLp (m ∘ X) 2 μ →
      IsCEF μ X (fun ω => Y ω-m (X ω)) (fun _ => 0) ∧
      (∫ ω, Y ω-m (X ω) ∂μ) = 0 ∧
      (∀ g : E → ℝ, Measurable g → MemLp (g ∘ X) 2 μ →
        covariance (g ∘ X) (fun ω => Y ω-m (X ω)) μ = 0) ∧
      (∀ v : E → ℝ, IsCEF μ X (fun ω => (Y ω-m (X ω))^2) v →
        IsCEF μ X (fun ω => ((Y ω-m (X ω))-0)^2) v ∧
        variance (fun ω => Y ω-m (X ω)) μ = ∫ ω, v (X ω) ∂μ)) ∧
    (∀ (X : Ω → E) (Y : Ω → ℝ), Measurable X → Measurable Y →
      ∀ m : E → ℝ, Measurable m → ∀ s : ℝ, 0 < s →
      μ.map (fun ω => (X ω, Y ω)) =
        ((μ.map X).prod (gaussianReal 0 ⟨s^2, sq_nonneg _⟩)).map
          (fun xy => (xy.1, m xy.1+xy.2)) →
      μ.map (fun ω => Y ω-m (X ω)) = gaussianReal 0 ⟨s^2, sq_nonneg _⟩ ∧
      IndepFun X (fun ω => Y ω-m (X ω)) μ) ) ∧ T73Statement

/-- The mean of the corrected two-point conditional PMF at a fixed covariate vector. -/
def binaryChoiceMean {K : ℕ} (x b : Fin (K+1) → ℝ) (h : ℝ → ℝ) : ℝ :=
  0*(1-h (∑ k, x k*b k))+1*h (∑ k, x k*b k)

def T75Statement : Prop :=
  ∀ {K : ℕ} (x b : Fin (K+1) → ℝ) (h : ℝ → ℝ), (∀ t, 0 ≤ h t ∧ h t ≤ 1) →
    binaryChoiceMean x b h = h (∑ k, x k*b k) ∧ binaryChoiceMean x b h ∈ Set.Icc 0 1

def normalLogLikelihood {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ)
    (b : Fin (K+1) → ℝ) (s : ℝ) : ℝ :=
  -(n : ℝ)*Real.log s-(n : ℝ)/2*Real.log (2*Real.pi)-olsRSS X Y b/(2*s^2)

def T76Statement : Prop :=
  ∀ {n K : ℕ}, 0 < n → ∀ (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ),
    (∀ (bstar : Fin (K+1) → ℝ) (s : ℝ), 0 < s →
      ((∀ b, normalLogLikelihood X Y b s ≤ normalLogLikelihood X Y bstar s) ↔
        (∀ b, olsRSS X Y bstar ≤ olsRSS X Y b))) ∧
    (∀ (bstar : Fin (K+1) → ℝ) (s t : ℝ), 0 < s → 0 < t →
      ((∀ b, normalLogLikelihood X Y b s ≤ normalLogLikelihood X Y bstar s) ↔
        (∀ b, normalLogLikelihood X Y b t ≤ normalLogLikelihood X Y bstar t)))

end SAP.P001d
