import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P017

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical

noncomputable section

/- Population means use integrable effects in all target statements.
The closed pushforward support has extended bounds; infinite radius clips identically.
Weighting requires a finite numerator and a finite positive denominator. -/

def populationMean {Ω : Type*} [MeasurableSpace Ω] (G : Measure Ω) (τ : Ω → ℝ) : ℝ :=
  ∫ ω, τ ω ∂G

def effectSupport {Ω : Type*} [MeasurableSpace Ω] (G : Measure Ω) (τ : Ω → ℝ) : Set ℝ :=
  (G.map τ).support

def supportInf (S : Set ℝ) : EReal := sInf ((fun x : ℝ => (x : EReal)) '' S)

def supportSup (S : Set ℝ) : EReal := sSup ((fun x : ℝ => (x : EReal)) '' S)

def effectRadius {Ω : Type*} [MeasurableSpace Ω] (G : Measure Ω) (τ : Ω → ℝ) : ℝ≥0∞ :=
  (min (supportSup (effectSupport G τ) - (populationMean G τ : EReal))
    ((populationMean G τ : EReal) - supportInf (effectSupport G τ))).toENNReal

def clipReal (μ c x : ℝ) : ℝ := min (μ + c) (max (μ - c) x)

def clipTarget (μ : ℝ) (c : ℝ≥0∞) (x : ℝ) : ℝ :=
  if c = ⊤ then x else clipReal μ c.toReal x

def residual (μ c x : ℝ) : ℝ := x - clipReal μ c x

def inside (μ : ℝ) (c : ℝ≥0∞) (x : ℝ) : Prop := ENNReal.ofReal |x - μ| ≤ c

def AdmissibleWeight {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) (τ w : Ω → ℝ) : Prop :=
  Measurable w ∧ (∀ ω, 0 ≤ w ω) ∧ Integrable w G ∧
    0 < (∫ ω, w ω ∂G) ∧ Integrable (fun ω => w ω * τ ω) G

def weightedMean {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) (τ w : Ω → ℝ) : ℝ :=
  (∫ ω, w ω * τ ω ∂G) / (∫ ω, w ω ∂G)

def Representable {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) (τ : Ω → ℝ) (t : ℝ) : Prop :=
  ∃ w, AdmissibleWeight G τ w ∧ weightedMean G τ w = t

def pr {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω) : ℝ := P.real A

def sqrtN (n : ℕ) : ℝ := Real.sqrt (n : ℝ)

def LittleOp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (V : ℕ → Ω → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → Tendsto (fun n => pr P {ω | |V n ω| > η * a n}) atTop (𝓝 0)

def BoundedInProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (V : ℕ → Ω → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 < M ∧ ∀ᶠ n in atTop,
    pr P {ω | |V n ω| > M} < ε

def Consistent {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hat : ℕ → Ω → ℝ) (μ : ℝ) : Prop :=
  ∀ b : ℝ, 0 < b → Tendsto (fun n => pr P {ω | |hat n ω - μ| > b}) atTop (𝓝 0)

def RootNNormal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hat : ℕ → Ω → ℝ) (μ : ℝ) : Prop :=
  ∃ v : ℝ≥0, 0 < v ∧ TendstoInDistribution
    (fun n ω => sqrtN n * (hat n ω - μ)) atTop (fun z : ℝ => z)
    (fun _ => P) (gaussianReal 0 v)

def NormalRemainder {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hat Z ε : ℕ → Ω → ℝ) (μ : ℝ) (v : ℝ≥0) : Prop :=
  (∀ n, 1 ≤ n → Measurable (Z n) ∧ P.map (Z n) = gaussianReal 0 v) ∧
  (∀ n, 1 ≤ n → Measurable (ε n) ∧ Integrable (fun ω => ε n ω ^ 2) P) ∧
  (∀ n, 1 ≤ n → ∀ᵐ ω ∂P, sqrtN n * (hat n ω - μ) = Z n ω + ε n ω)

def SmallRemainderMS {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ε : ℕ → Ω → ℝ) : Prop :=
  Tendsto (fun n => sqrtN n * (∫ ω, ε n ω ^ 2 ∂P)) atTop (𝓝 0)

def SmallMSE {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (V : ℕ → Ω → ℝ) : Prop :=
  Tendsto (fun n : ℕ => (n : ℝ) * (∫ ω, V n ω ^ 2 ∂P)) atTop (𝓝 0)

def normalCDF (x : ℝ) : ℝ := pr (gaussianReal 0 1) (Iic x)

def normalTail (n : ℕ) (c σ : ℝ) : ℝ :=
  2 * ∫ x in Ioi c, x ^ 2 * (sqrtN n / (σ * Real.sqrt (2 * Real.pi))) *
    Real.exp (-(x ^ 2 * (n : ℝ)) / (2 * σ ^ 2))

def InteriorOrEndpointAtom {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) (τ : Ω → ℝ) (t : ℝ) : Prop :=
  (supportInf (effectSupport G τ) < (t : EReal) ∧
    (t : EReal) < supportSup (effectSupport G τ)) ∨
  (((t : EReal) = supportInf (effectSupport G τ) ∨
    (t : EReal) = supportSup (effectSupport G τ)) ∧ 0 < pr G {ω | τ ω = t})

end
end SAP.P017
