import Mathlib
import SAP.P001b.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section

def T30Statement : Prop :=
  (∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (f g : ℝ → ℝ), Density ν f → Density ν g →
    f =ᵐ[volume] g ∧
    (∀ᵐ x ∂volume, HasDerivAt (fun t => probability ν (Set.Iic t)) (f x) x) ∧
    (∀ x, DifferentiableAt ℝ (fun t => probability ν (Set.Iic t)) x →
      0 ≤ deriv (fun t => probability ν (Set.Iic t)) x) ∧ (∫ x, f x) = 1) ∧
  (∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (f h : ℝ → ℝ),
    Density ν f → (∀ x, 0 ≤ h x) → h =ᵐ[volume] f →
    Density ν h ∧ ∀ x : ℝ, probability ν (Set.Iic x) = ∫ t in Set.Iic x, h t) ∧
  (∀ (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν] (f g : ℝ × ℝ → ℝ),
    JointDensity ν f → JointDensity ν g → f =ᵐ[volume] g) ∧
  (∀ y : ℝ, y ∈ Set.Ioo (0 : ℝ) 1 →
    ¬ DifferentiableAt ℝ
      (fun u => deriv (fun v => uniformDistributionFunction u * uniformDistributionFunction v) y) 0) ∧
  (∀ x y : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
    uniformDistributionFunction x * uniformDistributionFunction y = x * y) ∧
  (∀ (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    (f : ℝ × ℝ → ℝ) (fx fy : ℝ → ℝ),
    JointDensity ν f → Density (ν.map Prod.fst) fx → Density (ν.map Prod.snd) fy →
    (ν = (ν.map Prod.fst).prod (ν.map Prod.snd) ↔
      f =ᵐ[volume] (fun xy => fx xy.1 * fy xy.2)))

def T31Statement : Prop :=
  IsClosed fatCantorSet ∧ volume fatCantorSet = 1/2 ∧
  IsProbabilityMeasure cantorProbability ∧
  Measurable (fun x : fatCantorSet => x.val) ∧
  Density (cantorProbability.map (fun x : fatCantorSet => x.val)) cantorDensity ∧
  Set.range (fun x : fatCantorSet => x.val) = fatCantorSet ∧
  {x | 0 < cantorDensity x} = fatCantorSet ∧
  ∀ a b : ℝ, a < b → ¬ Set.Icc a b ⊆ fatCantorSet

def T32Statement : Prop :=
  (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ), Measurable X → ∀ f : ℝ → ℝ, Density (μ.map X) f →
    (∀ t : ℝ, μ {ω | X ω = t} = 0) ∧ ¬ (Set.range X).Countable ∧ ¬ Countable Ω) ∧
  (let C : Set ℝ := Set.Icc (0 : ℝ) (1/2) \ Set.range (fun q : ℚ => (q : ℝ))
   ∃ ν : Measure C,
    MeasurableSet C ∧ volume C = 1/2 ∧ IsProbabilityMeasure ν ∧
    Measurable (fun x : C => x.val) ∧ Set.range (fun x : C => x.val) = C ∧
    Density (ν.map (fun x : C => x.val)) (fun x => if x ∈ C then 2 else 0) ∧
    ¬ C.Countable ∧ ¬ Countable C ∧
    ∀ a b : ℝ, a < b → ¬ Set.Icc a b ⊆ Set.range (fun x : C => x.val))

def T33Statement : Prop :=
  ∀ {Ω : Type*} (X : Ω → ℝ) (g h : ℝ → ℝ),
    g ∘ X = h ∘ X ↔ ∀ x ∈ Set.range X, g x = h x

def T34Statement : Prop :=
  (∀ z, 0 ≤ negativeRectangleDensity z) ∧ Integrable negativeRectangleDensity volume ∧
  (∫ z : ℝ × ℝ, negativeRectangleDensity z) = 1 ∧
  (∫ z in {z : ℝ × ℝ | 0 ≤ z.1 ∧ z.1 ≤ 1 ∧ z.2 ≤ z.1}, negativeRectangleDensity z) = 1 ∧
  (∫ x in Set.Icc (0 : ℝ) 1, ∫ y in Set.Icc 0 x, negativeRectangleDensity (x,y)) = 0 ∧
  (∫ z in {z : ℝ × ℝ | 0 ≤ z.1 ∧ z.1 ≤ 1 ∧ z.2 ≤ z.1}, negativeRectangleDensity z) ≠
    (∫ x in Set.Icc (0 : ℝ) 1, ∫ y in Set.Icc 0 x, negativeRectangleDensity (x,y))

def T35Statement : Prop :=
  ∀ (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν] (f : ℝ × ℝ → ℝ), JointDensity ν f →
  probability ν {z | 0 ≤ z.1 ∧ z.1 ≤ 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ z.1} =
    (∫ x in Set.Icc (0 : ℝ) 1, ∫ y in Set.Icc 0 x, f (x,y)) ∧
  probability ν {z | 0 ≤ z.1 ∧ z.1 ≤ 1 ∧ z.2 ≤ z.1} =
    (∫ x in Set.Icc (0 : ℝ) 1, ∫ y in Set.Icc 0 x, f (x,y)) +
    probability ν {z | 0 ≤ z.1 ∧ z.1 ≤ 1 ∧ z.2 < 0} ∧
  (probability ν {z | 0 ≤ z.1 ∧ z.1 ≤ 1 ∧ z.2 ≤ z.1} =
    (∫ x in Set.Icc (0 : ℝ) 1, ∫ y in Set.Icc 0 x, f (x,y)) ↔
    probability ν {z | 0 ≤ z.1 ∧ z.1 ≤ 1 ∧ z.2 < 0} = 0)

def T36Statement : Prop :=
  ContDiff ℝ ⊤ infiniteSliceDensity ∧ (∀ z, 0 < infiniteSliceDensity z) ∧
  Integrable infiniteSliceDensity volume ∧ (∫ z, infiniteSliceDensity z) = 1 ∧
  (∫⁻ x : ℝ, ENNReal.ofReal (infiniteSliceDensity (x,0))) = ∞ ∧
  (∀ y : ℝ, y ≠ 0 → Integrable (fun x => infiniteSliceDensity (x,y)) volume)

def T37Statement : Prop :=
  (∀ (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν] (f : ℝ × ℝ → ℝ), JointDensity ν f →
    (∀ᵐ y ∂volume, (∫⁻ x : ℝ, ENNReal.ofReal (f (x,y))) < ∞) ∧
    ∀ g : ℝ → ℝ, (∀ y, 0 ≤ g y) →
      (∀ᵐ y ∂volume, ENNReal.ofReal (g y) = (∫⁻ x : ℝ, ENNReal.ofReal (f (x,y)))) →
      Density (ν.map Prod.snd) g ∧
      ∀ y : ℝ, probability (ν.map Prod.snd) (Set.Iic y) = ∫ v in Set.Iic y, g v) ∧
  (∀ f : ℝ × ℝ → ℝ, Measurable f → (∀ xy, 0 ≤ f xy) →
    ∀ x : ℝ, Integrable (fun y => f (x,y)) volume → (0 < ∫ y, f (x,y)) →
    Integrable (fun y => f (x,y) / (∫ t, f (x,t))) volume ∧
    (∀ y, 0 ≤ f (x,y) / (∫ t, f (x,t))) ∧
    (∫ y, f (x,y) / (∫ t, f (x,t))) = 1)

def T38Statement : Prop :=
  (let W := (gaussianReal 0 1).map (fun _ : ℝ => (0 : ℝ))
   W = Measure.dirac 0 ∧ W {0} = 1 ∧
   (¬ ∃ f : ℝ → ℝ, Density W f) ∧
   (∀ (m : ℝ) (s : ℝ≥0), 0 < s → W ≠ gaussianReal m s)) ∧
  (∀ x : ℝ, 0 * x = 0) ∧
  (1 : ℝ) ∈ Set.Icc (-1) 1 ∧ (-1 : ℝ) ∈ Set.Icc (-1) 1 ∧
  (1 - (1 : ℝ)^2 = 0 ∧ 1 - (-1 : ℝ)^2 = 0) ∧
  (2 * (1 - (1 : ℝ)^2) = 0 ∧ 2 * (1 - (-1 : ℝ)^2) = 0) ∧
  (2 * Real.pi * Real.sqrt (1 - (1 : ℝ)^2) = 0) ∧
  (2 * Real.pi * Real.sqrt (1 - (-1 : ℝ)^2) = 0) ∧
  (∀ xy : ℝ × ℝ, printedBivariateNormal 0 0 1 1 1 xy = 0 ∧
    printedBivariateNormal 0 0 1 1 (-1) xy = 0) ∧
  (∫ xy : ℝ × ℝ, printedBivariateNormal 0 0 1 1 1 xy) = 0 ∧
  (∫ xy : ℝ × ℝ, printedBivariateNormal 0 0 1 1 (-1) xy) = 0 ∧ (0 : ℝ) ≠ 1

end
end SAP.P001b
