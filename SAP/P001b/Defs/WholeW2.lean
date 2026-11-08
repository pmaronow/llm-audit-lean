import Mathlib
import SAP.P001b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001b

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- The nonnegative lower-tail integral definition of a PDF (Definition 1.2.14).
Lebesgue measurability means almost-everywhere measurability for `volume`.
The equality is in the extended nonnegative reals: for a probability law its
right side is finite, so an infinite integral cannot masquerade as a real zero.
Neither global integrability nor equality with a weighted measure is assumed. -/
def CDFDensity (ν : Measure ℝ) (f : ℝ → ℝ) : Prop :=
  AEMeasurable f volume ∧ (∀ x, 0 ≤ f x) ∧
    ∀ x : ℝ, (∫⁻ t in Set.Iic x, ENNReal.ofReal (f t)) = ν (Set.Iic x)

/-- The nonnegative iterated lower-tail definition of a joint PDF
(Definition 1.3.10). Tonelli integrals allow exceptional nonintegrable slices;
the finite joint-CDF value guards the entire lower-rectangle integral.
No extra pointwise slice regularity or global integrability is assumed. -/
def JointCDFDensity (ν : Measure (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) : Prop :=
  AEMeasurable f volume ∧ (∀ z, 0 ≤ f z) ∧
    ∀ x y : ℝ,
      (∫⁻ u in Set.Iic x, ∫⁻ v in Set.Iic y, ENNReal.ofReal (f (u, v))) =
        ν (Set.Iic x ×ˢ Set.Iic y)

/-- Joint CDF of a planar law, evaluated only for probability laws below. -/
def jointDistributionFunction (ν : Measure (ℝ × ℝ)) (x y : ℝ) : ℝ :=
  probability ν (Set.Iic x ×ˢ Set.Iic y)

/-- Uniform probability law on the unit interval; its interval has volume one. -/
def unitUniformLaw : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

/-- P001-T30. Location: p. 24 (PDF p. 42), sentence after Definition 1.2.14;
p. 25 (PDF p. 43), Definition 1.2.15 and Theorem 1.2.16; p. 36 (PDF p. 54),
Definitions 1.3.10 and 1.3.11; p. 38 (PDF p. 56), Definition 1.3.16;
p. 39 (PDF p. 57), Theorem 1.3.17.
Nonnegative Lebesgue integral PDF versions agree almost everywhere, equal the CDF
derivative almost everywhere, and integrate to one. The CDF has a nonnegative
derivative wherever it is differentiable. Every nonnegative almost-everywhere
replacement is another PDF. Joint integral PDF versions agree almost everywhere.
The product uniform law has CDF xy on the unit square, but its mixed derivative,
first in the second variable, fails at (0,y) for every 0 < y < 1, even though
the inner derivative exists. Continuous independence is equivalent both to
almost-everywhere PDF factorization and to the product being a joint PDF version.
For discrete real random variables, PMF factorization is pointwise. -/
def T30WholeStatement : Prop :=
  (∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (f g : ℝ → ℝ),
    CDFDensity ν f → CDFDensity ν g →
      f =ᵐ[volume] g ∧
      (∀ᵐ x ∂volume, HasDerivAt (fun t => probability ν (Set.Iic t)) (f x) x) ∧
      (∀ x, DifferentiableAt ℝ (fun t => probability ν (Set.Iic t)) x →
        0 ≤ deriv (fun t => probability ν (Set.Iic t)) x) ∧
      Integrable f volume ∧ (∫ x, f x) = 1 ∧
      ∀ x : ℝ, probability ν (Set.Iic x) = ∫ t in Set.Iic x, f t) ∧
  (∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (f h : ℝ → ℝ),
    CDFDensity ν f → (∀ x, 0 ≤ h x) → h =ᵐ[volume] f →
      CDFDensity ν h ∧ Integrable h volume ∧
      ∀ x : ℝ, probability ν (Set.Iic x) = ∫ t in Set.Iic x, h t) ∧
  (∀ (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν] (f g : ℝ × ℝ → ℝ),
    JointCDFDensity ν f → JointCDFDensity ν g → f =ᵐ[volume] g) ∧
  (let ν := unitUniformLaw.prod unitUniformLaw;
    IsProbabilityMeasure unitUniformLaw ∧ IsProbabilityMeasure ν ∧
    IndepFun Prod.fst Prod.snd ν ∧
    (∀ t : ℝ, probability unitUniformLaw (Set.Iic t) = uniformDistributionFunction t) ∧
    (∀ x y : ℝ, jointDistributionFunction ν x y =
      uniformDistributionFunction x * uniformDistributionFunction y) ∧
    (∀ x y : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
      jointDistributionFunction ν x y = x * y) ∧
    (∀ y : ℝ, y ∈ Set.Ioo (0 : ℝ) 1 →
      (∀ u : ℝ, HasDerivAt (fun v => jointDistributionFunction ν u v)
        (uniformDistributionFunction u) y) ∧
      ¬ DifferentiableAt ℝ (fun u => deriv (fun v => jointDistributionFunction ν u v) y) 0)) ∧
  (∀ (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    (f : ℝ × ℝ → ℝ) (fx fy : ℝ → ℝ),
    JointCDFDensity ν f → CDFDensity (ν.map Prod.fst) fx →
    CDFDensity (ν.map Prod.snd) fy →
      (ν = (ν.map Prod.fst).prod (ν.map Prod.snd) ↔
        f =ᵐ[volume] (fun z => fx z.1 * fy z.2)) ∧
      (f =ᵐ[volume] (fun z => fx z.1 * fy z.2) ↔
        JointCDFDensity ν (fun z => fx z.1 * fy z.2))) ∧
  (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ), Measurable X → Measurable Y →
    (Set.range X).Countable → (Set.range Y).Countable →
      (IndepFun X Y μ ↔ ∀ x y : ℝ,
        probability μ {ω | X ω = x ∧ Y ω = y} =
          probability μ {ω | X ω = x} * probability μ {ω | Y ω = y}))

end
end SAP.P001b
