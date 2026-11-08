import SAP.P004b.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b

universe u

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology
noncomputable section

def T20Statement : Prop :=
  ∀ {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (μ : ∀ N, Measure (Ω N)) (hμ : ∀ N, IsProbabilityMeasure (μ N))
    (V : ∀ N, Fin N → Ω N → ℝ) (B : ∀ N, Fin N → Finset (Fin N))
    (hmeas : ∀ N i, Measurable (V N i))
    (hmean : ∀ N i, ∫ ω, V N i ω ∂μ N = 0)
    (hbound : ∃ M : ℝ, ∀ N i, ∀ᵐ ω ∂μ N, |V N i ω| ≤ M)
    (hdep : ∀ N, DependencyGraph (μ N) (V N) (B N))
    (hdegree : ∃ D : ℕ, ∀ N i, (B N i).card ≤ D)
    (hvar : ∃ v : ℝ, 0 < v ∧ ∀ᶠ N : ℕ in atTop,
      v*N ≤ (∫ ω, (∑ i, V N i ω)^2 ∂μ N)),
    ∀ x : ℝ, Tendsto (fun N => ((μ N) {ω |
      (∑ i, V N i ω) / Real.sqrt (∫ ω', (∑ i, V N i ω')^2 ∂μ N) ≤ x}).toReal)
        atTop (nhds (normalCDF x))

def T21Statement : Prop :=
  ∀ {N : ℕ} (p : ℝ) (R : CircleTable N) (B : Fin N → Finset (Fin N)),
  0 < N → (0 < p ∧ p < 1) → (∀ i, i ∈ B i) →
  (∀ i j, j ∈ B i ↔ i ∈ B j) →
  (∀ i j, j ∉ B i → ¬ sharesSource R i j) →
  let π := fun _ : Fin N => p
  let g := fun (_ : Fin N) a => barMu π R a
  (∀ i, variance π (residualContrast π R g i) =
    marginal π (fun j z => (R j z-g j true)^2) i true/p +
    marginal π (fun j z => (R j z-g j false)^2) i false/(1-p) -
    (residualEffect π R g i)^2) ∧
  variance π (linearHajek π R) ≤ sahLimit π R B g

def T22Statement : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ),
  0 < N → (∀ i, 0 < p i ∧ p i < 1) → (∀ i, i ∈ B i) →
  (∀ i j, j ∉ B i → ¬ sharesSource R i j) →
  variance p (augmented p R g) = secondMomentBound p R B g - homophilyQ p R B g/N ∧
  (0 ≤ homophilyQ p R B g → variance p (augmented p R g) ≤ secondMomentBound p R B g)

def T23Statement : Prop :=
  ∀ {N : ℕ} (phat : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) (z : Assignment N)
    (hN : 0 < N) (h1 : 0 < armCount z true) (h0 : 0 < armCount z false)
    (hp : ∀ i, 0 < phat i ∧ phat i < 1),
    (∀ i, lambda z i * weightedEpsilon phat R g z i = residualContrast phat R g i z / N) ∧
    sandwich z (weightedEpsilon phat R g z) (Matrix.of (fun i j => if j ∈ B i then 1 else 0)) 1 1 =
      oracleHAC phat R B g z

def T24Statement : Prop :=
  ∀ {N : ℕ} (z : Assignment N)
    (h1 : 0 < armCount z true) (h0 : 0 < armCount z false)
    (e : Fin N → ℝ) (Q : Matrix (Fin N) (Fin N) ℝ),
    (residualMaker z).transpose = residualMaker z ∧
    residualMaker z * residualMaker z = residualMaker z ∧
    residualMaker z * designMatrix z = 0 ∧
    (∀ i, (((designMatrix z).transpose * designMatrix z)⁻¹ * (designMatrix z).transpose) 1 i = lambda z i) ∧
    (((designMatrix z).transpose * designMatrix z)⁻¹) 1 1 = N/(armCount z true * armCount z false) ∧
    (∑ i, (lambda z i)^2) = N/(armCount z true * armCount z false) ∧
    sandwich z e Q 1 1 = kernelVariance z e Q

def T25Statement : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (μ1 μ0 : ℝ) (hN : 0 < N) (hp : ∀ i, 0 < p i ∧ p i < 1),
    (∀ i, expect p (centeredSummand p R μ1 μ0 i) = 0) ∧
    (∀ z, (∑ i, centeredSummand p R μ1 μ0 i z) =
      augmented p R (fun _ a => if a then μ1 else μ0) z - ame p R) ∧
    (∀ i, expect p (fun z => centeredSummand p R μ1 μ0 i z +
      ((1 : ℝ)/N-1)*nodeEffect p R i) = ((1 : ℝ)/N-1)*nodeEffect p R i)

def T26Statement : Prop :=
  ∀ {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)],
  ∀ (P : PopulationSequence Space) (p d : ℝ)
    (K φ : ℝ → ℝ) (bandwidth : ℕ → ℝ) (hp : 0 < p ∧ p < 1)
    (hb : BoundedOutcomes P) (hWD : ∀ N, WellDefined (P N) d)
    (hmetric : MetricNodeDistances P) (hspacing : QuadraticSpacing P) (hK : KernelConditions K)
    (hdiv : Tendsto bandwidth atTop atTop) (hpos : ∀ N, 0 < bandwidth N)
    (hφ : ∀ s, 0 ≤ s → 0 ≤ φ s)
    (henvelope : ∀ᶠ N in atTop, ∀ i j,
      |nodeEffect (fun _ => p) (circleAverage (P N) d) i-ame (fun _ => p) (circleAverage (P N) d)| *
      |nodeEffect (fun _ => p) (circleAverage (P N) d) j-ame (fun _ => p) (circleAverage (P N) d)| ≤
        φ (nodeSeparation (P N) i j))
    (htail : ∀ r : ℕ → ℝ, Tendsto r atTop atTop →
      Tendsto (tailEnvelope P φ r) atTop (nhds 0)),
    Tendsto (kernelHomophily P p d K bandwidth) atTop (nhds 0)

end
end SAP.P004b
