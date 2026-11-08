import SAP.P001d.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d

/-- Positive sample sizes are indexed by n+1 throughout this moment criterion. -/
def T62Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ],
  ( (∀ (X : ℕ → Ω → ℝ), (∀ i, Measurable (X i)) →
      ∀ T : {n : ℕ} → (Fin n → ℝ) → ℝ, (∀ n, Measurable (@T n)) →
      ∀ φ : ℝ, 0 < φ →
      BootstrapWeakCP μ X (fun n => n+1) T (gaussianReal 0 ⟨φ^2, sq_nonneg _⟩) →
      (( (∀ ε : ℝ, 0 < ε → Tendsto
          (fun K : ℕ => Filter.limsup (fun n => prob μ {ω | ε <
            bootstrapTestMean T (firstSample X (n+1) ω)
              (fun z => if (K : ℝ) < |z| then z^2 else 0)}) atTop) atTop (nhds 0)) ↔
          CP μ (fun n ω => (n+1 : ℕ)*bootVar T (firstSample X (n+1) ω)) (φ^2)) ∧
        (CP μ (fun n ω => (n+1 : ℕ)*bootVar T (firstSample X (n+1) ω)) (φ^2) →
          CP μ (fun n ω => Real.sqrt (n+1 : ℕ)*Real.sqrt (bootVar T (firstSample X (n+1) ω))) φ))) ∧
  (∀ {n : ℕ}, 0 < n → ∀ x : Fin n → ℝ,
    (n : ℝ)*bootVar finiteSampleMean x = (∑ i, (x i)^2)/(n : ℝ)-(finiteSampleMean x)^2) ∧
  (∀ X : ℕ → Ω → ℝ, IID μ X → MemLp (X 0) 2 μ → 0 < variance (X 0) μ →
    CP μ (fun n ω => (n+1 : ℕ)*bootVar finiteSampleMean (firstSample X (n+1) ω))
      (variance (X 0) μ) ∧
    CP μ (fun n ω => Real.sqrt (n+1 : ℕ)*Real.sqrt
      (bootVar finiteSampleMean (firstSample X (n+1) ω))) (Real.sqrt (variance (X 0) μ))) ∧
  (∀ X : ℕ → Ω → ℝ, IID μ X → ∀ (m : ℝ) (f : ℝ → ℝ) (δ : ℝ), 0 < δ →
    (μ.map (X 0)).restrict (Metric.ball m δ) =
      (volume.restrict (Metric.ball m δ)).withDensity (fun x => ENNReal.ofReal (f x)) →
    (∀ x ∈ Metric.ball m δ, 0 ≤ f x) → AEMeasurable f (volume.restrict (Metric.ball m δ)) →
    ContinuousAt f m → 0 < f m →
    (cdf μ (X 0) m = 1/2 ∧ (∀ x, x < m → cdf μ (X 0) x < 1/2) ∧
      (∀ x, m < x → 1/2 < cdf μ (X 0) x)) →
    ∀ η : ℝ, 0 < η → Integrable (fun ω => |X 0 ω|^η) μ →
    CP μ (fun n ω => (n+1 : ℕ)*bootVar sampleMedian (firstSample X (n+1) ω)) (1/(4*(f m)^2)) ∧
    CP μ (fun n ω => Real.sqrt (n+1 : ℕ)*Real.sqrt
      (bootVar sampleMedian (firstSample X (n+1) ω))) (1/(2*f m))) )

def sampleMean {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, X i ω)/(n : ℝ)

def clusterAverage {Ω : Type*} {m : ℕ} (X : ℕ → Ω → Fin m → ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  (∑ j, X i ω j)/(m : ℝ)

def clusterMean {Ω : Type*} {m : ℕ} (X : ℕ → Ω → Fin m → ℝ) (l : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range l, ∑ j, X i ω j)/((l : ℝ)*(m : ℝ))

def T63Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ}, 0 < m →
    ∀ X : ℕ → Ω → Fin m → ℝ, IID μ X → (∀ j, MemLp (fun ω => X 0 ω j) 2 μ) →
    IID μ (clusterAverage X) ∧
    (∀ l, 0 < l → clusterMean X l = sampleMean (clusterAverage X) l ∧
      (∫ ω, clusterMean X l ω ∂μ) = ∫ ω, clusterAverage X 0 ω ∂μ) ∧
    (∫ ω, clusterAverage X 0 ω ∂μ) = (∑ j, ∫ ω, X 0 ω j ∂μ)/(m : ℝ) ∧
    (∀ l, 0 < l → variance (clusterMean X l) μ = variance (clusterAverage X 0) μ/(l : ℝ) ∧
      variance (clusterMean X l) μ =
        (∑ j, ∑ k, covariance (fun ω => X 0 ω j) (fun ω => X 0 ω k) μ)/
          ((l : ℝ)*(m : ℝ)^2)) ∧
    CP μ (fun n => clusterMean X (n+1)) (∫ ω, clusterAverage X 0 ω ∂μ)

def blockResample {l m : ℕ} (X : Fin l → Fin m → ℝ) (draw : Fin l → Fin l) :
    Fin l → Fin m → ℝ := fun i j => X (draw i) j

def T64Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ( (∀ (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ}, 0 < m →
      ∀ X : ℕ → Ω → Fin m → ℝ, IID μ X → (∀ j, MemLp (fun ω => X 0 ω j) 2 μ) →
      ∀ l : ℕ, 0 < l → ∀ s ρ : ℝ, 0 < s → ρ ∈ Set.Icc 0 1 →
      (∀ j, covariance (fun ω => X 0 ω j) (fun ω => X 0 ω j) μ = s) →
      (∀ j k, j ≠ k → covariance (fun ω => X 0 ω j) (fun ω => X 0 ω k) μ = ρ*s) →
      variance (clusterMean X l) μ = s/((l : ℝ)*m)*(1+ρ*((m : ℝ)-1)) ∧
      (ρ = 0 → variance (clusterMean X l) μ = s/((l : ℝ)*m)) ∧
      (ρ = 1 → variance (clusterMean X l) μ = s/(l : ℝ))) ∧
    (∀ {l m : ℕ} (hl : 0 < l), 0 < m → ∀ X : Fin l → Fin m → ℝ,
      letI : NeZero l := ⟨Nat.ne_of_gt hl⟩
      let ρ := Measure.pi (fun _ : Fin l => (PMF.uniformOfFintype (Fin l)).toMeasure)
      IsProbabilityMeasure ρ ∧ iIndepFun (fun i (a : Fin l → Fin l) => a i) ρ ∧
      (∀ i j, prob ρ {a | a i = j} = 1/(l : ℝ)) ∧
      (∀ a : Fin l → Fin l, prob ρ {b | b = a} = (1/(l : ℝ))^l) ∧
      Fintype.card (Fin l × Fin m) = l*m ∧
      (∀ a i j, blockResample X a i j = X (a i) j)) )

end SAP.P001d
