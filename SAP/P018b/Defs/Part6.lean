import SAP.P018b.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018b
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

def T25Statement : Prop :=
  ¬ (∀ (N : ℕ) (_hN : 3 ≤ N), ∃ t1 t2 σ : ℝ,
    0 ≤ t1 ∧ 0 ≤ t2 ∧ 0 ≤ σ ∧ sharedCov N 1 1 = twoRoleCov N t1 t2 σ)

def T26Statement : Prop :=
  ¬ ∀ {U : Type} [MeasurableSpace U] {k : ℕ} (K : Kernel U k), Standing K → SampleRank K →
    (∀ N : ℕ, 3 ≤ N → varMat (unitSampleLaw K N) (scoreSum K) = printedSigma K N) ∧
    (∃ ν : Measure (Vec k), weakLimit (unitSampleLaw K)
      (fun N ω => Real.sqrt N • coefficientError K ω) ν ∧
      (∀ a, MemLp (fun x : Vec k => x a) 2 ν) ∧ meanVec ν id = 0 ∧
      Tendsto (trueTarget K) atTop (𝓝 (varMat ν id)))

def T27Statement : Prop :=
  ∀ {U : Type} [MeasurableSpace U] {k : ℕ} (K : Kernel U k),
    Standing K → SampleRank K → Proposition1Extra K →
    inProbability (unitSampleLaw K) (fun N ω =>
      (N : ℝ) • sampleVariance members (design K ω) (response K ω) - trueTarget K N)

def T28Statement : Prop :=
  ¬ (Tendsto (fun N : ℕ => (N : ℝ) * ProbabilityTheory.variance
      (fun ω => sampleOLS (design signKernel ω) (response signKernel ω) 0)
      (unitSampleLaw signKernel N) - 4 / Dreal N) atTop (𝓝 0) ∧
    inProbability (unitSampleLaw signKernel) (fun N ω =>
      (N : ℝ) * (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 -
        4 / Dreal N))

end SAP.P018b
