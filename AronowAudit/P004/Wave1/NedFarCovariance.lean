import AronowAudit.P004.Wave1.NedFarCovarianceBlueprint
import AronowAudit.P004.Wave1.NedFarCovariance.E1
import AronowAudit.P004.Wave1.NedFarCovariance.E2
import AronowAudit.P004.Wave1.NedFarCovariance.E3

/-! Far-pair covariance bound, uniform over bounded deterministic fits,
with the population-arm-mean specialization as its second conjunct. -/

universe u

namespace AronowAudit.P004.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

theorem ned_far_covariance_under_uniform_spacing :
  ∀ {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    (P : PopulationSequence Space) (p d : ℝ) (K ψ : ℝ → ℝ) (bandwidth : ℕ → ℝ)
    (_hp : 0 < p ∧ p < 1) (_hb : BoundedOutcomes P) (_hmetric : MetricNodeDistances P)
    (_hspacing : QuadraticSpacing P) (_hK : KernelConditions K)
    (_hψ : ∀ s, 0 ≤ s → 0 ≤ ψ s) (_hψanti : AntitoneOn ψ (Set.Ici 0))
    (_hNED : ∃ G : ℝ, ∀ N i s, 0 ≤ s → l2Norm (fun _ => p)
      (fun z => circleAverage (P N) d i z - conditionOn (fun _ => p)
        (ball (nodeSeparation (P N)) i s) (circleAverage (P N) d i) z) ≤ G*ψ s)
    (_hWD : ∀ᶠ N in atTop, WellDefined (P N) d) (_hband : ∀ᶠ N in atTop, 1 ≤ bandwidth N),
    (∀ M : ℝ, 0 < M → ∃ C : ℝ, ∀ᶠ N in atTop, ∀ μ1 μ0 : ℝ, |μ1| < M → |μ0| < M →
      ∀ i j, 3*bandwidth N < nodeSeparation (P N) i j →
      |cov (fun _ => p)
        (nedVRow p (circleAverage (P N) d) (nodeSeparation (P N)) K (bandwidth N) μ1 μ0 i)
        (nedVRow p (circleAverage (P N) d) (nodeSeparation (P N)) K (bandwidth N) μ1 μ0 j)| ≤
      C*(bandwidth N)^2/(N : ℝ)^4 * max
        (∑ k ∈ ball (nodeSeparation (P N)) i (bandwidth N),
          ψ (nodeSeparation (P N) i j/3-nodeSeparation (P N) i k))
        (∑ l ∈ ball (nodeSeparation (P N)) j (bandwidth N),
          ψ (nodeSeparation (P N) i j/3-nodeSeparation (P N) j l))) ∧
    (∃ C : ℝ, ∀ᶠ N in atTop, ∀ i j, 3*bandwidth N < nodeSeparation (P N) i j →
      |cov (fun _ => p)
        (nedVRow p (circleAverage (P N) d) (nodeSeparation (P N)) K (bandwidth N)
          (barMu (fun _ => p) (circleAverage (P N) d) true)
          (barMu (fun _ => p) (circleAverage (P N) d) false) i)
        (nedVRow p (circleAverage (P N) d) (nodeSeparation (P N)) K (bandwidth N)
          (barMu (fun _ => p) (circleAverage (P N) d) true)
          (barMu (fun _ => p) (circleAverage (P N) d) false) j)| ≤
      C*(bandwidth N)^2/(N : ℝ)^4 * max
        (∑ k ∈ ball (nodeSeparation (P N)) i (bandwidth N),
          ψ (nodeSeparation (P N) i j/3-nodeSeparation (P N) i k))
        (∑ l ∈ ball (nodeSeparation (P N)) j (bandwidth N),
          ψ (nodeSeparation (P N) i j/3-nodeSeparation (P N) j l))) := by
  exact NedFarCovariance.assemble NedFarCovariance.e3_proof

end
end AronowAudit.P004.Wave1
