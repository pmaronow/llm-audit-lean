import SAP.P031.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P031

open scoped BigOperators Matrix Topology
open Finset Filter

noncomputable section

def footnoteSigns (k : ℕ) (i : Fin (4 * k)) : ℝ := if i.val < 2 * k then -1 else 1

def footnotePopulation (a : ℝ) (n : ℕ) : Population where
  N := 4 * (n + 2)
  M := n + 2
  y0 := footnoteSigns (n + 2)
  y1 := fun i => a * footnoteSigns (n + 2) i + 2
  hM := by omega
  hMN := by omega

def shiftedPopulation (P : Population) (c d : ℝ) : Population where
  N := P.N
  M := P.M
  y1 := fun i => P.y1 i + (c + d)
  y0 := fun i => P.y0 i + c
  hM := P.hM
  hMN := P.hMN

/-- The three fixed-first-moment families and their OLS limits;
the CE limit is outside this counterexample target and is excluded. -/
def FootnoteVarianceWitness (a q : ℝ) : Prop :=
  GrowingPopulations (footnotePopulation a) ∧
  (∀ n, (footnotePopulation a n).N ≠ 2 * (footnotePopulation a n).M) ∧
  (∀ n, ((footnotePopulation a n).M : ℝ) / (footnotePopulation a n).N = 1 / 4 ∧
    groupMean univ (footnotePopulation a n).y0 = 0 ∧
    groupMean univ (footnotePopulation a n).y1 = 2 ∧
    populationEffect (footnotePopulation a n) = 2 ∧
    popVariance (footnotePopulation a n).y0 = 1 ∧
    popVariance (footnotePopulation a n).y1 = a ^ 2 ∧
    popCovariance (footnotePopulation a n).y1 (footnotePopulation a n).y0 = a) ∧
  Tendsto (fun n => ((footnotePopulation a n).N : ℝ) * trueVariance (footnotePopulation a n))
    atTop (𝓝 (3 * a ^ 2 + 2 * a + 1 / 3)) ∧
  Tendsto (fun n => ((footnotePopulation a n).N : ℝ) *
    expectation (footnotePopulation a n).M (fun s => olsEstimator (footnotePopulation a n) s))
    atTop (𝓝 (4 * a ^ 2 / 3 + 4)) ∧
  ConvergesInProbability (footnotePopulation a) (fun Q s => (Q.N : ℝ) * olsEstimator Q s)
    (4 * a ^ 2 / 3 + 4) ∧
  ConvergesInProbability (footnotePopulation a) (fun Q s => olsEstimator Q s / trueVariance Q) q

/-- Sample second-moment convergence means consistency of both
centered traditional arm variances for the divisor-N population variances. -/
def ArmSecondMomentsConverge (P : ℕ → Population) : Prop :=
  ConvergesInProbability P (fun Q s => sampleVariance s Q.y1 - popVariance Q.y1) 0 ∧
  ConvergesInProbability P (fun Q s => sampleVariance sᶜ Q.y0 - popVariance Q.y0) 0

def UniformlyBoundedOutcomes (P : ℕ → Population) : Prop :=
  ∃ B : ℝ, ∀ n i, |(P n).y1 i| ≤ B ∧ |(P n).y0 i| ≤ B

end
end SAP.P031
