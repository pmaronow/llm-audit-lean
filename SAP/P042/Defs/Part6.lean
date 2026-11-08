import SAP.P042.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P042

noncomputable section
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

/-- A difference of disjoint pools retains all within- and between-pool covariances. -/
def PooledDifferenceLaw : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (N A : Finset ι),
    N.Nonempty → A.Nonempty → Disjoint N A → ∀ (D : ι → Ω → ℝ),
    (∀ j, MemLp (D j) 2 μ) → (∀ j, 0 < variance (D j) μ) →
    let v := fun j => variance (D j) μ
    let aN := subsetWeight N v
    let aA := subsetWeight A v
    let b := fun j => aN j-aA j
    variance (fun ω => pooled aN D ω-pooled aA D ω) μ =
      covarianceForm b (fun j k => covariance (D j) (D k) μ) ∧
    variance (fun ω => pooled aN D ω-pooled aA D ω) μ =
      variance (pooled aN D) μ + variance (pooled aA D) μ -
        2*covariance (pooled aN D) (pooled aA D) μ

/-- A three-contrast block gives the specified correction to the diagonal variance. -/
def ThreeContrastLaw : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ℕ), 0 < J → ∀ (D : Fin J → Ω → ℝ),
    (∀ j, MemLp (D j) 2 μ) → (∀ j, 0 < variance (D j) μ) →
    ∀ (e : Fin 3 ↪ Fin J) (a c12 c13 c23 : ℝ),
    (∀ g, normalizedWeight (fun j => variance (D j) μ) (e g) = a) →
    (∀ j k, j ≠ k → covariance (D j) (D k) μ =
      if (j = e 0 ∧ k = e 1) ∨ (j = e 1 ∧ k = e 0) then c12 else
      if (j = e 0 ∧ k = e 2) ∨ (j = e 2 ∧ k = e 0) then c13 else
      if (j = e 1 ∧ k = e 2) ∨ (j = e 2 ∧ k = e 1) then c23 else 0) →
    variance (pooled (normalizedWeight (fun j => variance (D j) μ)) D) μ =
      (totalWeight (fun j => variance (D j) μ))⁻¹ + 2*a^2*(c12+c13+c23) ∧
    (c12 = c13 → c13 = c23 →
      variance (pooled (normalizedWeight (fun j => variance (D j) μ)) D) μ =
        (totalWeight (fun j => variance (D j) μ))⁻¹ + 6*a^2*c12)

/-- Complete three-arm randomization and the sharp-null specialization. -/
def FinitePopulationLaw : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∀ (n : Fin 3 → ℕ),
    (∀ g, 0 < n g) → (∑ g, n g) ≤ N → ∀ (Y : Fin N → Fin 3 → ℝ),
    let S := completeThreeAllocations N n
    let D1 := fun z => randomizedArmMean n Y 1 z-randomizedArmMean n Y 0 z
    let D2 := fun z => randomizedArmMean n Y 2 z-randomizedArmMean n Y 0 z
    let tau1 := fun i => Y i 1-Y i 0
    let tau2 := fun i => Y i 2-Y i 0
    S.Nonempty ∧
    finiteCovariance S D1 D2 =
      populationCovariance (fun i => Y i 0) (fun i => Y i 0)/(n 0:ℝ) -
      populationCovariance tau1 tau2/(N:ℝ) ∧
    populationCovariance tau1 tau2 =
      populationCovariance (fun i => Y i 1) (fun i => Y i 2) -
      populationCovariance (fun i => Y i 1) (fun i => Y i 0) -
      populationCovariance (fun i => Y i 0) (fun i => Y i 2) +
      populationCovariance (fun i => Y i 0) (fun i => Y i 0) ∧
    ((∀ i, Y i 1 = Y i 0 ∧ Y i 2 = Y i 0) →
      finiteCovariance S D1 D2 =
        populationCovariance (fun i => Y i 0) (fun i => Y i 0)/(n 0:ℝ))

def T2Statement : Prop :=
  LinearPoolingLaw ∧ PrecisionPoolingLaw ∧ SharedControlLaw ∧ IndependentArmLaw ∧
  CovarianceBoundLaw ∧ PooledDifferenceLaw ∧ ThreeContrastLaw ∧ FinitePopulationLaw

end
end SAP.P042
