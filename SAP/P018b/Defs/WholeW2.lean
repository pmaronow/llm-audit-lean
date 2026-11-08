import Mathlib
import SAP.P018b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018b

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise ENNReal

/-- The nonconstant regressor in simulation equation (4). -/
def simulationPredictor {N T : ℕ} (ω : SimulationIndex N T → ℝ) (d : Dyad N) : ℝ :=
  |simulationX ω (firstUnit d) - simulationX ω (secondUnit d)|

/-- The linear conditional mean, including the intercept, in equation (4). -/
def simulationMean {N T : ℕ} (β₀ β₁ : ℝ)
    (ω : SimulationIndex N T → ℝ) (d : Dyad N) : ℝ :=
  β₀ + β₁ * simulationPredictor ω d

/-- The response in equation (4); the printed simulation uses β₀ = 0 and β₁ = 1. -/
def simulationY {N T : ℕ} (β₀ β₁ : ℝ)
    (ω : SimulationIndex N T → ℝ) (d : Dyad N) (t : Fin T) : ℝ :=
  simulationMean β₀ β₁ ω d + simulationError ω d t

/-- The joint error law, its independence from all covariates, and its first two moments.
The intersection formula includes all four covariance cases in the claim. -/
def simulationErrorFacts {Ω : Type*} [MeasurableSpace Ω] {N T : ℕ}
    (μ : Measure Ω) (Z : Ω → SimulationIndex N T → ℝ) : Prop :=
  IsGaussian (μ.map (fun ω =>
    fun dt : Dyad N × Fin T => simulationError (Z ω) dt.1 dt.2)) ∧
  IndepFun (fun ω => fun dt : Dyad N × Fin T => simulationError (Z ω) dt.1 dt.2)
    (fun ω => fun i : Fin N => simulationX (Z ω) i) μ ∧
  (∀ d t, MemLp (fun ω => simulationError (Z ω) d t) 2 μ) ∧
  (∀ d t, (∫ ω, simulationError (Z ω) d t ∂μ) = 0) ∧
  (∀ d f : Dyad N, ∀ t u : Fin T, ProbabilityTheory.covariance
    (fun ω => simulationError (Z ω) d t) (fun ω => simulationError (Z ω) f u) μ =
      ((members d ∩ members f).card : ℝ) + (if d = f ∧ t = u then 1 else 0))

/-- P018-T22; p. 569 (PDF p. 6), sentence after equation (4).
With the corrected symbol ν, mutually independent standard-normal covariates, unit effects and
observation errors give jointly Gaussian mean-zero compound errors, independent of all covariates.
Their covariance is the number of shared units plus the same-observation indicator (hence 3, 2,
1 or 0). Their conditional means given all covariates vanish. For equation (4), the conditional
response mean given the endpoint covariates, and given the regressors (1, |Xᵢ-Xⱼ|), is
β₀ + β₁|Xᵢ-Xⱼ|. Thus this regression is correctly specified, in particular for β₀ = 0, β₁ = 1
and T = 1 or 2. The usual measure-theoretic conditions are assumed; the finite moments used
below follow from the Gaussian input laws. -/
def T22WholeStatement : Prop :=
  ∀ N T : ℕ, 2 ≤ N → 1 ≤ T →
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → SimulationIndex N T → ℝ), Measurable Z →
    (∀ a, HasLaw (fun ω => Z ω a) (gaussianReal 0 1) μ) →
    iIndepFun (fun a ω => Z ω a) μ →
    simulationErrorFacts μ Z ∧
    (∀ d t, MeasureTheory.condExp (MeasurableSpace.comap
      (fun ω => fun i : Fin N => simulationX (Z ω) i) inferInstance) μ
      (fun ω => simulationError (Z ω) d t) =ᵐ[μ] 0) ∧
    (∀ (β₀ β₁ : ℝ) (d : Dyad N) (t : Fin T),
      MeasureTheory.condExp (MeasurableSpace.comap
        (fun ω => (simulationX (Z ω) (firstUnit d),
          simulationX (Z ω) (secondUnit d))) inferInstance) μ
        (fun ω => simulationY β₀ β₁ (Z ω) d t) =ᵐ[μ]
          (fun ω => simulationMean β₀ β₁ (Z ω) d) ∧
      MeasureTheory.condExp (MeasurableSpace.comap
        (fun ω => ((1 : ℝ), simulationPredictor (Z ω) d)) inferInstance) μ
        (fun ω => simulationY β₀ β₁ (Z ω) d t) =ᵐ[μ]
          (fun ω => simulationMean β₀ β₁ (Z ω) d))

/-- P018-T24; p. 571 (PDF p. 8), Section 5, second paragraph; Table 1, p. 572 (PDF p. 9).
The nine exact dyadic/heteroskedastic standard-error ratios have the displayed values, minimum
24749/10734 and maximum 172/39, and are all below 5 and 10. Rounding to three decimals cannot
conceal a tenfold ratio: the exact row bounds are as displayed and at most 17/3. Each row has
D > C > H, with D/C ranging from 185/181 to 86/47. The international-organizations ratio is
11/8 < 1.64. On the full one-sided domains, |b| ≤ 23/2000 and se ≥ 15/2000 imply
|b|/se ≤ 23/15 < 1.64; independently, |b| ≥ 21/2000 and 0 < se ≤ 5/2000 imply
|b|/se ≥ 21/5 > 1.64. -/
def T24WholeStatement : Prop :=
  tableExactFacts ∧ tableMagnitudeFacts ∧
  (∀ r ∈ tableSE, r.2.2 / r.1 < 10) ∧
  (∀ r ∈ tableSE, 0 < (r.1 : ℝ) - 1/2000 ∧
    (r.2.2 : ℝ) + 1/2000 < 10 * ((r.1 : ℝ) - 1/2000) ∧
    ((r.2.2 : ℝ) + 1/2000) / ((r.1 : ℝ) - 1/2000) ≤ 17/3) ∧
  (∀ b se : ℝ, |b| ≤ 23/2000 → 15/2000 ≤ se →
    |b|/se ≤ 23/15 ∧ (23/15 : ℝ) < 41/25) ∧
  (∀ b se : ℝ, 21/2000 ≤ |b| → 0 < se → se ≤ 5/2000 →
    21/5 ≤ |b|/se ∧ (41/25 : ℝ) < 21/5) ∧
  (185/1000 : ℚ) / (181/1000) = 185/181 ∧
  (344/1000 : ℚ) / (188/1000) = 86/47 ∧
  (11/1000 : ℝ) / (8/1000) = 11/8

/-- The printed claim is false: its Appendix B assertion E[Vhat - V] → 0 fails in the
bounded iid fair-sign intercept model Xᵢⱼ = 1, Yᵢⱼ = Uᵢ + Uⱼ.
P018-T27; p. 567 (PDF p. 4), Proposition 1; pp. 573–574 (PDF pp. 10–11), Appendix B.
This model satisfies the standing assumptions, eventual sample rank and all exported bounded
fitted-residual and nonzero-moment assumptions. Its population Gram is 1 and population slope is
0. For N ≥ 4 the target V is 4 and E[Vhat] = 4(N-2)(N-3)/(N²(N-1)). Consequently
E[Vhat - V] → -4 and does not tend to 0, refuting the full printed assertion including its proof.
The usual measure-theoretic conditions are assumed; the expectation in the refutation is
integrable for every N. This refutation concerns the printed mean assertion. -/
def T27WholeStatement : Prop :=
  Standing signKernel ∧ SampleRank signKernel ∧ Proposition1Extra signKernel ∧
  populationGram signKernel = (1 : Mat 1) ∧ populationBeta signKernel = 0 ∧
  (∀ N : ℕ, Integrable (fun ω =>
    (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 -
      (trueTarget signKernel N) 0 0) (unitSampleLaw signKernel N)) ∧
  (∀ N : ℕ, 4 ≤ N → trueTarget signKernel N = !![4] ∧
    (∫ ω, (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0
      ∂ unitSampleLaw signKernel N) =
      4 * ((N : ℝ)-2) * ((N : ℝ)-3) / ((N : ℝ)^2 * ((N : ℝ)-1))) ∧
  Tendsto (fun N : ℕ => ∫ ω,
    (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 -
      (trueTarget signKernel N) 0 0 ∂ unitSampleLaw signKernel N) atTop (𝓝 (-4)) ∧
  ¬ Tendsto (fun N : ℕ => ∫ ω,
    (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 -
      (trueTarget signKernel N) 0 0 ∂ unitSampleLaw signKernel N) atTop (𝓝 0)

end SAP.P018b
