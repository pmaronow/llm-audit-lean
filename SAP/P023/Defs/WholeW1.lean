import Mathlib
import SAP.P023.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P023
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

/-- Squared prediction loss as a nonnegative extended expectation, including infinite risk. -/
def extendedPredictionRisk (ν : Measure (ℝ × ℝ)) (f : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal ((z.2 - f z.1)^2) ∂ν

/-- T3(c): polynomial nonlocality needs no close-window counts. Those counts
are required only when comparing the two defined RD means and coarsened fits. -/
def WholeFiniteNonlocality : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : ℕ) (hJ : 1 ≤ J) (k : ℝ) (hk : 0 < k ∧ k < 1) (x d : ι → ℝ)
    (hdata : TwoParty x d) (hfull : FullRank (polynomialDesign J x d))
    (hboth : (∃ i, d i = 1) ∧ (∃ i, d i = 0)),
    ((Finset.univ.filter (fun i => x i < 0 ∧ finiteWeight J x d i = 0)).image x).card ≤ J ∧
    ((Finset.univ.filter (fun i => 0 < x i ∧ finiteWeight J x d i = 0)).image x).card ≤ J ∧
    (((Finset.univ.filter (fun i => i ∉ close k x ∧ x i ≠ 0)).image x).card > 2*J →
      ∃ (i : ι) (y y' : ι → ℝ), i ∉ close k x ∧
      (∀ l, l ≠ i → y l = y' l) ∧ (∀ l ∈ close k x, y l = y' l) ∧
      polynomialOLS J x d y ≠ polynomialOLS J x d y' ∧
      ((0 < ∑ l ∈ close k x, d l) → (0 < ∑ l ∈ close k x, (1-d l)) →
      rd k x d y = rd k x d y' ∧
      (∀ β β', CoarsenedOLS k x d y β → CoarsenedOLS k x d y' β' → β = β')))

/-- The population projections in the uniform examples exist, have positive
normalization, and use positive definite regressor moments at every finite degree. -/
def WholeUniformProjections : Prop :=
  ∀ J : ℕ, 1 ≤ J → MomentPositiveDefinite uniformMargins J ∧
    IsProjection uniformMargins J (projection uniformMargins J) ∧
    0 < residualVariance uniformMargins J

/-- T3(f): the fixed-tolerance union bound and its common-consistency consequence.
The estimators may be dependent and need not satisfy separate rank/count conditions. -/
def WholeSharedConsistency : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (A B : ℕ → Ω → ℝ) (β : ℝ),
    (∀ N ε, 0 < ε → P {ω | ε < |A N ω - B N ω|} ≤
      P {ω | ε/2 < |A N ω - β|} + P {ω | ε/2 < |B N ω - β|}) ∧
    (ConvergesInProbability P A β → ConvergesInProbability P B β →
      ConvergesInProbability P (fun N ω => A N ω - B N ω) 0)

/-- P023-T3; p. 3 (PDF p. 3) and p. 7 (PDF p. 7); Section 5, p. 8 (PDF p. 8).
Coarsened OLS has exactly the localized RD weights and a unique party coefficient.
Full-rank polynomial OLS has the residual weights, root-count nonlocality and
conditional moments stated in clauses (b)–(d). The uniform degree-one and
degree-seven examples share the cutoff target while retaining distant influence.
For every positive tolerance the difference-event probability is bounded by the
two half-tolerance error probabilities; shared consistency implies convergence
of the estimator difference without an independence or sample-admissibility premise. -/
def T3WholeStatement : Prop :=
  PrintedBinEquivalence ∧ CoarsenedWeights ∧ CoarsenedLocalization ∧
  FinitePolynomialWeights ∧ WholeFiniteNonlocality ∧ ConditionalMoments ∧
  UniformIllustration ∧ WholeUniformProjections ∧ WholeSharedConsistency

/-- The numerical T4 sampling limits, without additional sample-rank or count assumptions. -/
def WholeSigmoidSampling : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (sample : ℕ → Ω → ℝ × ℝ)
    (hiid : IIDSample P (witnessLaw uniformMargins (sigmoid (1/20) (1/10000))) sample)
    (k : ℕ → ℝ) (hpos : ∀ N, 0 < k N) (hk : Tendsto k atTop (nhds 0))
    (hnk : Tendsto (fun N : ℕ => (N:ℝ)*k N) atTop atTop),
    ConvergesInProbability P (fun N => samplePolynomial sample N 1) (99980001/1000000000) ∧
    ConvergesInProbability P (fun N => samplePolynomial sample N 7)
      (4896723787999993532000048047999857/49000000000000000000000000000000000) ∧
    ConvergesInProbability P (sampleRD sample k) 0

/-- T4's coefficient is the residual ratio and the fixed-degree probability
limit for every member of the family, not only the numerical example.
All regressor losses are integrable, so the real fitted-risk infimum has no
undefined-integral candidates. -/
def WholeSigmoidFamily : Prop :=
  ∀ a η : ℝ, 0 < a → 0 < η → η ≤ 1 →
    let ν := witnessLaw uniformMargins (sigmoid a η)
    ProbabilityLaw ν ∧ marginLaw ν = uniformMargins ∧
    Integrable (fun z => z.2^2) ν ∧
    Continuous (fun x => 1/2 + sigmoid a η x) ∧
    (1/2 + sigmoid a η 0 = (1/2 : ℝ)) ∧
    (∀ J (c : Fin (J+2) → ℝ), Integrable
      (fun z => (z.2-predict (polynomialDesign J (fun x : ℝ => x) party) c z.1)^2) ν) ∧
    (∀ J, 1 ≤ J → populationCoefficient uniformMargins J (fun x => 1/2+sigmoid a η x) =
      biasFunctional uniformMargins J (fun x => 1/2+sigmoid a η x)) ∧
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (sample : ℕ → Ω → ℝ × ℝ),
      IIDSample P ν sample → ∀ J, 1 ≤ J →
      ConvergesInProbability P (fun N => samplePolynomial sample N J)
        (populationCoefficient uniformMargins J (fun x => 1/2+sigmoid a η x)))

/-- Every measurable competing predictor is allowed; infinite risks cannot
improve a finite fitted risk. The fitted regression risk is finite. -/
def WholeSigmoidAllRisks : Prop :=
  ∀ a η : ℝ, 0 < a → 0 < η → η ≤ 1 → ∀ J : ℕ, 1 ≤ J →
    let ν := witnessLaw uniformMargins (sigmoid a η)
    ∀ f : ℝ → ℝ, Measurable f →
      ENNReal.ofReal (1/100) ≤ extendedPredictionRisk ν f ∧
      ENNReal.ofReal (fittedRisk ν J) ≤
        extendedPredictionRisk ν f + ENNReal.ofReal (a^2*η/3)

/-- P023-T4; p. 7 (PDF p. 7) and p. 10 (PDF p. 10).
For every positive amplitude and positive width at most one, the uniform-margin
clipped linear family has a continuous Lipschitz conditional mean whose centered
part is odd, and zero cutoff jump. Its RD
means, residuals, degree-one and degree-seven coefficients and numerical outcome
bounds are as displayed. At every degree the fitted risk lies between the noise
risk and that risk plus a squared amplitude times width divided by three; no
measurable predictor, including one with infinite risk, improves it by more.
For fixed degree the coefficient tends to twice the amplitude as width vanishes,
while the risk bound vanishes. Every family member has the stated fixed-degree
sampling limit; the numerical degree-one and degree-seven limits remain separated
from shrinking-window RD under IID sampling and the stated bandwidth limits alone. -/
def T4WholeStatement : Prop :=
  SigmoidPopulation ∧ SigmoidFit ∧ WholeSigmoidSampling ∧ WholeSigmoidFamily ∧
  UniformSymmetry ∧ WholeUniformProjections ∧
  residualVariance uniformMargins 1 = 1/16 ∧
  residualVariance uniformMargins 7 = 1225/65536 ∧ WholeSigmoidAllRisks ∧
  (∀ J, 1 ≤ J →
    let ν := witnessLaw uniformMargins (sigmoid (1/20) (1/10000))
    (fittedRisk ν J - 1/100) / fittedRisk ν J ≤ 1/120000) ∧
  (∀ a : ℝ, Tendsto (fun η : ℝ => a^2*η/3)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
  (∀ (a : ℝ) (J : ℕ), ∃ c : Fin (J+2) → ℝ,
    ∀ x : ℝ, predict (polynomialDesign J (fun x : ℝ => x) party) c x =
      1/2 + a*(2*party x-1))

/-- T5's comparison includes every measurable predictor, with infinite risk
permitted. The constant predictor's risk on the left is also an extended integral. -/
def WholeClusteredAllRisks : Prop :=
  ∀ d : ℝ, 0 < d → d ≤ 1/2 →
    let ν := witnessLaw (clusteredMargins d) (clusterSmooth d)
    ∀ f : ℝ → ℝ, Measurable f →
      ENNReal.ofReal (1/100) ≤ extendedPredictionRisk ν f ∧
      extendedPredictionRisk ν (fun _ => 1/2) ≤
        extendedPredictionRisk ν f + ENNReal.ofReal ((d/2)^2) ∧
      (∀ J, 1 ≤ J → ENNReal.ofReal (fittedRisk ν J) ≤
        extendedPredictionRisk ν f + ENNReal.ofReal ((d/2)^2))

/-- Every polynomial candidate in the clustered fitted-risk infimum has
integrable squared loss. Thus no undefined Bochner integral enters that infimum. -/
def WholeClusteredLossIntegrable : Prop :=
  ∀ d : ℝ, 0 < d → d ≤ 1/2 → ∀ J (c : Fin (J+2) → ℝ),
    Integrable (fun z : ℝ × ℝ =>
      (z.2-predict (polynomialDesign J (fun x : ℝ => x) party) c z.1)^2)
      (witnessLaw (clusteredMargins d) (clusterSmooth d))

/-- P023-T5; p. 10 (PDF p. 10); Proposition 2 and its Remark, p. 7 (PDF p. 7).
The clustered continuous positive-density family has continuous Lipschitz
conditional means with odd centered parts and zero cutoff jumps, all the displayed
moments and RD values, and a coefficient tending to minus one while the uniform
zero-polynomial error tends to zero.
At the numerical witness the coefficient, outcome bounds and error bound are
as displayed. The constant and fitted predictors can be improved by at most
the squared half-width by any measurable predictor, even one with infinite risk.
Consequently no coefficient-error constant can be uniform over the stated laws. -/
def T5WholeStatement : Prop :=
  ClusteredPopulation ∧ ClusteredFit ∧ WholeClusteredAllRisks ∧ WholeClusteredLossIntegrable ∧
  (∀ (d : ℝ), 0 < d → d ≤ 1/2 → ∀ J : ℕ,
    (0 : Polynomial ℝ).natDegree ≤ J ∧ ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |clusterSmooth d x - (0 : Polynomial ℝ).eval x| ≤ d/2) ∧
  (∀ d : ℝ, 0 < d → d ≤ 1/2 →
    0 < (1-d^4)*(d/2)^2/6+d^4/12 ∧
    populationCoefficient (clusteredMargins d) 1 (fun x => 1/2+clusterSmooth d x) =
      -((1-d^4)*(d/2)^2/6+2*d^4*(d/2)^3) /
        ((1-d^4)*(d/2)^2/6+d^4/12)) ∧
  (∀ J : ℕ, (0 : Polynomial ℝ).natDegree ≤ J ∧
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |clusterSmooth (1/1000) x - (0 : Polynomial ℝ).eval x| ≤ 1/2000) ∧
  Tendsto (fun d : ℝ => d/2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/-- Equality for the printed design under the exact existence conditions for
the two RD means; no strict-interior witness or nonempty nuisance bin is needed. -/
def WholePositiveCountEquality : Prop :=
  ∀ {ι : Type} [Fintype ι] (k : ℝ), 0 < k ∧ k < 1 →
    ∀ (x d y : ι → ℝ), TwoParty x d →
    (0 < ∑ i ∈ close k x, d i) → (0 < ∑ i ∈ close k x, (1-d i)) →
    ∀ c : Fin (binCount k+2) → ℝ, IsOLS (coarsenedDesign k x d) y c →
      c ⟨1, by omega⟩ = rd k x d y

def wholeEndpointMargins : Fin 2 → ℝ := ![-1/4, 1/2]
def wholeEndpointParties : Fin 2 → ℝ := ![0, 1]
def wholeEndpointOutcomes : Fin 2 → ℝ := ![0, 1]

/-- The printed claim is false: P023-T11; p. 6 (PDF p. 6); Conditions 1–3
and the necessity remark, p. 5 (PDF p. 5); Appendix A, p. 9 (PDF p. 9).
The Proposition 1 equality under Conditions 1–3 is retained, and holds whenever
the close winner and loser counts are positive. The auxiliary assertion that
Condition 1 is necessary for an RD estimate is false: at bandwidth one half,
the two margins minus one quarter and one half, indicators zero and one, and
outcomes zero and one have both counts equal to one and RD equal to one, but
there is no strictly interior positive margin. -/
def T11WholeStatement : Prop :=
  PropositionOne ∧ WholePositiveCountEquality ∧
  TwoParty wholeEndpointMargins wholeEndpointParties ∧
  ¬ Condition1 (1/2) wholeEndpointMargins ∧
  close (1/2) wholeEndpointMargins = Finset.univ ∧
  (∑ i ∈ close (1/2) wholeEndpointMargins, wholeEndpointParties i) = 1 ∧
  (∑ i ∈ close (1/2) wholeEndpointMargins, (1-wholeEndpointParties i)) = 1 ∧
  rd (1/2) wholeEndpointMargins wholeEndpointParties wholeEndpointOutcomes = 1

/-- P023-T8; p. 7 (PDF p. 7); Appendix B, p. 10 (PDF p. 10).
Under the stated finite-second-moment IID, local density domination, Lipschitz
mean, bounded local conditional variance and shrinking-bandwidth assumptions,
all the positive-definite moment, residual-variance, zero-constant polynomial
approximation, population bias, fixed-degree, RD and growing-degree conclusions
(a)–(g) hold, including existence of a slow degree schedule. The smallest moment
eigenvalues and residual normalizations are positive. No separate singular-design
or empty-window probability assumptions are required. -/
def T8WholeStatement : Prop :=
    ∀ {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure (ℝ × ℝ)) (sample : ℕ → Ω → ℝ × ℝ)
    (α β : ℝ) (h : ℝ → ℝ) (c δ L σ2 : ℝ)
    (hr : RepairedRegularity ν α β h c δ L σ2) (hiid : IIDSample P ν sample)
    (k : ℕ → ℝ) (hkpos : ∀ N, 0 < k N)
    (hk0 : Tendsto k atTop (nhds 0))
    (hnk : Tendsto (fun N : ℕ => (N : ℝ) * k N) atTop atTop),
    let μ := marginLaw ν
    let m := fun x => α + β*party x + h x
    (∀ J, 1 ≤ J → MomentPositiveDefinite μ J ∧
      0 < smallestMomentEigenvalue μ J ∧
      IsProjection μ J (projection μ J) ∧ 0 < residualVariance μ J ∧
      residualVariance μ J ≥ c*δ/(4*((J:ℝ)+1))) ∧
    (∀ J, 1 ≤ J → ∃ p : Polynomial ℝ, p.natDegree ≤ J ∧ p.eval 0 = 0 ∧
      supError h p ≤ 4*jacksonK*L/((J:ℝ)+1)) ∧
    (∀ J, 1 ≤ J → |populationCoefficient μ J m - β| ≤
      8*jacksonK*L / Real.sqrt (c*δ*((J:ℝ)+1))) ∧
    Tendsto (fun J => populationCoefficient μ J m) atTop (nhds β) ∧
    (∀ J, 1 ≤ J → ConvergesInProbability P (fun N => samplePolynomial sample N J) (populationCoefficient μ J m)) ∧
    (∀ k', 0 < k' → k' ≤ δ → |populationRD μ m k' - β| ≤ 2*L*k') ∧
    ConvergesInProbability P (sampleRD sample k) β ∧
    (∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, 1 ≤ J →
      ConvergesInProbability P (fun N ω => samplePolynomial sample N J ω - sampleRD sample k N ω)
        (populationCoefficient μ J m - β) ∧ |populationCoefficient μ J m - β| < ε) ∧
    (∀ degrees : ℕ → ℕ, Tendsto degrees atTop atTop →
      Tendsto (fun N => ((degrees N : ℝ)+2)^2 /
        ((N:ℝ) * (smallestMomentEigenvalue μ (degrees N))^3)) atTop (nhds 0) →
      ConvergesInProbability P (fun N ω => samplePolynomial sample N (degrees N) ω -
        populationCoefficient μ (degrees N) m) 0 ∧
      ConvergesInProbability P (fun N ω => samplePolynomial sample N (degrees N) ω - sampleRD sample k N ω) 0) ∧
    (∃ degrees : ℕ → ℕ, (∀ N, 1 ≤ degrees N) ∧ Tendsto degrees atTop atTop ∧
      Tendsto (fun N => ((degrees N : ℝ)+2)^2 /
        ((N:ℝ) * (smallestMomentEigenvalue μ (degrees N))^3)) atTop (nhds 0))

end
end SAP.P023
