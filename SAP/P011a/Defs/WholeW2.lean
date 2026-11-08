import Mathlib
import SAP.P011a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section
set_option linter.unusedVariables false

/-- Assumption 2 on the observed rows. Positive sample sizes and their growth are fields of
`Family`; no monotonicity or embeddings of the observed graphs are assumed. -/
def RowScaling (F : Family) (c1 c2 c3 c4 : ℝ) : Prop :=
  0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧ 0 < c4 ∧
  (∀ k, Dependency (F.model k)) ∧
  (∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i,
    |weighted (F.model k) y i - beta (F.model k)| ≤ c1) ∧
  (∀ k i, (degree (F.model k).G i : ℝ) ≤ c2) ∧
  Tendsto (scaledTrue F) atTop (𝓝 c3) ∧ (∀ k i, |(F.model k).theta i| < c4)

/-- The OracleConvergence component with the row version of Assumption 2. -/
def OracleConvergenceWhole : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : RowScaling F c1 c2 c3 c4),
  InProbability F
      (fun k y => (F.size k : ℝ) * V1 (F.model k).G (weighted (F.model k) y))
      (fun k => (F.size k : ℝ) * var (F.model k) (betaHat (F.model k)) + meanBias (F.model k))


/-- The OracleExpectation component with the row version of Assumption 2. -/
def OracleExpectationWhole : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : RowScaling F c1 c2 c3 c4) (k : ℕ),
  |expectation (F.model k) (scaledOracle F k) - scaledTrue F k - meanBias (F.model k)|
      ≤ 3*(1+c2)^2*c1^2/(F.size k : ℝ)


/-- The SampleVarianceConvergence component with the row version of Assumption 2. -/
def SampleVarianceConvergenceWhole : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : RowScaling F c1 c2 c3 c4),
  InProbability F (fun k y => sampleVariance (weighted (F.model k) y))
      (fun k => meanVariance (F.model k) + meanSpread (F.model k))


/-- The OracleMeanConditions component with the row version of Assumption 2. -/
def OracleMeanConditionsWhole : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : RowScaling F c1 c2 c3 c4),
  (InProbability F (scaledOracle F) (scaledTrue F) ↔
      Tendsto (fun k => meanBias (F.model k)) atTop (𝓝 0)) ∧
    (Conservative F (fun k y => V1 (F.model k).G (weighted (F.model k) y)) ↔
      0 ≤ Filter.liminf (fun k => meanBias (F.model k)) atTop) ∧
    ((∀ k i, delta (F.model k) i = 0) →
      InProbability F (scaledOracle F) (scaledTrue F)) ∧
    ((∀ k, PSD (oracleMatrix (F.model k).G)) →
      Conservative F (fun k y => V1 (F.model k).G (weighted (F.model k) y)))


/-- The ResidualRootRate component with the row version of Assumption 2. -/
def ResidualRootRateWhole : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ) (h : RowScaling F c1 c2 c3 c4)
    (p : ℕ) (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (γ : Fin p → ℝ)
    (γhat : ∀ k, (Fin (F.size k) → ℝ) → (Fin p → ℝ))
    (hmeas : ∀ k, AEMeasurable (γhat k) (F.model k).law)
    (hmean : ∀ k, MeanModel (F.model k) (D k) γ)
    (hbound : ∃ B : ℝ, ∀ k i, l2 (D k i) ≤ B)
    (hrate : Tight F (fun k y => Real.sqrt (F.size k : ℝ)*l2 (γhat k y-γ)))
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)) (hv : Valid F)
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => VResidual B (fittedResidual (F.model k) (D k) (γhat k) y)) (A k y)),
  (∀ k i, expectation (F.model k) (fun y => trueResidual (F.model k) (D k) γ y i) = 0) ∧
    (∀ k i j, expectation (F.model k) (fun y =>
      trueResidual (F.model k) (D k) γ y i*trueResidual (F.model k) (D k) γ y j) =
      covariance (F.model k) i j) ∧
    Tight F (fun k y => Real.sqrt (F.size k : ℝ)*maxAbs
      (fittedResidual (F.model k) (D k) (γhat k) y-trueResidual (F.model k) (D k) γ y)) ∧
    Tight F (fun k y => l2
      (fittedResidual (F.model k) (D k) (γhat k) y-trueResidual (F.model k) (D k) γ y)) ∧
    Tight F (fun k y => l2 (trueResidual (F.model k) (D k) γ y)/Real.sqrt (F.size k : ℝ)) ∧
    InProbability F
      (fun k y => (F.size k : ℝ)*VResidual (F.model k).G
        (fittedResidual (F.model k) (D k) (γhat k) y)) (scaledTrue F) ∧
    Conservative F (fun k y => VResidual (A k y)
      (fittedResidual (F.model k) (D k) (γhat k) y))


/-- The ResidualPrediction component with the row version of Assumption 2. -/
def ResidualPredictionWhole : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : RowScaling F c1 c2 c3 c4) (p : ℕ)
    (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (γ : Fin p → ℝ)
    (γhat : ∀ k, (Fin (F.size k) → ℝ) → (Fin p → ℝ))
    (hmeas : ∀ k, AEMeasurable (γhat k) (F.model k).law)
    (hmean : ∀ k, MeanModel (F.model k) (D k) γ)
    (hz : ∃ B : ℝ, ∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i, |trueResidual (F.model k) (D k) γ y i| ≤ B)
    (herr : InProbability F (fun k y => l2
      (fittedResidual (F.model k) (D k) (γhat k) y-trueResidual (F.model k) (D k) γ y)
        /Real.sqrt (F.size k : ℝ)) (fun _ => 0))
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)) (hv : Valid F)
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => VResidual B (fittedResidual (F.model k) (D k) (γhat k) y)) (A k y)),
  InProbability F (fun k y => (F.size k : ℝ)*VResidual (F.model k).G
      (fittedResidual (F.model k) (D k) (γhat k) y)) (scaledTrue F) ∧
    Conservative F (fun k y => VResidual (A k y) (fittedResidual (F.model k) (D k) (γhat k) y))


/-- The ResidualMisspecification component with the row version of Assumption 2. -/
def ResidualMisspecificationWhole : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : RowScaling F c1 c2 c3 c4) (p : ℕ)
    (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (γstar : Fin p → ℝ)
    (γhat : ∀ k, (Fin (F.size k) → ℝ) → (Fin p → ℝ))
    (hmeas : ∀ k, AEMeasurable (γhat k) (F.model k).law)
    (hz : ∃ B : ℝ, ∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i, |trueResidual (F.model k) (D k) γstar y i| ≤ B)
    (herr : InProbability F (fun k y => l2
      (fittedResidual (F.model k) (D k) (γhat k) y-trueResidual (F.model k) (D k) γstar y)
        /Real.sqrt (F.size k : ℝ)) (fun _ => 0)),
  InProbability F
      (fun k y => (F.size k : ℝ)*VResidual (F.model k).G
        (fittedResidual (F.model k) (D k) (γhat k) y)-scaledTrue F k)
      (fun k => quadratic (oracleMatrix (F.model k).G)
        (fun i => expectation (F.model k) (fun y => weighted (F.model k) y i)
          -(F.model k).theta i*(D k *ᵥ γstar) i) / (F.size k : ℝ))


/-- Repeated regressor (1,0,-1,0) in the unstable OLS example. -/
def unstableW (m : ℕ) (i : Fin (4*m)) : ℝ :=
  (![1,0,-1,0] : Fin 4 → ℝ) (localIndex (by decide) i)

def unstableDesign (m : ℕ) : Matrix (Fin (4*m)) (Fin 2) ℝ :=
  fun i j => if j = 0 then 1 else unstableW m i

def unstableResidualStatistic (m : ℕ) (y : Fin (4*m) → ℝ) : ℝ :=
  (4*m : ℝ)*VResidual (unstableModel m).G
    (fittedResidual (unstableModel m) (unstableDesign m) (ols (unstableDesign m)) y)

/-- The finite assertions of part (d), including the LUE weights and the samplewise formula. -/
def ResidualFailureFiniteWhole : Prop :=
  (∀ m : ℕ, 0 < m →
    (∀ i, (unstableModel m).theta i = 2*unstableW m i) ∧
    (∀ y, ols (unstableDesign m) y 0 = average y ∧
      ols (unstableDesign m) y 1 = (2/(4*m : ℝ))*∑ i, unstableW m i*y i ∧
      betaHat (unstableModel m) y = ols (unstableDesign m) y 1 ∧
      unstableResidualStatistic m y = (4/(4*m : ℝ))*
        ∑ i with unstableW m i ≠ 0,
          (y i-average y-unstableW m i*ols (unstableDesign m) y 1)^2) ∧
    (4*m : ℝ)*var (unstableModel m) (betaHat (unstableModel m)) = 2 ∧
    beta (unstableModel m) = 0 ∧
    (∀ i, expectation (unstableModel m) (fun y => y i) = 0) ∧
    (∀ᵐ y ∂(unstableModel m).law, ∀ i, |weighted (unstableModel m) y i| ≤ 2)) ∧
  expectation (unstableModel 1) (unstableResidualStatistic 1) = 17/4 ∧
  expectation (unstableModel 2) (unstableResidualStatistic 2) = 73/8

/-- P011-T9; replaces centring in (3.1) and (3.5), pp. 2242 and 2244 (PDF pp. 5 and 7),
for the regression example, pp. 2240–2241 (PDF pp. 3–4); corrected statement, not printed.
Under Assumption 2 and the correct bounded finite-dimensional mean model, root-n coefficient
estimation gives zero-mean residuals with covariance C, the three stated stochastic norm rates,
oracle consistency and maximal-estimator conservativeness. The finite symmetric quadratic
perturbation bound holds. Bounded residuals and prediction error o_p(sqrt(n)) also suffice;
a misspecified model adds the quadratic mean term. The independent-sign OLS example satisfies
Assumption 2 with exact scaled variance 2, but has intercept variance n/2+1/(2n), residual
expectation n+2-7/n (17/4 and 73/8 at n=4 and 8) and fails consistency, with the explicit
slope weights and samplewise residual sum. No observed-graph nesting is required. -/
def T9WholeStatement : Prop :=
  ResidualRootRateWhole ∧ ResidualPredictionWhole ∧ ResidualMisspecificationWhole ∧
  ResidualFailure ∧ ResidualPerturbation ∧ ResidualFailureFiniteWhole

/-- A variance rule can inspect exactly the observed outcomes, degree caps, weights and
recruitment graph. Its arguments contain neither the unknown law nor its variance. -/
abbrev ObservedVarianceRule := ∀ n : ℕ,
  (Fin n → ℝ) → (Fin n → ℕ) → (Fin n → ℝ) → Graph n → ℝ

def UniversalRuleConsistency (V : ObservedVarianceRule) : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), RowScaling F c1 c2 c3 c4 →
    InProbability F
      (fun k y => (F.size k : ℝ)*V (F.size k) y (F.model k).d
        (F.model k).theta (F.model k).R) (scaledTrue F)

/-- Impossibility on the displayed common finite supports, with no Borel restriction on T. -/
def ArbitraryStatisticImpossibility : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b →
  (¬ ∃ T : ∀ k, (Fin (k+1) → ℝ) → ℝ,
    (∀ s : ℕ → Bool, InProbability (fixedMeanFamily a b s) T (fun _ => b^2)) ∧
    InProbability (mixtureFamily a b) T (fun _ => a^2+b^2)) ∧
  (∀ T : ∀ k, (Fin (k+1) → ℝ) → ℝ,
    (∀ ε : ℝ, 0 < ε → Tendsto (fun k => probability (mixtureModel a b (k+1))
      {y | a^2+b^2-T k y > ε}) atTop (𝓝 0)) →
    ¬ ∀ s : ℕ → Bool, InProbability (fixedMeanFamily a b s) T (fun _ => b^2))

/-- P011-T10; bears on the abstract, p. 2238 (PDF p. 1), and Proposition 1, p. 2242
(PDF p. 5); corrected statement, not printed.
For every a,b>0 the independent fixed-sign-mean and random-sign-mixture models satisfy all
scaling assumptions, have the stated finite means and scaled variances b² and a²+b², and
obey the exact finite mixture identity. No statistic is scaled consistent in all these
models, and mixture conservativeness prevents consistency in every fixed mean pattern.
Consequently no law-independent observed-data variance rule is universally scaled consistent.
The zero statistic is unscaled consistent under Assumption 2. Extra sampling-design information
can permit unbiased variance estimation: independent half-probability inclusion of population
values 1 gives betaHat=average(2I) and the unbiased estimator average(2I)/n. -/
def T10WholeStatement : Prop :=
  UniversalImpossibility ∧ MixtureMoments ∧ ArbitraryStatisticImpossibility ∧
  (¬ ∃ V : ObservedVarianceRule, UniversalRuleConsistency V) ∧
  (∀ (F : Family) (c1 c2 c3 c4 : ℝ), RowScaling F c1 c2 c3 c4 →
    InProbability F (fun _ _ => 0) (fun k => var (F.model k) (betaHat (F.model k)))) ∧
  (∀ n : ℕ, 0 < n →
    let m := fixedMeanModel 1 1 (fun _ => true) n
    m.law = uniformLaw (fun u : Fin n → Bool => fun i =>
      2*(if u i then (1 : ℝ) else 0)) ∧
    var m (betaHat m) = 1/(n : ℝ) ∧
    expectation m (fun y => betaHat m y/(n : ℝ)) = var m (betaHat m))

/-- P011-T1; Proposition 1, p. 2242 (PDF p. 5); Corollary 1, p. 2245 (PDF p. 8);
sentence after Assumption 3, p. 2246 (PDF p. 9); Corollary 3, p. 2248 (PDF p. 11).
The stated independent-sign four-cycle constructions satisfy Assumptions 1–3 and have a
singleton compatible set, exact scaled variance 4 and mean bias -9/4, all stated finite
moments, estimator limit 7/4, failure probabilities tending to one, and the exact all-alpha
undercoverage formula. At alpha=0.05 its coverage limit is between 0.8045 and 0.8055.
The a=3 construction has limit -5 and the stated positive-probability negative estimate.
These counterexample facts refute the quoted printed assertions. -/
def T1WholeStatement : Prop :=
  T1Statement ∧
  (8045/10000 < 2*Phi (normalQuantile (1/20)*Real.sqrt (7/16))-1 ∧
    2*Phi (normalQuantile (1/20)*Real.sqrt (7/16))-1 < 8055/10000) ∧
  (∀ a : ℝ, ∀ k i, covariance ((cycleFamily a).model k) i i = 2) ∧
  Tendsto (fun k => probability ((cycleFamily (3/2)).model k)
    {y | 0 < V1 ((cycleFamily (3/2)).model k).G
      (weighted ((cycleFamily (3/2)).model k) y)}) atTop (𝓝 1)

/-- Local block of an arbitrary path-block data vector. -/
def pathBlockVector (K : ℕ) (y : Fin (3*K) → ℝ) (b : Fin K) : Fin 3 → ℝ :=
  fun r => y ⟨3*b.val+r.val, by have := b.isLt; have := r.isLt; omega⟩

def pathS (y : Fin 3 → ℝ) : ℝ := ∑ i, y i

def pathL (y : Fin 3 → ℝ) : ℝ := ∑ i, ∑ j, oracleMatrix pathGraph i j*y j

def pathQ (y : Fin 3 → ℝ) : ℝ := quadratic (oracleMatrix pathGraph) y

/-- The missing samplewise and all-block-count facts of the path example. -/
def PathFiniteWhole : Prop :=
  (∀ t : ℝ, (t = 1 ∨ t = 2) → ∀ K : ℕ, 0 < K →
    (∀ᵐ y ∂(pathModel t K).law, ∀ i, |y i| ≤ 27/5) ∧
    (∀ i, expectation (pathModel t K) (fun y => y i) =
      (![t,-2*t,t] : Fin 3 → ℝ) (localIndex (by decide) i)) ∧
    (∀ i j, covariance (pathModel t K) i j =
      if blockIndex (by decide) i = blockIndex (by decide) j then
        (![![1,3/5,0],![3/5,1,4/5],![0,4/5,1]] : Matrix (Fin 3) (Fin 3) ℝ)
          (localIndex (by decide) i) (localIndex (by decide) j)
      else 0) ∧
    (∀ y, (3*K : ℝ)*V1 (pathModel t K).G y =
      (∑ b, pathQ (pathBlockVector K y b))/(3*K : ℝ) -
      (2/3)*average y*((∑ b, pathL (pathBlockVector K y b))/(K : ℝ)) +
      (7/3)*(average y)^2)) ∧
  (∀ t : ℝ, ∀ u v : Bool,
    pathS (pathBlock t (sign u) (sign v)) = (8/5)*sign u+(9/5)*sign v ∧
    pathL (pathBlock t (sign u) (sign v)) = -2*t+(19/5)*sign u+(22/5)*sign v ∧
    pathQ (pathBlock t (sign u) (sign v)) =
      29/5-2*t^2-2*t*(sign u+sign v)+(94/25)*sign u*sign v)

/-- P011-T2; Proposition 1, p. 2242 (PDF p. 5); Corollary 1, p. 2245 (PDF p. 8);
sentence after Assumption 3, p. 2246 (PDF p. 9); Corollary 3, p. 2248 (PDF p. 11).
Both independent-sign path-block laws satisfy Assumptions 1–3, the bound 27/5, the displayed
mean/covariance matrices, singleton compatibility, all S/L/Q polynomials and block moments,
the samplewise centering formula and the exact finite oracle expectation. For t=1 the
estimator tends to 19/15 instead of 29/15 and its all-alpha coverage is strictly deficient;
at alpha=0.05 its coverage limit is between 0.8873623230 and 0.8873623231. For t=2 it
tends to -11/15, is negative with probability tending to one and has zero clipped coverage.
Both are correctly specified OLS intercept examples. These facts refute the printed assertions. -/
def T2WholeStatement : Prop :=
  T2Statement ∧ PathFiniteWhole ∧
  (8873623230/10000000000 < 2*Phi (normalQuantile (1/20)*Real.sqrt (19/29))-1 ∧
    2*Phi (normalQuantile (1/20)*Real.sqrt (19/29))-1 < 8873623231/10000000000)

/-- P011-T3; p. 2242 (PDF p. 5), replacing the proof step on p. 2243 (PDF p. 6).
Under Assumption 2, without induced nesting of observed graphs, the scaled oracle converges
to the scaled true variance plus the mean quadratic b_n. Its expectation remainder is bounded
by 3(1+c2)²c1²/n and the sample variance converges to average marginal variance plus mean
spread. Consistency is equivalent to b_n tending to zero; common means suffice.
Conservativeness is equivalent to liminf b_n≥0; positive semidefiniteness suffices.
The mean deviations sum to zero and |b_n|≤(1+c2)c1². The matrix I+A is positive semidefinite
exactly for disjoint unions of cliques, with the stated clique-square variance formula. -/
def T3WholeStatement : Prop :=
  OracleConvergenceWhole ∧ OracleExpectationWhole ∧ SampleVarianceConvergenceWhole ∧
  OracleMeanConditionsWhole ∧ CliqueCharacterization ∧
  (∀ (F : Family) (c1 c2 c3 c4 : ℝ), RowScaling F c1 c2 c3 c4 → ∀ k,
    (∑ i, delta (F.model k) i) = 0 ∧ |meanBias (F.model k)| ≤ (1+c2)*c1^2)

end
end SAP.P011a
