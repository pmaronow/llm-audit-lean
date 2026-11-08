import SAP.P037a.Defs.Part7

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P037a

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology

def individualUnbiased : Prop :=
  ∀ {Ω : Type} [Fintype Ω]
      (d : Design Ω) (I : Ω → ℝ) (pi y g : ℝ)
      (hpi : pi ≠ 0) (hI : mean d I = pi),
    mean d (fun w => contribution (I w) pi y g) = y

def individualBound : Prop :=
  ∀ (I pi y g K eta : ℝ)
      (hI : I=0 ∨ I=1) (heta : 0 < eta) (hpi : eta ≤ pi)
      (hy : |y| ≤ K) (hg : |g| ≤ K),
    |contribution I pi y g| ≤ K + 2*K/eta

def blockUnbiased : Prop :=
  ∀ {B : ℕ} (r : RetainedRow B) (b : Fin B),
    mean (r.law b) (blockTotal r b) = ∑ i, r.y b i

def oracleUnbiasedVariance : Prop :=
  ∀ {B : ℕ} (r : RetainedRow B) (hSize : 0 < populationSize r),
    mean (independentDesign r.law) (oracleMean r) = potentialMean r ∧
      variance (independentDesign r.law) (oracleMean r) =
        totalBlockVariance r/(populationSize r:ℝ)^2

def oracleFiniteBounds : Prop :=
  ∀ (r : ∀ B, RetainedRow (B+1))
      (m : ℕ) (c eta K : ℝ) (h : BlockBounds r m c eta K)
      (B : ℕ) (eps : ℝ) (heps : 0 < eps),
    (∀ b z, |blockTotal (r B) b z| ≤ m*(K+2*K/eta)) ∧
      (∀ b, variance ((r B).law b) (blockTotal (r B) b) ≤
        (m:ℝ)^2*(K+2*K/eta)^2) ∧
      totalBlockVariance (r B)/(populationSize (r B):ℝ)^2 ≤
        (m:ℝ)^2*(K+2*K/eta)^2/(c^2*(B+1)) ∧
      rowProbability (r B) (fun w => eps < |oracleMean (r B) w-potentialMean (r B)|) ≤
        (m:ℝ)^2*(K+2*K/eta)^2/(c^2*(B+1)*eps^2)

def oracleConsistency : Prop :=
  ∀ (r : ∀ B, RetainedRow (B+1))
      (m : ℕ) (c eta K : ℝ) (h : BlockBounds r m c eta K)
      (eps : ℝ) (heps : 0 < eps),
    Filter.Tendsto (fun B => rowProbability (r B)
        (fun w => eps < |oracleMean (r B) w-potentialMean (r B)|))
        Filter.atTop (nhds 0)

def oracleNormality : Prop :=
  ∀ (r : ∀ B, RetainedRow (B+1))
      (m : ℕ) (c eta K sigmaSquared : ℝ)
      (h : BlockBounds r m c eta K) (hs : 0 < sigmaSquared)
      (hv : ∀ B, sigmaSquared*(B+1) ≤ totalBlockVariance (r B)),
    (∀ (B : ℕ) (eps : ℝ), 0 < eps → 2*m*(K+2*K/eta) < eps*Real.sqrt (sigmaSquared*(B+1)) →
        (∑ b, mean ((r B).law b) (fun z =>
          let U := blockTotal (r B) b z - mean ((r B).law b) (blockTotal (r B) b)
          U^2 * if eps*Real.sqrt (totalBlockVariance (r B)) < |U| then 1 else 0)) = 0) ∧
      (∀ x : ℝ, Filter.Tendsto (fun B => rowProbability (r B) (fun w =>
        (populationSize (r B):ℝ)*(oracleMean (r B) w-potentialMean (r B)) /
          Real.sqrt (totalBlockVariance (r B)) ≤ x)) Filter.atTop
        (nhds ((ProbabilityTheory.gaussianReal 0 1 (Set.Iic x)).toReal)))

def centeredBlockBound : Prop :=
  ∀ {B : ℕ} (r : RetainedRow B)
      (m : ℕ) (eta K : ℝ) (heta : 0 < eta) (hK : 0 ≤ K)
      (hn : ∀ b, r.students b ≤ m)
      (hb : ∀ b i, eta ≤ r.pi b i ∧ |r.y b i| ≤ K ∧ |r.g b i| ≤ K),
    ∀ b z, |blockTotal r b z-mean (r.law b) (blockTotal r b)| ≤
        2*m*(K+2*K/eta)

def blockIndependence : Prop :=
  ∀ {B : ℕ} (r : RetainedRow B) (f : (b : Fin B) → ℝ → ℝ),
  mean (independentDesign r.law) (fun w => ∏ b, f b (blockTotal r b (w b))) =
    ∏ b, mean (r.law b) (fun z => f b (blockTotal r b z))

def centeredTotalIdentity : Prop :=
  ∀ {B : ℕ} (r : RetainedRow B), 0 < populationSize r →
  ∀ w : RowAssignment r,
    (∑ b, (blockTotal r b (w b) - mean (r.law b) (blockTotal r b))) =
      (populationSize r : ℝ) * (oracleMean r w - potentialMean r)

end SAP.P037a
