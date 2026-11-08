import SAP.P042.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P042

noncomputable section
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

/-- Exact fixed-effects calculation on the two deposited recorded-call rows. -/
def RoboFixedExact : Prop :=
  roboVariances 0 = 3031081/9765625 ∧
  roboVariances 1 = 1672073881/2500000000 ∧
  totalWeight roboVariances = 23906548994140625/5068191371295361 ∧
  roboFixedMean = 114191974724271/61200765425000 ∧
  roboFixedVariance = 5068191371295361/23906548994140625

/-- Exact DerSimonian–Laird calculation on the same inputs. -/
def RoboRandomExact : Prop :=
  roboQ = (roboEffects 0-roboEffects 1)^2/(roboVariances 0+roboVariances 1) ∧
  roboQ = 5357654416/2448030617 ∧ 1 < roboQ ∧
  roboC = 2/(roboVariances 0+roboVariances 1) ∧
  roboC = 5000000000/2448030617 ∧
  roboTauSq = 2909623799/5000000000 ∧
  precisionWeight roboRandomVariances 0 = 5000000000/4461537271 ∧
  precisionWeight roboRandomVariances 1 = 5000000000/6253771561 ∧
  roboRandomMean = 12592252377/7319600000 ∧
  roboRandomVariance = 27901434903721350031/53576544160000000000

/-- The alternative point estimate and endpoints lie in the printed rounding bins. -/
def RoboRandomRounding : Prop :=
  ((17195:ℝ)/10000 ≤ roboRandomMean ∧ roboRandomMean < 17205/10000) ∧
  (∀ z : ℝ, 19599/10000 ≤ z → z ≤ 49/25 →
    3055/10000 ≤ roboRandomMean-z*Real.sqrt roboRandomVariance ∧
    roboRandomMean-z*Real.sqrt roboRandomVariance < 3065/10000 ∧
    31345/10000 ≤ roboRandomMean+z*Real.sqrt roboRandomVariance ∧
    roboRandomMean+z*Real.sqrt roboRandomVariance < 31355/10000)

def T3Statement : Prop :=
  RoboFixedExact ∧
  ((18655:ℝ)/10000 < roboFixedMean ∧ roboFixedMean < 18665/10000 ∧
    (17205:ℝ)/10000 < roboFixedMean) ∧
  (∀ z : ℝ, 19599/10000 ≤ z → z ≤ 49/25 →
    9625/10000 < roboFixedMean-z*Real.sqrt roboFixedVariance ∧
    (3065:ℝ)/10000 < 9625/10000 ∧
    roboFixedMean+z*Real.sqrt roboFixedVariance < 27685/10000 ∧
    (27685:ℝ)/10000 < 31345/10000) ∧
  RoboRandomExact ∧ RoboRandomRounding

/-- Under the stipulated variances and zero covariance, the diagonal value
is also the actual variance of the precision-weighted random average. -/
def RoboStochasticVariance : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Fin 2 → Ω → ℝ), (∀ j, MemLp (D j) 2 μ) →
    (∀ j, variance (D j) μ = roboVariances j) → covariance (D 0) (D 1) μ = 0 →
    variance (pooled (normalizedWeight roboVariances) D) μ = roboFixedVariance

def T4Statement : Prop :=
  RoboFixedExact ∧
  ((18655:ℝ)/10000 ≤ roboFixedMean ∧ roboFixedMean < 18665/10000) ∧
  (∀ z : ℝ, 19599/10000 ≤ z → z ≤ 49/25 →
    9625/10000 ≤ roboFixedMean-z*Real.sqrt roboFixedVariance ∧
    roboFixedMean-z*Real.sqrt roboFixedVariance < 9635/10000 ∧
    27675/10000 ≤ roboFixedMean+z*Real.sqrt roboFixedVariance ∧
    roboFixedMean+z*Real.sqrt roboFixedVariance < 27685/10000) ∧
  (∀ z : ℝ, 0 ≤ z → z ≤ 49/25 →
    0 < roboFixedMean-z*Real.sqrt roboFixedVariance) ∧
  RoboStochasticVariance ∧ RoboRandomExact ∧ RoboRandomRounding

end
end SAP.P042
