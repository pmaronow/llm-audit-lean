import Mathlib
import SAP.P033.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace SAP.P033

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology ContDiff

noncomputable section

/-- The population score distribution, uniform on the open interval (-1,1).
The open or closed endpoint convention gives the same distribution. -/
def wholeScoreLaw : Measure ℝ := ProbabilityTheory.cond volume (Ioo (-1) 1)

/-- Eight independent unit Gaussian errors, indexed by side and distance. -/
def wholeErrorLaw : Measure ((Fin 2 × Fin 4) → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

/-- Independent uniform scores and independent Gaussian errors, with the two
vectors independent of each other. Potential outcomes below share their unit's error. -/
def wholePopulationLaw : Measure
    (((Fin 2 × Fin 4) → ℝ) × ((Fin 2 × Fin 4) → ℝ)) :=
  (Measure.pi (fun _ : Fin 2 × Fin 4 => wholeScoreLaw)).prod wholeErrorLaw

def wholeSharpTreatment (x : ℝ) : Bool := decide (0 ≤ x)

def wholePotentialOutcome (treated : Bool) (x error : ℝ) : ℝ :=
  (if treated then 6 else 2) + x + error

def wholeFixedScore (si : Fin 2 × Fin 4) : ℝ :=
  if si.1 = 0 then -m1Distance si.2 else m1Distance si.2

/-- The explicitly stipulated conditional response kernel at the eight scores.
This is a kernel evaluation, not conditioning by division by a zero event mass. -/
def wholeFixedResponse (error : (Fin 2 × Fin 4) → ℝ) (si : Fin 2 × Fin 4) : ℝ :=
  wholePotentialOutcome (wholeSharpTreatment (wholeFixedScore si))
    (wholeFixedScore si) (error si)

def wholeSideSum (side : Fin 2) (a : Fin 4 → ℝ)
    (Y : (Fin 2 × Fin 4) → ℝ) : ℝ := ∑ i, a i * Y (side, i)

/-- Existence certificates for the quantile used by the claims. -/
def wholeCriticalWellDefined : Prop :=
  {x : ℝ | 39/40 ≤ normalCDF x}.Nonempty ∧
  BddBelow {x : ℝ | 39/40 ≤ normalCDF x} ∧
  normalCDF normalCritical = 39/40 ∧ 0 < normalCritical

/-- P033-T1; p. 7 (PDF p. 7), Results, paragraph beginning “Panel 3(c)”;
Abstract, p. 1; Introduction, p. 2; Concluding remarks, p. 10.
In the stipulated eight-score Gaussian sharp RD model, both weighted estimators
are unbiased and have exact Gaussian inference, although the replacement has a
larger standard error and loses realized significance. Includes both Gram and WLS
certificates, every one-side variance and covariance, and the population and
conditional-kernel construction. This is a pointwise witness at the specified
affine means, with no claim of uniform coverage over a smoothness class. -/
def T1WholeStatement : Prop :=
  T1Statement ∧ wholeCriticalWellDefined ∧
  IsProbabilityMeasure wholeScoreLaw ∧ IsProbabilityMeasure wholePopulationLaw ∧
  (∀ treated x, Integrable (wholePotentialOutcome treated x) (gaussianReal 0 1) ∧
    (∫ e, wholePotentialOutcome treated x e ∂gaussianReal 0 1) =
      if treated then m1Treated x else m1Control x) ∧
  wholeErrorLaw.map wholeFixedResponse = rdConditionalLaw m1Treated m1Control ∧
  MemLp (rdEstimator m1Linear) 2 (rdConditionalLaw m1Treated m1Control) ∧
  MemLp (rdEstimator m1Corrected) 2 (rdConditionalLaw m1Treated m1Control) ∧
  (∀ side : Fin 2,
    MemLp (wholeSideSum side m1Linear) 2 (rdConditionalLaw m1Treated m1Control) ∧
    MemLp (wholeSideSum side m1Bias) 2 (rdConditionalLaw m1Treated m1Control) ∧
    MemLp (wholeSideSum side m1Corrected) 2 (rdConditionalLaw m1Treated m1Control) ∧
    variance (wholeSideSum side m1Linear) (rdConditionalLaw m1Treated m1Control) = 83/50 ∧
    variance (wholeSideSum side m1Bias) (rdConditionalLaw m1Treated m1Control) = 243/50 ∧
    covariance (wholeSideSum side m1Linear) (wholeSideSum side m1Bias)
      (rdConditionalLaw m1Treated m1Control) = -21/25 ∧
    variance (wholeSideSum side m1Corrected) (rdConditionalLaw m1Treated m1Control) = 41/5)

/-- P033-T2; Abstract, p. 1; Introduction, p. 2; Results, p. 7, paragraph
beginning “Panel 3(c)”; Concluding remarks, p. 10 (printed and PDF pages agree).
The affine model and its smooth quartic alternative induce the same conditional
data law but different coverage. Includes the general Gaussian coverage formula,
the polynomial and cutoff identities, bias and tail bounds, all study-count and
nonidentification conclusions, and the square-integrable bias-adjustment variance
identity. All conditional mean functions and the perturbation are C-infinity.
The empirical counts in the replacement prose are expressly outside its formal claim. -/
def T2WholeStatement : Prop :=
  T2Statement.{u, v, w} ∧ wholeCriticalWellDefined ∧
  ContDiff ℝ ∞ m1Control ∧ ContDiff ℝ ∞ m1Treated ∧
  ContDiff ℝ ∞ m2Perturbation ∧ ContDiff ℝ ∞ m2Treated ∧
  MemLp (rdEstimator m1Linear) 2 (rdConditionalLaw m2Treated m1Control) ∧
  (49/50 : ℝ) ≤ normalCDF 5 ∧
  (5 : ℝ) < 20/m1SELinear - 49/25 ∧
  Integrable (fun Y => ((rdEstimator m1Linear Y-4)/m1SELinear)^2)
    (rdConditionalLaw m2Treated m1Control) ∧
  (∫ Y, ((rdEstimator m1Linear Y-4)/m1SELinear)^2
    ∂rdConditionalLaw m2Treated m1Control) = 1 ∧
  intervalCoverage (rdConditionalLaw m1Treated m1Control) (rdEstimator m1Linear)
    4 ((49/25)*m1SELinear) = 2*normalCDF (49/25)-1 ∧
  (1-(25/49 : ℝ)^2 = 1776/2401)

/-- Physical distance of cluster j+1 from the cutoff. There are n(n+1)
clusters on each side and five records in each cluster. -/
def wholePhysicalDistance (n : ℕ) (j : Fin (n*(n+1))) : ℝ :=
  ((j : ℝ)+1) / ((n : ℝ)*((n : ℝ)+1))

/-- Both the point-estimation bandwidth h and bias bandwidth b are 1/n. -/
def wholeBandwidth (n : ℕ) : ℝ := 1/(n : ℝ)

def wholePhysicalKernel (n : ℕ) (j : Fin (n*(n+1))) : ℝ :=
  max 0 (1 - |wholePhysicalDistance n j / wholeBandwidth n|)

def wholeActiveIndex (n : ℕ) (j : Fin n) : Fin (n*(n+1)) :=
  Fin.castLE (Nat.le_mul_of_pos_right n (Nat.succ_pos n)) j

def wholePaddedWeight (n : ℕ) (a : Fin n → ℝ) (j : Fin (n*(n+1))) : ℝ :=
  if h : j.val < n then a ⟨j.val, h⟩ else 0

/-- Coefficients of a weighted polynomial fit, in increasing power order.
This is the normal-equation definition of WLS. Every use below certifies that
the Gram matrix is invertible, so the inverse never supplies a junk fit. -/
def wholeGridGram {ι : Type*} [Fintype ι] (x w : ι → ℝ) (p : ℕ) :
    Matrix (Fin (p+1)) (Fin (p+1)) ℝ :=
  fun r s => ∑ j, w j * x j ^ (r.val+s.val)

def wholeGridFit {ι : Type*} [Fintype ι] (x w y : ι → ℝ) (p : ℕ) :
    Fin (p+1) → ℝ :=
  Matrix.mulVec (wholeGridGram x w p)⁻¹ (fun r => ∑ j, w j * x j ^ r.val * y j)

def wholeNormalizedFit (n p : ℕ) (y : Fin n → ℝ) : Fin (p+1) → ℝ :=
  wholeGridFit (shrinkingDistance n) (shrinkingKernel n) y p

/-- Physical WLS uses every record, including all zero-weight outer clusters. -/
def wholePhysicalFit (n p : ℕ) (y : Fin (n*(n+1)) → Fin 5 → ℝ) :
    Fin (p+1) → ℝ :=
  wholeGridFit (fun ji : Fin (n*(n+1)) × Fin 5 => wholePhysicalDistance n ji.1)
    (fun ji => wholePhysicalKernel n ji.1) (fun ji => y ji.1 ji.2) p

def wholeClusterMean (n : ℕ) (y : Fin (n*(n+1)) → Fin 5 → ℝ)
    (j : Fin (n*(n+1))) : ℝ := (∑ i, y j i)/5

def wholeActiveMean (n : ℕ) (y : Fin (n*(n+1)) → Fin 5 → ℝ) (j : Fin n) : ℝ :=
  wholeClusterMean n y (wholeActiveIndex n j)

def wholePhysicalMoment (n k : ℕ) : ℝ :=
  ∑ j, wholePhysicalKernel n j * wholePhysicalDistance n j ^ k

/-- The linear intercept's cluster weights (record weights are these divided by five). -/
def wholePhysicalIntercept (n : ℕ) (j : Fin (n*(n+1))) : ℝ :=
  wholePhysicalKernel n j *
    (wholePhysicalMoment n 2 - wholePhysicalMoment n 1 * wholePhysicalDistance n j) /
    (wholePhysicalMoment n 0 * wholePhysicalMoment n 2 - wholePhysicalMoment n 1 ^ 2)

def wholePhysicalBiasMoment (n : ℕ) : ℝ :=
  ∑ j, wholePhysicalIntercept n j * wholePhysicalDistance n j ^ 2

/-- Bias correction uses the quadratic coefficient at the same physical bandwidth. -/
def wholePhysicalCorrected (n : ℕ) (y : Fin (n*(n+1)) → Fin 5 → ℝ) : ℝ :=
  wholePhysicalFit n 1 y 0 - wholePhysicalBiasMoment n * wholePhysicalFit n 2 y 2

def wholeNormalizedCorrected (n : ℕ) (y : Fin n → ℝ) : ℝ :=
  wholeNormalizedFit n 1 y 0 -
    (∑ j, shrinkingIntercept n j * shrinkingDistance n j ^ 2) * wholeNormalizedFit n 2 y 2

/-- Right minus left intercept, expressed using its cluster weights. -/
def wholePhysicalEstimator (n : ℕ) (y : (Fin 2 × Fin (n*(n+1))) → Fin 5 → ℝ) : ℝ :=
  ∑ j, wholePhysicalIntercept n j *
    (wholeClusterMean n (fun k => y (1,k)) j - wholeClusterMean n (fun k => y (0,k)) j)

def wholePhysicalSignEstimator (n : ℕ) (data : (Fin 2 × Fin (n*(n+1))) → Bool) : ℝ :=
  wholePhysicalEstimator n (fun g _ => signShock (data g))

def wholePhysicalNoisyEstimator (n : ℕ)
    (data : ((Fin 2 × Fin (n*(n+1))) ⊕ ((Fin 2 × Fin (n*(n+1))) × Fin 5)) → Bool) : ℝ :=
  wholePhysicalEstimator n (fun g i => signShock (data (.inl g)) + signShock (data (.inr (g,i))))

/-- A general active cluster-weight vector, padded by zero on the full grid.
These auxiliary estimators allow the probability transfer to be independent of WLS algebra. -/
def wholePaddedEstimator (n : ℕ) (a : Fin n → ℝ)
    (y : (Fin 2 × Fin (n*(n+1))) → Fin 5 → ℝ) : ℝ :=
  ∑ j, wholePaddedWeight n a j *
    (wholeClusterMean n (fun k => y (1,k)) j - wholeClusterMean n (fun k => y (0,k)) j)

def wholePaddedSignEstimator (n : ℕ) (a : Fin n → ℝ)
    (data : (Fin 2 × Fin (n*(n+1))) → Bool) : ℝ :=
  wholePaddedEstimator n a (fun g _ => signShock (data g))

def wholePaddedNoisyEstimator (n : ℕ) (a : Fin n → ℝ)
    (data : ((Fin 2 × Fin (n*(n+1))) ⊕ ((Fin 2 × Fin (n*(n+1))) × Fin 5)) → Bool) : ℝ :=
  wholePaddedEstimator n a (fun g i => signShock (data (.inl g)) + signShock (data (.inr (g,i))))

/-- Physical support, rescaling, and deletion of zero-weight rows. The sum
identity is quantified over arbitrary functions, so it applies to every moment
and normal-equation right-hand side, including noisy records. -/
def wholePhysicalGeometry (n : ℕ) : Prop :=
  0 < wholeBandwidth n ∧
  (∀ j, wholePhysicalDistance n j / wholeBandwidth n = ((j : ℝ)+1)/((n : ℝ)+1)) ∧
  (∀ j, 0 < wholePhysicalKernel n j ↔ j.val < n) ∧
  (Finset.univ.filter (fun j => 0 < wholePhysicalKernel n j)).card = n ∧
  (∀ j, wholePhysicalKernel n (wholeActiveIndex n j) = shrinkingKernel n j) ∧
  (∀ F : Fin (n*(n+1)) → ℝ,
    (∑ j, wholePhysicalKernel n j * F j) =
      ∑ j : Fin n, shrinkingKernel n j * F (wholeActiveIndex n j)) ∧
  (∀ (a : Fin n → ℝ) (F : Fin (n*(n+1)) → ℝ),
    (∑ j, wholePaddedWeight n a j * F j) =
      ∑ j : Fin n, a j * F (wholeActiveIndex n j))

/-- Full-grid and active-grid Gram matrices are nonsingular at both degrees. -/
def wholePhysicalRank (n : ℕ) : Prop :=
  ∀ p : ℕ, p = 1 ∨ p = 2 →
    IsUnit (wholeGridGram (shrinkingDistance n) (shrinkingKernel n) p) ∧
    IsUnit (wholeGridGram
      (fun ji : Fin (n*(n+1)) × Fin 5 => wholePhysicalDistance n ji.1)
      (fun ji => wholePhysicalKernel n ji.1) p)

/-- The coefficient of power r in physical units is h^(-r) times the active coefficient. -/
def wholePhysicalRescaling (n : ℕ) : Prop :=
  ∀ p : ℕ, p = 1 ∨ p = 2 → ∀ y : Fin (n*(n+1)) → Fin 5 → ℝ,
    ∀ r : Fin (p+1), wholeBandwidth n ^ r.val * wholePhysicalFit n p y r =
      wholeNormalizedFit n p (wholeActiveMean n y) r

/-- Normalized WLS identifies the linear weights and the same-bandwidth correction. -/
def wholeNormalizedRows (n : ℕ) : Prop :=
  (∀ y : Fin n → ℝ, wholeNormalizedFit n 1 y 0 = ∑ j, shrinkingIntercept n j * y j) ∧
  (∀ y : Fin n → ℝ, wholeNormalizedCorrected n y = wholeNormalizedFit n 2 y 0)

/-- The intercept row and the curvature bias correction are identified,
rather than merely named. -/
def wholePhysicalRows (n : ℕ) : Prop :=
  (∀ y : Fin (n*(n+1)) → Fin 5 → ℝ,
    wholePhysicalFit n 1 y 0 = ∑ j, wholePhysicalIntercept n j * wholeClusterMean n y j) ∧
  (∀ j, wholePhysicalIntercept n j = wholePaddedWeight n (shrinkingIntercept n) j) ∧
  wholePhysicalBiasMoment n = wholeBandwidth n ^ 2 *
    (∑ j, shrinkingIntercept n j * shrinkingDistance n j ^ 2) ∧
  (∀ y : Fin (n*(n+1)) → Fin 5 → ℝ,
    wholePhysicalCorrected n y = wholeNormalizedCorrected n (wholeActiveMean n y) ∧
    wholePhysicalCorrected n y = wholePhysicalFit n 2 y 0)

def wholePhysicalFits (n : ℕ) : Prop :=
  wholePhysicalRescaling n ∧ wholePhysicalRows n

/-- P033-T4; Methodology, p. 7; Power analysis and Table 2, p. 9;
Table 3, p. 10, election panel (printed and PDF pages agree).
Within-cell nearest-neighbour residuals cancel in nested clusters. The full
n(n+1)-cluster-per-side physical grid, with five records per cluster and h=b=1/n,
has exactly n positive triangular weights per side and the stated normalized
linear and same-bandwidth bias-corrected fits. The true sign-model variances
are V_n and (6/5)V_n with record noise, n V_n tends to 48/5, and estimated
nearest-neighbour variances are zero for every outcome array. Includes the
independent finite-second-moment cluster plug-in identities, the ten-cluster
examples, and the stipulated table-share arithmetic. -/
def T4WholeStatement : Prop :=
  T4Statement.{u, v} ∧
  Tendsto wholeBandwidth atTop (𝓝 0) ∧ ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)) ∧
  (∀ n : ℕ, 3 ≤ n →
    wholePhysicalGeometry n ∧ wholePhysicalRank n ∧ wholePhysicalFits n ∧
    finiteMean (wholePhysicalSignEstimator n) = 0 ∧
    finiteVariance (wholePhysicalSignEstimator n) = shrinkingVariance n ∧
    finiteMean (wholePhysicalNoisyEstimator n) = 0 ∧
    finiteVariance (wholePhysicalNoisyEstimator n) = (6/5)*shrinkingVariance n ∧
    (∀ f : ℝ, ∀ ell : (Fin 2 × Fin (n*(n+1))) → ℝ,
      ∀ y : (Fin 2 × Fin (n*(n+1))) → Fin 5 → ℝ,
      f * (∑ g, ((ell g/5) * ∑ i, nnResidual (y g) i)^2) = 0))

/-- P033-T5; Power analysis and Table 2, p. 9, row 0.1, column 95;
Table 3, p. 10, second panel, row 0.1, column 95; Figure 4, p. 8.
The binary individual-outcome fuzzy RD witness has individual squared Cohen
effect 4/75 but count-standardized squared effect 1/80000. Doubling all cell
counts preserves the Wald effect and individual standardization, while dividing
the count-standardized squared effect by four. In general positive count scaling
preserves the Wald ratio, scales the sample standard deviation, and divides the
count-standardized effect by the scale. Wald and standardization denominators
are nonzero, and sample standard deviations use at least two observations. -/
def T5WholeStatement : Prop := T5Statement

end
end SAP.P033
