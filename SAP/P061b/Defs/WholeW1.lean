import Mathlib
import SAP.P061b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061b
open scoped BigOperators Classical

/-- The exposed set, encoded by its binary membership vector. -/
noncomputable def exposureMaskW1 {Ω : Type} {N : ℕ} (g : Schedule Ω N)
    (d : ℝ) (z : Ω) : Fin N → Fin 2 :=
  fun i => if g i z = d then 1 else 0

/-- Uniformity of the sampled set among all n-subsets. This constrains only
the exposed set, and permits infinitely many raw assignments per exposed set. -/
def SimpleRandomExposureW1 {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Schedule Ω N) (d : ℝ) (n : ℕ) : Prop :=
  ∀ b : Fin N → Fin 2,
    eventProbability D (fun z => exposureMaskW1 g d z = b) =
      if (Finset.univ.filter (fun i => b i = 1)).card = n then
        (Nat.choose N n : ℝ)⁻¹ else 0

/-- The binary assignment vector as a real assignment vector. -/
def binaryAssignmentW1 {N : ℕ} (b : Fin N → Fin 2) : Fin N → ℝ :=
  fun i => (b i).val

/-- The feasible intervention set contains the entire binary cube. -/
def ContainsBinaryCubeW1 {N : ℕ} (Z : Set (Fin N → ℝ)) : Prop :=
  ∀ b : Fin N → Fin 2, binaryAssignmentW1 b ∈ Z

/-- Individualistic exposure on a feasible set of real assignment vectors. -/
def coordinateExposureW1 {N : ℕ} {Z : Set (Fin N → ℝ)} : Schedule Z N :=
  fun i z => z.val i

/-- The printed completely randomized experiment law on the full feasible
set: uniform on binary assignments with n ones, and zero at every other point. -/
def UniformBinaryDesignW1 {N : ℕ} {Z : Set (Fin N → ℝ)}
    (D : AtomicDesign Z) (n : ℕ) : Prop :=
  ∀ z, D.p z =
    if (∀ i, z.val i = 0 ∨ z.val i = 1) ∧
        (Finset.univ.filter (fun i => z.val i = 1)).card = n then
      (Nat.choose N n : ℝ)⁻¹ else 0

/-- P061-T17; supplement pp. 1–2, Equation (2) and the take-away sentence.
Equal positive exposure margins reduce HT to the fixed-denominator exposed mean,
which is the sample mean when the exposed count is fixed. A simple random sample
without replacement, including the census, has sample mean
unbiased for the AEPO on arbitrary raw assignment spaces. A completely randomized
binary experiment on any feasible set containing the binary cube has difference
in means unbiased for the AEED. No stability assumption is needed. The usual
measure-theoretic conditions are assumed; survey exposure first moments make
the conditional means defined, and the experiment supplies its moments. -/
def T17WholeStatement : Prop :=
  (∀ {Ω : Type} {N : ℕ} (D : AtomicDesign Ω) (g y : Schedule Ω N) (d : ℝ) (n : ℕ),
    0 < N → 0 < n → (∀ i, exposureProbability D g i d = (n : ℝ) / N) →
    ∀ z, htMean D g y d z = exposedMean g y d n z) ∧
  (∀ {Ω : Type} {N : ℕ} (D : AtomicDesign Ω) (g y : Schedule Ω N) (d : ℝ) (n : ℕ),
    0 < n → n ≤ N → SimpleRandomExposureW1 D g d n → ExposureMoment D g y d →
    (∀ z, InSupport D z → (Finset.univ.filter (fun i => g i z = d)).card = n) ∧
    (∀ i, exposureProbability D g i d = (n : ℝ) / N) ∧
    (∀ z, htMean D g y d z = exposedMean g y d n z) ∧
    HasFirstMoment D (exposedMean g y d n) ∧
    designMean D (exposedMean g y d n) = averageExposureMean D g y d) ∧
  (∀ {N : ℕ} (Z : Set (Fin N → ℝ)) (D : AtomicDesign Z) (y : Schedule Z N) (n : ℕ),
    ContainsBinaryCubeW1 Z → 0 < n → n < N → UniformBinaryDesignW1 D n →
    (∀ z, InSupport D z →
      (Finset.univ.filter (fun i => coordinateExposureW1 i z = 1)).card = n ∧
      (Finset.univ.filter (fun i => coordinateExposureW1 i z = 0)).card = N - n) ∧
    (∀ i, exposureProbability D coordinateExposureW1 i 1 = (n : ℝ) / N ∧
      exposureProbability D coordinateExposureW1 i 0 = ((N - n : ℕ) : ℝ) / N) ∧
    ExposureMoment D coordinateExposureW1 y 1 ∧
    ExposureMoment D coordinateExposureW1 y 0 ∧
    HasFirstMoment D (fun z => exposedMean coordinateExposureW1 y 1 n z -
      exposedMean coordinateExposureW1 y 0 (N - n) z) ∧
    designMean D (fun z => exposedMean coordinateExposureW1 y 1 n z -
      exposedMean coordinateExposureW1 y 0 (N - n) z) =
      averageContrast D coordinateExposureW1 y 1 0)

/-- The pairwise Young upper bound estimated using only marginal probabilities. -/
noncomputable def youngPairEstimateW1 {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y : Schedule Ω N) (d : ℝ) (i j : Fin N) (z : Ω) : ℝ :=
  (if g i z = d then y i z ^ 2 / 2 else 0) / exposureProbability D g i d +
  (if g j z = d then y j z ^ 2 / 2 else 0) / exposureProbability D g j d

/-- One observed-data statistic is unbiased for the product for every unknown
NURVA schedule. The design, mapping, exposure and pair are fixed before choosing
the statistic; the schedule is quantified afterwards. -/
def UnbiasedProductStatisticW1 {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Schedule Ω N) (d : ℝ) (i j : Fin N)
    (T : Ω × (Fin N → ℝ) → ℝ) : Prop :=
  ∀ v : Schedule Ω N, SupportStable D g v →
    HasFirstMoment D (fun z => T (z, fun k => v k z)) ∧
    designMean D (fun z => T (z, fun k => v k z)) =
      exposureMean D g v i d * exposureMean D g v j d

/-- P061-T19; supplement pp. 3–4, Equations (6)–(8).
Under individual positivity and NURVA, the joint-positive HT variance estimator
is unbiased with the printed covariance-sum expectation, and the Young-corrected
estimator is conservative in expectation. Each pair's Young bound admits an
integrable unbiased estimator using only marginal exposure probabilities.
If a joint exposure probability is zero, the two target cells are never jointly
revealed on support, and no single observed-data statistic is unbiased for their
EPO product for every NURVA outcome schedule. All sums include ordered diagonal
pairs. The usual measure-theoretic conditions are assumed; all displayed moments
follow from positivity and NURVA even with infinite raw support. -/
def T19WholeStatement : Prop :=
  ∀ {Ω : Type} {N : ℕ} (D : AtomicDesign Ω) (g y : Schedule Ω N) (d : ℝ),
    0 < N → (∀ i, 0 < exposureProbability D g i d) → SupportStable D g y →
    ExposureMoment D g y d ∧
    HasFirstMoment D (htMean D g y d) ∧
    HasFirstMoment D (fun z => (htMean D g y d z - designMean D (htMean D g y d)) ^ 2) ∧
    ((∀ i j, 0 < jointExposureProbability D g i j d d) →
      HasFirstMoment D (htVarianceEstimate D g y d) ∧
      designMean D (htVarianceEstimate D g y d) = designVariance D (htMean D g y d) ∧
      designMean D (htVarianceEstimate D g y d) = covarianceSum D g y d d) ∧
    HasFirstMoment D (conservativeVarianceEstimate D g y d) ∧
    designMean D (conservativeVarianceEstimate D g y d) ≥ designVariance D (htMean D g y d) ∧
    (∀ i j, |exposureMean D g y i d * exposureMean D g y j d| ≤
        exposureMean D g y i d ^ 2 / 2 + exposureMean D g y j d ^ 2 / 2 ∧
      HasFirstMoment D (youngPairEstimateW1 D g y d i j) ∧
      designMean D (youngPairEstimateW1 D g y d i j) =
        exposureMean D g y i d ^ 2 / 2 + exposureMean D g y j d ^ 2 / 2) ∧
    (∀ i j, jointExposureProbability D g i j d d = 0 →
      i ≠ j ∧ (∀ z, InSupport D z → ¬(g i z = d ∧ g j z = d)) ∧
      ¬∃ T : Ω × (Fin N → ℝ) → ℝ, UnbiasedProductStatisticW1 D g d i j T)

end SAP.P061b
