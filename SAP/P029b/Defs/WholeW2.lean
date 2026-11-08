import Mathlib
import SAP.P029b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b

universe u v

open scoped BigOperators Classical Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

/-- The normalized Lebesgue law on the open interval `(-r,r)`. Only `r=1,2` is used. -/
def uniformIntervalW2 (r : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Ioo (-r) r)

/-- Location zero, scale three logistic CDF; scale is not standard deviation. -/
def logisticCDFW2 (t : ℝ) : ℝ := (1 + Real.exp (-t / 3))⁻¹

/-- Eight dataset-level coefficients, and six independent coordinates per unit:
three covariates, two latent-index errors, and the outcome error. -/
abbrev SimCoordinateW2 (k : ℕ) := Fin 8 ⊕ (Fin (2*k) × Fin 6)

abbrev SimSpaceW2 (k : ℕ) := (SimCoordinateW2 k → ℝ) × Finset (Fin (2*k))

/-- Uniform choice of exactly half the units, including the empty design at `k=0`. -/
def balancedLawW2 (k : ℕ) : Measure (Finset (Fin (2*k))) :=
  (PMF.uniformOfFinset ((Finset.univ : Finset (Fin (2*k))).powersetCard k)
    (Finset.powersetCard_nonempty.mpr (by simp; omega))).toMeasure

/-- `wrong=true` selects the nonlinear design. The Gaussian parameter is variance nine. -/
def simCoordinateLawW2 (Λ : Measure ℝ) (k : ℕ) (wrong : Bool) :
    SimCoordinateW2 k → Measure ℝ
  | .inl _ => uniformIntervalW2 2
  | .inr (_, j) =>
      if j.val < 3 then uniformIntervalW2 1
      else if j.val < 5 then (if wrong then Λ else gaussianReal 0 9)
      else gaussianReal 0 1

def simLawW2 (Λ : Measure ℝ) (k : ℕ) (wrong : Bool) : Measure (SimSpaceW2 k) :=
  (Measure.pi (simCoordinateLawW2 Λ k wrong)).prod (balancedLawW2 k)

def simAssignmentW2 {k : ℕ} (ω : SimSpaceW2 k) (i : Fin (2*k)) : Bool :=
  decide (i ∈ ω.2)

def simIndexACW2 {k : ℕ} (wrong : Bool) (r : SimCoordinateW2 k → ℝ)
    (i : Fin (2*k)) : ℝ :=
  (if wrong then nonlinearACIndex else baselineACIndex)
    (r (.inl 0)) (r (.inl 1)) (r (.inl 2)) (r (.inl 3))
    (r (.inr (i,0))) (r (.inr (i,1))) (r (.inr (i,2))) (r (.inr (i,3)))

def simIndexAW2 {k : ℕ} (wrong : Bool) (r : SimCoordinateW2 k → ℝ)
    (i : Fin (2*k)) : ℝ :=
  (if wrong then nonlinearAIndex else baselineAIndex)
    (r (.inl 4)) (r (.inl 5)) (r (.inl 6)) (r (.inl 7))
    (r (.inr (i,0))) (r (.inr (i,1))) (r (.inr (i,2))) (r (.inr (i,4)))

def simY0W2 {k : ℕ} (wrong : Bool) (r : SimCoordinateW2 k → ℝ)
    (i : Fin (2*k)) : ℝ := 5 * latentAC (simIndexACW2 wrong r i) + r (.inr (i,5))

def simTauW2 {k : ℕ} (wrong : Bool) (r : SimCoordinateW2 k → ℝ)
    (i : Fin (2*k)) : ℝ :=
  5 * (1 + r (.inr (i,0)) + r (.inr (i,1)) + r (.inr (i,2)) +
    if wrong then r (.inr (i,0)) * r (.inr (i,1)) else 0)

/-- The probabilistic part of each named simulation recipe. Independence of coordinates
includes independence across units, and assignment is independent of the entire array. -/
def SimulationRecipeW2 (Λ : Measure ℝ) (k : ℕ) (wrong : Bool) : Prop :=
  IsProbabilityMeasure (simLawW2 Λ k wrong) ∧
  iIndepFun (fun j (ω : SimSpaceW2 k) => ω.1 j) (simLawW2 Λ k wrong) ∧
  (∀ j, Measure.map (fun ω : SimSpaceW2 k => ω.1 j) (simLawW2 Λ k wrong) =
    simCoordinateLawW2 Λ k wrong j) ∧
  IndepFun (fun ω : SimSpaceW2 k => ω.2) (fun ω => ω.1) (simLawW2 Λ k wrong) ∧
  (∀ᵐ ω ∂simLawW2 Λ k wrong, ω.2.card = k) ∧
  (∀ s : Finset (Fin (2*k)),
    simLawW2 Λ k wrong {ω | ω.2 = s} =
      if s.card = k then ((Nat.choose (2*k) k : ℝ≥0∞))⁻¹ else 0) ∧
  (∀ i : Fin (2*k), simLawW2 Λ k wrong {ω | simAssignmentW2 ω i = true} = 1/2)

/-- P029-T19; supplement pp. A1-A2, baseline and misspecified simulation designs.
Independent uniform covariates and shared coefficients, normal errors of standard
deviation three (baseline), logistic errors of location zero and scale three
(nonlinear design), standard normal outcome errors, and independent uniformly
balanced assignment realize the corrected recipes for every even sample size.
Thresholded indices give binary disjoint types, monotone potential treatments and
the stated type characterizations. The corrected treatment is the realized potential
treatment; an assigned complier receives treatment. The printed treatment equation
can have no solution or two solutions. The printed outcome and effect formulas obey
the potential-outcome identity. The usual measure-theoretic conditions are assumed. -/
def T19WholeStatement : Prop :=
  (∃ Λ : Measure ℝ, IsProbabilityMeasure Λ ∧
    (∀ t : ℝ, cdf Λ t = logisticCDFW2 t) ∧
    ∀ k : ℕ, ∀ wrong : Bool, SimulationRecipeW2 Λ k wrong) ∧
  ((∫ x : ℝ, x ∂gaussianReal 0 9) = 0 ∧
    Real.sqrt (Var[id; gaussianReal 0 9]) = 3) ∧
  T19Statement ∧
  (∀ iAC iA : ℝ,
    (latentD iAC iA false = 1 ∧ latentD iAC iA true = 1 ↔ latentA iAC iA = 1) ∧
    (latentC iAC iA = 1 → latentD iAC iA true = 1)) ∧
  (∀ (k : ℕ) (wrong : Bool) (i : Fin (2*k)),
    Measurable (fun r : SimCoordinateW2 k → ℝ => simIndexACW2 wrong r i) ∧
    Measurable (fun r : SimCoordinateW2 k → ℝ => simIndexAW2 wrong r i) ∧
    Measurable (fun r : SimCoordinateW2 k → ℝ => simY0W2 wrong r i) ∧
    Measurable (fun r : SimCoordinateW2 k → ℝ => simTauW2 wrong r i)) ∧
  (∀ (k : ℕ) (wrong : Bool) (ω : SimSpaceW2 k) (i : Fin (2*k)),
    let ac := simIndexACW2 wrong ω.1 i
    let a := simIndexAW2 wrong ω.1 i
    let d := latentC ac a * bit (simAssignmentW2 ω i) + latentA ac a
    d = latentD ac a (simAssignmentW2 ω i) ∧
    simY0W2 wrong ω.1 i + simTauW2 wrong ω.1 i * d =
      simY0W2 wrong ω.1 i + d *
        ((simY0W2 wrong ω.1 i + simTauW2 wrong ω.1 i) - simY0W2 wrong ω.1 i))

/-- The integrable envelope controlling substitution of inverse fitted scores. -/
def inverseErrorW2 {Ω : Type u} {X : Type v} (U : ℕ → Ω → PotentialUnit X)
    (c : X → ℝ) (s : ℕ → ℕ → Ω → ℝ) (n i : ℕ) (ω : Ω) : ℝ :=
  |1 / s n i ω - 1 / c (U i ω).x| * (1 + |(U i ω).y0| + |(U i ω).y1|)

/-- Additional assumptions for an auxiliary sufficient consistency proposition.
Row symmetry and uniform integrability are substantive additions. Neither follows
from pointwise Assumption 2, and neither is identified with the article's unlisted
regularity conditions. This structure is not a contract for a whole replacement. -/
structure ICSWRegularityW2 {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : ℕ → Ω → PotentialUnit X) (Z : ℕ → Ω → Bool)
    (c m : X → ℝ) (s : ℕ → ℕ → Ω → ℝ) : Prop where
  iv : ∀ i, IVAssumptions μ (U i) (Z i)
  independent : iIndepFun (fun i => jointVariables (U i) (Z i)) μ
  identical : ∀ i, IdentDistrib (jointVariables (U i) (Z i)) (jointVariables (U 0) (Z 0)) μ μ
  score : ∀ i, ScoreVersions μ (U i) c m
  overlap : ∃ ε : ℝ, 0 < ε ∧ ∀ i, ∀ᵐ ω ∂μ, ε < c (U i ω).x ∧ c (U i ω).x ≤ 1
  estimated_measurable : ∀ n i, Measurable (s n i)
  estimated_range : ∀ n, ∀ᵐ ω ∂μ, ∀ i : Fin (n+1), 0 < s n i.val ω ∧ s n i.val ω ≤ 1
  pointwise_consistency : ∀ i, TendstoInMeasure μ (fun n => s n i) atTop
    (fun ω => c (U i ω).x)
  symmetric : ∀ n (i : Fin (n+1)),
    IdentDistrib (fun ω => (s n i.val ω, jointVariables (U i.val) (Z i.val) ω))
      (fun ω => (s n 0 ω, jointVariables (U 0) (Z 0) ω)) μ μ
  uniform_integrability : UniformIntegrable (fun n => inverseErrorW2 U c s n 0) 1 μ

/-- Fitted weighted outcome (`outcome=true`) or receipt arm contrast. -/
def fittedContrastW2 {Ω : Type u} {X : Type v} (U : ℕ → Ω → PotentialUnit X)
    (Z : ℕ → Ω → Bool) (s : ℕ → ℕ → Ω → ℝ) (outcome : Bool) (n : ℕ) (ω : Ω) : ℝ :=
  let v := fun i : Fin (n+1) => if outcome then (U i.val ω).outcome (Z i.val ω)
    else bit ((U i.val ω).receipt (Z i.val ω))
  sampleArm (fun i : Fin (n+1) => 1/s n i.val ω) v (fun i => Z i.val ω) true -
    sampleArm (fun i : Fin (n+1) => 1/s n i.val ω) v (fun i => Z i.val ω) false

/-- Population equalities (8)-(14), including the unweighted ITT and the cancellations. -/
def AppendixIdentitiesW2 {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : Ω → PotentialUnit X) (Z : Ω → Bool) (c m : X → ℝ) : Prop :=
  let W := ∫ ω, 1/c (U ω).x ∂μ
  let M := ∫ ω, m (U ω).x ∂μ
  Integrable (fun ω => 1/c (U ω).x) μ ∧ 0 < W ∧
  (mCE μ (fun ω => (U ω).outcome (Z ω)) {ω | Z ω = true} -
    mCE μ (fun ω => (U ω).outcome (Z ω)) {ω | Z ω = false} =
      mP μ {ω | (U ω).complier} * mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier}) ∧
  (mP μ {ω | (U ω).complier} * mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} =
    ∫ ω, c (U ω).x * m (U ω).x ∂μ) ∧
  (mP μ {ω | (U ω).complier} = ∫ ω, c (U ω).x ∂μ) ∧
  (∀ᵐ ω ∂μ, (c (U ω).x * m (U ω).x) / c (U ω).x = m (U ω).x ∧
    c (U ω).x / c (U ω).x = 1) ∧
  (mArm μ Z (fun ω => 1/c (U ω).x) (fun ω => (U ω).outcome (Z ω)) true -
    mArm μ Z (fun ω => 1/c (U ω).x) (fun ω => (U ω).outcome (Z ω)) false = M/W) ∧
  (mArm μ Z (fun ω => 1/c (U ω).x) (fun ω => bit ((U ω).receipt (Z ω))) true -
    mArm μ Z (fun ω => 1/c (U ω).x) (fun ω => bit ((U ω).receipt (Z ω))) false = 1/W) ∧
  mWald μ U Z (fun ω => 1/c (U ω).x) = M ∧
  (A1Versions μ U m → M = ∫ ω, (U ω).tau ∂μ)

/-- P029-T26; p. 498, Section 3.4; pp. 504-505, Appendix equations (8)-(14).
Auxiliary sufficient specialization: under the IV assumptions, Assumptions 1-3,
rowwise equality of the joint fitted-score/unit laws, and uniform integrability of
the inverse-score error envelope, the population identities and both sample arm
contrasts have their stated limits, and ICSW converges to the ATE. Symmetry and
uniform integrability are additional substantive hypotheses, not consequences of
Assumption 2 or authorized usual measure-theoretic conditions. This proposition
is not a whole replacement of the canonical claim. Usual measure-theoretic
conditions are also assumed; initial undefined ratios use their real extension. -/
def T26SufficientStatementW2 : Prop :=
  (∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool),
    IVAssumptions μ U Z → ∀ (c m : X → ℝ), ScoreVersions μ U c m →
    ∀ ε : ℝ, 0 < ε → (∀ᵐ ω ∂μ, ε < c (U ω).x ∧ c (U ω).x ≤ 1) →
      AppendixIdentitiesW2 μ U Z c m) ∧
  (∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ℕ → Ω → PotentialUnit X)
    (Z : ℕ → Ω → Bool) (c m : X → ℝ) (s : ℕ → ℕ → Ω → ℝ),
    ICSWRegularityW2 μ U Z c m s → A1Versions μ (U 0) m →
    let W := ∫ ω, 1/c (U 0 ω).x ∂μ
    let ATE := ∫ ω, (U 0 ω).tau ∂μ
    TendstoInMeasure μ (fittedContrastW2 U Z s true) atTop (fun _ => ATE/W) ∧
    TendstoInMeasure μ (fittedContrastW2 U Z s false) atTop (fun _ => 1/W) ∧
    TendstoInMeasure μ (icswSequence U Z s) atTop (fun _ => ATE))

/-- Twelve equally likely atoms: a profile, one of C/A/N, and assignment. -/
abbrev CancelAtomW2 := (Bool × Fin 3) × Bool

abbrev cancelLawW2 : Measure CancelAtomW2 := (PMF.uniformOfFintype CancelAtomW2).toMeasure

def cancelSignW2 (x : Bool) : ℝ := if x then 2 else -2

def cancelUnitW2 (a : CancelAtomW2) : PotentialUnit Bool :=
  ⟨a.1.1, decide (a.1.2.val = 1), decide (a.1.2.val ≠ 2),
    if a.1.2.val = 1 then -cancelSignW2 a.1.1 else 0,
    if a.1.2.val = 2 then cancelSignW2 a.1.1 else 0⟩

abbrev CancelSpaceW2 := ℕ → CancelAtomW2

def cancelSampleLawW2 : Measure CancelSpaceW2 := Measure.infinitePi (fun _ => cancelLawW2)

def cancelDrawW2 (i : ℕ) (ω : CancelSpaceW2) : PotentialUnit Bool := cancelUnitW2 (ω i)

def cancelZW2 (i : ℕ) (ω : CancelSpaceW2) : Bool := (ω i).2

/-- Within-cell empirical receipt proportion; zero is only a temporary value for empty cells. -/
def cancelRateW2 (n : ℕ) (ω : CancelSpaceW2) (x z : Bool) : ℝ :=
  (∑ i : Fin (n+1), if (ω i.val).1.1 = x ∧ (ω i.val).2 = z then
    bit ((cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω)) else 0) /
  (∑ i : Fin (n+1), if (ω i.val).1.1 = x ∧ (ω i.val).2 = z then (1 : ℝ) else 0)

/-- The event on which the unconstrained cell MLE belongs to the interior nested model. -/
def cancelFitGoodW2 (n : ℕ) (ω : CancelSpaceW2) : Prop :=
  ∀ x : Bool, 0 < cancelRateW2 n ω x false ∧
    cancelRateW2 n ω x false < cancelRateW2 n ω x true ∧ cancelRateW2 n ω x true < 1

/-- The saturated nested ML score on its interior domain. The fallback is a positive
extension on exceptional samples, whose probability tends to zero. -/
def cancelFittedScoreW2 (n i : ℕ) (ω : CancelSpaceW2) : ℝ :=
  if cancelFitGoodW2 n ω then
    cancelRateW2 n ω (ω i).1.1 true - cancelRateW2 n ω (ω i).1.1 false else 1/3

def cancelLikelihoodW2 (n : ℕ) (ω : CancelSpaceW2) (q : Bool × Bool → ℝ) : ℝ :=
  ∏ i : Fin (n+1), bernoulliFactor (q ((ω i.val).1.1, (ω i.val).2))
    ((cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω))

def cancelCellFractionW2 (n : ℕ) (ω : CancelSpaceW2) (x z : Bool) : ℝ :=
  (∑ i : Fin (n+1), if (ω i.val).1.1 = x ∧ (ω i.val).2 = z then (1 : ℝ) else 0) /
    (n+1)

def CancellationCellLimitsW2 : Prop :=
  ∀ x z : Bool,
    TendstoInMeasure cancelSampleLawW2 (fun n ω => cancelCellFractionW2 n ω x z)
      atTop (fun _ => 1/4) ∧
    TendstoInMeasure cancelSampleLawW2 (fun n ω => cancelRateW2 n ω x z)
      atTop (fun _ => if z then 2/3 else 1/3)

/-- The population certificate: valid randomized IV, strict overlap, heterogeneous
effects, failure of A1 at both positive-mass profiles, and zero ATE/observed outcomes. -/
def CancellationPopulationW2 : Prop :=
  IVAssumptions cancelLawW2 cancelUnitW2 Prod.snd ∧
  (∀ x : Bool, mP cancelLawW2 {a | (cancelUnitW2 a).x = x} = 1/2 ∧
    scoreAt cancelLawW2 cancelUnitW2 x = 1/3 ∧
    mCE cancelLawW2 (fun a => (cancelUnitW2 a).tau) {a | (cancelUnitW2 a).complier ∧
      (cancelUnitW2 a).x = x} = 0 ∧
    mCE cancelLawW2 (fun a => (cancelUnitW2 a).tau) {a | (cancelUnitW2 a).x = x} =
      (if x then 4/3 else -4/3) ∧
    ¬ latentAt cancelLawW2 cancelUnitW2 x) ∧
  (∀ x z : Bool,
    mCE cancelLawW2 (fun a => bit ((cancelUnitW2 a).receipt a.2))
      {a | (cancelUnitW2 a).x = x ∧ a.2 = z} = if z then 2/3 else 1/3) ∧
  (∫ a, (cancelUnitW2 a).tau ∂cancelLawW2) = 0 ∧
  (∀ a, (cancelUnitW2 a).outcome a.2 = 0)

/-- Every interior probability is attained by the standard-normal probit link.
Consequently a saturated binary-profile model realizes every interior nested
receipt pair, both at the population law and at the fitted cell MLE. -/
def ProbitCompleteW2 : Prop :=
  ∀ p : ℝ, 0 < p → p < 1 → ∃ θ : ℝ, cdf (gaussianReal 0 1) θ = p

/-- The printed claim is false: P029-T27; pp. 499-500, paragraph on failure of Assumption 1.
Failure of latent ignorability need not produce
asymptotic bias. An iid randomized twelve-atom law has strict positive overlap,
interior nested receipt probabilities, heterogeneous effects, and failure of
Assumption 1 at both profiles. Its ATE and every observed outcome are zero.
Saturated nested ML scores are consistent on an event of probability tending to one,
and the zero extension of ICSW converges to the zero ATE. The usual measure-theoretic
conditions are satisfied. -/
def T27WholeStatement : Prop :=
  ProbitCompleteW2 ∧ CancellationPopulationW2 ∧
  IsProbabilityMeasure cancelSampleLawW2 ∧
  iIndepFun (fun i => jointVariables (cancelDrawW2 i) (cancelZW2 i)) cancelSampleLawW2 ∧
  (∀ i, IdentDistrib (jointVariables (cancelDrawW2 i) (cancelZW2 i))
    (jointVariables (cancelDrawW2 0) (cancelZW2 0)) cancelSampleLawW2 cancelSampleLawW2) ∧
  (∀ i, IVAssumptions cancelSampleLawW2 (cancelDrawW2 i) (cancelZW2 i)) ∧
  (∀ i, ScoreVersions cancelSampleLawW2 (cancelDrawW2 i) (fun _ => 1/3) (fun _ => 0)) ∧
  (∀ i, ¬ A1Versions cancelSampleLawW2 (cancelDrawW2 i) (fun _ => 0)) ∧
  (∀ i, (∫ ω, (cancelDrawW2 i ω).tau ∂cancelSampleLawW2) = 0) ∧
  ((1/4 : ℝ) > 0 ∧ (1/4 : ℝ) < 1/3 ∧ (1/3 : ℝ) ≤ 1) ∧
  (∀ n i, Measurable (cancelFittedScoreW2 n i)) ∧
  (∀ n i ω, 0 < cancelFittedScoreW2 n i ω ∧ cancelFittedScoreW2 n i ω ≤ 1) ∧
  (∀ i, TendstoInMeasure cancelSampleLawW2 (fun n => cancelFittedScoreW2 n i)
    atTop (fun _ => 1/3)) ∧
  Tendsto (fun n => cancelSampleLawW2 {ω | cancelFitGoodW2 n ω}) atTop (𝓝 1) ∧
  Tendsto (fun n => cancelSampleLawW2 {ω |
    SampleDefined (fun i : Fin (n+1) => 1/cancelFittedScoreW2 n i.val ω)
      (fun i => (cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω))
      (fun i => cancelZW2 i.val ω)}) atTop (𝓝 1) ∧
  (∀ n ω, cancelFitGoodW2 n ω →
    ∀ q : ReceiptParameters, cancelLikelihoodW2 n ω q.val ≤
      cancelLikelihoodW2 n ω (fun xz => cancelRateW2 n ω xz.1 xz.2)) ∧
  (∀ n ω, icswSequence cancelDrawW2 cancelZW2 cancelFittedScoreW2 n ω = 0) ∧
  TendstoInMeasure cancelSampleLawW2
    (icswSequence cancelDrawW2 cancelZW2 cancelFittedScoreW2) atTop
    (fun _ => ∫ ω, (cancelDrawW2 0 ω).tau ∂cancelSampleLawW2)

end
end SAP.P029b
