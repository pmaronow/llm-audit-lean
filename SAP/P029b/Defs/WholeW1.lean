import Mathlib
import SAP.P029b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b

universe u v

set_option linter.unusedVariables false

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

/-- The closed binomial kernel, including the convention `0^0 = 1`. -/
def BinomialKernelW1 (n k : ℕ) (p : ℝ) : ℝ := p^k * (1-p)^(n-k)

def SaturatedLikelihoodW1 (n1 n0 k1 k0 : ℕ) (v : ℝ × ℝ) : ℝ :=
  BinomialKernelW1 n1 k1 v.1 * BinomialKernelW1 n0 k0 v.2

def ReceiptTriangleW1 : Set (ℝ × ℝ) := {v | 0 ≤ v.2 ∧ v.2 ≤ v.1 ∧ v.1 ≤ 1}

def SaturatedFitW1 (n1 n0 k1 k0 : ℕ) : ℝ × ℝ :=
  if (k0 : ℝ)/n0 ≤ (k1 : ℝ)/n1 then ((k1 : ℝ)/n1, (k0 : ℝ)/n0)
  else (((k1 : ℝ)+k0)/(n1+n0), ((k1 : ℝ)+k0)/(n1+n0))

def MLConclusionW1 (n1 n0 k1 k0 : ℕ) : Prop :=
  SaturatedFitW1 n1 n0 k1 k0 ∈ ReceiptTriangleW1 ∧
  (∀ v ∈ ReceiptTriangleW1,
    SaturatedLikelihoodW1 n1 n0 k1 k0 v ≤
      SaturatedLikelihoodW1 n1 n0 k1 k0 (SaturatedFitW1 n1 n0 k1 k0) ∧
    (SaturatedLikelihoodW1 n1 n0 k1 k0 v =
      SaturatedLikelihoodW1 n1 n0 k1 k0 (SaturatedFitW1 n1 n0 k1 k0) ↔
      v = SaturatedFitW1 n1 n0 k1 k0)) ∧
  (SaturatedFitW1 n1 n0 k1 k0).1 - (SaturatedFitW1 n1 n0 k1 k0).2 =
    positiveScore ((k1 : ℝ)/n1) ((k0 : ℝ)/n0)

/-- Simultaneous consistency for finitely many strata. No independence between
strata is required: each stratum has the specified independent two-arm marginal. -/
def JointStratumConsistencyW1 : Prop :=
  ∀ {G : Type u} {Ω : Type v} [Fintype G] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n1 n0 : G → ℕ → ℕ) (p1 p0 : G → ℝ)
    (hn1 : ∀ g n, 0 < n1 g n) (hn0 : ∀ g n, 0 < n0 g n)
    (ht1 : ∀ g, Tendsto (n1 g) atTop atTop)
    (ht0 : ∀ g, Tendsto (n0 g) atTop atTop)
    (hp : ∀ g, 0 ≤ p0 g ∧ p0 g ≤ p1 g ∧ p1 g ≤ 1)
    (K : (g : G) → (n : ℕ) → Ω → Fin (n1 g n+1) × Fin (n0 g n+1))
    (hK : ∀ g n, Measurable (K g n))
    (hmarg : ∀ g n k, mP μ {ω | K g n ω = k} =
      binomialArmLaw (n1 g n) (n0 g n) (p1 g) (p0 g) k),
    ∀ δ : ℝ, 0 < δ → Tendsto (fun n => mP μ
      {ω | ∃ g, δ < |armRateScore (n1 g n) (n0 g n) (K g n ω) -
        (p1 g-p0 g)|}) atTop (𝓝 0)

/-- P029-T14; p. 500, Assumption 2; pp. 496–497, Section 3.1.
With boundary probabilities allowed, the saturated ordered binomial likelihood has
the unique separate-rate or pooled maximizer and compliance score max(r1-r0,0).
The interior nested parameters, finite bias and extreme-event probability,
contraction and tail bound, per-stratum and simultaneous finite-stratum consistency,
and one-sided unbiasedness (requiring only a nonempty treated arm) all hold.
The usual measure-theoretic conditions are assumed. -/
def T14WholeStatement : Prop :=
  (∀ n1 n0 k1 k0 : ℕ, 0 < n1 → 0 < n0 → k1 ≤ n1 → k0 ≤ n0 →
    MLConclusionW1 n1 n0 k1 k0) ∧
  (∀ p q : ℝ, 0 < q → q < p → p < 1 →
    p ∈ Ioo (0 : ℝ) 1 ∧ q/p ∈ Ioo (0 : ℝ) 1 ∧
    nestedReceipt p (q/p) false = q ∧ nestedReceipt p (q/p) true = p ∧
    p*(1-q/p) = p-q) ∧
  T14Statement ∧
  (∀ n1 n0 : ℕ, 0 < n1 → 0 < n0 → ∀ p1 p0 : ℝ,
    0 ≤ p0 → p0 ≤ p1 → p1 ≤ 1 →
    fP (binomialArmLaw n1 n0 p1 p0) (fun k => k.1.val = 0 ∧ k.2.val = n0) =
      (1-p1)^n1 * p0^n0 ∧
    (0 < p0 → p1 < 1 → 0 < (1-p1)^n1 * p0^n0)) ∧
  JointStratumConsistencyW1.{u,v} ∧
  (∀ n : ℕ, 0 < n → ∀ p : ℝ, p ∈ Icc (0 : ℝ) 1 →
    fE (binomialMass n p) (fun k => (k.val : ℝ)/n) = p)

/-- The empirical CDF of a nonempty vector. -/
def EmpiricalCDFW1 {n : ℕ} (s : Fin (n+1) → ℝ) (t : ℝ) : ℝ :=
  ((Finset.univ.filter (fun i => s i ≤ t)).card : ℝ)/(n+1)

/-- Generalized inverse of the empirical CDF. The nonempty, bounded-below
superlevel set is part of the definition, excluding a spurious infimum. -/
def InverseEmpiricalQuantileW1 {n : ℕ} (s : Fin (n+1) → ℝ)
    (level c : ℝ) : Prop :=
  {t | level ≤ EmpiricalCDFW1 s t}.Nonempty ∧
  BddBelow {t | level ≤ EmpiricalCDFW1 s t} ∧
  c = sInf {t | level ≤ EmpiricalCDFW1 s t}

/-- P029-T15; p. 498, footnote 6.
The constant-score counterexample satisfies the five IV assumptions and Assumptions
1–3, with receipt-arm means 3/4 and 1/4 and ATE and population ICSW equal to one.
Both inverse empirical-CDF and type-7 quantiles of its nonempty half-score vectors
exist and equal one half, including at every positive power level n^(-alpha).
The cutoff therefore does not tend to zero; no scores or weights change.
The usual measure-theoretic conditions are assumed. -/
def T15WholeStatement : Prop :=
  T15Statement ∧
  (fCE sixMass (fun i => bit ((constantUnit i.1).receipt i.2))
      (fun i => i.2 = true) = 3/4 ∧
    fCE sixMass (fun i => bit ((constantUnit i.1).receipt i.2))
      (fun i => i.2 = false) = 1/4) ∧
  (∀ i : Fin 3, (constantUnit i).tau = 1) ∧
  (∀ n (level : ℝ), level ∈ Ioc (0 : ℝ) 1 →
    InverseEmpiricalQuantileW1 (fun _ : Fin (n+1) => (1/2 : ℝ)) level (1/2) ∧
    ∀ c, InverseEmpiricalQuantileW1 (fun _ : Fin (n+1) => (1/2 : ℝ)) level c →
      c = 1/2) ∧
  (∀ α : ℝ, 0 < α → ∀ n : ℕ,
    let level := ((n+1 : ℕ) : ℝ)^(-α)
    Type7Quantile (fun _ : Fin (n+1) => (1/2 : ℝ)) level (1/2) ∧
    InverseEmpiricalQuantileW1 (fun _ : Fin (n+1) => (1/2 : ℝ)) level (1/2) ∧
    |(1/2 : ℝ)-0| = 1/2) ∧
  (∀ n (Y : Fin (n+1) → ℝ) (D Z : Fin (n+1) → Bool),
    (∀ i : Fin (n+1), max (1/2 : ℝ) (1/2) = 1/2 ∧
      1/max (1/2 : ℝ) (1/2) = 2) ∧
    sampleWald (fun _ => 1/max (1/2 : ℝ) (1/2)) Y D Z =
      sampleWald (fun _ => 2) Y D Z)

/-- The raw finite-profile iid assumptions of T16(iv). In particular no
conditional-expectation versions or eventual sample-definedness are inputs. -/
def FiniteSampleConditionsW1 {Ω : Type u} {X : Type v} [MeasurableSpace Ω]
    [MeasurableSpace X] (μ : Measure Ω) (U : ℕ → Ω → PotentialUnit X)
    (Z : ℕ → Ω → Bool) (s : ℕ → ℕ → Ω → ℝ) : Prop :=
  (∀ i, IVAssumptions μ (U i) (Z i)) ∧
  iIndepFun (fun i => jointVariables (U i) (Z i)) μ ∧
  (∀ i, IdentDistrib (jointVariables (U i) (Z i))
    (jointVariables (U 0) (Z 0)) μ μ) ∧
  (∀ n i, Measurable (s n i)) ∧
  (∀ n, ∀ᵐ ω ∂μ, ∀ i : Fin (n+1), 0 < s n i.val ω ∧ s n i.val ω ≤ 1) ∧
  (∃ ε : ℝ, 0 < ε ∧ ∀ x, 0 < mP μ {ω | (U 0 ω).x = x} →
    ε < scoreAt μ (U 0) x ∧ scoreAt μ (U 0) x ≤ 1) ∧
  TendstoInMeasure μ (uniformScoreError U (scoreAt μ (U 0)) s) atTop (fun _ => 0)

def WinsorizationLimitsW1 {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [Fintype X]
    (μ : Measure Ω) (U : ℕ → Ω → PotentialUnit X) (Z : ℕ → Ω → Bool)
    (s : ℕ → ℕ → Ω → ℝ) (cutoff : ℕ → Ω → ℝ) : Prop :=
  TendstoInMeasure μ (fun n ω => winsorizedSequence U Z s cutoff n ω -
    icswSequence U Z s n ω) atTop (fun _ => 0) ∧
  TendstoInMeasure μ (icswSequence U Z s) atTop
    (fun _ => ∑ x, mP μ {ω | (U 0 ω).x = x} * complierAt μ (U 0) x) ∧
  TendstoInMeasure μ (winsorizedSequence U Z s cutoff) atTop
    (fun _ => ∑ x, mP μ {ω | (U 0 ω).x = x} * complierAt μ (U 0) x) ∧
  ((∀ x, 0 < mP μ {ω | (U 0 ω).x = x} → latentAt μ (U 0) x) →
    (∑ x, mP μ {ω | (U 0 ω).x = x} * complierAt μ (U 0) x) =
      ∫ ω, (U 0 ω).tau ∂μ)

/-- P029-T16; p. 498, footnote 6, corrected.
The type-7 changed count is at most floor(1+(n-1)lambda), and its fraction is at
most lambda+1/n. The inverse empirical-CDF convention obeys the same bounds.
At fixed positive power levels both changed fractions vanish. Quantiles preserve
common lower bounds; half-score cutoffs exist and stay one half. The pointwise
inverse-weight and bounded weighted-mean bounds hold. Under the printed finite-
profile iid, overlap, integrability and uniform score consistency conditions,
ordinary and Winsorized ICSW have the stated common limit and vanishing difference,
with ATE identification under Assumption 1. The usual measure-theoretic conditions,
including measurable scores and cutoffs, are assumed. Ratios use their real-valued
extension on undefined samples; no eventual-definedness assumption is imposed. -/
def T16WholeStatement : Prop :=
  (∀ {n : ℕ} (s : Fin (n+1) → ℝ) (level c b : ℝ),
    level ∈ Ioo (0 : ℝ) 1 → Type7Quantile s level c → (∀ i, b ≤ s i) →
    belowCount s c ≤ ⌊1+(n : ℝ)*level⌋₊ ∧
    (⌊1+(n : ℝ)*level⌋₊ : ℝ) ≤ 1+n*level ∧
    (belowCount s c : ℝ)/(n+1) ≤ level+1/(n+1) ∧ b ≤ c) ∧
  (∀ {n : ℕ} (s : Fin (n+1) → ℝ) (level : ℝ),
    level ∈ Ioc (0 : ℝ) 1 →
    (∃ c, InverseEmpiricalQuantileW1 s level c) ∧
    ∀ c b, InverseEmpiricalQuantileW1 s level c → (∀ i, b ≤ s i) →
      belowCount s c ≤ ⌊1+(n : ℝ)*level⌋₊ ∧
      (belowCount s c : ℝ)/(n+1) ≤ level+1/(n+1) ∧ b ≤ c) ∧
  (∀ (s : (n : ℕ) → Fin (n+1) → ℝ) (c : ℕ → ℝ) (α : ℝ), 0 < α →
    (∀ n, Type7Quantile (s n) (((n+1 : ℕ) : ℝ)^(-α)) (c n) ∨
      InverseEmpiricalQuantileW1 (s n) (((n+1 : ℕ) : ℝ)^(-α)) (c n)) →
    Tendsto (fun n => (belowCount (s n) (c n) : ℝ)/(n+1)) atTop (𝓝 0)) ∧
  (∀ {n : ℕ} (s V : Fin (n+1) → ℝ) (level c b K : ℝ),
    level ∈ Ioo (0 : ℝ) 1 → Type7Quantile s level c →
    0 < b → (∀ i, b ≤ s i ∧ s i ≤ 1) → 0 ≤ K → (∀ i, |V i| ≤ K) →
    (∀ i, 0 ≤ weightChange (s i) c ∧
      weightChange (s i) c ≤ (1/b)*(if s i < c then 1 else 0)) ∧
    |(∑ i, weightChange (s i) c * V i)/(n+1)| ≤ (K/b)*(level+1/(n+1))) ∧
  ((∀ n (level : ℝ), level ∈ Icc (0 : ℝ) 1 →
    Type7Quantile (fun _ : Fin (n+1) => (1/2 : ℝ)) level (1/2) ∧
    ∀ c, Type7Quantile (fun _ : Fin (n+1) => (1/2 : ℝ)) level c → c = 1/2) ∧
    (∀ (α : ℝ), 0 < α → ∀ n,
      Type7Quantile (fun _ : Fin (n+1) => (1/2 : ℝ))
        (((n+1 : ℕ) : ℝ)^(-α)) (1/2)) ∧
    ¬ Tendsto (fun _ : ℕ => (1/2 : ℝ)) atTop (𝓝 0)) ∧
  (∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ℕ → Ω → PotentialUnit X)
    (Z : ℕ → Ω → Bool) (s : ℕ → ℕ → Ω → ℝ) (cutoff : ℕ → Ω → ℝ),
    FiniteSampleConditionsW1 μ U Z s → ∀ α : ℝ, 0 < α →
    (∀ n, Measurable (cutoff n)) →
    (∀ n, ∀ᵐ ω ∂μ, Type7Quantile (fun i : Fin (n+1) => s n i.val ω)
      (((n+1 : ℕ) : ℝ)^(-α)) (cutoff n ω)) →
    WinsorizationLimitsW1 μ U Z s cutoff)

/-- P029-T17; p. 497, footnote 3 and equation (7), corrected.
The one-sided nested Bernoulli likelihood reduces to the treated-arm likelihood,
and their maximizer predicates agree. For every interior probability the printed
additive factor has the stated two formulas and is at least one; at three quarters
it gives seven quarters and five quarters instead of the Bernoulli probabilities.
The usual measure-theoretic conditions are assumed. -/
def T17WholeStatement : Prop :=
  T17Statement.{u,v} ∧
  (∀ (π : ℝ) (z d : Bool), π ∈ Ioo (0 : ℝ) 1 →
    (π*bit z)^(if d then 1 else 0 : ℕ) +
        (1-π*bit z)^(if d then 0 else 1 : ℕ) =
      (if d then π*bit z+1 else 2-π*bit z) ∧
    1 ≤ (π*bit z)^(if d then 1 else 0 : ℕ) +
      (1-π*bit z)^(if d then 0 else 1 : ℕ))

def ReceiptConditionsW1 {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : Ω → PotentialUnit X) (Z : Ω → Bool) : Prop :=
  Measurable (fun ω => (U ω).x) ∧ Measurable (fun ω => (U ω).d0) ∧
  Measurable (fun ω => (U ω).d1) ∧ Measurable Z ∧
  μ {ω | (U ω).defier} = 0 ∧
  IndepFun Z (fun ω => ((U ω).x, (U ω).d0, (U ω).d1)) μ ∧
  0 < mP μ {ω | Z ω = true} ∧ mP μ {ω | Z ω = true} < 1

def ReceiptProfileConclusionW1 {Ω : Type u} {X : Type v} [MeasurableSpace Ω]
    (μ : Measure Ω) (U : Ω → PotentialUnit X) (Z : Ω → Bool) (x : X) : Prop :=
  let a := mCE μ (fun ω => bit (U ω).d1) {ω | (U ω).x = x}
  let a0 := mCE μ (fun ω => bit (U ω).d0) {ω | (U ω).x = x}
  let c := scoreAt μ U x
  a = a0+c ∧
  (∀ z, mCE μ (fun ω => bit ((U ω).receipt (Z ω)))
    {ω | (U ω).x = x ∧ Z ω = z} = c*bit z+a0) ∧
  mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | (U ω).x = x} =
    a0 + mP μ {ω | Z ω = true}*c ∧
  (μ {ω | (U ω).d0 = true} = 0 → a0 = 0)

/-- The corrected single-hat display, using the same inverse score in every sum. -/
def SingleHatEstimatorW1 {n : ℕ} (s Y : Fin n → ℝ) (D Z : Fin n → Bool) : ℝ :=
  (((∑ i, (1/s i)*bit (Z i)*Y i)/(∑ i, (1/s i)*bit (Z i))) -
    ((∑ i, (1/s i)*(1-bit (Z i))*Y i)/(∑ i, (1/s i)*(1-bit (Z i))))) /
  (((∑ i, (1/s i)*bit (Z i)*bit (D i))/(∑ i, (1/s i)*bit (Z i))) -
    ((∑ i, (1/s i)*(1-bit (Z i))*bit (D i))/(∑ i, (1/s i)*(1-bit (Z i)))))

/-- P029-T18; pp. 496–497, Section 3.1; p. 504, equation (9) and the estimator display.
Under random assignment and no defiers, the type partition, conditional compliance
and receipt formulas, positive-AC nested representation, and interior probability
range hold. Every law with no always-takers, conditional compliance probability one half at the profile,
and assignment probability one half gives the printed misconditioning discrepancy. With existing weighted expectations and positive
compliance almost surely, weighted ITT equals the corrected covariate-law integral
in (9), which cancels to (10). The single-hat sample display equals Section 3.3.
The usual measure-theoretic conditions are assumed, including measurable versions
of the conditional means and integrability of the displayed expectations.
No uniform positive lower bound on compliance is required for the integral identity. -/
def T18WholeStatement : Prop :=
  (∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → PotentialUnit X) (Z : Ω → Bool), ReceiptConditionsW1 μ U Z →
    (∀ᵐ ω ∂μ, ¬ ((U ω).complier ∧ (U ω).d0 = true) ∧
      ((U ω).complier ∨ (U ω).d0 = true ↔ (U ω).d1 = true)) ∧
    ∀ x, 0 < mP μ {ω | (U ω).x = x} →
      ReceiptProfileConclusionW1 μ U Z x ∧
      (0 < mCE μ (fun ω => bit (U ω).d1) {ω | (U ω).x = x} →
        let a := mCE μ (fun ω => bit (U ω).d1) {ω | (U ω).x = x}
        let b := alwaysAmongAC μ U x
        a*b = mCE μ (fun ω => bit (U ω).d0) {ω | (U ω).x = x} ∧
        a*(1-b) = scoreAt μ U x ∧
        ∀ z, mCE μ (fun ω => bit ((U ω).receipt (Z ω)))
          {ω | (U ω).x = x ∧ Z ω = z} = nestedReceipt a b z) ∧
      (μ {ω | (U ω).d0 = true} = 0 → scoreAt μ U x = 1/2 →
        mP μ {ω | Z ω = true} = 1/2 →
        mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | (U ω).x = x} = 1/4 ∧
        (∀ z, scoreAt μ U x*bit z +
          mCE μ (fun ω => bit (U ω).d0) {ω | (U ω).x = x} =
          if z then 1/2 else 0))) ∧
  (∀ a b : ℝ, a ∈ Ioo (0 : ℝ) 1 → b ∈ Ioo (0 : ℝ) 1 → ∀ z : Bool,
    nestedReceipt a b z ∈ Ioo (0 : ℝ) 1 ∧
      nestedReceipt a b z = if z then a else a*b) ∧
  (∀ p m : ℝ, 0 < p → (p*m)/p = m) ∧
  (∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X)
    (Z : Ω → Bool) (c m : X → ℝ), IVAssumptions μ U Z → ScoreVersions μ U c m →
    (∀ᵐ ω ∂μ, 0 < c (U ω).x) →
    Integrable (fun ω => 1/c (U ω).x) μ →
    (∀ z, Integrable (fun ω => (1/c (U ω).x)*(U ω).outcome z) μ) →
    (∫ ω, 1/c (U ω).x ∂μ) ≠ 0 →
    Integrable m (Measure.map (fun ω => (U ω).x) μ) ∧
    (mArm μ Z (fun ω => 1/c (U ω).x) (fun ω => (U ω).outcome (Z ω)) true -
      mArm μ Z (fun ω => 1/c (U ω).x) (fun ω => (U ω).outcome (Z ω)) false) =
      (1/(∫ ω, 1/c (U ω).x ∂μ))*
        (∫ x, (c x*m x)/c x ∂Measure.map (fun ω => (U ω).x) μ) ∧
    (1/(∫ ω, 1/c (U ω).x ∂μ))*
        (∫ x, (c x*m x)/c x ∂Measure.map (fun ω => (U ω).x) μ) =
      (1/(∫ ω, 1/c (U ω).x ∂μ))*
        (∫ x, m x ∂Measure.map (fun ω => (U ω).x) μ)) ∧
  (∀ {n : ℕ} (s Y : Fin n → ℝ) (D Z : Fin n → Bool),
    (∀ i, s i ∈ Ioc (0 : ℝ) 1) → SampleDefined (fun i => 1/s i) D Z →
    SingleHatEstimatorW1 s Y D Z = sampleWald (fun i => 1/s i) Y D Z)

end
end SAP.P029b
