import Mathlib
import SAP.P013a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P013a

open scoped BigOperators Topology NNReal ENNReal
open Filter Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- P013-T1; Proposition 6.2, as printed, p. 1926 (PDF p. 15), and Appendix A.7,
p. 1943 (PDF p. 32). The paired family satisfies the standing conditions and genuine
degree-two dependence, but its positive unbiased variance estimate has scaled probability
limit six instead of eight and its Wald intervals strictly undercover. All finite identities,
asymptotic limits and the decimal coverage at level 95 percent are included. -/
def T1WholeStatement : Prop :=
  T1Statement ∧
  (∀ r (hr : 2 ≤ r) (i : Fin (2*r)),
    (∑ j : Fin (2*r), if pairIndex r i = pairIndex r j then 1 else 0 : ℕ) = 2) ∧
  (let P := fun n : ℕ => pairedDesign (n+2) (by omega)
   let F := fun n : ℕ => pairedPopulation (n+2) (by omega)
   let N := fun n : ℕ => (2*(n+2) : ℝ)
   ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
     variance (P n) (fun z => N n * effectVariance (F n) 1 0 z) ≤ C / N n) ∧
  (91037489444/100000000000 <
    2*normalCDF (normalCritical (1/20)*Real.sqrt (3/4))-1 ∧
   2*normalCDF (normalCritical (1/20)*Real.sqrt (3/4))-1 <
    91037489445/100000000000)

/-- Corrected coverage, centered at the population contrast. The sequence uses the nested
unit sets `Fin (n+1)`; fixed potential outcomes belong to each experiment, without requiring
an identical outcome table across different population sizes. -/
def WholeWaldCoverage : Prop :=
  ∀ S : ExperimentSequence, ComparisonBounded S → Condition5Genuine S →
    Condition6 S → LowerTailCondition S →
    ∀ α : ℝ, 0 < α → α < 1 → 1-α ≤ liminf (seqCoverage S α) atTop

/-- The corrected hypotheses without the additional lower-tail condition permit strict
undercoverage, even with stable outcomes across sizes and genuine dependency graphs. -/
def WholeWaldFailure : Prop :=
  ∃ S : ExperimentSequence, NestedPopulationSetup S ∧ StandingPositivity S ∧
    Condition3 S ∧ Condition5Genuine S ∧ Condition6 S ∧
    liminf (seqCoverage S (1/2)) atTop < 1/2

/-- P013-T2; corrected Proposition 6.2, p. 1926 (PDF p. 15), and Appendix A.7,
p. 1943 (PDF p. 32). Comparison boundedness, genuine bounded-degree dependence, positive
limiting scaled variance and the added lower-tail condition ensure nominal lower-limit
coverage of the population contrast. Centered concentration suffices; both joint-probability
rates and their concentration consequences hold without outcome stability across sizes.
The three original conditions alone permit strict undercoverage. -/
def T2WholeStatement : Prop :=
  WholeWaldCoverage ∧
  (∀ S : ExperimentSequence, ScaledVarianceConcentration S → LowerTailCondition S) ∧
  (∀ S : ExperimentSequence, ScaledVarianceVanishes S →
    ScaledVarianceConcentration S ∧ LowerTailCondition S) ∧
  (∀ S : ExperimentSequence, ComparisonBounded S → Condition5Genuine S →
    ∀ b : ℝ, 0 < b → JointLowerBound S b →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      variance (seqLaw S n) (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z) ≤ C/(n+1 : ℝ)) ∧
    ScaledVarianceConcentration S ∧ LowerTailCondition S) ∧
  (∀ S : ExperimentSequence, ComparisonBounded S → Condition5Genuine S →
    ∀ b : ℕ → ℝ,
    (∀ n, PositiveJointDomain S n → IsMinimumPositiveJoint S n (b n)) →
    (∀ᶠ n in atTop, PositiveJointDomain S n) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      variance (seqLaw S n) (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z) ≤
        C/((n+1 : ℝ)*b n)) ∧
    (Tendsto (fun (n : ℕ) => (n+1 : ℝ)*b n) atTop atTop →
      ScaledVarianceConcentration S ∧ LowerTailCondition S)) ∧
  WholeWaldFailure

/-- A fixed, everywhere-defined extension of the variance-ratio square root. -/
def wholeRatioRoot (V Vhat : ℝ) : ℝ :=
  if 0 < Vhat then Real.sqrt (V/Vhat) else 0

/-- A fixed, everywhere-defined extension of the studentized error. -/
def wholeStudentized (estimate target Vhat : ℝ) : ℝ :=
  if 0 < Vhat then (estimate-target)/Real.sqrt Vhat else 0

/-- P013-T8; corrected concentration and coverage argument, Appendix A.7,
p. 1943 (PDF p. 32). Conservativeness and vanishing variance of the scaled estimate give
centered concentration, the finite relative lower-tail bound and both coverage lower limits.
If its expectation converges to a finite value, the scaled estimate, variance ratio and
studentized error have the stated limits. Ratios and studentization are extended by zero
where the estimated variance is nonpositive; that event has probability tending to zero. -/
def T8WholeStatement : Prop :=
  ∀ {L : ℕ → Type} [∀ n, Fintype (L n)] (P : ∀ n, Design (L n))
    (estimate Vhat : ∀ n, L n → ℝ) (target V : ℕ → ℝ),
    (∀ n, V n=variance (P n) (estimate n) ∧ 0 < V n) →
    ∀ (c : ℝ) (hc : 0 < c),
    Tendsto (fun (n : ℕ) => (n+1 : ℝ)*V n) atTop (𝓝 c) →
    TendsNormal P (fun n z => (estimate n z-target n)/Real.sqrt (V n)) 0 1 →
    (∀ (n : ℕ), (n+1 : ℝ)*V n ≤ expectation (P n) (fun z => (n+1 : ℝ)*Vhat n z)) →
    Tendsto (fun n => variance (P n) (fun z => (n+1 : ℝ)*Vhat n z)) atTop (𝓝 0) →
    let W := fun (n : ℕ) z => (n+1 : ℝ)*Vhat n z
    let v := fun (n : ℕ) => (n+1 : ℝ)*V n
    ConvergesInProbability P (fun n z => W n z-expectation (P n) (W n)) 0 ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 →
      (∀ n, probability (P n) (fun z => W n z < (1-ε)*v n) ≤
        variance (P n) (W n)/(ε^2*(v n)^2)) ∧
      Tendsto (fun n => probability (P n) (fun z => W n z < (1-ε)*v n)) atTop (𝓝 0)) ∧
    (∀ α : ℝ, 0 < α → α < 1 →
      (∀ ε : ℝ, 0 < ε → ε < 1 →
        2*normalCDF (normalCritical α*Real.sqrt (1-ε))-1 ≤
          liminf (fun n => probability (P n) (fun z => 0 ≤ Vhat n z ∧
            |estimate n z-target n| ≤ normalCritical α*Real.sqrt (Vhat n z))) atTop) ∧
      1-α ≤ liminf (fun n => probability (P n) (fun z => 0 ≤ Vhat n z ∧
        |estimate n z-target n| ≤ normalCritical α*Real.sqrt (Vhat n z))) atTop) ∧
    (∀ (s : ℝ) (hsc : c ≤ s),
      Tendsto (fun n => expectation (P n) (W n)) atTop (𝓝 s) →
      ConvergesInProbability P W s ∧
      Tendsto (fun n => probability (P n) (fun z => Vhat n z ≤ 0)) atTop (𝓝 0) ∧
      ConvergesInProbability P (fun n z => wholeRatioRoot (V n) (Vhat n z)) (Real.sqrt (c/s)) ∧
      0 < Real.sqrt (c/s) ∧ Real.sqrt (c/s) ≤ 1 ∧
      TendsNormal P (fun n z => wholeStudentized (estimate n z) (target n) (Vhat n z)) 0
        ⟨c/s, div_nonneg hc.le (le_trans hc.le hsc)⟩)

/-- The relative-bias guidance explicitly concerns the fixed population total. Independent
simulation is represented by the product design; signed outcomes retain their cancellation
factor and relative bias is asserted only when the total is nonzero. -/
def WholeReplicationGuidance : Prop :=
  ∀ {Ω : Type} [Fintype Ω] {N K : ℕ} {P : Design Ω} (F : Population P N K),
    0 < N → ∀ d : Fin K, Positivity F d → ∀ R : ℕ, 1 ≤ R →
    ∀ p0 : ℝ, IsMinimumPi F d p0 →
    let E := expectation (independentProduct P (replicateDesign P R)) (simulatedHTTotal F d R)
    let T := potentialTotal F d
    let κ := cancellationFactor F d
    E = ∑ i, F.outcome i d * (1-(1-pi F i d)^(R+1)) ∧
    E = T - ∑ i, F.outcome i d * (1-pi F i d)^(R+1) ∧
    |E-T| ≤ (1-p0)^(R+1)*(∑ i, |F.outcome i d|) ∧
    (T ≠ 0 → 1 ≤ κ ∧ |(E-T)/T| ≤ κ*(1-p0)^(R+1) ∧
      (((∀ i, 0 ≤ F.outcome i d) ∨ (∀ i, F.outcome i d ≤ 0)) →
        κ = 1 ∧ |(E-T)/T| ≤ (1-p0)^(R+1) ∧
        (∀ b : ℝ, 0 < b → (R : ℝ) ≥ Real.log b/Real.log (1-p0)-1 → |(E-T)/T| ≤ b)) ∧
      (∀ b : ℝ, 0 < b → (R : ℝ) ≥ Real.log (b/κ)/Real.log (1-p0)-1 → |(E-T)/T| ≤ b))

/-- P013-T9; corrected targets in Appendix A.6, p. 1942 (PDF p. 31), Proposition 6.2,
p. 1926 (PDF p. 15), Appendix A.7, p. 1943 (PDF p. 32), and the sentence preceding
Proposition 4.1, p. 1920 (PDF p. 9). HT means and their contrast are consistent for the
population quantities under Conditions 3 and 4. The corrected Wald conclusion covers the
population contrast, the positive-variance studentization display is an identity, and
simulation guidance bounds relative bias for the fixed population total. -/
def T9WholeStatement : Prop :=
  (∀ S : ExperimentSequence, StandingPositivity S → Condition3 S → Condition4 S →
    ConvergesInProbability (seqLaw S)
      (fun n z => htMean (seqPopulation S n) (S.treated n) z-
        potentialMean (seqPopulation S n) (S.treated n)) 0 ∧
    ConvergesInProbability (seqLaw S)
      (fun n z => htMean (seqPopulation S n) (S.control n) z-
        potentialMean (seqPopulation S n) (S.control n)) 0 ∧
    ConvergesInProbability (seqLaw S) (fun n z => seqEstimate S n z-seqTarget S n) 0) ∧
  WholeWaldCoverage ∧
  (∀ estimate target V Vhat : ℝ, 0 < V → 0 < Vhat →
    (estimate-target)/Real.sqrt Vhat =
      ((estimate-target)/Real.sqrt V)*Real.sqrt (V/Vhat)) ∧
  WholeReplicationGuidance

/-- Finite sampling law and binary inclusion indicators, allowing zero-weight atoms and
certainty inclusion. No independence or joint positivity is imposed. -/
structure WholeSamplingDesign (U Ω : Type) [Fintype U] [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ z, 0 ≤ weight z
  total : ∑ z, weight z = 1
  selected : Ω → U → Bool

variable {U Ω : Type} [Fintype U] [Fintype Ω]

def samplingExpect (D : WholeSamplingDesign U Ω) (X : Ω → ℝ) : ℝ :=
  ∑ z, D.weight z * X z
def samplingIndicator (D : WholeSamplingDesign U Ω) (z : Ω) (i : U) : ℝ :=
  if D.selected z i then 1 else 0
def samplingPi (D : WholeSamplingDesign U Ω) (i : U) : ℝ :=
  samplingExpect D (fun z => samplingIndicator D z i)
def samplingJoint (D : WholeSamplingDesign U Ω) (i j : U) : ℝ :=
  samplingExpect D (fun z => samplingIndicator D z i * samplingIndicator D z j)
def samplingVariance (D : WholeSamplingDesign U Ω) (X : Ω → ℝ) : ℝ :=
  samplingExpect D (fun z => (X z-samplingExpect D X)^2)
def samplingTotal (D : WholeSamplingDesign U Ω) (y : U → ℝ) (z : Ω) : ℝ :=
  ∑ i, samplingIndicator D z i * (y i/samplingPi D i)
def samplingVarianceHT (D : WholeSamplingDesign U Ω) (y : U → ℝ) (z : Ω) : ℝ :=
  ∑ i, ∑ j, if 0 < samplingJoint D i j then
    samplingIndicator D z i * samplingIndicator D z j *
      ((samplingJoint D i j-samplingPi D i*samplingPi D j)/samplingJoint D i j) *
      (y i/samplingPi D i) * (y j/samplingPi D j) else 0
def samplingMissingA (D : WholeSamplingDesign U Ω) (y : U → ℝ) : ℝ :=
  ∑ i, ∑ j, if i ≠ j ∧ samplingJoint D i j = 0 then y i*y j else 0
def samplingYoungCorrection (D : WholeSamplingDesign U Ω) (y : U → ℝ)
    (a b : U → U → ℝ) (z : Ω) : ℝ :=
  ∑ i, ∑ j, if i ≠ j ∧ samplingJoint D i j = 0 then
    samplingIndicator D z i * (|y i| ^ (a i j)/(a i j*samplingPi D i)) +
    samplingIndicator D z j * (|y j| ^ (b i j)/(b i j*samplingPi D j)) else 0
def samplingQuadraticCorrection (D : WholeSamplingDesign U Ω) (y : U → ℝ) (z : Ω) : ℝ :=
  ∑ i, ∑ j, if i ≠ j ∧ samplingJoint D i j = 0 then
    samplingIndicator D z i * (y i^2/(2*samplingPi D i)) +
    samplingIndicator D z j * (y j^2/(2*samplingPi D j)) else 0

/-- P013-T14; Lemma 5.1 and Propositions 5.1–5.2, pp. 1921–1922 (PDF pp. 10–11),
and Appendix A.5, Propositions A.1–A.2 and Corollary A.2, pp. 1939–1942 (PDF pp. 28–31).
The exposure variance estimate has the stated unbiasedness, missing-joint bias and quadratic
conservativeness. For general binary inclusion sampling with positive marginals, including
certainty units, the same bias identity and both conjugate-power and quadratic conservative
corrections hold. All missing-pair sums are ordered and outcomes may have either sign. -/
def T14WholeStatement : Prop :=
  T14Statement.{0} ∧
  (∀ {U Ω : Type} [Fintype U] [Fintype Ω] (D : WholeSamplingDesign U Ω),
    (∀ i, 0 < samplingPi D i) → ∀ y : U → ℝ,
    samplingExpect D (samplingVarianceHT D y) =
      samplingVariance D (samplingTotal D y)+samplingMissingA D y ∧
    (∀ a b : U → U → ℝ,
      (∀ i j, i ≠ j ∧ samplingJoint D i j = 0 →
        0 < a i j ∧ 0 < b i j ∧ 1/a i j+1/b i j=1) →
      samplingVariance D (samplingTotal D y) ≤
        samplingExpect D (fun z => samplingVarianceHT D y z+samplingYoungCorrection D y a b z)) ∧
    samplingVariance D (samplingTotal D y) ≤
      samplingExpect D (fun z => samplingVarianceHT D y z+samplingQuadraticCorrection D y z))

end
end SAP.P013a
