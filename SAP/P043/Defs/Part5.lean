import SAP.P043.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P043

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
universe u v

/-! Crossed-margin weights and conditional effects for bounded integer doses. -/

def doseIncrement {Ω : Type u} (m : IVModel Ω) (j : ℕ) (i : Ω) : ℝ :=
  m.response j i - m.response (j-1) i

def crossing {Ω : Type u} (m : IVModel Ω) (j : ℕ) (i : Ω) : ℝ :=
  indicator (m.knowledge false i < j ∧ j ≤ m.knowledge true i)

def signedCrossing {Ω : Type u} (m : IVModel Ω) (j : ℕ) (i : Ω) : ℝ :=
  indicator (j ≤ m.knowledge true i) - indicator (j ≤ m.knowledge false i)

def marginProb {Ω : Type u} [Fintype Ω] (P : Population Ω) (m : IVModel Ω) (j : ℕ) : ℝ :=
  eventProb P (fun i => m.knowledge false i < j ∧ j ≤ m.knowledge true i)

def marginWeight {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (m : IVModel Ω) (j : ℕ) : ℝ := marginProb P m j / firstStage P p m

def marginEffect {Ω : Type u} [Fintype Ω] (P : Population Ω) (m : IVModel Ω) (j : ℕ) : ℝ :=
  eventMean P (fun i => m.knowledge false i < j ∧ j ≤ m.knowledge true i) (doseIncrement m j)

def IVPopulationContrastClaims {Ω : Type u} [Fintype Ω] (P : Population Ω) (p : ℝ) (m : IVModel Ω) : Prop :=
    firstStage P p m = mean P (fun i => (m.knowledge true i : ℝ) - m.knowledge false i) ∧
    ivReducedForm P p m = mean P (fun i => m.response (m.knowledge true i) i -
      m.response (m.knowledge false i) i)

def IVCovarianceClaims {Ω : Type u} [Fintype Ω] (P : Population Ω) (p : ℝ) (m : IVModel Ω) : Prop :=
    covariance P p (fun z _ => assignment z) (ivKnowledge m) = p*(1-p)*firstStage P p m ∧
    covariance P p (fun z _ => assignment z) (ivOutcome m) = p*(1-p)*ivReducedForm P p m ∧
    (firstStage P p m ≠ 0 →
      covariance P p (fun z _ => assignment z) (ivOutcome m) /
        covariance P p (fun z _ => assignment z) (ivKnowledge m) = ivRatio P p m)

def IVSignedUnitClaims {Ω : Type u} (m : IVModel Ω) (J : ℕ) (i : Ω) : Prop :=
    m.response (m.knowledge true i) i - m.response (m.knowledge false i) i =
      ∑ r ∈ range J, signedCrossing m (r+1) i * doseIncrement m (r+1) i ∧
    (m.knowledge true i : ℝ) - m.knowledge false i =
      ∑ r ∈ range J, signedCrossing m (r+1) i

def IVMonotoneUnitClaims {Ω : Type u} (m : IVModel Ω) (J : ℕ) (i : Ω) : Prop :=
    m.response (m.knowledge true i) i - m.response (m.knowledge false i) i =
      ∑ r ∈ range J, crossing m (r+1) i * doseIncrement m (r+1) i ∧
    (m.knowledge true i : ℝ) - m.knowledge false i =
      ∑ r ∈ range J, crossing m (r+1) i

def IVMarginTotalClaims {Ω : Type u} [Fintype Ω] (P : Population Ω) (p : ℝ) (m : IVModel Ω) (J : ℕ) : Prop :=
    ivReducedForm P p m = ∑ r ∈ range J, mean P (fun i => crossing m (r+1) i * doseIncrement m (r+1) i) ∧
    firstStage P p m = ∑ r ∈ range J, marginProb P m (r+1)

def IVMarginAverageClaims {Ω : Type u} [Fintype Ω] (P : Population Ω) (p : ℝ) (m : IVModel Ω) (J : ℕ) : Prop :=
    (∀ j, 0 ≤ marginWeight P p m j) ∧
    (∑ r ∈ range J, marginWeight P p m (r+1)) = 1 ∧
    ivRatio P p m = ∑ r ∈ (range J).filter (fun r => 0 < marginProb P m (r+1)),
      marginWeight P p m (r+1) * marginEffect P m (r+1)

/-- Finite-population corrected IV formula and the signed identities exported with it. -/
def IVRepairConclusions {Ω : Type u} [Fintype Ω]
    (P : Population Ω) (p : ℝ) (m : IVModel Ω) (J : ℕ) : Prop :=
  IVPopulationContrastClaims P p m ∧ IVCovarianceClaims P p m ∧
  (∀ i, IVMonotoneUnitClaims m J i) ∧ IVMarginTotalClaims P p m J ∧
  IVMarginAverageClaims P p m J ∧
  (∀ (m' : IVModel Ω) J' i, m'.knowledge false i ≤ J' ∧ m'.knowledge true i ≤ J' →
    IVSignedUnitClaims m' J' i) ∧
  (∀ i j, ¬ increaser m i → crossing m j i = 0) ∧
  (∀ i j, signedCrossing m j i ∈ ({-1,0,1} : Finset ℝ) ∧
    signedCrossing m j i = crossing m j i) ∧
  (∀ (m' : IVModel Ω) i j, m'.knowledge true i < j ∧ j ≤ m'.knowledge false i →
    signedCrossing m' j i = -1)

/-- The finite-population specialization, under individual monotonicity and
positive first stage. Conditional increments occur only at positive-probability margins. -/
def T5Statement : Prop :=
  ∀ {Ω : Type u} [Fintype Ω] (P : Population Ω) (p : ℝ), 0 < p ∧ p < 1 →
    ∀ (m : IVModel Ω) (J : ℕ),
    (∀ i, m.knowledge false i ≤ J ∧ m.knowledge true i ≤ J) →
    (∀ i, m.knowledge false i ≤ m.knowledge true i) →
    0 < mean P (fun i => (m.knowledge true i : ℝ) - m.knowledge false i) →
    IVRepairConclusions P p m J

end
end SAP.P043
