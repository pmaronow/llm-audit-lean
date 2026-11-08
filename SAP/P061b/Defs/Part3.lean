import SAP.P061b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061b
open scoped BigOperators Classical

def T12Statement : Prop :=
  (∀ {Ω : Type} {N : ℕ} (D : AtomicDesign Ω) (g y : Schedule Ω N)
      (h : Fin N → ℝ → ℝ),
    (∀ i z, y i z = h i (g i z)) → ∀ d e : ℝ, 0 < N →
    (∀ i, 0 < exposureProbability D g i d) →
    (∀ i, 0 < exposureProbability D g i e) →
    (∀ i, exposureMean D g y i d = h i d ∧ exposureMean D g y i e = h i e ∧
      unitContrast D g y i d e = h i d - h i e) ∧
    averageContrast D g y d e = (N : ℝ)⁻¹ * ∑ i, (h i d - h i e)) ∧
  (∀ {Ω : Type} {N : ℕ} (D D' : AtomicDesign Ω) (g y : Schedule Ω N),
    GloballyStable g y → ∀ d e : ℝ, 0 < N →
    (∀ i, 0 < exposureProbability D g i d ∧ 0 < exposureProbability D g i e) →
    (∀ i, 0 < exposureProbability D' g i d ∧ 0 < exposureProbability D' g i e) →
    (∀ i, exposureMean D g y i d = exposureMean D' g y i d ∧
      exposureMean D g y i e = exposureMean D' g y i e) ∧
    averageContrast D g y d e = averageContrast D' g y d e) ∧
  (∀ {Ω : Type} {N : ℕ} (D : AtomicDesign Ω) (g y : Schedule Ω N),
    GloballyStable g y → ∀ (i : Fin N) (d : ℝ), 0 < exposureProbability D g i d →
    ∀ z, g i z = d → exposureMean D g y i d = y i z) ∧
  GloballyStable housemateAssignment housemateAssignment ∧
  (∀ D : AtomicDesign Household,
    (∀ i, 0 < exposureProbability D housemateAssignment i 1 ∧
      0 < exposureProbability D housemateAssignment i 0) →
    averageContrast D housemateAssignment housemateAssignment 1 0 = 1) ∧
  averageContrast bothOrNeither housemateAssignment housemateAssignment 1 0 = 1 ∧
  averageContrast independentHousehold housemateAssignment housemateAssignment 1 0 = 1

def T13Statement : Prop :=
  ∀ {Ω : Type} {N : ℕ} (D : AtomicDesign Ω) (g y : Schedule Ω N),
  (SupportStable D g y →
    (∀ (i : Fin N) (d : ℝ), 0 < exposureProbability D g i d →
      ∀ z, InSupport D z → g i z = d → exposureMean D g y i d = y i z) ∧
    (∀ (i : Fin N) (d e : ℝ), 0 < exposureProbability D g i d →
      0 < exposureProbability D g i e → ∀ z w,
      InSupport D z → InSupport D w → g i z = d → g i w = e →
      unitContrast D g y i d e = y i z - y i w) ∧
    ∃ y' : Schedule Ω N, GloballyStable g y' ∧
      (∀ i z, InSupport D z → y i z = y' i z) ∧
      ∀ A, observedEventProbability D y A = observedEventProbability D y' A) ∧
  (GloballyStable g y → SupportStable D g y) ∧
  (∀ y' : Schedule Ω N, (∀ i z, InSupport D z → y i z = y' i z) →
    ∀ A, observedEventProbability D y A = observedEventProbability D y' A) ∧
  (∀ L : (Ω × (Fin N → ℝ) → Prop) → ℝ,
    (∃ w : Schedule Ω N, SupportStable D g w ∧
      ∀ A, observedEventProbability D w A = L A) ↔
    (∃ w : Schedule Ω N, GloballyStable g w ∧
      ∀ A, observedEventProbability D w A = L A))

def T14Statement : Prop :=
  averageExposureMean oneTreated ownAssignment housemateAssignment 1 = 0 ∧
  averageExposureMean oneTreated ownAssignment housemateAssignment 0 = 1 ∧
  averageContrast oneTreated ownAssignment housemateAssignment 1 0 = -1 ∧
  SupportStable oneTreated ownAssignment housemateAssignment ∧
  ¬GloballyStable ownAssignment housemateAssignment ∧
  averageContrast bothOrNeither ownAssignment housemateAssignment 1 0 = 1 ∧
  averageContrast independentHousehold ownAssignment housemateAssignment 1 0 = 0 ∧
  ownAssignment 0 (1, 0) = 1 ∧ ownAssignment 0 (1, 1) = 1 ∧
  housemateAssignment 0 (1, 0) = 0 ∧ housemateAssignment 0 (1, 1) = 1 ∧
  ¬InSupport oneTreated (1, 1)

def T15Statement : Prop :=
  (averageContrast oneTreated ownAssignment attenuatedOutcome 1 0 = 1 ∧
    averageContrast bothOrNeither ownAssignment attenuatedOutcome 1 0 = 0 ∧
    SupportStable oneTreated ownAssignment attenuatedOutcome ∧
    SupportStable bothOrNeither ownAssignment attenuatedOutcome ∧
    ¬GloballyStable ownAssignment attenuatedOutcome ∧
    averageContrast oneTreated ownAssignment amplifiedOutcome 1 0 = 0 ∧
    averageContrast bothOrNeither ownAssignment amplifiedOutcome 1 0 = 1 ∧
    SupportStable oneTreated ownAssignment amplifiedOutcome ∧
    SupportStable bothOrNeither ownAssignment amplifiedOutcome ∧
    ¬GloballyStable ownAssignment amplifiedOutcome) ∧
  ((∀ i : Fin 2,
      exposureProbability (oneVersionTreated 1 (Or.inl rfl)) versionCategory i 1 = 1/2 ∧
      exposureProbability (oneVersionTreated 1 (Or.inl rfl)) versionCategory i 0 = 1/2 ∧
      exposureProbability (oneVersionTreated 2 (Or.inr rfl)) versionCategory i 1 = 1/2 ∧
      exposureProbability (oneVersionTreated 2 (Or.inr rfl)) versionCategory i 0 = 1/2) ∧
    averageContrast (oneVersionTreated 1 (Or.inl rfl)) versionCategory versionResponse 1 0 = 1 ∧
    averageContrast (oneVersionTreated 2 (Or.inr rfl)) versionCategory versionResponse 1 0 = 2 ∧
    SupportStable (oneVersionTreated 1 (Or.inl rfl)) versionCategory versionResponse ∧
    SupportStable (oneVersionTreated 2 (Or.inr rfl)) versionCategory versionResponse ∧
    ¬GloballyStable versionCategory versionResponse ∧
    ∀ i z w, (if i = 0 then z.1 else z.2) = (if i = 0 then w.1 else w.2) →
      versionResponse i z = versionResponse i w)

end SAP.P061b
