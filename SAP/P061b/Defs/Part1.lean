import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061b
open scoped BigOperators Classical Topology

/-- A normalized atomic design on all feasible assignments, including zero-mass ones. -/
structure AtomicDesign (Ω : Type) where
  p : Ω → ℝ
  nonneg : ∀ z, 0 ≤ p z
  summable : Summable p
  total : (∑' z, p z) = 1

abbrev Schedule (Ω : Type) (N : ℕ) := Fin N → Ω → ℝ

def InSupport {Ω : Type} (D : AtomicDesign Ω) (z : Ω) : Prop := 0 < D.p z

noncomputable def eventProbability {Ω : Type} (D : AtomicDesign Ω) (A : Ω → Prop) : ℝ :=
  ∑' z, if A z then D.p z else 0

/-- A signed mean is interpreted only when the corresponding absolute moment exists. -/
noncomputable def designMean {Ω : Type} (D : AtomicDesign Ω) (X : Ω → ℝ) : ℝ :=
  ∑' z, D.p z * X z

def HasFirstMoment {Ω : Type} (D : AtomicDesign Ω) (X : Ω → ℝ) : Prop :=
  Summable (fun z => D.p z * |X z|)

noncomputable def exposureProbability {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Schedule Ω N) (i : Fin N) (d : ℝ) : ℝ :=
  eventProbability D (fun z => g i z = d)

def PositiveExposure {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Schedule Ω N) (d : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ exposureProbability D g i d

def ExposureMoment {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y : Schedule Ω N) (d : ℝ) : Prop :=
  ∀ i, HasFirstMoment D (fun z => if g i z = d then y i z else 0)

noncomputable def exposureMean {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y : Schedule Ω N) (i : Fin N) (d : ℝ) : ℝ :=
  designMean D (fun z => if g i z = d then y i z else 0) / exposureProbability D g i d

noncomputable def averageExposureMean {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y : Schedule Ω N) (d : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, exposureMean D g y i d

noncomputable def unitContrast {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y : Schedule Ω N) (i : Fin N) (d e : ℝ) : ℝ :=
  exposureMean D g y i d - exposureMean D g y i e

noncomputable def averageContrast {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y : Schedule Ω N) (d e : ℝ) : ℝ :=
  averageExposureMean D g y d - averageExposureMean D g y e

noncomputable def htMean {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y : Schedule Ω N) (d : ℝ) (z : Ω) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, (if g i z = d then y i z else 0) / exposureProbability D g i d

noncomputable def htDifference {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y : Schedule Ω N) (d e : ℝ) (z : Ω) : ℝ :=
  htMean D g y d z - htMean D g y e z

def SupportStable {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y : Schedule Ω N) : Prop :=
  ∀ i z w, InSupport D z → InSupport D w → g i z = g i w → y i z = y i w

def GloballyStable {Ω : Type} {N : ℕ} (g y : Schedule Ω N) : Prop :=
  ∀ i z w, g i z = g i w → y i z = y i w

noncomputable def observedEventProbability {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (y : Schedule Ω N) (A : Ω × (Fin N → ℝ) → Prop) : ℝ :=
  eventProbability D (fun z => A (z, fun i => y i z))

noncomputable def jointExposureProbability {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Schedule Ω N) (i j : Fin N) (d e : ℝ) : ℝ :=
  eventProbability D (fun z => g i z = d ∧ g j z = e)

noncomputable def designVariance {Ω : Type} (D : AtomicDesign Ω) (X : Ω → ℝ) : ℝ :=
  designMean D (fun z => (X z - designMean D X)^2)

noncomputable def designCovariance {Ω : Type} (D : AtomicDesign Ω) (X Y : Ω → ℝ) : ℝ :=
  designMean D (fun z => (X z - designMean D X) * (Y z - designMean D Y))

/-- Fixed-denominator exposed sum; it is the sample mean when the exposed count is n. -/
noncomputable def exposedMean {Ω : Type} {N : ℕ} (g y : Schedule Ω N)
    (d : ℝ) (n : ℕ) (z : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, if g i z = d then y i z else 0

def UniformFixedCount {N : ℕ} (D : AtomicDesign (Fin N → Fin 2)) (n : ℕ) : Prop :=
  ∀ z, D.p z = if (Finset.univ.filter (fun i => z i = 1)).card = n then
    (Nat.choose N n : ℝ)⁻¹ else 0

noncomputable def exposureIndicator {Ω : Type} {N : ℕ} (g : Schedule Ω N)
    (i : Fin N) (d : ℝ) (z : Ω) : ℝ := if g i z = d then 1 else 0

def EventIndependent {Ω A B : Type} (D : AtomicDesign Ω) (X : Ω → A) (Y : Ω → B) : Prop :=
  ∀ E : A → Prop, ∀ F : B → Prop,
    eventProbability D (fun z => E (X z) ∧ F (Y z)) =
      eventProbability D (fun z => E (X z)) * eventProbability D (fun z => F (Y z))

/-- Equality of conditional and unconditional prediction means at every positive indicator cell. -/
def MeanIndependent {Ω : Type} (D : AtomicDesign Ω) (F I : Ω → ℝ) : Prop :=
  ∀ b : ℝ, 0 < eventProbability D (fun z => I z = b) →
    designMean D (fun z => if I z = b then F z else 0) /
      eventProbability D (fun z => I z = b) = designMean D F

end SAP.P061b
