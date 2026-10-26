import AronowAudit.P029.P029_Audit

/-!
# Finite atomic laws as measures (P029)

Finite sums `fE`, `fP`, `fCE`, `FIndep`, `FCondIndep`, and `FIV` are related to
measure-theoretic integrals, `mP`, `mCE`, `IndepFun`, and `IVAssumptions`.
These identities transfer the finite counterexamples for P029-T20 and P029-T21
to probability measures.

The assumptions `[Fintype L]`, `[MeasurableSpace L]`,
`[MeasurableSingletonClass L]`, and `ValidLaw p` are explicit. The signed masses
`p = (2,-1)` invalidate the independence statements without `ValidLaw p`, and
a trivial sigma-algebra invalidates the integral statement without measurable
singletons. The independence statements also assume measurable singletons in
the codomains.

Dependencies between the propositions are explicit hypotheses, as in
`N3 : N1 → N2 → ...`.
-/

namespace AronowAudit.P029.Wave1.FiniteMeasure

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

noncomputable section

/-- The atomic measure `A_p = ∑ᵢ ofReal(pᵢ) • δᵢ` of a finite law `p`.
For `ValidLaw p` it is a probability measure whose integrals and event masses are
the finite sums `fE p`, `fP p`. -/
def atomicMeasure {L : Type*} [Fintype L] [MeasurableSpace L] (p : L → ℝ) : Measure L :=
  ∑ i, ENNReal.ofReal (p i) • Measure.dirac i

/-- The normalized conditional finite law
`p_x(i) = 1{X i = x} pᵢ / P_p(X = x)`. -/
def condLaw {L Y : Type*} [Fintype L] (p : L → ℝ) (X : L → Y) (x : Y) : L → ℝ :=
  fun i => if X i = x then p i / fP p (fun j => X j = x) else 0

/-- For a valid finite law on a finite type with measurable singletons, the atomic
measure is a probability measure, every real function is integrable with integral `fE p v`,
event masses are `fP`, and normalized restricted means are `fCE`. -/
def N1 : Prop :=
  ∀ {L : Type} [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L] (p : L → ℝ),
    ValidLaw p →
      IsProbabilityMeasure (atomicMeasure p) ∧
      (∀ v : L → ℝ, Integrable v (atomicMeasure p) ∧ ∫ i, v i ∂(atomicMeasure p) = fE p v) ∧
      (∀ B : Set L, mP (atomicMeasure p) B = fP p (fun i => i ∈ B)) ∧
      (∀ (v : L → ℝ) (B : Set L), mCE (atomicMeasure p) v B = fCE p v (fun i => i ∈ B))

/-- Finite independence of a valid law gives measure-theoretic independence under the atomic
measure. Proof idea: preimages are finite unions of value fibres; sum the finite
factorization over the attained values. -/
def N2 : Prop :=
  ∀ {L A B : Type} [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (p : L → ℝ), ValidLaw p → ∀ (V : L → A) (W : L → B), FIndep p V W →
      IndepFun V W (atomicMeasure p)

/-- The finite five IV assumptions `FIV` give `IVAssumptions` for the atomic measure. Takes `N1` and
`N2` as hypotheses (measurability is automatic on a finite discrete domain; integrability
from finiteness; independence from `N2` and `IndepFun.symm`; masses and the first stage
from `N1`). -/
def N3 : Prop :=
  N1 → N2 →
  ∀ {L X : Type} [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : L → ℝ) (U : L → PotentialUnit X) (Z : L → Bool),
      FIV p U Z → IVAssumptions (atomicMeasure p) U Z

/-- Normalized restriction of an atomic measure to a positive-mass covariate
profile is the atomic measure of the normalized conditional law, which is a valid law. -/
def N4 : Prop :=
  ∀ {L Y : Type} [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    (p : L → ℝ), ValidLaw p → ∀ (X : L → Y) (x : Y), 0 < fP p (fun i => X i = x) →
      ValidLaw (condLaw p X x) ∧
      ENNReal.ofReal ((fP p (fun i => X i = x))⁻¹) • (atomicMeasure p).restrict {i | X i = x} =
        atomicMeasure (condLaw p X x)

/-- Finite conditional independence gives independence under the literal normalized
restricted atomic measure at each positive-mass profile. Takes `N2` and `N4`. -/
def N5 : Prop :=
  N2 → N4 →
  ∀ {L A B Y : Type} [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (p : L → ℝ), ValidLaw p → ∀ (V : L → A) (W : L → B) (X : L → Y), FCondIndep p V W X →
      ∀ x : Y, 0 < fP p (fun i => X i = x) →
        IndepFun V W
          (ENNReal.ofReal ((fP p (fun i => X i = x))⁻¹) • (atomicMeasure p).restrict {i | X i = x})

/-- Population Wald ratios and compliance scores of
the atomic measure are the finite `fWald` and `fScore`, for every weight. Takes `N1` (both
sides are built from the same normalized means). -/
def N6 : Prop :=
  N1 →
  ∀ {L X : Type} [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    (p : L → ℝ), ValidLaw p → ∀ (U : L → PotentialUnit X) (Z : L → Bool),
      (∀ w : L → ℝ, mWald (atomicMeasure p) U Z w = fWald p U Z w) ∧
      (∀ x : X, scoreAt (atomicMeasure p) U x = fScore p U x)

end

end AronowAudit.P029.Wave1.FiniteMeasure
