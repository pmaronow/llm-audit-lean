import AronowAudit.P029.P029_Audit

/-!
# Wave1 blueprint, shared module: finite atomic laws as genuine measures (P029)

Shared infrastructure for the four P029 refutations T20 (`printed_ignorability_ordering`,
`printed_ignorability_ordering_all_profiles`) and T21 (`printed_conditional_sufficiency`,
`printed_marginal_sufficiency`). The existing finite certificates in `P029_Audit.lean`
(`ignorability_counterexample`, `marginal_independence_counterexample`,
`conditional_independence_counterexample`) are stated with finite sums `fE`, `fP`, `fCE`,
`FIndep`, `FCondIndep`, `FIV`. The held declarations are stated with measures `mP`, `mCE`,
`IndepFun`, `IVAssumptions`. The nodes below are the bridge (mapper map-P029-P044, "Shared
lemmas" 1 and 2).

This module has no `Target` of its own: its nodes are hypotheses of the `assemble` theorems
of the record blueprints `IgnorabilityOrderingBlueprint`, `IgnorabilityAllProfilesBlueprint`,
`ConditionalSufficiencyBlueprint` and `MarginalSufficiencyBlueprint`. Each node is proved
once, in `AronowAudit/P029/Wave1/FiniteMeasure/Nk.lean` as `theorem nk_proof : Nk`.

Referee fixes applied (ref1 and ref2, records 1-4): every node states
`[Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]` and `ValidLaw p` explicitly
(the signed-mass counterexample `p = (2,-1)` shows the independence nodes are false without
`ValidLaw p`, and a trivial sigma-algebra makes the integral node false without measurable
singletons); codomain measurable-singleton assumptions are kept as the referees asked.

Convention: a node whose proof needs earlier nodes takes them as explicit hypotheses
(`N3 : N1 → N2 → ...`), so every node can be proved independently and in parallel.
-/

namespace AronowAudit.P029.Wave1.FiniteMeasure

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

noncomputable section

/-- The atomic measure `A_p = ∑ᵢ ofReal(pᵢ) • δᵢ` of a finite law `p` (mapper, shared
lemma 1). For `ValidLaw p` it is a probability measure whose integrals and event masses are
the finite sums `fE p`, `fP p`. -/
def atomicMeasure {L : Type*} [Fintype L] [MeasurableSpace L] (p : L → ℝ) : Measure L :=
  ∑ i, ENNReal.ofReal (p i) • Measure.dirac i

/-- The normalized conditional finite law `p_x(i) = 1{X i = x} pᵢ / P_p(X = x)`
(mapper, shared lemma 2; node `atomic_normalized_restriction`). -/
def condLaw {L Y : Type*} [Fintype L] (p : L → ℝ) (X : L → Y) (x : Y) : L → ℝ :=
  fun i => if X i = x then p i / fP p (fun j => X j = x) else 0

/-- **Node FM-N1** (`atomic_operations_adapter`; mapper record 1, step 5 and shared lemma 1;
ref1 fix 1). For a valid finite law on a finite type with measurable singletons, the atomic
measure is a probability measure, every real function is integrable with integral `fE p v`,
event masses are `fP`, and normalized restricted means are `fCE`. -/
def N1 : Prop :=
  ∀ {L : Type} [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L] (p : L → ℝ),
    ValidLaw p →
      IsProbabilityMeasure (atomicMeasure p) ∧
      (∀ v : L → ℝ, Integrable v (atomicMeasure p) ∧ ∫ i, v i ∂(atomicMeasure p) = fE p v) ∧
      (∀ B : Set L, mP (atomicMeasure p) B = fP p (fun i => i ∈ B)) ∧
      (∀ (v : L → ℝ) (B : Set L), mCE (atomicMeasure p) v B = fCE p v (fun i => i ∈ B))

/-- **Node FM-N2** (`atomic_independence_adapter`; mapper shared lemma 2; ref1 fix 2, ref2 fix
1). Finite independence of a valid law gives measure-theoretic independence under the atomic
measure. Proof idea: preimages are finite unions of value fibres; sum the finite
factorization over the attained values. -/
def N2 : Prop :=
  ∀ {L A B : Type} [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (p : L → ℝ), ValidLaw p → ∀ (V : L → A) (W : L → B), FIndep p V W →
      IndepFun V W (atomicMeasure p)

/-- **Node FM-N3** (`atomic_iv_adapter`; mapper record 1, step 2 and shared lemma 2). The
finite five IV assumptions `FIV` give `IVAssumptions` for the atomic measure. Takes FM-N1 and
FM-N2 as hypotheses (measurability is automatic on a finite discrete domain; integrability
from finiteness; independence from FM-N2 and `IndepFun.symm`; masses and the first stage
from FM-N1). -/
def N3 : Prop :=
  N1 → N2 →
  ∀ {L X : Type} [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : L → ℝ) (U : L → PotentialUnit X) (Z : L → Bool),
      FIV p U Z → IVAssumptions (atomicMeasure p) U Z

/-- **Node FM-N4** (`atomic_normalized_restriction`; mapper record 3, shared lemma 2; ref1 fix
for record 3). Normalized restriction of an atomic measure to a positive-mass covariate
profile is the atomic measure of the normalized conditional law, which is a valid law. -/
def N4 : Prop :=
  ∀ {L Y : Type} [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    (p : L → ℝ), ValidLaw p → ∀ (X : L → Y) (x : Y), 0 < fP p (fun i => X i = x) →
      ValidLaw (condLaw p X x) ∧
      ENNReal.ofReal ((fP p (fun i => X i = x))⁻¹) • (atomicMeasure p).restrict {i | X i = x} =
        atomicMeasure (condLaw p X x)

/-- **Node FM-N5** (`conditional_finite_to_measure_independence`; mapper record 3, step 3;
ref1 and ref2 fixes for record 3: explicit `ValidLaw p` and finite measurable-singleton
domain). Finite conditional independence gives independence under the literal normalized
restricted atomic measure at each positive-mass profile. Takes FM-N2 and FM-N4. -/
def N5 : Prop :=
  N2 → N4 →
  ∀ {L A B Y : Type} [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (p : L → ℝ), ValidLaw p → ∀ (V : L → A) (W : L → B) (X : L → Y), FCondIndep p V W X →
      ∀ x : Y, 0 < fP p (fun i => X i = x) →
        IndepFun V W
          (ENNReal.ofReal ((fP p (fun i => X i = x))⁻¹) • (atomicMeasure p).restrict {i | X i = x})

/-- **Node FM-N6** (`atomic_wald_and_score`; mapper record 3, step 6, "the atomic
operations/IV bridge transfers ... mWald"). Population Wald ratios and compliance scores of
the atomic measure are the finite `fWald` and `fScore`, for every weight. Takes FM-N1 (both
sides are built from the same normalized means). -/
def N6 : Prop :=
  N1 →
  ∀ {L X : Type} [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    (p : L → ℝ), ValidLaw p → ∀ (U : L → PotentialUnit X) (Z : L → Bool),
      (∀ w : L → ℝ, mWald (atomicMeasure p) U Z w = fWald p U Z w) ∧
      (∀ x : X, scoreAt (atomicMeasure p) U x = fScore p U x)

end

end AronowAudit.P029.Wave1.FiniteMeasure
