import Mathlib
import SAP.P047.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace SAP.P047

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

/-- Uniform (0,1); changing the included endpoint changes no mass. -/
def uniform01 : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)

instance uniform01_probability : IsProbabilityMeasure uniform01 := by
  constructor
  simp [uniform01, Real.volume_Ioc]

/-- Conditional factorization for every test of the pair of potential outcomes. -/
def JointIgnorable (L : CausalLaw) : Prop :=
  ∀ (a : Bool) (f : ℝ × ℝ → ℝ), Measurable f →
    Integrable (fun u => f (potential false u, potential true u)) L.measure →
    L.measure[fun u => arm a u * f (potential false u, potential true u) |
      covariateSigma] =ᵐ[L.measure]
      fun u => armPropensity L.propensity a u *
        (L.measure[fun v => f (potential false v, potential true v) |
          covariateSigma]) u

/-- The unrestricted, binary-outcome model with uniform covariate and common
overlap [1/4,3/4]. Procedures below are not supplied with the propensity. -/
def UnknownModel (L : CausalLaw) : Prop :=
  L.measure.map covariate = uniform01 ∧ JointIgnorable L ∧
    (∀ a, ∀ᵐ u ∂L.measure, potential a u = 0 ∨ potential a u = 1) ∧
    (∀ᵐ u ∂L.measure, (1 / 4 : ℝ) ≤ L.propensity (covariate u) ∧
      L.propensity (covariate u) ≤ 3 / 4)

abbrev ObservedUnit := ℝ × Bool × ℝ

def observedSample (n : ℕ) (s : ℕ → UnitData) : Fin n → ObservedUnit :=
  fun i => (covariate (s i.val), (s i.val).2.1, observed (s i.val))

def fairBool : Measure Bool :=
  bernoulliMeasure true false ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩

instance fairBool_probability : IsProbabilityMeasure fairBool := by
  unfold fairBool
  infer_instance

/-- The single fixed law S: independent uniform W, fair A and fair Y(1),
with Y(0)=0. This definition specifies the full population distribution. -/
def baselineLaw : Measure UnitData :=
  (uniform01.prod (fairBool.prod fairBool)).map
    (fun x => (x.1, x.2.1, (0, if x.2.2 then (1 : ℝ) else 0)))

instance baselineLaw_probability : IsProbabilityMeasure baselineLaw := by
  unfold baselineLaw
  infer_instance

/-- Worst-case weak error, allowing an independent random seed with law Q.
The inserted zero and the probability bounds keep the supremum finite. -/
def randRisk {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q]
    (E : (n : ℕ) → ((Fin n → ObservedUnit) × R) → ℝ) (n : ℕ) (η : ℝ) : ℝ :=
  sSup (insert (0 : ℝ) {r | ∃ L : CausalLaw, UnknownModel L ∧
    r = ((sampleLaw L.measure).prod Q).real
      {z | η ≤ |E n (observedSample n z.1, z.2) - ate L|}})

def randStrictRisk {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q]
    (E : (n : ℕ) → ((Fin n → ObservedUnit) × R) → ℝ) (n : ℕ) (η : ℝ) : ℝ :=
  sSup (insert (0 : ℝ) {r | ∃ L : CausalLaw, UnknownModel L ∧
    r = ((sampleLaw L.measure).prod Q).real
      {z | η < |E n (observedSample n z.1, z.2) - ate L|}})

/-- Worst-case interval coverage; the inserted one keeps the infimum defined. -/
def randCoverage {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q]
    (lo hi : (n : ℕ) → ((Fin n → ObservedUnit) × R) → EReal) (n : ℕ) : ℝ :=
  sInf (insert (1 : ℝ) {r | ∃ L : CausalLaw, UnknownModel L ∧
    r = ((sampleLaw L.measure).prod Q).real
      {z | lo n (observedSample n z.1, z.2) ≤ (ate L : EReal) ∧
        (ate L : EReal) ≤ hi n (observedSample n z.1, z.2)}})

/-- For finite ordered endpoints this is precisely width > 1/6. Writing it
without subtraction also treats unbounded and empty intervals. -/
def widthProb {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q]
    (lo hi : (n : ℕ) → ((Fin n → ObservedUnit) × R) → EReal) (n : ℕ) : ℝ :=
  ((sampleLaw baselineLaw).prod Q).real
    {z | lo n (observedSample n z.1, z.2) + ((1 / 6 : ℝ) : EReal) <
      hi n (observedSample n z.1, z.2)}

/-- The finite minimax and asymptotic impossibility conclusions, including
independent randomization and the fixed-law interval lower bound. -/
def T3Statement : Prop :=
  ∀ {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q],
    (∀ E : (n : ℕ) → ((Fin n → ObservedUnit) × R) → ℝ,
      (∀ n, Measurable (E n)) →
        (∀ n : ℕ, 1 ≤ n → (1 / 2 : ℝ) ≤ randRisk Q E n (1 / 12)) ∧
        (∃ η : ℝ, 0 < η ∧
          0 < Filter.limsup (fun n => randStrictRisk Q E n η) atTop)) ∧
    (∀ lo hi : (n : ℕ) → ((Fin n → ObservedUnit) × R) → EReal,
      (∀ n, Measurable (lo n)) → (∀ n, Measurable (hi n)) →
      ∀ α : ℝ, 0 < α → α < 1 / 2 →
        1 - α ≤ Filter.liminf (randCoverage Q lo hi) atTop →
        (1 - 2 * α ≤ Filter.liminf (widthProb Q lo hi) atTop) ∧ 0 < 1 - 2 * α)

end

end SAP.P047
