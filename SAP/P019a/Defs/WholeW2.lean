import Mathlib
import SAP.P019a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a

open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory

noncomputable section
open Classical
universe u

/-- The observable record for a list with `J` control items. The baseline count is
at most `J`, and the reported count is at most `J + 1`. The respondent space itself
need not be finite. Coordinates are W, X, Y, Z, V, in that order. -/
abbrev T11Observation (J : ℕ) :=
  Fin (J + 1) × Bool × Bool × Bool × Fin (J + 2)

namespace T11Observation

def W {J : ℕ} (t : T11Observation J) : ℕ := t.1.val
def X {J : ℕ} (t : T11Observation J) : Bool := t.2.1
def Y {J : ℕ} (t : T11Observation J) : Bool := t.2.2.1
def Z {J : ℕ} (t : T11Observation J) : Bool := t.2.2.2.1
def V {J : ℕ} (t : T11Observation J) : ℕ := t.2.2.2.2.val

def cell {J : ℕ} (z y : Bool) (t : T11Observation J) : Prop :=
  t.Z = z ∧ t.Y = y

end T11Observation

/-- A probability law and its measurable, bounded count/binary observations.
Using a finite observable range expresses the fixed finite list assumption;
there is no finiteness assumption on the underlying probability space. -/
structure T11Population (J : ℕ) (Ω : Type u) [MeasurableSpace Ω] where
  law : Measure Ω
  probability : IsProbabilityMeasure law
  observe : Ω → T11Observation J
  measurable_observe : Measurable observe

instance {J : ℕ} {Ω : Type u} [MeasurableSpace Ω] (S : T11Population J Ω) :
    IsProbabilityMeasure S.law := S.probability

/-- The finite law of a measurable finite-valued observation. All fibers have
finite measure, so no use of `toReal` at infinity is involved. -/
def wholeFiniteLaw {Ω : Type u} [MeasurableSpace Ω] {A : Type*} [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Ω → A) (hf : Measurable f) : FiniteLaw A where
  mass := fun a => P.real (f ⁻¹' {a})
  nonneg := fun _ => measureReal_nonneg
  total := by
    have h := sum_measureReal_preimage_singleton (μ := P) (Finset.univ : Finset A)
      (fun a _ => hf (measurableSet_singleton a))
    simpa using h

namespace T11Population

variable {J : ℕ} {Ω : Type u} [MeasurableSpace Ω]

/-- Expectation of a function of the bounded observation. Every such function
has finite range and is integrable. -/
def mean (S : T11Population J Ω) (f : T11Observation J → ℝ) : ℝ :=
  ∫ ω, f (S.observe ω) ∂S.law

def prob (S : T11Population J Ω) (D : T11Observation J → Prop) : ℝ :=
  S.law.real {ω | D (S.observe ω)}

/-- Event conditional expectation. Its uses in the whole statement have
positive event probability; all the integrands have finite range. -/
def ce (S : T11Population J Ω) (f : T11Observation J → ℝ)
    (D : T11Observation J → Prop) : ℝ :=
  S.mean (fun t => if D t then f t else 0) / S.prob D

def variance (S : T11Population J Ω) (f : T11Observation J → ℝ) : ℝ :=
  S.mean (fun t => f t ^ 2) - (S.mean f) ^ 2

def cv (S : T11Population J Ω) (f : T11Observation J → ℝ)
    (D : T11Observation J → Prop) : ℝ :=
  S.ce (fun t => f t ^ 2) D - (S.ce f D) ^ 2

def mu (S : T11Population J Ω) : ℝ := S.prob (fun t => t.X = true)

def monotone (S : T11Population J Ω) : Prop :=
  ∀ᵐ ω ∂S.law, (S.observe ω).Y = true → (S.observe ω).X = true

def noLiarsDesign (S : T11Population J Ω) : Prop :=
  ∀ᵐ ω ∂S.law,
    ((S.observe ω).V : ℝ) = ((S.observe ω).W : ℝ) +
      bitVal (S.observe ω).X * bitVal (S.observe ω).Z

/-- Factorization against all functions of (W,X,Y), equivalent here to the
independence of that finite-valued triple and the binary treatment. -/
def treatmentIndependent (S : T11Population J Ω) : Prop :=
  ∀ (f : ℕ → Bool → Bool → ℝ) (z : Bool),
    S.mean (fun t => if t.Z = z then f t.W t.X t.Y else 0) =
      S.prob (fun t => t.Z = z) * S.mean (fun t => f t.W t.X t.Y)

/-- Assumption 4, including existence of the four conditioning distributions. -/
def nondegenerate (S : T11Population J Ω) : Prop :=
  (∀ z y, 0 < S.prob (T11Observation.cell z y) ∧
    0 < S.cv (fun t => (t.V : ℝ)) (T11Observation.cell z y)) ∧
  0 < S.variance (fun t => bitVal t.Z) ∧
  0 < S.variance (fun t => bitVal t.Y)

def standing (S : T11Population J Ω) : Prop :=
  S.monotone ∧ S.noLiarsDesign ∧ S.treatmentIndependent ∧ S.nondegenerate

/-- Exact observable pushforward, using the existing finite-study definitions. -/
def finiteStudy (S : T11Population J Ω) : Study (T11Observation J) where
  law := wholeFiniteLaw S.law S.observe S.measurable_observe
  W := T11Observation.W
  X := T11Observation.X
  Y := T11Observation.Y
  Z := T11Observation.Z
  V := T11Observation.V

/-- The iid law of n respondents on the original probability space. -/
def sampleLaw (S : T11Population J Ω) (n : ℕ) : Measure (Fin n → Ω) :=
  Measure.pi (fun _ : Fin n => S.law)

def sampleObservations (S : T11Population J Ω) {n : ℕ} (s : Fin n → Ω) :
    Fin n → T11Observation J := fun i => S.observe (s i)

end T11Population

/-- Natural domain of the printed interval formulas: a nonempty sample, both
negative-response cells large enough for variance with divisor N-1, and positive
empirical denominators. This imposes no finite-sample assumption on the model. -/
def T11FiniteDomain {A : Type*} [Fintype A] (S : Study A) {n : ℕ}
    (s : Fin n → A) : Prop :=
  0 < n ∧ 2 ≤ S.cellCount s true false ∧ 2 ≤ S.cellCount s false false ∧
    S.ybar s < 1 ∧ 0 < S.gammaHat s ∧ S.gammaHat s < 1

namespace T11Population

variable {J : ℕ} {Ω : Type u} [MeasurableSpace Ω]

def intervalDomain (S : T11Population J Ω) {n : ℕ} (s : Fin n → Ω) : Prop :=
  T11FiniteDomain S.finiteStudy (S.sampleObservations s)

/-- On `intervalDomain` this is exactly ybar + (1-ybar)(vbar_10-vbar_00).
The completion arguments have no effect there. -/
def estimate (S : T11Population J Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) : ℝ :=
  S.finiteStudy.muHat (S.sampleObservations s) c1 c0

/-- On `intervalDomain` this is the paper's plug-in variance with cell sample
variances of divisor N-1. The completion arguments have no effect there. -/
def varianceEstimate (S : T11Population J Ω) {n : ℕ} (s : Fin n → Ω)
    (c1 c0 cV : ℝ) : ℝ :=
  S.finiteStudy.muVarianceHat (S.sampleObservations s) c1 c0 cV

end T11Population

/-- P019-T11; Lemma 1 proof and equation (2), p. 48; Corollary 1, p. 49;
Lemma 2 proof, p. 62; Proposition 2 proof, p. 64.
For any probability space with the standing bounded count and binary observations,
the corrected treatment-arm means, affirmative-response sensitive mean, and
affirmative-cell list-mean shift hold under their respective stated assumptions.
Under Assumptions 1-4, the printed Wald interval is defined with probability
tending to one and its coverage tends to 1-alpha for every 0 < alpha < 1,
independently of fixed completions outside its domain. No quantile-set premise
is needed. The correction in (d) labels the negative responders and has no
independent mathematical assertion. -/
def T11WholeStatement : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (J : ℕ) (S : T11Population J Ω),
    (S.noLiarsDesign → S.treatmentIndependent →
      0 < S.prob (fun t => t.Z = false) → 0 < S.prob (fun t => t.Z = true) →
      S.ce (fun t => (t.V : ℝ)) (fun t => t.Z = true) =
        S.mean (fun t => (t.W : ℝ)) + S.mu ∧
      S.ce (fun t => (t.V : ℝ)) (fun t => t.Z = false) =
        S.mean (fun t => (t.W : ℝ)) ∧
      S.ce (fun t => (t.V : ℝ)) (fun t => t.Z = true) -
        S.ce (fun t => (t.V : ℝ)) (fun t => t.Z = false) = S.mu) ∧
    (S.monotone → 0 < S.prob (fun t => t.Y = true) →
      S.ce (fun t => bitVal t.X) (fun t => t.Y = true) = 1) ∧
    (S.standing →
      Tendsto (fun n : ℕ => (S.sampleLaw n).real {s | S.intervalDomain s})
        atTop (nhds 1) ∧
      ∀ α : ℝ, 0 < α → α < 1 → ∀ c1 c0 cV : ℝ,
        Tendsto (fun n : ℕ => (S.sampleLaw n).real {s |
          S.intervalDomain s ∧ |S.estimate s c1 c0 - S.mu| ≤
            normalQuantile (1 - α / 2) * Real.sqrt (S.varianceEstimate s c1 c0 cV)})
          atTop (nhds (1 - α))) ∧
    (S.monotone → S.noLiarsDesign → S.treatmentIndependent →
      0 < S.prob (T11Observation.cell false true) →
      0 < S.prob (T11Observation.cell true true) →
      S.ce (fun t => (t.V : ℝ)) (T11Observation.cell true true) =
        S.ce (fun t => (t.V : ℝ)) (T11Observation.cell false true) + 1)

end
end SAP.P019a
