import SAP.P009a.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P009a

open Filter MeasureTheory
open scoped BigOperators Topology Classical

noncomputable section

structure ExperimentSequence where
  N : ℕ → ℕ
  positive : ∀ t, 0 < N t
  grows : Tendsto N atTop atTop
  experiment : (t : ℕ) → FiniteExperiment (N t)

def sampleSize (S : ExperimentSequence) (t : ℕ) : ℝ := S.N t

def SequenceRegularity (S : ExperimentSequence) (k q s : ℝ) : Prop :=
  ∀ t, Regularity (S.experiment t) k q s

def SparseDependence (S : ExperimentSequence) : Prop :=
  Tendsto (fun t => averageDependence (S.experiment t) / sampleSize S t) atTop (nhds 0)

def vanishingRelativeTo (f g : ℕ → ℝ) : Prop := Tendsto (fun t => f t / g t) atTop (nhds 0)

def boundedRelativeTo (f g : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ᶠ t in atTop, |f t| ≤ C * |g t|

def ConvergesInProbability (S : ExperimentSequence) (X : (t : ℕ) → TreatmentVector (S.N t) → ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fun t => probability (S.experiment t).design (fun z => ε < |X t z|))
    atTop (nhds 0)

def VarianceConservative (S : ExperimentSequence) (Vhat : (t : ℕ) → TreatmentVector (S.N t) → ℝ) : Prop :=
  ∃ L : ℝ → ℝ,
    (∀ ε > 0, Tendsto (fun t => probability (S.experiment t).design (fun z =>
      sampleSize S t / averageDependence (S.experiment t) *
        (Vhat t z - variance (S.experiment t).design (htEstimate (S.experiment t))) ≤ -ε))
      atTop (nhds (L ε))) ∧ Tendsto L (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

def EventuallyPositiveLowerBound (a : ℕ → ℝ) : Prop :=
  ∃ c > 0, ∀ᶠ t in atTop, c ≤ a t

def ConvergesInLaw (S : ExperimentSequence) (X : (t : ℕ) → TreatmentVector (S.N t) → ℝ)
    (G : ℝ → ℝ) : Prop :=
  ∀ x, ContinuousAt G x → Tendsto
    (fun t => probability (S.experiment t).design (fun z => X t z ≤ x)) atTop (nhds (G x))

def standardNormalCDF (x : ℝ) : ℝ :=
  (ProbabilityTheory.gaussianReal 0 1 (Set.Iic x)).toReal

def IntervalCovers (T θ Vhat α : ℝ) : Prop := |T - θ| ≤ Real.sqrt (Vhat / α)

abbrev ExtendedOrder := WithTop ℝ

def OrderBound {Ω : Type*} [Fintype Ω] (P : FiniteDistribution Ω) (X : Ω → ℝ)
    (k : ℝ) (q : ExtendedOrder) : Prop :=
  if q = ⊤ then ∀ ω, 0 < P.mass ω → |X ω| ≤ k
  else expectation P (fun ω => Real.rpow |X ω| (q.untopD 0)) ≤ Real.rpow k (q.untopD 0)

def ObservedOrderAdmissible (S : ExperimentSequence) (q : ExtendedOrder) : Prop :=
  2 ≤ q ∧ ∃ k > 0, ∀ t i,
    OrderBound (S.experiment t).design ((S.experiment t).outcome i) k q

def PotentialOrderAdmissible (S : ExperimentSequence) (s : ExtendedOrder) : Prop :=
  1 ≤ s ∧ ∃ k > 0, ∀ t i b,
    OrderBound (S.experiment t).design (potentialResponse (S.experiment t) i b) k s

def MaximalOrders (S : ExperimentSequence) (q s : ExtendedOrder) : Prop :=
  ObservedOrderAdmissible S q ∧ (∀ r, ObservedOrderAdmissible S r → r ≤ q) ∧
  PotentialOrderAdmissible S s ∧ (∀ r, PotentialOrderAdmissible S r → r ≤ s)

end
end SAP.P009a
