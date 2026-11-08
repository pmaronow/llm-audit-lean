import Mathlib
import SAP.P029b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b

universe u v

set_option linter.unusedVariables false
set_option warn.classDefReducibility false

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

def baselineACIndex (a b c d x1 x2 x3 ε : ℝ) : ℝ := 2+a+b*x1+c*x2+d*x3+ε

def baselineAIndex (e f g h x1 x2 x3 ε : ℝ) : ℝ := -2+e+f*x1+g*x2+h*x3+ε

def nonlinearACIndex (a b c d x1 x2 x3 ℓ : ℝ) : ℝ := 2+a+(1+b*x1)*(1+c*x2)+d*x3^3/3+ℓ

def nonlinearAIndex (e f g h x1 x2 x3 ℓ : ℝ) : ℝ := -2+e+(1+f*x1)*(1+g*x2)+h*x3^3/3+ℓ

def sampleArm {n : ℕ} (w Y : Fin n → ℝ) (Z : Fin n → Bool) (z : Bool) : ℝ :=
  (∑ i, w i * (if Z i = z then Y i else 0)) /
    (∑ i, w i * (if Z i = z then 1 else 0))

def sampleWald {n : ℕ} (w Y : Fin n → ℝ) (D Z : Fin n → Bool) : ℝ :=
  (sampleArm w Y Z true - sampleArm w Y Z false) /
    (sampleArm w (fun i => bit (D i)) Z true - sampleArm w (fun i => bit (D i)) Z false)

def sampleCross {n : ℕ} (Z : Fin n → Bool) (V : Fin n → ℝ) : ℝ :=
  ∑ i, (bit (Z i) - (∑ j, bit (Z j))/n) * (V i - (∑ j, V j)/n)

def covariateSigma {Ω X : Type*} [MeasurableSpace X] (U : Ω → PotentialUnit X) :
    MeasurableSpace Ω := MeasurableSpace.comap (fun ω => (U ω).x) inferInstance

def ScoreVersions {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : Ω → PotentialUnit X) (c m : X → ℝ) : Prop :=
  Measurable c ∧ Measurable m ∧
  (fun ω => c (U ω).x) =ᵐ[μ]
    condExp (covariateSigma U) μ (fun ω => if (U ω).complier then (1 : ℝ) else 0) ∧
  (fun ω => c (U ω).x * m (U ω).x) =ᵐ[μ]
    condExp (covariateSigma U) μ (fun ω => if (U ω).complier then (U ω).tau else 0)

def A1Versions {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : Ω → PotentialUnit X) (m : X → ℝ) : Prop :=
  (fun ω => m (U ω).x) =ᵐ[μ] condExp (covariateSigma U) μ (fun ω => (U ω).tau)

def jointVariables {Ω X : Type*} (U : Ω → PotentialUnit X) (Z : Ω → Bool) :
    Ω → (X × Bool × Bool × ℝ × ℝ) × Bool :=
  fun ω => (((U ω).x,(U ω).d0,(U ω).d1,(U ω).y0,(U ω).y1),Z ω)

def uniformScoreError {Ω X : Type*} (U : ℕ → Ω → PotentialUnit X)
    (c : X → ℝ) (s : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n+1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n))
    (fun i => |s n i ω - c (U i ω).x|)

structure ICSWConditions {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : ℕ → Ω → PotentialUnit X) (Z : ℕ → Ω → Bool)
    (c m : X → ℝ) (s : ℕ → ℕ → Ω → ℝ) : Prop where
  iv : ∀ i, IVAssumptions μ (U i) (Z i)
  independent : iIndepFun (fun i => jointVariables (U i) (Z i)) μ
  identical : ∀ i, IdentDistrib (jointVariables (U i) (Z i)) (jointVariables (U 0) (Z 0)) μ μ
  score : ∀ i, ScoreVersions μ (U i) c m
  overlap : ∃ ε : ℝ, 0 < ε ∧ ∀ i, ∀ᵐ ω ∂μ, ε < c (U i ω).x ∧ c (U i ω).x ≤ 1
  estimated_measurable : ∀ n i, Measurable (s n i)
  estimated_range : ∀ n, ∀ᵐ ω ∂μ, ∀ i : Fin (n+1), 0 < s n i.val ω ∧ s n i.val ω ≤ 1
  uniform_consistency : TendstoInMeasure μ (uniformScoreError U c s) atTop (fun _ => 0)

def icswSequence {Ω X : Type*} (U : ℕ → Ω → PotentialUnit X) (Z : ℕ → Ω → Bool)
    (s : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  sampleWald (fun i : Fin (n+1) => 1/s n i.val ω)
    (fun i => (U i.val ω).outcome (Z i.val ω))
    (fun i => (U i.val ω).receipt (Z i.val ω)) (fun i => Z i.val ω)

def winsorizedSequence {Ω X : Type*} (U : ℕ → Ω → PotentialUnit X) (Z : ℕ → Ω → Bool)
    (s : ℕ → ℕ → Ω → ℝ) (cutoff : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  sampleWald (fun i : Fin (n+1) => 1/max (s n i.val ω) (cutoff n ω))
    (fun i => (U i.val ω).outcome (Z i.val ω))
    (fun i => (U i.val ω).receipt (Z i.val ω)) (fun i => Z i.val ω)

def complierCovariateLaw {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : Ω → PotentialUnit X) : Measure X :=
  Measure.map (fun ω => (U ω).x)
    (ENNReal.ofReal ((mP μ {ω | (U ω).complier})⁻¹) • μ.restrict {ω | (U ω).complier})

def alwaysAmongAC {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → PotentialUnit X) (x : X) : ℝ :=
  mP μ {ω | (U ω).d0 = true ∧ (U ω).d1 = true ∧ (U ω).x = x} /
    mP μ {ω | (U ω).d1 = true ∧ (U ω).x = x}

abbrev ReceiptParameters : Type :=
  {q : Bool × Bool → ℝ // ∀ x : Bool, 0 < q (x, false) ∧ q (x, false) < q (x, true) ∧ q (x, true) < 1}

abbrev Observation : Type := Bool × Bool × Fin 4

def receiptData (i : Observation) : Bool := decide (i.2.2.val < twoSidedSuccesses (i.1, i.2.1))

def receiptLikelihood (q : ReceiptParameters) (i : Observation) : ℝ := bernoulliFactor (q.val (i.1, i.2.1)) (receiptData i)

def observationWeight (i : Observation) : ℝ := if receiptData i then 9 else 1
/-- Both weighted arm means and the treatment first stage are defined. -/
def SampleDefined {n : ℕ} (w : Fin n → ℝ) (D Z : Fin n → Bool) : Prop :=
  (∀ z, (∑ i, w i * (if Z i = z then 1 else 0)) ≠ 0) ∧
  sampleArm w (fun i => bit (D i)) Z true -
    sampleArm w (fun i => bit (D i)) Z false ≠ 0

/-- Along almost every draw sequence, all sample ratios are eventually defined. -/
def RatiosEventuallyDefined {Ω X : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (U : ℕ → Ω → PotentialUnit X) (Z : ℕ → Ω → Bool)
    (w : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
    SampleDefined (fun i : Fin (n+1) => w n i.val ω)
      (fun i => (U i.val ω).receipt (Z i.val ω)) (fun i => Z i.val ω)

end
end SAP.P029b
