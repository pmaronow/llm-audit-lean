import Mathlib
import SAP.P009b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators Topology
open Filter

namespace SAP.P009b
noncomputable section
attribute [local instance] Classical.propDecidable

def vSR {n : ℕ} (E : Experiment n) (z : Assignment n) : ℝ := lambdaMax E * vBER E z

structure Study where
  N : ℕ → ℕ
  positive : ∀ t, 0 < N t
  grows : Tendsto N atTop atTop
  experiment : (t : ℕ) → Experiment (N t)

def size (S : Study) (t : ℕ) : ℝ := S.N t

def RegularSequence (S : Study) (k q s : ℝ) : Prop :=
  ∀ t, Regular (S.experiment t) k q s

def LittleO (f g : ℕ → ℝ) : Prop := Tendsto (fun t => f t / g t) atTop (nhds 0)

def InProbability (S : Study) (X : (t : ℕ) → Assignment (S.N t) → ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fun t => prob (S.experiment t).design (fun z => ε < |X t z|))
    atTop (nhds 0)

def balance {n : ℕ} (G : Finset (Fin n)) (z : Assignment n) : ℝ :=
  ∑ j ∈ G, (2 * bit (z j) - 1)

def multiplier (b : ℝ) : ℝ := if 0 < b then 2 else if b = 0 then 1 else 0

def fullOutcome {n : ℕ} (b : Fin n → ℝ) (i : Fin n) (z : Assignment n) : ℝ :=
  multiplier (balance (Finset.univ.erase i) z) * bit (z i) + b i

def oneSourceOutcome {n : ℕ} (h : ℕ) (c : Fin n → ℝ)
    (i : Fin n) (z : Assignment n) : ℝ :=
  if 0 < i.val ∧ i.val < h then 2 * bit (z ⟨0, by have := i.isLt; omega⟩) * bit (z i) + c i
  else bit (z i) + c i

def fairLaw (n : ℕ) : Law (Assignment n) where
  mass := fun _ => 1 / (2 : ℝ) ^ n
  nonneg := fun _ => by positivity
  total := by simp [Fintype.card_fin, Fintype.card_bool]

def fairExperiment (n : ℕ) (y : Fin n → Assignment n → ℝ) : Experiment n :=
  ⟨fairLaw n, y⟩

def armVariable {n : ℕ} (E : Experiment n) (b : Bool) (a : ℕ) (i : Fin n)
    (z : Assignment n) : ℝ := if z i = b then E.outcome i z ^ a else 0

def treatedIncoming {n : ℕ} (E : Experiment n) (i : Fin n) (z : Assignment n) : ℕ :=
  ∑ j, if j ≠ i ∧ Interferes E j i ∧ z j = true then 1 else 0

def hypergeomMass (n m draws t : ℕ) : ℝ :=
  (m.choose t : ℝ) * ((n-m).choose (draws-t) : ℝ) / (n.choose draws : ℝ)

def sixOutcome (i : Fin 6) (z : Assignment 6) : ℝ :=
  if i = 0 then bit (z 0)+bit (z 2)+bit (z 4)
  else if i = 1 then bit (z 1)+bit (z 3)+bit (z 5) else bit (z i)

def sixPartner : Fin 6 → Fin 6 := ![1,0,3,2,5,4]

def sixPairing : Pairing 6 where
  partner := { toFun := sixPartner
               invFun := sixPartner
               left_inv := by intro i; fin_cases i <;> rfl
               right_inv := by intro i; fin_cases i <;> rfl }
  involution := by intro i; fin_cases i <;> rfl
  no_fixed := by intro i; fin_cases i <;> decide

/-- The historical algebraic specialization used in the original illustration.
Its source baseline is outside the support of the stated nonnegative uniform
baseline draws, so it is not a simulation-model counterexample. -/
def offSupportIllustrationExperiment : Experiment 6 :=
  fairExperiment 6 (oneSourceOutcome 4 (fun i => if i = 0 then -1/4 else 1))

/-- The support of the independent uniform baseline draws in Supplement B.
This describes possible realized values; independence is supplied by
`uniformBaselines` below. -/
def UniformBaselineSupport6 (x ε : Fin 6 → ℝ) : Prop :=
  ∀ i, 0 ≤ x i ∧ x i ≤ 3 ∧ 0 ≤ ε i ∧ ε i ≤ 7

def empiricalBias (R : ℕ) (estimates : Fin R → ℝ) : ℝ :=
  (∑ r, (estimates r - 1)) / (R : ℝ)

def reportedBias (R : ℕ) (estimates : Fin R → ℝ) : ℝ := |empiricalBias R estimates|

def uniformBaselines (n : ℕ) : MeasureTheory.Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (MeasureTheory.Measure.pi (fun _ : Fin n =>
    (3:ENNReal)⁻¹ • MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 3))).prod
  (MeasureTheory.Measure.pi (fun _ : Fin n =>
    (7:ENNReal)⁻¹ • MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 7)))

def AdjacentRanks {n : ℕ} (x : Fin n → ℝ) (ρ : Pairing n) : Prop :=
  ∃ order : Fin n ≃ Fin n, Monotone (fun i => x (order i)) ∧
    ∀ i j, i.val/2 = j.val/2 → i ≠ j → ρ.partner (order i) = order j

def approximationError {Ω : Type*} [Fintype Ω] (P : Law Ω) (α : ℝ) (f : Ω → ℝ) : ℝ :=
  |prob P (fun ω => f ω = 1)-α/2| + |prob P (fun ω => f ω = -1)-α/2|

def threePointDistance (x : ℝ) : ℝ := min |x+1| (min |x| |x-1|)

def sharpLaw (α : ℝ) (hα : 0 < α ∧ α < 1) : Law (Fin 3) where
  mass := ![α/2, 1-α, α/2]
  nonneg := by intro i; fin_cases i <;> simp <;> linarith [hα.1, hα.2]
  total := by simp [Fin.sum_univ_succ]; ring

def sharpValue : Fin 3 → ℝ := ![-1,0,1]

def sharpCDF (α x : ℝ) : ℝ :=
  if x < -1 then 0 else if x < 0 then α/2 else if x < 1 then 1-α/2 else 1

def SimulationIntegrable {n : ℕ} (P : Law (Assignment n))
    (Q : (Fin n → ℝ) → Law (Assignment n)) : Prop :=
  let cr := fun b : (Fin n → ℝ) × (Fin n → ℝ) =>
    (⟨P, fullOutcome (fun i => b.1 i+b.2 i)⟩ : Experiment n)
  let pair := fun b : (Fin n → ℝ) × (Fin n → ℝ) =>
    (⟨Q b.1, fullOutcome (fun i => b.1 i+b.2 i)⟩ : Experiment n)
  ∀ paired hajekEstimator : Bool,
    let experiment := if paired then pair else cr
    let estimator := fun b => if hajekEstimator then hajek (experiment b) else ht (experiment b)
    MeasureTheory.Integrable
      (fun b => mean (experiment b).design (estimator b)-eate (experiment b)) (uniformBaselines n) ∧
    MeasureTheory.Integrable
      (fun b => var (experiment b).design (estimator b)) (uniformBaselines n) ∧
    MeasureTheory.Integrable
      (fun b => mean (experiment b).design
        (fun z => (estimator b z-eate (experiment b))^2)) (uniformBaselines n)

end
end SAP.P009b
