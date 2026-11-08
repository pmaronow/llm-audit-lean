import SAP.P019b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019b

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory
noncomputable section
open Classical
variable {Ω : Type*} [Fintype Ω]

def normalCDF (t : ℝ) : ℝ := ((gaussianReal 0 1) (Set.Iic t)).toReal

/-- Used only at probabilities strictly between zero and one. -/
def normalQuantile (u : ℝ) : ℝ := sInf {x : ℝ | u ≤ normalCDF x}

/-- Weak convergence against every bounded continuous test function. -/
def WeakLimit {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    (P : FiniteLaw Ω) (T : (n : ℕ) → (Fin n → Ω) → E) (Q : Measure E) : Prop :=
  ∀ f : E → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    Tendsto (fun n => (P.iid n).mean (fun s => f (T n s))) atTop (nhds (∫ x, f x ∂Q))

def ProbabilityLimit (P : FiniteLaw Ω) (T : (n : ℕ) → (Fin n → Ω) → ℝ)
    (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => (P.iid n).prob (fun s => ε < |T n s - a|)) atTop (nhds 0)

def RootNTight (S : Study Ω) (c1 c0 : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 < M ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (S.law.iid n).prob (fun s => M < |Real.sqrt n * (S.muHat s c1 c0 - S.mu)|) < ε

/-- Division by a zero standard error gives statistic zero and p-value one. -/
def normalPValue (estimate null varianceEstimate : ℝ) : ℝ :=
  2 * normalCDF (-|estimate - null| / Real.sqrt varianceEstimate)

def planningS (p1 p2 : ℝ) : ℝ := p1*(1-p1) + p2*(1-p2)
def planningV (p1 p2 : ℝ) : ℝ := (p1+p2)*(1-(p1+p2)/2)

def favoredTail (n p1 p2 c : ℝ) : ℝ :=
  normalCDF ((Real.sqrt n * |p1-p2| - c*Real.sqrt (planningV p1 p2)) /
    Real.sqrt (planningS p1 p2))

def oppositeTail (n p1 p2 c : ℝ) : ℝ :=
  normalCDF ((-Real.sqrt n * |p1-p2| - c*Real.sqrt (planningV p1 p2)) /
    Real.sqrt (planningS p1 p2))

def twoSidedPlanningPower (n p1 p2 c : ℝ) : ℝ :=
  ((gaussianReal 0 1) {g : ℝ | c * Real.sqrt (planningV p1 p2 / n) <
    abs (abs (p1-p2) + Real.sqrt (planningS p1 p2/n)*g)}).toReal

def fairBit {n : ℕ} (ω : Fin n) (k : ℕ) : Bool :=
  decide ((ω.val / 2^k) % 2 = 1)

def cnnLaw : FiniteLaw (Fin 12) where
  mass := fun ω => if ω.val / 4 < 2 then 1/16 else 1/8
  nonneg := by intro ω; split_ifs <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

/-- The two CNN readings share this entire law and all observable variables. -/
def cnnWitness : Study (Fin 12) where
  law := cnnLaw
  W := fun ω => 1 + (if fairBit ω 0 then 1 else 0)
  X := fun ω => decide (ω.val / 4 < 2)
  Y := fun ω => decide (ω.val / 4 = 0)
  Z := fun ω => fairBit ω 1
  V := fun ω => 1 + (if fairBit ω 0 then 1 else 0) +
    (if decide (ω.val / 4 < 2) && fairBit ω 1 then 1 else 0)

def cnnWatching (worldB : Bool) (ω : Fin 12) : Bool :=
  decide (ω.val / 4 = 0) || (worldB && decide (ω.val / 4 = 1))

def cnnReading (worldB : Bool) (ω : Fin 12) : Bool :=
  !worldB && decide (ω.val / 4 = 1)

/-- Binomial(4, 2/5) atom masses. -/
def ceilingBaseline : FiniteLaw (Fin 5) where
  mass := ![81/625, 216/625, 216/625, 96/625, 16/625]
  nonneg := by intro w; fin_cases w <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

def printedAffected (w : Fin 5) : ℝ := (min (w.val + 1) 4 : ℕ)
def unaffected (w : Fin 5) : ℝ := (w.val : ℝ) + 1

/-- Population contrast for an independent mixture with affected share ρ. -/
def ceilingBeta (affectedResponse : Fin 5 → ℝ) (ρ : ℝ) : ℝ :=
  ceilingBaseline.mean (fun w => (1 - ρ) * unaffected w + ρ * affectedResponse w) -
    ceilingBaseline.mean (fun w => (w.val : ℝ))

end
end SAP.P019b
