import SAP.P043.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P043

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
universe u v

/-! Integer-dose IV quantities and both specified counterexamples. Exclusion and consistency hold by construction; observable laws are finite point-mass functions. -/

structure IVModel (Ω : Type u) where
  knowledge : Bool → Ω → ℕ
  response : ℕ → Ω → ℝ

def ivPotentialSupport {Ω : Type u} (m : IVModel Ω) (_z : Bool) (k : ℕ) (i : Ω) : ℝ :=
  m.response k i

def ivKnowledge {Ω : Type u} (m : IVModel Ω) (z : Bool) (i : Ω) : ℝ := m.knowledge z i

def ivOutcome {Ω : Type u} (m : IVModel Ω) (z : Bool) (i : Ω) : ℝ :=
  m.response (m.knowledge z i) i

def firstStage {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (m : IVModel Ω) : ℝ := contrast P p (ivKnowledge m)

def ivReducedForm {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (m : IVModel Ω) : ℝ := contrast P p (ivOutcome m)

def ivRatio {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (m : IVModel Ω) : ℝ := ivReducedForm P p m / firstStage P p m

def increaser {Ω : Type u} (m : IVModel Ω) (i : Ω) : Prop :=
  m.knowledge false i < m.knowledge true i

def increaserEffect {Ω : Type u} [Fintype Ω] (P : Population Ω) (m : IVModel Ω) : ℝ :=
  eventMean P (increaser m)
    (fun i => m.response (m.knowledge true i) i - m.response (m.knowledge false i) i)

def conditionalObservableLaw {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (m : IVModel Ω) (z : Bool) (k : ℕ) (y : ℝ) : ℝ :=
  eventProb P (fun i => m.knowledge z i = k ∧ ivOutcome m z i = y)

def observableLaw {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (m : IVModel Ω) (x : Bool × (ℕ × ℝ)) : ℝ :=
  armProb p x.1 * conditionalObservableLaw P m x.1 x.2.1 x.2.2

def knowledgeMargin (k : ℕ) : ℝ := indicator (9 ≤ k)

def upDownPopulation : Population Bool where
  mass := fun i => if i then 2/3 else 1/3
  nonneg := fun i => by cases i <;> norm_num
  total := by norm_num

def upDownWitness : IVModel Bool :=
  ⟨fun z i => if i then (if z then 9 else 8) else (if z then 8 else 9),
   fun k i => if i then 3 + knowledgeMargin k else 2 + 2*knowledgeMargin k⟩

def modelA : IVModel (Fin 5) :=
  ⟨fun z i => if z then ![9,9,8,8,9] i else ![8,8,9,8,9] i,
   fun k i => ![3+knowledgeMargin k, 3+knowledgeMargin k, 2+2*knowledgeMargin k, 2, 4] i⟩

def modelB : IVModel (Fin 5) :=
  ⟨fun z i => if z then ![9,9,8,9,8] i else ![8,8,9,8,9] i,
   fun k i => ![3+knowledgeMargin k, 3+knowledgeMargin k,
     2+2*knowledgeMargin k, 2+2*knowledgeMargin k, 2+2*knowledgeMargin k] i⟩

def fiveTypeObservableLaw (z : Bool) (k : ℕ) (y : ℝ) : ℝ :=
  if z then (2/5)*indicator (k=8 ∧ y=2) + (3/5)*indicator (k=9 ∧ y=4)
  else (1/5)*indicator (k=8 ∧ y=2) + (2/5)*indicator (k=8 ∧ y=3) +
    (2/5)*indicator (k=9 ∧ y=4)

def UpDownNumericClaims : Prop :=
  armMean upDownPopulation (1/2) false (ivKnowledge upDownWitness) = 25/3 ∧
  armMean upDownPopulation (1/2) true (ivKnowledge upDownWitness) = 26/3 ∧
  firstStage upDownPopulation (1/2) upDownWitness = 1/3 ∧
  0 < firstStage upDownPopulation (1/2) upDownWitness ∧
  armMean upDownPopulation (1/2) false (ivOutcome upDownWitness) = 10/3 ∧
  armMean upDownPopulation (1/2) true (ivOutcome upDownWitness) = 10/3 ∧
  ivReducedForm upDownPopulation (1/2) upDownWitness = 0 ∧
  ivRatio upDownPopulation (1/2) upDownWitness = 0 ∧
  covariance upDownPopulation (1/2) (fun z _ => assignment z) (ivKnowledge upDownWitness) = 1/12 ∧
  covariance upDownPopulation (1/2) (fun z _ => assignment z) (ivOutcome upDownWitness) = 0 ∧
  covariance upDownPopulation (1/2) (fun z _ => assignment z) (ivOutcome upDownWitness) /
    covariance upDownPopulation (1/2) (fun z _ => assignment z) (ivKnowledge upDownWitness) = 0 ∧
  eventProb upDownPopulation (increaser upDownWitness) = 2/3 ∧
  increaserEffect upDownPopulation upDownWitness = 1 ∧
  (2/3 : ℝ)*1 + (1/3)*(-2) = 0

def UpDownUnitClaims (i : Bool) : Prop :=
    (increaser upDownWitness i ↔ i = true) ∧
    (increaser upDownWitness i → upDownWitness.knowledge false i = 8 ∧
      upDownWitness.knowledge true i = 9 ∧
      upDownWitness.response 9 i - upDownWitness.response 8 i = 1) ∧
    (∀ z, upDownWitness.knowledge z i ∈ ({8,9} : Finset ℕ) ∧ upDownWitness.knowledge z i ≤ 18) ∧
    (∀ k, upDownWitness.response k i ∈ ({2,3,4} : Finset ℝ) ∧
      0 ≤ upDownWitness.response k i ∧ upDownWitness.response k i ≤ 7) ∧
    Monotone (fun k => upDownWitness.response k i)

def FiveTypeNumericClaims (m : IVModel (Fin 5)) : Prop :=
  armMean (uniformPopulation (Fin 5)) (1/2) false (ivKnowledge m) = 42/5 ∧
  armMean (uniformPopulation (Fin 5)) (1/2) true (ivKnowledge m) = 43/5 ∧
  firstStage (uniformPopulation (Fin 5)) (1/2) m = 1/5 ∧
  0 < firstStage (uniformPopulation (Fin 5)) (1/2) m ∧
  armMean (uniformPopulation (Fin 5)) (1/2) false (ivOutcome m) = 16/5 ∧
  armMean (uniformPopulation (Fin 5)) (1/2) true (ivOutcome m) = 16/5 ∧
  ivReducedForm (uniformPopulation (Fin 5)) (1/2) m = 0 ∧
  ivRatio (uniformPopulation (Fin 5)) (1/2) m = 0

def FiveTypeUnitClaims (m : IVModel (Fin 5)) (i : Fin 5) : Prop :=
    (∀ z, m.knowledge z i ∈ ({8,9} : Finset ℕ) ∧ m.knowledge z i ≤ 18) ∧
    (∀ k, 0 ≤ m.response k i ∧ m.response k i ≤ 7) ∧
    Monotone (fun k => m.response k i) ∧
    (increaser m i → m.knowledge false i = 8 ∧ m.knowledge true i = 9)

def IncreaserNonidentificationClaim : Prop :=
    ¬ ∃ F : ((Bool × (ℕ × ℝ) → ℝ) → ℝ),
      F (observableLaw (uniformPopulation (Fin 5)) (1/2) modelA) =
        increaserEffect (uniformPopulation (Fin 5)) modelA ∧
      F (observableLaw (uniformPopulation (Fin 5)) (1/2) modelB) =
        increaserEffect (uniformPopulation (Fin 5)) modelB

/-- The two IV witnesses, including full-law nonidentification. Nonzero
increaser probabilities guard the two conditional-effect quantities. -/
def T4Statement : Prop :=
  UpDownNumericClaims ∧ (∀ i, UpDownUnitClaims i) ∧
  FiveTypeNumericClaims modelA ∧ FiveTypeNumericClaims modelB ∧
  observableLaw (uniformPopulation (Fin 5)) (1/2) modelA =
    observableLaw (uniformPopulation (Fin 5)) (1/2) modelB ∧
  increaserEffect (uniformPopulation (Fin 5)) modelA = 1 ∧
  increaserEffect (uniformPopulation (Fin 5)) modelB = 4/3 ∧
  (∀ z k y, conditionalObservableLaw (uniformPopulation (Fin 5)) modelA z k y =
      fiveTypeObservableLaw z k y ∧
    conditionalObservableLaw (uniformPopulation (Fin 5)) modelB z k y =
      fiveTypeObservableLaw z k y) ∧
  (∀ i, FiveTypeUnitClaims modelA i) ∧
  (∀ i, FiveTypeUnitClaims modelB i) ∧
  IncreaserNonidentificationClaim ∧
  eventProb (uniformPopulation (Fin 5)) (increaser modelA) ≠ 0 ∧
  eventProb (uniformPopulation (Fin 5)) (increaser modelB) ≠ 0

end
end SAP.P043
