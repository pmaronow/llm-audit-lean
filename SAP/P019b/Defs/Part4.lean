import SAP.P019b.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019b

open Filter MeasureTheory ProbabilityTheory
noncomputable section
open Classical

def T12Statement : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (S : Study Ω),
    S.monotone → S.noLiarsDesign → S.treatmentIndependent →
    0 < S.law.prob (S.cell false true) → 0 < S.law.prob (S.cell true true) →
    S.beta = 1

/-- A single observable population with two different reading/watching labels. -/
def T13Statement : Prop :=
  cnnWitness.standing ∧
  (∀ (b : Bool) (ω : Fin 12),
    cnnWitness.X ω = (cnnReading b ω || cnnWatching b ω)) ∧
  cnnWitness.law.prob (fun ω => cnnWatching false ω = true) = 1/4 ∧
  cnnWitness.law.prob (fun ω => cnnWatching true ω = true) = 1/2 ∧
  cnnWitness.law.prob (fun ω => cnnWitness.Y ω ≠ cnnWatching false ω) = 0 ∧
  cnnWitness.law.prob (fun ω => cnnWitness.Y ω ≠ cnnWatching true ω) = 1/4 ∧
  cnnWitness.combined = 1/2 ∧ cnnWitness.mu = 1/2 ∧
  cnnWitness.beta = 1 ∧ cnnWitness.delta = 0

def T14Statement : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (S : Study Ω) (R Q : Ω → Bool),
    (∀ ω, S.Y ω = Q ω) → (∀ ω, S.X ω = (R ω || Q ω)) →
    S.noLiarsDesign → tripleIndependent S.law S.W R Q S.Z →
    0 < S.law.prob (fun ω => S.Z ω = true) →
    S.law.prob (fun ω => S.Z ω = true) < 1 →
    0 < S.law.prob (fun ω => Q ω = true) →
    S.law.prob (fun ω => Q ω = true) < 1 →
    let b := S.law.prob (fun ω => Q ω = true)
    let a := S.law.prob (fun ω => R ω = true ∧ Q ω = false)
    let listContrast :=
      S.law.ce (fun ω => (S.V ω : ℝ)) (fun ω => S.Z ω = true) -
      S.law.ce (fun ω => (S.V ω : ℝ)) (fun ω => S.Z ω = false)
    S.monotone ∧ S.noLiarsDesign ∧ S.treatmentIndependent ∧
    S.listMean true false - S.listMean false false =
      S.law.ce (fun ω => bitVal (S.X ω)) (fun ω => S.Y ω = false) ∧
    S.law.ce (fun ω => bitVal (S.X ω)) (fun ω => S.Y ω = false) = a / (1-b) ∧
    S.combined = b+a ∧ S.mu = b+a ∧ listContrast = b+a ∧
    S.law.mean (fun ω => bitVal (S.Y ω)) = b ∧
    S.combined - b = a ∧ listContrast - b = a ∧
    (S.combined = b ↔ a = 0) ∧ (listContrast = b ↔ a = 0) ∧
    S.beta = 1 ∧ S.delta = 0

def T15Statement : Prop :=
  (∀ n p1 p2 α : ℝ, 0 < n →
    0 ≤ p1 → p1 ≤ 1 → 0 ≤ p2 → p2 ≤ 1 →
    0 < planningS p1 p2 → 0 < α → α < 1 →
    let c := normalQuantile (1-α/2)
    0 < c ∧
    planningV p1 p2 - planningS p1 p2 = (p1-p2)^2/2 ∧
    0 ≤ planningV p1 p2 - planningS p1 p2 ∧
    twoSidedPlanningPower n p1 p2 c = favoredTail n p1 p2 c + oppositeTail n p1 p2 c ∧
    oppositeTail n p1 p2 c = 1 -
      normalCDF ((Real.sqrt n * |p1-p2| + c*Real.sqrt (planningV p1 p2)) /
        Real.sqrt (planningS p1 p2)) ∧
    0 < oppositeTail n p1 p2 c ∧ oppositeTail n p1 p2 c ≤ α/2 ∧
    (oppositeTail n p1 p2 c = α/2 ↔ p1=p2) ∧
    twoSidedPlanningPower n p1 p2 c - favoredTail n p1 p2 c = oppositeTail n p1 p2 c) ∧
  (let c := normalQuantile (1-(1/20 : ℝ)/2);
    planningS (1/2) (1/2) = 1/2 ∧ planningV (1/2) (1/2) = 1/2 ∧
    |(1/2 : ℝ) - 1/2| = 0 ∧
    favoredTail 50 (1/2) (1/2) c = normalCDF (-c) ∧
    normalCDF (-c) = 1/40 ∧ oppositeTail 50 (1/2) (1/2) c = 1/40 ∧
    twoSidedPlanningPower 50 (1/2) (1/2) c = 1/20)

def T16Statement : Prop :=
  ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
    ceilingBeta printedAffected ρ = 1 - (16/625)*ρ

def T17Statement : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (S : Study Ω),
    (S.standing → S.mu = S.combined) ∧
    (S.noLiarsDesign → S.treatmentIndependent → S.nondegenerate →
      0 < S.law.prob (fun ω => S.X ω = false ∧ S.Y ω = true) →
      S.combined = S.mu + S.law.prob (fun ω => S.X ω = false ∧ S.Y ω = true) ∧
      S.mu < S.combined)

end
end SAP.P019b
