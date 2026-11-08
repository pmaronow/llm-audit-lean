import SAP.P019a.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
noncomputable section
open Classical
universe u

/-- The exact discrepancy between the two ceiling mechanisms, in mixture form. -/
def T1Statement : Prop :=
  (∀ w : Fin 5, ceilingBaseline.mass w =
    (Nat.choose 4 w.val : ℝ)*(2/5)^w.val*(3/5)^(4-w.val)) ∧
  ceilingBaseline.mean (fun w => (w.val : ℝ)) = 8/5 ∧
  ceilingBaseline.variance (fun w => (w.val : ℝ)) = 24/25 ∧
  (∀ w : Fin 5, printedAffected w = ![(1 : ℝ), 2, 3, 4, 4] w ∧
    codedAffected w = ![(2 : ℝ), 3, 4, 5, 5] w ∧
    unaffected w = ![(1 : ℝ), 2, 3, 4, 5] w) ∧
  ceilingBeta printedAffected (1/5) = 3109/3125 ∧
  ceilingBeta codedAffected (1/5) = 3734/3125 ∧
  ceilingBeta printedAffected (1/5) - 1 = -16/3125 ∧
  ceilingBeta codedAffected (1/5) - 1 = 609/3125 ∧
  ceilingBeta codedAffected (1/5) - ceilingBeta printedAffected (1/5) = 1/5

def T2Statement : Prop :=
  ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
  (∀ w : Fin 5, codedAffected w = if w.val < 4 then (w.val : ℝ) + 2 else 5) ∧
  (∀ (w : Fin 5) (affected : Bool),
    (if affected then codedAffected w else unaffected w) - (w.val : ℝ) =
      1 + (if affected = true ∧ w.val < 4 then 1 else 0) ∧
    (if affected then printedAffected w else unaffected w) - (w.val : ℝ) =
      1 - (if affected = true ∧ w.val = 4 then 1 else 0)) ∧
  ceilingBeta codedAffected ρ = 1 + ρ * (1 - ceilingBaseline.mass 4) ∧
  ceilingBeta codedAffected ρ = 1 + (609/625) * ρ ∧
  ceilingBeta printedAffected ρ = 1 - ρ * ceilingBaseline.mass 4 ∧
  ceilingBeta printedAffected ρ = 1 - (16/625) * ρ ∧
  ceilingBeta codedAffected ρ - ceilingBeta printedAffected ρ = ρ ∧
  (0 < ρ → 1 < ceilingBeta codedAffected ρ) ∧
  ceilingBeta codedAffected (1/5) = 3734/3125 ∧
  ceilingBeta printedAffected (1/5) = 3109/3125

def T3Statement : Prop :=
  let S := finiteSampleWitness
  let P := S.law.iid 4
  let A := @Study.sampleA (Fin 16) _ S 4
  let B := fun s : Fin 4 → Fin 16 => S.sampleB s 0 0
  S.standing ∧
  (∀ (n : ℕ) (z : Bool),
    (S.law.iid n).prob (fun s => S.cellCount s z false = 0) = (5/8)^n ∧
    0 < (S.law.iid n).prob (fun s => S.cellCount s z false = 0)) ∧
  S.law.cov (fun ω => 1 - bitVal (S.Y ω)) (singletonMean S true false) = 5/64 ∧
  S.law.cov (fun ω => 1 - bitVal (S.Y ω)) (singletonMean S false false) = 3/64 ∧
  0 < S.law.prob (fun ω => S.Y ω = false) ∧
  S.law.ce (fun ω => if S.Z ω = true then 1 else 0) (fun ω => S.Y ω = false) = 1/2 ∧
  S.law.ce (singletonMean S true false) (fun ω => S.Y ω = false) = 5/12 ∧
  S.listMean true false = 5/6 ∧
  (1 - (1 - (1/2 : ℝ))^0 = 0 ∧
    1 - (1 - (1/2 : ℝ))^1 = 1/2 ∧
    1 - (1 - (1/2 : ℝ))^2 = 3/4 ∧
    1 - (1 - (1/2 : ℝ))^4 = 15/16) ∧
  P.prob S.occupied = 1431/2048 ∧ 0 < P.prob S.occupied ∧
  P.ccov A B S.occupied = 0 ∧
  P.ccov (fun s => S.cellMean s true false 0) (fun s => S.cellMean s false false 0)
    S.occupied = 0 ∧
  P.cv (fun s => S.muHat s 0 0) S.occupied = 141205/404496 ∧
  (P.ce A S.occupied)^2 * P.cv B S.occupied +
    P.cv A S.occupied * (P.ce B S.occupied)^2 +
    P.cv A S.occupied * P.cv B S.occupied = 75809/202248 ∧
  P.cv (fun s => S.muHat s 0 0) S.occupied -
    ((P.ce A S.occupied)^2 * P.cv B S.occupied +
      P.cv A S.occupied * (P.ce B S.occupied)^2 +
      P.cv A S.occupied * P.cv B S.occupied) = -1157/44944 ∧
  (4 : ℝ) * S.gamma = 2 ∧
  P.prob (fun s => S.armCount s true = 2) = 3/8 ∧
  P.prob (fun s => S.armCount s true = 0) = 1/16

def T5Statement : Prop :=
  let S := distributionWitness
  S.standing ∧
  S.law.ce (fun ω => if (S.V ω : ℝ) = 0 then 1 else 0) (S.cell false true) = 1/2 ∧
  S.law.ce (fun ω => if (S.V ω : ℝ) + 1 = 0 then 1 else 0) (S.cell true true) = 0 ∧
  S.law.ce (fun ω => if (S.V ω : ℝ) - 1 = 0 then 1 else 0) (S.cell true true) = 1/2

def T6Statement : Prop :=
  ∀ (Ω : Type u) [Fintype Ω] (S : Study Ω),
    S.monotone → S.noLiarsDesign → S.treatmentIndependent →
    0 < S.law.prob (S.cell false true) → 0 < S.law.prob (S.cell true true) →
    S.law.prob (fun ω => S.Y ω = true) ≠ 0 ∧
    ∀ t : ℝ,
      S.law.ce (fun ω => if (S.V ω : ℝ) = t then 1 else 0) (S.cell false true) =
        S.law.ce (fun ω => if (S.W ω : ℝ) = t then 1 else 0) (fun ω => S.Y ω = true) ∧
      S.law.ce (fun ω => if (S.V ω : ℝ) - 1 = t then 1 else 0) (S.cell true true) =
        S.law.ce (fun ω => if (S.W ω : ℝ) = t then 1 else 0) (fun ω => S.Y ω = true) ∧
      S.law.ce (fun ω => if (S.V ω : ℝ) = t then 1 else 0) (S.cell false true) =
        S.law.ce (fun ω => if (S.V ω : ℝ) - 1 = t then 1 else 0) (S.cell true true) ∧
      S.law.ce (fun ω => if (S.V ω : ℝ) = t then 1 else 0) (S.cell false true) =
        S.law.ce (fun ω => if (S.V ω : ℝ) = t + 1 then 1 else 0) (S.cell true true)

def T7Statement : Prop :=
  diagnosisWitness.monotone ∧ diagnosisWitness.noLiarsDesign ∧
  diagnosisWitness.nondegenerate ∧ diagnosisWitness.delta = 0 ∧
  diagnosisWitness.beta = 2 ∧ diagnosisWitness.beta ≠ 1 ∧
  ¬ diagnosisWitness.treatmentIndependent

def T8Statement : Prop :=
  ∀ (Ω : Type u) [Fintype Ω] (S : Study Ω),
    0 < S.law.prob (S.cell false true) → 0 < S.law.prob (S.cell true true) →
    (S.monotone → S.noLiarsDesign →
      S.beta = 1 + S.law.ce (fun ω => (S.W ω : ℝ)) (S.cell true true) -
        S.law.ce (fun ω => (S.W ω : ℝ)) (S.cell false true)) ∧
    (S.monotone → S.noLiarsDesign → S.treatmentIndependent →
      S.law.ce (fun ω => (S.W ω : ℝ)) (S.cell true true) =
        S.law.ce (fun ω => (S.W ω : ℝ)) (S.cell false true) ∧ S.beta = 1) ∧
    (S.beta ≠ 1 → ¬ S.monotone ∨ ¬ S.noLiarsDesign ∨ ¬ S.treatmentIndependent) ∧
    (S.monotone → S.noLiarsDesign → S.beta ≠ 1 → ¬ S.treatmentIndependent)

end
end SAP.P019a
