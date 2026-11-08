import SAP.P045a.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical
open Finset

namespace SAP.P045a
noncomputable section

/-- Substantive conclusions retained for P045-T15; see the Challenge docstring for scope. -/
def T15Statement : Prop :=
  (∀ (a b : ℕ) (A B : ℝ) (hab : 0 < a+b),
    pooledMean a b A B = some ((A+B)/(a+b : ℕ)) ∧
    (0 < a → 0 < b → (A+B)/(a+b : ℕ) =
      (a : ℝ)/(a+b : ℕ)*(A/a)+(b : ℝ)/(a+b : ℕ)*(B/b)) ∧
    (a=0 → A=0 → pooledMean a b A B = some (B/b)))
  ∧
  (∀ (H : Finset (Fin 6)) (m : Fin 6 → ℝ),
    H.card = (H.filter (fun g => tractPartner g ∈ H)).card +
      (H.filter (fun g => tractPartner g ∉ H)).card ∧
    (∑ g ∈ H, m g) = (∑ g ∈ H.filter (fun g => tractPartner g ∈ H), m g) +
      (∑ g ∈ H.filter (fun g => tractPartner g ∉ H), m g))
  ∧
  ((∀ ω : Finset (Fin 6) × TractAssignment, 0 ≤ tractTwoStageMass ω) ∧
    (∑ ω : Finset (Fin 6) × TractAssignment, tractTwoStageMass ω) = 1 ∧
    (∀ ω : Finset (Fin 6) × TractAssignment,
      0 < tractTwoStageMass ω ↔
        ω.1 ∈ firstStageSets 6 3 ∧
        ∀ g : Fin 6, treatedCount (ω.2 g) = tractRegimeCount ω.1 g) ∧
    (∀ H ∈ firstStageSets 6 3, ∀ w : TractAssignment,
      (∀ g : Fin 6, treatedCount (w g) = tractRegimeCount H g) →
      (∀ g ∈ H, ∀ b : Bool,
        armExists b (w g) ∧
        tractObservedArm w g b =
          (if tractPartner g ∈ H then
            (if b then 9 / 4 else 11 / 8)
          else (if b then 2 else 5 / 4))) ∧
      tractDirectEstimator H w =
        (∑ g ∈ H, (tractObservedArm w g true - tractObservedArm w g false)) / 3 ∧
      tractDirectEstimator H w =
        ((sameRegimeCount H : ℝ) / 3) * (7 / 8) +
          ((3 - (sameRegimeCount H : ℝ)) / 3) * (3 / 4)) ∧
    (∀ g : Fin 6, ∀ i : Fin 75, ∀ b : Bool,
      prob tractAllPsiMass (fun w => w g i = b) =
        (if b then (2 / 3 : ℝ) else 1 / 3) ∧
      tractPsiPsiPotential g i b = (if b then 9 / 4 else 11 / 8)) ∧
    tractPsiPsiTarget = 7 / 8 ∧
    average (firstStageSets 6 3)
      (fun H => (sameRegimeCount H : ℝ) / 3) = 2 / 5 ∧
    average (firstStageSets 6 3)
      (fun H => (3 - (sameRegimeCount H : ℝ)) / 3) = 3 / 5 ∧
    expect tractTwoStageMass
      (fun ω => tractDirectEstimator ω.1 ω.2) = 4 / 5 ∧
    expect tractTwoStageMass
      (fun ω => tractDirectEstimator ω.1 ω.2) - tractPsiPsiTarget = -3 / 40)

/-- Substantive conclusions retained for P045-T16; see the Challenge docstring for scope. -/
def T16Statement : Prop :=
  ((∀ i : Fin 10, let g := (univ.filter (fun j => printedAdj i j=true)).card
      pairExposureProb printedAdj i .d11 = (g : ℝ)/45 ∧
      pairExposureProb printedAdj i .d10 = (9-g : ℕ)/45 ∧
      pairExposureProb printedAdj i .d00 = (Nat.choose (9-g) 2 : ℝ)/45 ∧
      pairExposureProb printedAdj i .d01 = (36-(Nat.choose (9-g) 2 : ℝ))/45 ∧
      (∀ d, 0 < pairExposureProb printedAdj i d)) ∧
    ¬pairCellNonempty .d11 (5,8) ∧
    (∀ i : Fin 10, exposure printedAdj (pairAssignment (5,8)) i = .d00 ↔ i=0 ∨ i=1) ∧
    pairHT printedAdj (fun _ => dilated 1) .d11 (5,8) = 0 ∧
    pairHT printedAdj (fun _ => dilated 1) .d00 (5,8) = 15/2 ∧
    printedContrast (5,8) = -3/4 ∧
    (treatmentPairs.filter (pairCellNonempty .d11)).card = 20 ∧
    (treatmentPairs.filter (fun e => pairCellNonempty .d11 e ∧ pairCellNonempty .d00 e)).card = 19 ∧
    average treatmentPairs (pairHT printedAdj (fun _ => dilated 1) .d11) = 20 ∧
    average (treatmentPairs.filter (pairCellNonempty .d11)) (pairHT printedAdj (fun _ => dilated 1) .d11) = 45 ∧
    average treatmentPairs printedContrast = 1 ∧
    average (treatmentPairs.filter (pairCellNonempty .d11)) printedContrast = 651/200 ∧
    average (treatmentPairs.filter (fun e => pairCellNonempty .d11 e ∧ pairCellNonempty .d00 e)) printedContrast = 1227/380)

end
end SAP.P045a
