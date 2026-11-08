import SAP.P024.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P024
open scoped BigOperators
noncomputable section

/-- All numerical and inferential clauses of the four-period timing witness. -/
def T1Statement : Prop :=
  (∀ t : Fin 4, exposureProbability (uniformDesign (Fin 3)) onsetExposure t =
    (![0,1/3,2/3,1] : Fin 4 → ℝ) t) ∧
  calendarBaseline 0 = 1 ∧ calendarBaseline 1 = 4 ∧
  calendarBaseline 2 = 9 ∧ calendarBaseline 3 = 16 ∧
  (∀ t : Fin 4, calendarTreated t = (![3,6,11,18] : Fin 4 → ℝ) t) ∧
  calendarBaseline 0 ≠ calendarBaseline 1 ∧
  calendarHT 0 = 69/4 ∧ calendarHT 1 = 21/4 ∧ calendarHT 2 = -33/2 ∧
  averageEffect calendarEligible calendarBaseline calendarTreated = 2 ∧
  expectation (uniformDesign (Fin 3)) calendarHT = 2 ∧
  variance (uniformDesign (Fin 3)) calendarHT = 1561/8 ∧
  calendarBeforeAfter 0 = 26/3 ∧ calendarBeforeAfter 1 = 10 ∧
  calendarBeforeAfter 2 = 34/3 ∧
  randomizationP calendarBeforeAfter 0 = 1 ∧
  randomizationP calendarBeforeAfter 1 = 2/3 ∧
  randomizationP calendarBeforeAfter 2 = 1/3 ∧
  (∀ k : Fin 4, probability (uniformDesign (Fin 3))
    (fun s => randomizationP calendarBeforeAfter s ≤ (k.val : ℝ)/3) = (k.val : ℝ)/3) ∧
  (∀ α : ℝ, 0 ≤ α → α ≤ 1 → probability (uniformDesign (Fin 3))
    (fun s => randomizationP calendarBeforeAfter s ≤ α) ≤ α) ∧
  expectation (uniformDesign (Fin 3)) calendarHT =
    averageEffect calendarEligible calendarBaseline calendarTreated

/-- Corrected timing estimation, uniform sharp-null testing, and actual before-after bias. -/
def T2Statement : Prop :=
  (∀ (I Ω : Type*) [Fintype I] [Fintype Ω]
    (d : Design Ω) (z : Ω → I → Bool) (y0 y1 : I → ℝ),
    (overlap d z).Nonempty →
    expectation d (htEstimate (overlap d z) z y0 y1 (exposureProbability d z)) =
      averageEffect (overlap d z) y0 y1) ∧
  (∀ (Ω : Type*) [Fintype Ω] [Nonempty Ω] (D : Ω → ℝ) (α : ℝ),
    0 ≤ α → α ≤ 1 → probability (uniformDesign Ω) (fun ω => randomizationP D ω ≤ α) ≤ α) ∧
  expectation (uniformDesign (Fin 3)) calendarBeforeAfter = 10 ∧
  expectation (uniformDesign (Fin 3)) calendarBeforeAfter ≠ 0 ∧
  (∀ s, calendarObservedBeforeAfter s = calendarBeforeAfter s+2) ∧
  expectation (uniformDesign (Fin 3)) calendarObservedBeforeAfter = 12 ∧
  expectation (uniformDesign (Fin 3)) calendarObservedBeforeAfter ≠ 2

/-- The fixed-count, common-marginal branch of individual difference-in-means unbiasedness. -/
def T6Statement : Prop :=
  ∀ (J Ω : Type*) [Fintype J] [Fintype Ω] (d : Design Ω)
    (m : ℕ), 0 < m → m < Fintype.card J →
    ∀ (z : Ω → J → Bool) (y0 y1 : J → ℝ),
    (∀ ω, treatedCount (z ω) = m) →
    (∀ j, exposureProbability d z j = (m : ℝ)/Fintype.card J) →
    expectation d (fun ω => clusterDIM (fun _ => 1) y0 y1 (z ω)) =
      averageEffect Finset.univ y0 y1

/-- Weighted observed block means and unbiasedness under fixed counts and actual common marginals. -/
def T8Statement : Prop :=
  ∀ (B Ω : Type*) [Fintype B] [Nonempty B] [Fintype Ω]
    (I : B → Type*) [∀ b, Fintype (I b)] (d : Design Ω) (m : B → ℕ),
    (∀ b, 0 < m b) → (∀ b, m b < Fintype.card (I b)) →
    ∀ (z : Ω → (b : B) → I b → Bool) (y0 y1 : (b : B) → I b → ℝ),
    (∀ ω b, treatedCount (z ω b) = m b) →
    (∀ b i, exposureProbability d (fun ω => z ω b) i =
      (m b : ℝ)/Fintype.card (I b)) →
    (∀ ω, blockedHT I m z y0 y1 ω =
      ∑ b, (Fintype.card (I b) : ℝ)/blockPopulation I *
        clusterDIM (fun _ => 1) (y0 b) (y1 b) (z ω b)) ∧
    expectation d (blockedHT I m z y0 y1) =
      (∑ b, ∑ i, (y1 b i-y0 b i)) / blockPopulation I ∧
    expectation d (fun ω => ∑ b, (Fintype.card (I b) : ℝ)/blockPopulation I *
      clusterDIM (fun _ => 1) (y0 b) (y1 b) (z ω b)) =
      (∑ b, ∑ i, (y1 b i-y0 b i)) / blockPopulation I

end
end SAP.P024
