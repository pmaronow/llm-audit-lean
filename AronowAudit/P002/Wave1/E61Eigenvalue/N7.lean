import AronowAudit.P002.Wave1.E61EigenvalueBlueprint
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

namespace AronowAudit.P002.Wave1.E61Eigenvalue
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Transfer the sampling inequality to both arms, using complementation for controls. -/
theorem n7_proof : N7 := by
  intro hsample hentry n k P δ e A B r hA hr hP a s t τ hτ
  have hdesign : ValidDesign P.pop := hP.1
  have hn1pos : 0 < P.pop.n1 := hdesign.2.1
  have hn1lt : P.pop.n1 < n := hdesign.2.2
  have hn1le : P.pop.n1 ≤ n := hn1lt.le
  have halloc1 : r * (n : ℝ) ≤ (P.pop.n1 : ℝ) := hP.2.2.2.1
  have halloc0' : (P.pop.n1 : ℝ) ≤ (1 - r) * (n : ℝ) := hP.2.2.2.2.1
  have halloc0 : r * (n : ℝ) ≤ ((n - P.pop.n1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn1le]
    nlinarith [halloc0']
  have hn0pos : 1 ≤ n - P.pop.n1 := by omega
  have hn0lt : n - P.pop.n1 < n := by omega
  have hC : 0 < max (1 : ℝ) A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let z : Fin n → ℝ := fun i => augmented P.x i s * augmented P.x i t
  let E : Finset (Fin n) → Prop := fun S => τ ≤ |groupMean S z - mean z|
  have hmean : (∑ i, z i ^ 2) / (n : ℝ) ≤ max 1 A := by
    exact hentry n k P δ e A B r hP s t
  have hpopulation : gram P.x Finset.univ s t = mean z := by
    simp only [gram, groupMean, mean, Finset.card_univ, Fintype.card_fin, z]
  rw [hpopulation]
  change probability P.pop (fun S => E (if a then S else Sᶜ)) ≤
    2 * ((n : ℝ) + 1) * Real.exp (-2 * r ^ 2 * n * τ ^ 2 / max 1 A)
  cases a with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      -- Complement is an involution carrying n1-subsets to (n-n1)-subsets.
      have hcard :
          ((Finset.univ.powersetCard P.pop.n1).filter (fun S => E Sᶜ)).card =
            ((Finset.univ.powersetCard (n - P.pop.n1)).filter E).card := by
        refine Finset.card_nbij'
          (fun S : Finset (Fin n) => Sᶜ) (fun T : Finset (Fin n) => Tᶜ)
          ?_ ?_ ?_ ?_
        · intro S hS
          have hS' := Finset.mem_filter.mp hS
          have hScard : S.card = P.pop.n1 :=
            (Finset.mem_powersetCard.mp hS'.1).2
          refine Finset.mem_filter.mpr
            ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, hS'.2⟩
          simp only [Finset.card_compl, Fintype.card_fin, hScard]
        · intro T hT
          have hT' := Finset.mem_filter.mp hT
          have hTcard : T.card = n - P.pop.n1 :=
            (Finset.mem_powersetCard.mp hT'.1).2
          refine Finset.mem_filter.mpr
            ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, ?_⟩
          · simp only [Finset.card_compl, Fintype.card_fin, hTcard]
            omega
          · simpa only [compl_compl] using hT'.2
        · intro S _hS
          exact compl_compl S
        · intro T _hT
          exact compl_compl T
      have hcontrol := hsample n (n - P.pop.n1) r (max 1 A) τ z
        hn0pos hn0lt hr halloc0 hC hmean hτ
      calc
        probability P.pop (fun S => E Sᶜ) =
            (((Finset.univ.powersetCard (n - P.pop.n1)).filter E).card : ℝ) /
              (n.choose (n - P.pop.n1) : ℝ) := by
          unfold probability assignments
          rw [hcard]
          simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
          rw [Nat.choose_symm hn1le]
        _ ≤ 2 * ((n : ℝ) + 1) *
            Real.exp (-2 * r ^ 2 * n * τ ^ 2 / max 1 A) := hcontrol
  | true =>
      simp only [↓reduceIte]
      have htreated := hsample n P.pop.n1 r (max 1 A) τ z
        (by omega) hn1lt hr halloc1 hC hmean hτ
      simpa only [probability, assignments, Finset.card_powersetCard,
        Finset.card_univ, Fintype.card_fin, E] using htreated

end
end AronowAudit.P002.Wave1.E61Eigenvalue
