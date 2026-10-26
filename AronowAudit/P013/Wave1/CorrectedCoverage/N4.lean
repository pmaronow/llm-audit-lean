import AronowAudit.P013.Wave1.CorrectedCoverageBlueprint

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.CorrectedCoverage

open AronowAudit.P013 Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- Add loops to the genuine C5 graph and transfer full-vector independence to scores. -/
theorem n4_proof : N4 := by
  classical
  intro h2 S hc5
  obtain ⟨m, h, hh⟩ := hc5
  refine ⟨m + 1, ?_⟩
  intro n
  let X : Fin (n + 1) → Fin (S.experiment n).supportSize → ℝ :=
    htScore (seqPopulation S n) (S.treated n) (S.control n)
  let G : Fin (n + 1) → Fin (n + 1) → Prop := fun i j => i = j ∨ h n i j = true
  have hsymm : ∀ i j, G i j → G j i := by
    intro i j hij
    rcases hij with hij | hij
    · exact Or.inl hij.symm
    · exact Or.inr (by rw [← (hh n).1 i j]; exact hij)
  have hindep : ∀ A B : Finset (Fin (n + 1)),
      (∀ a ∈ A, ∀ b ∈ B, ¬ G a b) →
      ProbabilityTheory.IndepFun (fun z (i : A) => X i.1 z)
        (fun z (j : B) => X j.1 z) (designMeasure (seqLaw S n)) := by
    intro A B hsep
    have hdisj : Disjoint A B := Finset.disjoint_left.mpr (by
      intro i hiA hiB
      exact hsep i hiA i hiB (Or.inl rfl))
    have hno : CorrectedNoEdge (h n) A B := by
      apply (corrected_symmetric_equivalence (h n) (hh n).1 A B).mpr
      intro i hi j hj
      cases hij : h n i j with
      | false => rfl
      | true => exact False.elim (hsep i hi j hj (Or.inr hij))
    have hK : 0 < (S.experiment n).exposureSize :=
      lt_of_le_of_lt (Nat.zero_le (S.treated n).val) (S.treated n).isLt
    have hvec := h2 hK (seqLaw S n) (seqPopulation S n).exposure A B
      ((hh n).2.1 A B hdisj hno)
    let score : Fin (n + 1) → Fin (S.experiment n).exposureSize → ℝ := fun i a =>
      ((if a = S.treated n then 1 else 0) *
          ((seqPopulation S n).outcome i (S.treated n) /
            pi (seqPopulation S n) i (S.treated n)) -
        (if a = S.control n then 1 else 0) *
          ((seqPopulation S n).outcome i (S.control n) /
            pi (seqPopulation S n) i (S.control n))) -
      ((seqPopulation S n).outcome i (S.treated n) -
        (seqPopulation S n).outcome i (S.control n))
    let φ : (A → Fin (S.experiment n).exposureSize) → (A → ℝ) :=
      fun v i => score i.1 (v i)
    let ψ : (B → Fin (S.experiment n).exposureSize) → (B → ℝ) :=
      fun v i => score i.1 (v i)
    have hφ : Measurable φ := measurable_of_finite _
    have hψ : Measurable ψ := measurable_of_finite _
    simpa only [Function.comp_def, φ, ψ, score, X, htScore, indicator] using
      hvec.comp hφ hψ
  let D : Causalean.Mathlib.Probability.SteinMethod.DepGraph X
      (designMeasure (seqLaw S n)) := {
    G := G
    decG := inferInstance
    refl := fun i => Or.inl rfl
    symm := hsymm
    meas := fun i => measurable_of_finite _
    indep := hindep }
  refine ⟨D, ?_⟩
  intro i
  let H : Finset (Fin (n + 1)) := Finset.univ.filter (fun j => h n i j = true)
  have hsub : D.nbhd i ⊆ insert i H := by
    intro j hj
    have hij := D.mem_nbhd_iff.mp hj
    change i = j ∨ h n i j = true at hij
    rcases hij with hij | hij
    · subst j
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)
  have hcardH : H.card = ∑ j, (if h n i j = true then 1 else 0 : ℕ) := by
    simp only [H, Finset.card_eq_sum_ones, Finset.sum_filter]
  have hrow : H.card ≤ m := by
    rw [hcardH]
    exact (hh n).2.2 i
  calc
    (D.nbhd i).card ≤ (insert i H).card := Finset.card_le_card hsub
    _ ≤ H.card + 1 := Finset.card_insert_le i H
    _ ≤ m + 1 := Nat.add_le_add_right hrow 1

end

end AronowAudit.P013.Wave1.CorrectedCoverage
