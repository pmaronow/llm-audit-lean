import AronowAudit.P044.Wave1.SimulatedVarianceBlueprint

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

set_option maxRecDepth 10000 in
/-- Supported injective banks are in bijection with embeddings into the 66-point design. -/
theorem n7_proof : N7 := by
  classical
  intro h1 h6
  change Function.Injective cliqueAssignments at h1
  intro P hP G
  let bankOf : (Fin 65 ↪ Fin 66) → (Fin 65 → Assignment 12) :=
    fun σ r => cliqueAssignments (σ r)
  have hbankOf : Function.Injective bankOf := by
    intro σ τ h
    apply Function.Embedding.ext
    intro r
    exact h1 (congrFun h r)
  have hgood (σ : Fin 65 ↪ Fin 66) :
      Function.Injective (bankOf σ) ∧ ∀ r, bankOf σ r ∈ Set.range cliqueAssignments := by
    constructor
    · exact h1.comp σ.injective
    · intro r
      exact ⟨σ r, rfl⟩
  have hrepr (b : Fin 65 → Assignment 12)
      (hb : Function.Injective b ∧ ∀ r, b r ∈ Set.range cliqueAssignments) :
      ∃ σ : Fin 65 ↪ Fin 66, bankOf σ = b := by
    have hpre : ∀ r, ∃ t : Fin 66, cliqueAssignments t = b r := hb.2
    choose f hf using hpre
    have hfinj : Function.Injective f := by
      intro r s hrs
      apply hb.1
      calc
        b r = cliqueAssignments (f r) := (hf r).symm
        _ = cliqueAssignments (f s) := congrArg cliqueAssignments hrs
        _ = b s := hf s
    let σ : Fin 65 ↪ Fin 66 := ⟨f, hfinj⟩
    refine ⟨σ, ?_⟩
    funext r
    exact hf r
  let B : Finset (Fin 65 → Assignment 12) := Finset.univ.image bankOf
  have hout (b : Fin 65 → Assignment 12) (hb : b ∉ B) :
      ¬ (Function.Injective b ∧ ∀ r, b r ∈ Set.range cliqueAssignments) := by
    intro h
    obtain ⟨σ, hσ⟩ := hrepr b h
    apply hb
    exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, hσ⟩
  calc
    (∑ b, distinctBankMass P b * G b) =
        ∑ b ∈ B, distinctBankMass P b * G b := by
      symm
      apply Finset.sum_subset (Finset.subset_univ B)
      intro b _ hb
      rw [(h6 P hP b).2 (hout b hb), zero_mul]
    _ = ∑ σ : Fin 65 ↪ Fin 66, distinctBankMass P (bankOf σ) * G (bankOf σ) := by
      dsimp only [B]
      rw [Finset.sum_image (fun σ _ τ _ h => hbankOf h)]
    _ = ∑ σ : Fin 65 ↪ Fin 66, (1 / (Nat.factorial 66 : ℝ)) * G (bankOf σ) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [(h6 P hP (bankOf σ)).1 (hgood σ)]
    _ = (∑ σ : Fin 65 ↪ Fin 66, G (fun r => cliqueAssignments (σ r))) /
        (Nat.factorial 66 : ℝ) := by
      change (∑ σ : Fin 65 ↪ Fin 66, (1 / (Nat.factorial 66 : ℝ)) * G (bankOf σ)) =
        (∑ σ : Fin 65 ↪ Fin 66, G (bankOf σ)) / (Nat.factorial 66 : ℝ)
      rw [← Finset.mul_sum]
      ring

end

end AronowAudit.P044.Wave1.SimulatedVariance
