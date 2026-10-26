import AronowAudit.P044.Wave1.SimulatedVarianceBlueprint
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.CardEmbedding

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

set_option maxRecDepth 10000 in
/-- Every image misses one point, and the fiber at that point is the type of
embeddings into its 65-element complement. -/
theorem n8_proof : N8 := by
  classical
  change EmbeddingFiberSum
  intro F g hF
  have hex (σ : Fin 65 ↪ Fin 66) :
      ∃ t : Fin 66, t ∉ Finset.univ.map σ := by
    by_contra hn
    have hall : ∀ t : Fin 66, t ∈ Finset.univ.map σ := by
      intro t
      by_contra ht
      exact hn ⟨t, ht⟩
    have heq : Finset.univ.map σ = (Finset.univ : Finset (Fin 66)) :=
      Finset.eq_univ_of_forall hall
    have hc : (Finset.univ.map σ).card = 65 := by
      simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin]
    rw [heq] at hc
    norm_num at hc
  have hImage (σ : Fin 65 ↪ Fin 66) (t : Fin 66)
      (ht : t ∉ Finset.univ.map σ) :
      Finset.univ.map σ = Finset.univ.erase t := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro hxt
      exact ht (hxt ▸ hx)
    · simp only [Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_map,
        Finset.card_univ, Fintype.card_fin] <;> omega
  let omitted : (Fin 65 ↪ Fin 66) → Fin 66 := fun σ => Classical.choose (hex σ)
  have hNot (σ : Fin 65 ↪ Fin 66) : omitted σ ∉ Finset.univ.map σ :=
    Classical.choose_spec (hex σ)
  have hSpec (σ : Fin 65 ↪ Fin 66) :
      Finset.univ.map σ = Finset.univ.erase (omitted σ) :=
    hImage σ (omitted σ) (hNot σ)
  have hOmitted (σ : Fin 65 ↪ Fin 66) (t : Fin 66)
      (ht : Finset.univ.map σ = Finset.univ.erase t) : omitted σ = t := by
    by_contra hne
    apply hNot σ
    rw [ht]
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
  have hAvoid (t : Fin 66) (σ : Fin 65 ↪ Fin 66) (ht : omitted σ = t)
      (r : Fin 65) : σ r ≠ t := by
    intro hr
    apply hNot σ
    rw [ht]
    exact Finset.mem_map.mpr ⟨r, Finset.mem_univ _, hr⟩
  let restrict (t : Fin 66) (σ : {σ : Fin 65 ↪ Fin 66 // omitted σ = t}) :
      Fin 65 ↪ {x : Fin 66 // x ≠ t} :=
    { toFun := fun r => ⟨σ.1 r, hAvoid t σ.1 σ.2 r⟩
      inj' := by
        intro r s hrs
        exact σ.1.injective (congrArg Subtype.val hrs) }
  let extend (t : Fin 66) (τ : Fin 65 ↪ {x : Fin 66 // x ≠ t}) : Fin 65 ↪ Fin 66 :=
    { toFun := fun r => (τ r).val
      inj' := by
        intro r s hrs
        exact τ.injective (Subtype.ext hrs) }
  have hExtend (t : Fin 66) (τ : Fin 65 ↪ {x : Fin 66 // x ≠ t}) :
      omitted (extend t τ) = t := by
    apply hOmitted (extend t τ) t
    apply hImage (extend t τ) t
    intro ht
    obtain ⟨r, _, hr⟩ := Finset.mem_map.mp ht
    exact (τ r).property hr
  let fiberEquiv (t : Fin 66) :
      {σ : Fin 65 ↪ Fin 66 // omitted σ = t} ≃
        (Fin 65 ↪ {x : Fin 66 // x ≠ t}) :=
    { toFun := restrict t
      invFun := fun τ => ⟨extend t τ, hExtend t τ⟩
      left_inv := by
        intro σ
        apply Subtype.ext
        apply Function.Embedding.ext
        intro r
        rfl
      right_inv := by
        intro τ
        apply Function.Embedding.ext
        intro r
        apply Subtype.ext
        rfl }
  have hComplementCard (t : Fin 66) :
      Fintype.card {x : Fin 66 // x ≠ t} = 65 := by
    calc
      Fintype.card {x : Fin 66 // x ≠ t} =
          Fintype.card (Fin 66) - Fintype.card {x : Fin 66 // x = t} :=
        Fintype.card_subtype_compl (fun x : Fin 66 => x = t)
      _ = 65 := by
        norm_num only [Fintype.card_fin, Fintype.card_subtype_eq]
  have hFiberCard (t : Fin 66) :
      Fintype.card {σ : Fin 65 ↪ Fin 66 // omitted σ = t} = Nat.factorial 65 := by
    calc
      Fintype.card {σ : Fin 65 ↪ Fin 66 // omitted σ = t} =
          Fintype.card (Fin 65 ↪ {x : Fin 66 // x ≠ t}) :=
        Fintype.card_congr (fiberEquiv t)
      _ = Nat.factorial 65 := by
        rw [Fintype.card_embedding_eq, hComplementCard t, Fintype.card_fin,
          Nat.descFactorial_self]
  have hFiberFinsetCard (t : Fin 66) :
      (Finset.univ.filter (fun σ : Fin 65 ↪ Fin 66 => omitted σ = t)).card =
        Nat.factorial 65 := by
    calc
      (Finset.univ.filter (fun σ : Fin 65 ↪ Fin 66 => omitted σ = t)).card =
          Fintype.card {σ : Fin 65 ↪ Fin 66 // omitted σ = t} :=
        (Fintype.card_subtype (fun σ : Fin 65 ↪ Fin 66 => omitted σ = t)).symm
      _ = Nat.factorial 65 := hFiberCard t
  calc
    (∑ σ : Fin 65 ↪ Fin 66, F σ) =
        ∑ t : Fin 66, ∑ σ ∈ Finset.univ.filter (fun σ => omitted σ = t), F σ :=
      (Finset.sum_fiberwise (Finset.univ : Finset (Fin 65 ↪ Fin 66)) omitted F).symm
    _ = ∑ t : Fin 66, (Nat.factorial 65 : ℝ) * g t := by
      apply Finset.sum_congr rfl
      intro t _
      calc
        (∑ σ ∈ Finset.univ.filter (fun σ => omitted σ = t), F σ) =
            ∑ _σ ∈ Finset.univ.filter (fun σ => omitted σ = t), g t := by
          apply Finset.sum_congr rfl
          intro σ hσ
          have ht : omitted σ = t := (Finset.mem_filter.mp hσ).2
          apply hF σ t
          simpa only [ht] using hSpec σ
        _ = (Nat.factorial 65 : ℝ) * g t := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [hFiberFinsetCard t]
    _ = (Nat.factorial 65 : ℝ) * ∑ t : Fin 66, g t := by
      rw [Finset.mul_sum]

end

end AronowAudit.P044.Wave1.SimulatedVariance
