import SAP.P037b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037b.WH.W1.P.T22_L2

open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma iidComplementSumW1 {Ω : Type} [Fintype Ω] (mass : Ω → ℝ) (J : ℕ)
    (E : (Fin J → Ω) → Prop) :
    iidProbabilityW1 mass J E + iidProbabilityW1 mass J (fun draws => ¬ E draws) =
      ∑ draws : Fin J → Ω, iidMassW1 mass draws := by
  classical
  unfold iidProbabilityW1 iidExpectationW1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro draws _
  by_cases h : E draws <;> simp [h]

lemma passingSequenceW1 {Ω I : Type} [Fintype Ω]
    (D : Ω → I → Fin 5) (i : I)
    (hlabel : ∀ k : Fin 4, ∃ w, D w i = k.castSucc) :
    ∃ draws : Fin 10000 → Ω,
      i ∈ exposureProbabilityCutoff (estimatedExposureW1 D draws) (1/100) := by
  classical
  let w : Fin 4 → Ω := fun k => Classical.choose (hlabel k)
  have hw (k : Fin 4) : D (w k) i = k.castSucc := Classical.choose_spec (hlabel k)
  let lab (j : Fin 10000) : Fin 4 := ⟨j.val / 2500, by have := j.isLt; omega⟩
  let idx (k : Fin 4) (r : Fin 101) : Fin 10000 :=
    ⟨k.val * 2500 + r.val, by have hk := k.isLt; have hr := r.isLt; omega⟩
  let S (k : Fin 4) : Finset (Fin 10000) := Finset.univ.image (idx k)
  let draws : Fin 10000 → Ω := fun j => w (lab j)
  have hidx (k : Fin 4) : Function.Injective (idx k) := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    dsimp [idx] at hv
    omega
  have hcard (k : Fin 4) : (S k).card = 101 := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ (hidx k)]
    simp
  have hsub (k : Fin 4) : S k ⊆ Finset.univ.filter
      (fun j => D (draws j) i = k.castSucc) := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨r, _, rfl⟩
    have hlab : lab (idx k r) = k := by
      apply Fin.ext
      simp [lab, idx]
      omega
    simp [draws, hlab, hw]
  have hcount (k : Fin 4) : 101 ≤
      (Finset.univ.filter (fun j => D (draws j) i = k.castSucc)).card := by
    calc
      101 = (S k).card := (hcard k).symm
      _ ≤ _ := Finset.card_le_card (hsub k)
  have hfreq (k : Fin 4) : (1/100 : ℝ) < estimatedExposureW1 D draws i k := by
    change (1/100 : ℝ) <
      ((Finset.univ.filter (fun j => D (draws j) i = k.castSucc)).card : ℝ) / 10000
    have hc : (101 : ℝ) ≤
        ((Finset.univ.filter (fun j => D (draws j) i = k.castSucc)).card : ℝ) := by
      exact_mod_cast hcount k
    have hlow : (1/100 : ℝ) < (101 : ℝ) / 10000 := by norm_num
    have hhigh : (101 : ℝ) / 10000 ≤
        ((Finset.univ.filter (fun j => D (draws j) i = k.castSucc)).card : ℝ) / 10000 :=
      div_le_div_of_nonneg_right hc (by norm_num)
    exact lt_of_lt_of_le hlow hhigh
  refine ⟨draws, ?_⟩
  change ∀ k : Fin 4, (1/100 : ℝ) < estimatedExposureW1 D draws i k
  exact hfreq

lemma failingSequenceW1 {Ω I : Type} [Fintype Ω]
    (D : Ω → I → Fin 5) (i : I)
    (hlabel : ∀ k : Fin 4, ∃ w, D w i = k.castSucc) :
    ∃ draws : Fin 10000 → Ω,
      ¬ i ∈ exposureProbabilityCutoff (estimatedExposureW1 D draws) (1/100) := by
  classical
  let base : Ω := Classical.choose (hlabel 0)
  have hbase : D base i = (0 : Fin 4).castSucc := Classical.choose_spec (hlabel 0)
  let draws : Fin 10000 → Ω := fun _ => base
  have hneq : D base i ≠ (1 : Fin 4).castSucc := by
    rw [hbase]
    decide
  have hzero : (Finset.univ.filter
      (fun j : Fin 10000 => D (draws j) i = (1 : Fin 4).castSucc)).card = 0 := by
    simp [draws, hbase]
  refine ⟨draws, ?_⟩
  intro hpass
  have h1 := (Set.mem_setOf_eq.mp hpass) 1
  change (1/100 : ℝ) < estimatedExposureW1 D draws i 1 at h1
  rw [show estimatedExposureW1 D draws i 1 = 0 by
    change ((Finset.univ.filter
      (fun j : Fin 10000 => D (draws j) i = (1 : Fin 4).castSucc)).card : ℝ) / 10000 = 0
    rw [hzero]
    norm_num] at h1
  norm_num at h1

end SAP.P037b.WH.W1.P.T22_L2

theorem SAP.P037b.WH.W1.T22_L2_proof : SAP.P037b.WH.W1.T22_L2 := by
  classical
  unfold SAP.P037b.WH.W1.T22_L2 SAP.P037b.T22JointCutoffW1
  intro Ω I hΩ P D i hi
  have hi' : ∀ k : Fin 4,
      0 < eventProbability P (fun z => D z i = k.castSucc) ∧
      eventProbability P (fun z => D z i = k.castSucc) < 1 := by
    simpa [positiveExposurePopulation, Set.mem_setOf_eq] using hi
  have hlabel : ∀ k : Fin 4, ∃ w, D w i = k.castSucc := by
    intro k
    exact (AronowAudit.P037.Wave1.analysis_prob_positive_iff
      ⟨P.mass, P.positive, P.total⟩ (fun z => D z i = k.castSucc)).mp (hi' k).1
  obtain ⟨pass, hpass⟩ :=
    SAP.P037b.WH.W1.P.T22_L2.passingSequenceW1 D i hlabel
  obtain ⟨fail, hfail⟩ :=
    SAP.P037b.WH.W1.P.T22_L2.failingSequenceW1 D i hlabel
  let E : (Fin 10000 → Ω) → Prop := fun draws =>
    i ∈ exposureProbabilityCutoff (estimatedExposureW1 D draws) (1/100)
  have hmass (draws : Fin 10000 → Ω) : 0 < iidMassW1 P.mass draws := by
    unfold iidMassW1
    exact Finset.prod_pos (by
      intro j hj
      exact P.positive (draws j))
  have hpos : 0 < iidProbabilityW1 P.mass 10000 E := by
    have hs := AronowAudit.P037.Wave1.estimated_cutoff_event_pos
      (fun draws : Fin 10000 → Ω => iidMassW1 P.mass draws) hmass E ⟨pass, hpass⟩
    simpa [E, iidProbabilityW1, iidExpectationW1, iidMassW1] using hs
  have hneg : 0 < iidProbabilityW1 P.mass 10000 (fun draws => ¬ E draws) := by
    have hs := AronowAudit.P037.Wave1.estimated_cutoff_event_pos
      (fun draws : Fin 10000 → Ω => iidMassW1 P.mass draws) hmass
      (fun draws => ¬ E draws) ⟨fail, hfail⟩
    simpa [E, iidProbabilityW1, iidExpectationW1, iidMassW1] using hs
  have hsum : iidProbabilityW1 P.mass 10000 E +
      iidProbabilityW1 P.mass 10000 (fun draws => ¬ E draws) = 1 := by
    rw [SAP.P037b.WH.W1.P.T22_L2.iidComplementSumW1,
      SAP.P037b.WH.W1.iidTotalW1]
  constructor
  · simpa [E] using hpos
  · have hu : iidProbabilityW1 P.mass 10000 E < 1 := by linarith [hsum, hneg]
    simpa [E] using hu
