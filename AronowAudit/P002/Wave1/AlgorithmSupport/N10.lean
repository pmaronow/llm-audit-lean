import AronowAudit.P002.Wave1.AlgorithmSupportBlueprint
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Finset.Card

namespace AronowAudit.P002.Wave1.AlgorithmSupport
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Construct a terminating Step 4 tail by strong induction on the number of
global crossings strictly to the right of its current left endpoint. -/
theorem n10_proof : N10 := by
  intro hcons M g α J hJ hall
  let remaining : EReal → Finset ℝ :=
    fun l => J.toFinset.filter (fun β => l < (β : EReal))
  have hbuild : ∀ n : ℕ, ∀ (l : EReal) (m : Fin M),
      (remaining l).card = n →
      ∃ pieces : List (RecordedPiece M),
        (∃ r, pieces.head? = some ⟨l, r, m⟩) ∧
        ∀ i : Fin pieces.length,
          Algorithm2Step g α J (pieces.get i) (pieces[i.val + 1]?) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro k ih l m hk
    let C : Set ℝ :=
      {β | l < (β : EReal) ∧ ∃ s, g s ≠ g m ∧ g s β = g m β}
    have hCsub : C ⊆ {β : ℝ | β ∈ J} := by
      intro β hβ
      obtain ⟨s, hs, hsm⟩ := hβ.2
      exact (hJ.2 β).mpr ⟨s, m, hs, hsm⟩
    have hCfin : C.Finite := J.finite_toSet.subset hCsub
    by_cases hC : C.Nonempty
    · -- The least selected-curve crossing is also a global crossing in J.
      obtain ⟨e, he, hmin⟩ :=
        Set.exists_min_image C (fun β : ℝ => β) hCfin hC
      have hleast : IsLeast C e := ⟨he, hmin⟩
      have hle : l < (e : EReal) := he.1
      have heJ : e ∈ J := hCsub he

      -- Moving l to e removes e and cannot add a remaining crossing.
      have hsub : remaining (e : EReal) ⊆ remaining l := by
        intro β hβ
        have hβ' : β ∈ J.toFinset ∧ (e : EReal) < (β : EReal) :=
          Finset.mem_filter.mp hβ
        exact Finset.mem_filter.mpr ⟨hβ'.1, lt_trans hle hβ'.2⟩
      have heOld : e ∈ remaining l :=
        Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr heJ, hle⟩
      have heNew : e ∉ remaining (e : EReal) := by
        intro hem
        have hee : (e : EReal) < (e : EReal) := (Finset.mem_filter.mp hem).2
        exact (lt_irrefl (e : EReal)) hee
      have hstrict : remaining (e : EReal) ⊂ remaining l := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hsub, ?_⟩
        intro heq
        apply heNew
        rw [heq]
        exact heOld
      have hdecrease : (remaining (e : EReal)).card < k := by
        calc
          (remaining (e : EReal)).card < (remaining l).card :=
            Finset.card_lt_card hstrict
          _ = k := hk

      -- This is precisely Algorithm2Step's prescribed next sample, including
      -- the empty-E branch after the last global crossing.
      let E : List ℝ := J.filter (fun β => (e : EReal) < (β : EReal))
      let sample : ℝ :=
        if E = [] then (e : EReal).toReal + 1
        else ((e : EReal).toReal + E.head!) / 2
      obtain ⟨mNext, hmNext⟩ := hall sample
      obtain ⟨rest, ⟨r, hhead⟩, hsteps⟩ :=
        ih (remaining (e : EReal)).card hdecrease (e : EReal) mNext rfl
      let p : RecordedPiece M := ⟨l, (e : EReal), m⟩
      have hpStep : Algorithm2Step g α J p rest.head? := by
        change
          (if C.Nonempty then
            ∃ e' : ℝ, IsLeast C e' ∧ (e : EReal) = (e' : EReal)
          else (e : EReal) = ⊤) ∧
          (match rest.head? with
          | none => (e : EReal) = ⊤
          | some q => (e : EReal) ≠ ⊤ ∧ q.left = (e : EReal) ∧
              q.index ∈ mcIndices g α sample)
        constructor
        · rw [if_pos hC]
          exact ⟨e, hleast, rfl⟩
        · rw [hhead]
          change (e : EReal) ≠ ⊤ ∧ (e : EReal) = (e : EReal) ∧
            mNext ∈ mcIndices g α sample
          exact ⟨EReal.coe_ne_top e, rfl, hmNext⟩
      refine ⟨p :: rest, ?_, ?_⟩
      · exact ⟨(e : EReal), rfl⟩
      · exact (hcons (Algorithm2Step g α J) p rest).mpr ⟨hpStep, hsteps⟩
    · -- No selected-curve crossing remains: record [l, top] and terminate.
      let p : RecordedPiece M := ⟨l, ⊤, m⟩
      have hpStep : Algorithm2Step g α J p none := by
        change
          (if C.Nonempty then
            ∃ e : ℝ, IsLeast C e ∧ (⊤ : EReal) = (e : EReal)
          else (⊤ : EReal) = ⊤) ∧ (⊤ : EReal) = ⊤
        rw [if_neg hC]
        exact ⟨rfl, rfl⟩
      refine ⟨[p], ?_, ?_⟩
      · exact ⟨⊤, rfl⟩
      · apply (hcons (Algorithm2Step g α J) p []).mpr
        constructor
        · exact hpStep
        · intro i
          exact Fin.elim0 i
  intro l m
  exact hbuild (remaining l).card l m rfl

end
end AronowAudit.P002.Wave1.AlgorithmSupport
