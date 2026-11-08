import SAP.P002b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002b.WH.W1.P.T26_L4

open SAP.P002b

def openCell (cuts : Finset ℝ) (t : Finset ℝ) : Set ℝ :=
  {x | x ∉ cuts ∧ ∀ c ∈ cuts, (x < c ↔ c ∈ t)}

lemma openCell_ordConnected (cuts : Finset ℝ) (t : Finset ℝ) :
    Set.OrdConnected (openCell cuts t) := by
  apply Set.ordConnected_of_Ioo
  intro x hx y hy hxy z hz
  refine ⟨?_, ?_⟩
  · intro hzcut
    by_cases hct : z ∈ t
    · have hyz : y < z := (hy.2 z hzcut).2 hct
      exact (not_lt_of_ge (le_of_lt hz.2)) hyz
    · have hxz : x < z := hz.1
      exact hct ((hx.2 z hzcut).mp hxz)
  · intro c hc
    constructor
    · intro hzc
      by_contra hct
      have hxc : x < c := lt_trans hz.1 hzc
      exact hct ((hx.2 c hc).mp hxc)
    · intro hct
      have hyc : y < c := (hy.2 c hc).mpr hct
      exact lt_trans hz.2 hyc

lemma sameCell_of_mem {cuts : Finset ℝ} {t : Finset ℝ} {x y : ℝ}
    (hx : x ∈ openCell cuts t) (hy : y ∈ openCell cuts t) :
    SameOpenCell cuts x y := by
  refine ⟨hx.1, hy.1, ?_⟩
  intro c hc
  exact (hx.2 c hc).trans (hy.2 c hc).symm

noncomputable def cellPiece (s : Set ℝ) (cuts t : Finset ℝ) : Set ℝ := by
  classical
  exact if ∃ x, x ∈ openCell cuts t ∧ x ∈ s then openCell cuts t else ∅

noncomputable def cutPiece (s : Set ℝ) (c : ℝ) : Set ℝ := by
  classical
  exact if c ∈ s then {c} else ∅

lemma cellPiece_ordConnected (s : Set ℝ) (cuts t : Finset ℝ) :
    Set.OrdConnected (cellPiece s cuts t) := by
  classical
  by_cases h : ∃ x, x ∈ openCell cuts t ∧ x ∈ s
  · simpa [cellPiece, h] using openCell_ordConnected cuts t
  · simpa [cellPiece, h] using (Set.ordConnected_empty : Set.OrdConnected (∅ : Set ℝ))

lemma cutPiece_ordConnected (s : Set ℝ) (c : ℝ) :
    Set.OrdConnected (cutPiece s c) := by
  classical
  by_cases h : c ∈ s
  · simpa [cutPiece, h] using (Set.ordConnected_singleton : Set.OrdConnected ({c} : Set ℝ))
  · simpa [cutPiece, h] using (Set.ordConnected_empty : Set.OrdConnected (∅ : Set ℝ))

lemma cellPiece_subset (s : Set ℝ) (cuts : Finset ℝ)
    (hconst : ∀ x y : ℝ, SameOpenCell cuts x y → (x ∈ s ↔ y ∈ s))
    (t : Finset ℝ) : cellPiece s cuts t ⊆ s := by
  classical
  intro x hx
  by_cases h : ∃ y, y ∈ openCell cuts t ∧ y ∈ s
  · have hxcell : x ∈ openCell cuts t := by
      simpa [cellPiece, h] using hx
    rcases h with ⟨y, hycell, hys⟩
    exact (hconst x y (sameCell_of_mem hxcell hycell)).mpr hys
  · simp [cellPiece, h] at hx

lemma cutPiece_subset (s : Set ℝ) (c : ℝ) : cutPiece s c ⊆ s := by
  classical
  intro x hx
  by_cases h : c ∈ s
  · have hx' : x ∈ ({c} : Set ℝ) := by simpa [cutPiece, h] using hx
    simpa [Set.mem_singleton_iff.mp hx'] using h
  · simp [cutPiece, h] at hx

def piece (s : Set ℝ) (cuts : Finset ℝ) :
    ( {t : Finset ℝ // t ∈ cuts.powerset} ⊕ {c : ℝ // c ∈ cuts}) → Set ℝ
  | Sum.inl t => cellPiece s cuts t.1
  | Sum.inr c => cutPiece s c.1

end SAP.P002b.WH.W1.P.T26_L4

open SAP.P002b.WH.W1
open SAP.P002b.WH.W1.P.T26_L4

theorem SAP.P002b.WH.W1.T26_L4_proof : SAP.P002b.WH.W1.T26_L4 := by
  classical
  intro s cuts hconst
  let A := {t : Finset ℝ // t ∈ cuts.powerset}
  let B := {c : ℝ // c ∈ cuts}
  let J := A ⊕ B
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let I : Fin (Fintype.card J) → Set ℝ := fun i => piece s cuts (e.symm i)
  refine ⟨Fintype.card J, I, ?_, ?_⟩
  · intro i
    cases hidx : e.symm i with
    | inl t =>
        simpa [I, piece, hidx] using cellPiece_ordConnected s cuts t.1
    | inr c =>
        simpa [I, piece, hidx] using cutPiece_ordConnected s c.1
  · intro x
    constructor
    · intro hx
      by_cases hcut : x ∈ cuts
      · let c : B := ⟨x, hcut⟩
        refine ⟨e (Sum.inr c), ?_⟩
        change x ∈ piece s cuts (e.symm (e (Sum.inr c)))
        rw [Equiv.symm_apply_apply]
        change x ∈ cutPiece s c.1
        have hc : c.1 ∈ s := by simpa [c] using hx
        rw [cutPiece, if_pos hc]
        simp [c]
      · let t : Finset ℝ := cuts.filter (fun c => x < c)
        have ht : t ∈ cuts.powerset := by
          apply Finset.mem_powerset.2
          intro c hc
          have hc' : c ∈ cuts ∧ x < c := by simpa [t] using hc
          exact hc'.1
        have hcell : x ∈ openCell cuts t := by
          refine ⟨hcut, ?_⟩
          intro c hc
          have hmem : c ∈ t ↔ c ∈ cuts ∧ x < c := by simp [t]
          rw [hmem]
          simp [hc]
        let a : A := ⟨t, ht⟩
        refine ⟨e (Sum.inl a), ?_⟩
        change x ∈ piece s cuts (e.symm (e (Sum.inl a)))
        rw [Equiv.symm_apply_apply]
        change x ∈ cellPiece s cuts t
        have hex : ∃ y, y ∈ openCell cuts t ∧ y ∈ s := ⟨x, hcell, hx⟩
        simp [cellPiece, hex, hcell]
    · rintro ⟨i, hi⟩
      change x ∈ piece s cuts (e.symm i) at hi
      cases hidx : e.symm i with
      | inl t =>
          have hx' : x ∈ cellPiece s cuts t.1 := by
            simpa [piece, hidx] using hi
          exact cellPiece_subset s cuts hconst t.1 hx'
      | inr c =>
          have hx' : x ∈ cutPiece s c.1 := by
            simpa [piece, hidx] using hi
          exact cutPiece_subset s c.1 hx'
