import AronowAudit.P012.P012_Identification
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.Pi

/-!
Finite enumeration of the compatible states modulo unsampled names.
The quotient forgets the trait table outside the displayed vertex set.
-/

namespace AronowAudit.P012.Wave1

open Finset
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000
set_option linter.unusedVariables false

attribute [local simp] Finset.filter_insert Finset.image_insert Finset.sdiff_insert
  Finset.insert_sdiff_of_mem Finset.insert_sdiff_of_notMem Finset.insert_subset_iff
  Finset.filter_singleton Finset.image_singleton Finset.sdiff_singleton_eq_erase
  Finset.erase_insert_of_ne

theorem cfn_relabel_refl (D : Data) (H : State) : Relabeling D H H := by
  refine ⟨Equiv.refl _, ?_, ?_, ?_, ?_⟩ <;> simp

theorem cfn_relabel_symm (D : Data) {H K : State}
    (h : Relabeling D H K) : Relabeling D K H := by
  rcases h with ⟨e, he, hV, hE, ht⟩
  refine ⟨e.symm, ?_, ?_, ?_, ?_⟩
  · intro i hi
    apply e.injective
    rw [e.apply_symm_apply, he i hi]
  · rw [← hV, image_image]
    simp
  · rw [← hE, image_image]
    simp [Function.comp_def, image_image]
  · intro v hv
    rw [← hV] at hv
    rcases mem_image.mp hv with ⟨w, hw, rfl⟩
    simpa using (ht w hw).symm

theorem cfn_relabel_trans (D : Data) {H K L : State}
    (hHK : Relabeling D H K) (hKL : Relabeling D K L) : Relabeling D H L := by
  rcases hHK with ⟨e, he, hV, hE, ht⟩
  rcases hKL with ⟨f, hf, hV', hE', ht'⟩
  refine ⟨e.trans f, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [Equiv.trans_apply, he i hi, hf i hi]
  · calc
      H.vertices.image (e.trans f) = (H.vertices.image e).image f := by
        simp only [image_image, Equiv.coe_trans]
      _ = L.vertices := by rw [hV, hV']
  · calc
      H.edges.image (fun edge => edge.image (e.trans f)) =
          (H.edges.image (fun edge => edge.image e)).image
            (fun edge => edge.image f) := by
        simp only [image_image, Equiv.coe_trans, Function.comp_def]
      _ = L.edges := by rw [hE, hE']
  · intro v hv
    exact (ht' (e v) (hV ▸ mem_image_of_mem e hv)).trans (ht v hv)

def cfn_stateSetoid (D : Data) : Setoid State where
  r := Relabeling D
  iseqv := ⟨cfn_relabel_refl D,
    fun h => cfn_relabel_symm D h, fun h₁ h₂ => cfn_relabel_trans D h₁ h₂⟩

/-- A fixed pool large enough to hold all displayed unsampled vertices. -/
def cfn_carrier (D : Data) : Finset Vertex :=
  sampledVertices D ∪ (range (totalSpare D)).image (u 0)

theorem cfn_fresh_not_sampled (D : Data) (k : ℕ) :
    u 0 k ∉ sampledVertices D := by
  simp [sampledVertices, s, u]

/-- The finite renaming agrees with the identity at every sampled vertex. -/
theorem cfn_bounded_permutation (D : Data) (H : State) (hD : Admissible D)
    (hH : Compatible D H) :
    ∃ e : Equiv.Perm Vertex,
      (∀ i ∈ D.sampled, e (s i) = s i) ∧
      H.vertices.image e ⊆ cfn_carrier D := by
  classical
  obtain ⟨j⟩ : Nonempty (↥(unsampled D H) ↪ Fin (totalSpare D)) :=
    Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_coe, Fintype.card_fin] using
        unsampled_card_bound D H hD hH)
  let g : ↥H.vertices → Vertex := fun v =>
    if hv : (v : Vertex) ∈ sampledVertices D then (v : Vertex)
    else u 0 (j ⟨v, mem_sdiff.mpr ⟨v.property, hv⟩⟩).val
  have hg : Function.Injective g := by
    intro x y hxy
    by_cases hx : (x : Vertex) ∈ sampledVertices D
    · by_cases hy : (y : Vertex) ∈ sampledVertices D
      · apply Subtype.ext
        simpa only [g, dite_eq_left hx, dite_eq_left hy] using hxy
      · have heq : (x : Vertex) =
            u 0 (j ⟨y, mem_sdiff.mpr ⟨y.property, hy⟩⟩).val := by
          simpa only [g, dite_eq_left hx, dite_eq_right hy] using hxy
        exact False.elim (cfn_fresh_not_sampled D _ (heq ▸ hx))
    · by_cases hy : (y : Vertex) ∈ sampledVertices D
      · have heq : u 0 (j ⟨x, mem_sdiff.mpr ⟨x.property, hx⟩⟩).val =
            (y : Vertex) := by
          simpa only [g, dite_eq_right hx, dite_eq_left hy] using hxy
        exact False.elim (cfn_fresh_not_sampled D _ (heq.symm ▸ hy))
      · have heq : u 0 (j ⟨x, mem_sdiff.mpr ⟨x.property, hx⟩⟩).val =
            u 0 (j ⟨y, mem_sdiff.mpr ⟨y.property, hy⟩⟩).val := by
          simpa only [g, dite_eq_right hx, dite_eq_right hy] using hxy
        have hj : j ⟨x, mem_sdiff.mpr ⟨x.property, hx⟩⟩ =
            j ⟨y, mem_sdiff.mpr ⟨y.property, hy⟩⟩ :=
          Fin.ext (by simpa [u] using heq)
        have hval : (x : Vertex) = (y : Vertex) :=
          congrArg (fun v : ↥(unsampled D H) => (v : Vertex)) (j.injective hj)
        exact Subtype.ext hval
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair
    (fun v : ↥H.vertices => (v : Vertex)) g Subtype.val_injective hg
  refine ⟨e, ?_, ?_⟩
  · intro i hi
    have hs : s i ∈ sampledVertices D := mem_image_of_mem s hi
    have hvertex : s i ∈ H.vertices := hH.2.1 hs
    rw [he ⟨s i, hvertex⟩]
    simp only [g, dite_eq_left hs]
  · intro w hw
    rcases mem_image.mp hw with ⟨v, hv, rfl⟩
    rw [he ⟨v, hv⟩]
    dsimp only [g, cfn_carrier]
    split_ifs with hs
    · exact mem_union_left _ hs
    · apply mem_union_right
      exact mem_image.mpr ⟨_, mem_range.mpr (j _).isLt, rfl⟩

/-- Only a finite trait table is stored, even though `State.trait` is global. -/
abbrev cfn_Code (D : Data) :=
  ↥((cfn_carrier D).powerset) ×
    ↥((cfn_carrier D).powerset.powerset) × (↥(cfn_carrier D) → Bool)

def cfn_decode (D : Data) (c : cfn_Code D) : State where
  vertices := c.1.val
  edges := c.2.1.val
  trait := fun v => if hv : v ∈ cfn_carrier D then c.2.2 ⟨v, hv⟩ else false

/-- Every compatible class has a code in the fixed finite carrier. -/
theorem cfn_code_covers (D : Data) (H : State) (hD : Admissible D)
    (hH : Compatible D H) :
    ∃ c : cfn_Code D, Relabeling D H (cfn_decode D c) := by
  classical
  obtain ⟨e, he, hbound⟩ := cfn_bounded_permutation D H hD hH
  let V : Finset Vertex := H.vertices.image e
  let E : Finset (Finset Vertex) := H.edges.image (fun edge => edge.image e)
  have hE : E ⊆ (cfn_carrier D).powerset := by
    intro edge hedge
    rcases mem_image.mp hedge with ⟨oldEdge, holdEdge, rfl⟩
    apply mem_powerset.mpr
    intro w hw
    rcases mem_image.mp hw with ⟨v, hv, rfl⟩
    exact hbound (mem_image_of_mem e ((hH.1.1 oldEdge holdEdge).2 hv))
  let c : cfn_Code D :=
    (⟨V, mem_powerset.mpr hbound⟩, ⟨E, mem_powerset.mpr hE⟩,
      fun v => H.trait (e.symm v))
  refine ⟨c, e, he, rfl, rfl, ?_⟩
  intro v hv
  have hev : e v ∈ cfn_carrier D := hbound (mem_image_of_mem e hv)
  simp [cfn_decode, c, hev]

/-- Classes that contain an original compatible state. -/
def cfn_classSet (D : Data) : Set (Quotient (cfn_stateSetoid D)) :=
  {q | ∃ H, Compatible D H ∧ Quotient.mk (cfn_stateSetoid D) H = q}

theorem cfn_classes_finite (D : Data) (hD : Admissible D) :
    (cfn_classSet D).Finite := by
  classical
  let f : cfn_Code D → Quotient (cfn_stateSetoid D) :=
    fun c => Quotient.mk _ (cfn_decode D c)
  apply (Set.finite_range f).subset
  intro q hq
  rcases hq with ⟨H, hH, rfl⟩
  obtain ⟨c, hc⟩ := cfn_code_covers D H hD hH
  exact ⟨c, Quotient.sound (cfn_relabel_symm D hc)⟩

/-- Completeness and uniqueness follow by choosing one state in each finite class. -/
theorem compatible_finite_up_to_names_proof (D : Data) (hD : Admissible D) :
    ∃ m : ℕ, ∃ repr : Fin m → State, EnumeratesCompatible D repr := by
  classical
  let Q := ↥(cfn_classSet D)
  let instFintypeCfnQ : Fintype Q := (cfn_classes_finite D hD).fintype
  let e : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let chooseState : Q → State := fun q => Classical.choose q.property
  have hchoose (q : Q) : Compatible D (chooseState q) ∧
      Quotient.mk (cfn_stateSetoid D) (chooseState q) = q.val :=
    Classical.choose_spec q.property
  refine ⟨Fintype.card Q, fun i => chooseState (e.symm i), ?_⟩
  refine ⟨fun i => (hchoose (e.symm i)).1, ?_, ?_⟩
  · intro H hH
    let q : Q := ⟨Quotient.mk _ H, H, hH, rfl⟩
    refine ⟨e q, ?_⟩
    change Relabeling D H (chooseState (e.symm (e q)))
    rw [e.symm_apply_apply]
    exact Quotient.exact (hchoose q).2.symm
  · intro i j hij
    have hq : (e.symm i).val = (e.symm j).val := by
      rw [← (hchoose (e.symm i)).2, ← (hchoose (e.symm j)).2]
      exact Quotient.sound hij
    exact e.symm.injective (Subtype.ext hq)

end
end AronowAudit.P012.Wave1
