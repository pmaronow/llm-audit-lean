import SAP.P012a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a.WH.W2.P.T3_L1

open SAP.P012a
open SAP.P012a.WH.W2
open AronowAudit.P012
open Finset
open scoped Classical

lemma owner_leaf_ranges_disjoint (D : Data) :
    ∀ i ∈ D.sampled, ∀ j ∈ D.sampled, i ≠ j →
      Disjoint ((range (spare D i)).image (u i))
        ((range (spare D j)).image (u j)) := by
  intro i hi j hj hij
  rw [Finset.disjoint_left]
  intro v hvi hvj
  rcases Finset.mem_image.mp hvi with ⟨k, hk, hvk⟩
  rcases Finset.mem_image.mp hvj with ⟨l, hl, hvl⟩
  have heq : u i k = u j l := hvk.trans hvl.symm
  have hp : (i, k) = (j, l) := Sum.inr.inj heq
  exact hij (congrArg Prod.fst hp)

lemma leaf_vertices_card (D : Data) :
    (leafVertices D).card = totalSpare D := by
  rw [leafVertices]
  rw [Finset.card_biUnion (owner_leaf_ranges_disjoint D)]
  rw [totalSpare]
  apply Finset.sum_congr rfl
  intro i hi
  have hinj : Function.Injective (u i) := by
    intro k l h
    have hp : (i, k) = (i, l) := Sum.inr.inj h
    exact congrArg Prod.snd hp
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range]

end SAP.P012a.WH.W2.P.T3_L1

theorem SAP.P012a.WH.W2.T3_L1_proof : SAP.P012a.WH.W2.T3_L1 := by
  intro D same
  have hsample : (sampledVertices D).card = D.sampled.card := by
    rw [sampledVertices, Finset.card_image_of_injective]
    intro i j h
    exact Sum.inl.inj h
  have hdisj : Disjoint (sampledVertices D) (leafVertices D) := by
    rw [Finset.disjoint_left]
    intro v hvS hvL
    rcases Finset.mem_image.mp hvS with ⟨i, hi, hvi⟩
    rcases Finset.mem_biUnion.mp hvL with ⟨j, hj, hvj⟩
    rcases Finset.mem_image.mp hvj with ⟨k, hk, hvk⟩
    have : s i = u j k := hvi.trans hvk.symm
    cases this
  change (sampledVertices D ∪ leafVertices D).card = _
  rw [Finset.card_union_of_disjoint hdisj, hsample,
    SAP.P012a.WH.W2.P.T3_L1.leaf_vertices_card]
