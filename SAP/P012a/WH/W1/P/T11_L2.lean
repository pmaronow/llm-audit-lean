import SAP.P012a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a.WH.W1.P.T11_L2

open Finset
open scoped Classical

private theorem private_swap_true_edge_count_slots (H : State) (i j x y : ℕ)
    (hE : {s j,u j y} ∈ H.edges)
    (hzi : H.trait (s i) = false) (hzj : H.trait (s j) = true)
    (hu1 : H.trait (u i x) = false) (hu2 : H.trait (u j y) = true) :
    let K := wholeSwap H i j x y
    edgeCount K true + 1 = edgeCount H true := by
  dsimp only
  let P := fun e : Finset Vertex => ∀ v ∈ e, H.trait v = true
  have hp1 : ¬ P {s i,u i x} := by
    intro h
    have hh := h (s i) (by simp)
    rw [hzi] at hh
    cases hh
  have hp2 : P {s j,u j y} := by
    intro v hv
    rcases mem_insert.mp hv with hv | hv
    · rw [hv]; exact hzj
    · rw [mem_singleton.mp hv]; exact hu2
  have hp3 : ¬ P {s i,u j y} := by
    intro h
    have hh := h (s i) (by simp)
    rw [hzi] at hh
    cases hh
  have hp4 : ¬ P {s j,u i x} := by
    intro h
    have hh := h (u i x) (by simp)
    rw [hu1] at hh
    cases hh
  have hn : {s i,u i x} ∉ H.edges.filter P := fun h => hp1 (mem_filter.mp h).2
  have hin : {s j,u j y} ∈ H.edges.filter P := mem_filter.mpr ⟨hE,hp2⟩
  change ((insert {s j,u i x} (insert {s i,u j y}
    ((H.edges.erase {s i,u i x}).erase {s j,u j y}))).filter P).card+1 = (H.edges.filter P).card
  rw [filter_insert,if_neg hp4,filter_insert,if_neg hp3,filter_erase,filter_erase,
    erase_eq_of_notMem hn]
  exact card_erase_add_one hin

end SAP.P012a.WH.W1.P.T11_L2

open SAP.P012a
open scoped Classical

theorem SAP.P012a.WH.W1.T11_L2_proof : SAP.P012a.WH.W1.T11_L2 := by
  intro H i j x y
  dsimp only
  intro hH hK hE hz_i hz_j hu_i hu_j hV hT hM hG
  have hHS : AronowAudit.P012.Simple (SAP.P012a.Bridge.state H) := by
    simpa using hH
  have hKS : AronowAudit.P012.Simple (SAP.P012a.Bridge.state (wholeSwap H i j x y)) := by
    simpa using hK
  have hVS : (SAP.P012a.Bridge.state H).vertices =
      (SAP.P012a.Bridge.state (wholeSwap H i j x y)).vertices := hV
  have hTS : (SAP.P012a.Bridge.state H).trait =
      (SAP.P012a.Bridge.state (wholeSwap H i j x y)).trait := hT
  have hMS : (SAP.P012a.Bridge.state H).edges.card =
      (SAP.P012a.Bridge.state (wholeSwap H i j x y)).edges.card := hM
  have hGS : ∀ v, AronowAudit.P012.graphDegree (SAP.P012a.Bridge.state H) v =
      AronowAudit.P012.graphDegree (SAP.P012a.Bridge.state (wholeSwap H i j x y)) v := by
    intro v
    simpa using hG v
  have hQden := AronowAudit.P012.same_degree_h_denominator
    (SAP.P012a.Bridge.state H)
    (SAP.P012a.Bridge.state (wholeSwap H i j x y)) hVS hTS hMS hGS
  have hQ : degreeTraitSum H = degreeTraitSum (wholeSwap H i j x y) := by
    simpa using hQden.1
  have hcount := SAP.P012a.WH.W1.P.T11_L2.private_swap_true_edge_count_slots
    H i j x y hE hz_i hz_j hu_i hu_j
  have hcountR : (edgeCount (wholeSwap H i j x y) true : ℝ) + 1 =
      (edgeCount H true : ℝ) := by exact_mod_cast hcount
  have hnH := AronowAudit.P012.numerator_edge_identity (SAP.P012a.Bridge.state H) hHS
  have hnK := AronowAudit.P012.numerator_edge_identity
    (SAP.P012a.Bridge.state (wholeSwap H i j x y)) hKS
  have hnH' : hNumerator H = 2*(edgeCount H true : ℝ) -
      (degreeTraitSum H)^2/(2*(H.edges.card : ℝ)) := by simpa using hnH
  have hnK' : hNumerator (wholeSwap H i j x y) =
      2*(edgeCount (wholeSwap H i j x y) true : ℝ) -
      (degreeTraitSum (wholeSwap H i j x y))^2/
        (2*((wholeSwap H i j x y).edges.card : ℝ)) := by simpa using hnK
  rw [hnH', hnK', ← hQ, ← hM]
  linarith

