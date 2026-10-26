import AronowAudit.P045.Wave1.ClusterSamplerBlueprint
import Mathlib.Data.List.OfFn

/-! Length-indexed terminal-centre sums for the two singleton nets. -/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.ClusterSampler

open AronowAudit.P045 Finset
open scoped BigOperators

noncomputable section

private theorem n6_singleton_support (hc : TraceClassification) (a : Fin 4) (ha : a ≠ 0)
    (cs : List (Fin 4)) (hs : cs.toFinset = {a})
    (hm : traceMass (pathDistance (n := 4)) 3 true cs ≠ 0) : cs = [a] := by
  classical
  have hnozero : (0 : Fin 4) ∉ cs.toFinset := by
    simpa only [hs, Finset.mem_singleton] using Ne.symm ha
  rcases hc cs hm with h | h | h | ⟨r, j, hj, h⟩
  · have h1a : (1 : Fin 4) = a := by simpa [h] using hs
    simpa only [h1a] using h
  · have h2a : (2 : Fin 4) = a := by simpa [h] using hs
    simpa only [h2a] using h
  · exact False.elim (hnozero (by simp [h]))
  · have hz : (0 : Fin 4) ∈ cs.toFinset := by
      rw [h]
      simp [List.toFinset_append,
        List.toFinset_replicate_of_ne_zero (by omega : r + 1 ≠ 0)]
    exact False.elim (hnozero hz)

private theorem n6_singleton_sum (hc : TraceClassification) (a : Fin 4) (ha : a ≠ 0)
    (hmass : traceMass (pathDistance (n := 4)) 3 true [a] = 1 / 4) (t : ℕ) :
    (∑ z : Fin t → Fin 4, if (List.ofFn z).toFinset = ({a} : Finset (Fin 4)) then
      traceMass (pathDistance (n := 4)) 3 true (List.ofFn z) else 0) =
      (if t = 1 then (1 / 4 : ℝ) else 0) := by
  classical
  by_cases ht : t = 1
  · subst t
    let za : Fin 1 → Fin 4 := fun _ => a
    have hza : List.ofFn za = [a] := by simp [za, List.ofFn_succ]
    have hoff : ∀ z : Fin 1 → Fin 4, z ≠ za →
        (if (List.ofFn z).toFinset = ({a} : Finset (Fin 4)) then
          traceMass (pathDistance (n := 4)) 3 true (List.ofFn z) else 0) = 0 := by
      intro z hz
      by_cases hs : (List.ofFn z).toFinset = ({a} : Finset (Fin 4))
      · rw [if_pos hs]
        by_contra hm
        have hlist := n6_singleton_support hc a ha (List.ofFn z) hs hm
        exact hz (List.ofFn_injective (hlist.trans hza.symm))
      · exact if_neg hs
    rw [Fintype.sum_eq_single za hoff]
    simp only [hza, List.toFinset_cons, List.toFinset_nil, Finset.insert_empty,
      if_pos rfl, hmass]
  · rw [if_neg ht]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hs : (List.ofFn z).toFinset = ({a} : Finset (Fin 4))
    · rw [if_pos hs]
      by_contra hm
      have hlist := n6_singleton_support hc a ha (List.ofFn z) hs hm
      have hlen : t = 1 := by
        simpa only [List.length_ofFn, List.length_cons, List.length_nil] using
          congrArg List.length hlist
      exact ht hlen
    · exact if_neg hs

theorem n6_proof : N6 := by
  intro h4 hc t
  exact ⟨n6_singleton_sum hc 1 (by decide) h4.1 t,
    n6_singleton_sum hc 2 (by decide) h4.2.1 t⟩

end

end AronowAudit.P045.Wave1.ClusterSampler
