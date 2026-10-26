import AronowAudit.P045.Wave1.ClusterSamplerBlueprint
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
Nonzero terminating traces of the coded four-path sampler.
-/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.ClusterSampler

open AronowAudit.P045 Finset
open scoped BigOperators

noncomputable section

private theorem n5_nonzero_data {cs : List (Fin 4)}
    (hm : traceMass (pathDistance (n := 4)) 3 true cs ≠ 0) :
    (∀ k : Fin cs.length,
      marked pathDistance 3 (cs.take k.val).toFinset ≠ univ) ∧
      marked pathDistance 3 cs.toFinset = univ := by
  classical
  by_contra ht
  exact hm (by simp only [traceMass, if_neg ht])

/-- A nonempty continuation after a terminal prefix violates the prefix test. -/
private theorem n5_no_extra_after (pre rest : List (Fin 4))
    (ht : marked (pathDistance (n := 4)) 3 pre.toFinset = univ)
    (hm : traceMass (pathDistance (n := 4)) 3 true (pre ++ rest) ≠ 0) :
    rest = [] := by
  classical
  by_contra hrest
  have hpos : 0 < rest.length := List.ne_nil_iff_length_pos.mp hrest
  have hlt : pre.length < (pre ++ rest).length := by
    simp only [List.length_append]
    omega
  have hp := (n5_nonzero_data hm).1 ⟨pre.length, hlt⟩
  exact hp (by simpa only [List.take_append_length] using ht)

private theorem n5_nonzero_draw {cs : List (Fin 4)}
    (hm : traceMass (pathDistance (n := 4)) 3 true cs ≠ 0)
    (k : Fin cs.length) :
    centreDraw pathDistance 3 true (cs.take k.val).toFinset (cs.get k) ≠ 0 := by
  classical
  have ht := n5_nonzero_data hm
  have hprod :
      (∏ i : Fin cs.length,
        centreDraw pathDistance 3 true (cs.take i.val).toFinset (cs.get i)) ≠ 0 := by
    simpa only [traceMass, if_pos ht] using hm
  intro hk
  exact hprod (Finset.prod_eq_zero (Finset.mem_univ k) hk)

/-- From the state `{3}` the singleton-number draw can only choose `0`. -/
private theorem n5_draw_from_three (j : Fin 4) (hj : j ≠ 0) :
    centreDraw (pathDistance (n := 4)) 3 true {3} j = 0 := by
  have hR : (univ : Finset (Fin 4)) \ marked pathDistance 3 {3} = {0} := by
    decide
  fin_cases j <;> norm_num [centreDraw, hR] at *

theorem n5_proof : N5 := by
  classical
  intro hpeel
  have classify : ∀ m : ℕ, ∀ cs : List (Fin 4), cs.length = m →
      traceMass (pathDistance (n := 4)) 3 true cs ≠ 0 →
      cs = [1] ∨ cs = [2] ∨ cs = [3, 0] ∨
        ∃ r : ℕ, ∃ j : Fin 4, j ≠ 0 ∧ cs = List.replicate (r + 1) 0 ++ [j] := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro cs hlen hm
      cases cs with
      | nil =>
        have hnot : marked (pathDistance (n := 4)) 3
            ([] : List (Fin 4)).toFinset ≠ univ := by decide
        exact False.elim (hnot (n5_nonzero_data hm).2)
      | cons a rest =>
        fin_cases a
        · -- First draw `0`: only another `0` can retry this state.
          cases rest with
          | nil =>
            have hnot : marked (pathDistance (n := 4)) 3
                ([0] : List (Fin 4)).toFinset ≠ univ := by decide
            exact False.elim (hnot (n5_nonzero_data hm).2)
          | cons b tail =>
            by_cases hb : b = 0
            · subst b
              have hshort : traceMass (pathDistance (n := 4)) 3 true (0 :: tail) ≠ 0 := by
                intro hz
                apply hm
                change traceMass (pathDistance (n := 4)) 3 true (0 :: 0 :: tail) = 0
                rw [hpeel tail, hz, mul_zero]
              have hlt : (0 :: tail).length < m := by
                simp only [List.length_cons] at hlen ⊢
                omega
              rcases ih (0 :: tail).length hlt (0 :: tail) rfl hshort with
                h | h | h | ⟨r, j, hj, heq⟩
              · norm_num at h
              · norm_num at h
              · norm_num at h
              · right; right; right
                refine ⟨r + 1, j, hj, ?_⟩
                convert congrArg (List.cons (0 : Fin 4)) heq using 1 <;>
                  simp [List.replicate_succ, List.cons_append]
            · have hterminal : marked (pathDistance (n := 4)) 3
                  ([0, b] : List (Fin 4)).toFinset = univ := by
                simpa only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
                  using four_path_marking_certificate.2.2 b hb
              have htail : tail = [] := n5_no_extra_after [0, b] tail hterminal hm
              subst tail
              right; right; right
              exact ⟨0, b, hb, by simp⟩
        · -- First draw `1` is already terminal.
          have hterminal : marked (pathDistance (n := 4)) 3
              ([1] : List (Fin 4)).toFinset = univ := by decide
          have hrest : rest = [] := n5_no_extra_after [1] rest hterminal hm
          subst rest
          exact Or.inl rfl
        · -- First draw `2` is already terminal.
          have hterminal : marked (pathDistance (n := 4)) 3
              ([2] : List (Fin 4)).toFinset = univ := by decide
          have hrest : rest = [] := n5_no_extra_after [2] rest hterminal hm
          subst rest
          exact Or.inr (Or.inl rfl)
        · -- First draw `3` leaves only vertex `0` drawable.
          cases rest with
          | nil =>
            have hnot : marked (pathDistance (n := 4)) 3
                ([3] : List (Fin 4)).toFinset ≠ univ := by decide
            exact False.elim (hnot (n5_nonzero_data hm).2)
          | cons b tail =>
            have hb : b = 0 := by
              by_contra hb
              have hdraw := n5_nonzero_draw hm
                (⟨1, by simp⟩ : Fin (3 :: b :: tail).length)
              have hdraw' : centreDraw (pathDistance (n := 4)) 3 true {3} b ≠ 0 := by
                convert hdraw using 1 <;> simp [List.get_eq_getElem]
              exact hdraw' (n5_draw_from_three b hb)
            subst b
            have hterminal : marked (pathDistance (n := 4)) 3
                ([3, 0] : List (Fin 4)).toFinset = univ := by decide
            have htail : tail = [] := n5_no_extra_after [3, 0] tail hterminal hm
            subst tail
            exact Or.inr (Or.inr (Or.inl rfl))
  intro cs hm
  exact classify cs.length cs rfl hm

end

end AronowAudit.P045.Wave1.ClusterSampler
