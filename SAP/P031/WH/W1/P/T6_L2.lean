import SAP.P031.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P031.WH.W1.P.T6_L2

open scoped BigOperators
open AronowAudit.P031.Wave1.LargeSampleRefutation

private def complementDigits {k : ℕ} (v : Fin k → Fin 2) : Fin k → Fin 2 :=
  fun j => Equiv.swap (0 : Fin 2) 1 (v j)

private theorem swap_sign (d : Fin 2) :
    sgn2 (Equiv.swap (0 : Fin 2) 1 d) = -sgn2 d := by
  fin_cases d <;> norm_num [sgn2]

private def flip (n : ℕ) (i : Fin (hcN n)) : Fin (hcN n) :=
  let e := finFunctionFinEquiv (m := 2) (n := hcK n)
  e (complementDigits (e.symm i))

private theorem flip_digits (n : ℕ) (i : Fin (hcN n)) :
    hcDigits n (flip n i) = complementDigits (hcDigits n i) := by
  funext j
  simp [hcDigits, flip, complementDigits]

private theorem flip_involutive (n : ℕ) (i : Fin (hcN n)) :
    flip n (flip n i) = i := by
  let e := finFunctionFinEquiv (m := 2) (n := hcK n)
  change e (complementDigits (e.symm (flip n i))) = i
  have h : complementDigits (e.symm (flip n i)) = e.symm i := by
    funext j
    simp [e, flip, complementDigits]
  rw [h]
  exact e.apply_symm_apply i

private theorem q_flip (n : ℕ) (i : Fin (hcN n)) :
    hcQ n (flip n i) = -hcQ n i := by
  unfold hcQ
  rw [flip_digits]
  simp_rw [complementDigits, swap_sign]
  rw [Finset.sum_neg_distrib]
  ring

end SAP.P031.WH.W1.P.T6_L2

theorem SAP.P031.WH.W1.T6_L2_proof : SAP.P031.WH.W1.T6_L2 := by
  classical
  intro n
  let neg := Finset.univ.filter (fun i : Fin (AronowAudit.P031.Wave1.LargeSampleRefutation.hcN n) =>
    AronowAudit.P031.Wave1.LargeSampleRefutation.hcQ n i < 0)
  let pos := Finset.univ.filter (fun i : Fin (AronowAudit.P031.Wave1.LargeSampleRefutation.hcN n) =>
    0 < AronowAudit.P031.Wave1.LargeSampleRefutation.hcQ n i)
  change neg.card = pos.card
  refine Finset.card_bij (fun i _ => SAP.P031.WH.W1.P.T6_L2.flip n i) ?_ ?_ ?_
  · intro i hi
    simp only [neg, pos, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rw [SAP.P031.WH.W1.P.T6_L2.q_flip]
    linarith
  · intro a ha b hb hab
    simpa only [SAP.P031.WH.W1.P.T6_L2.flip_involutive] using
      congrArg (SAP.P031.WH.W1.P.T6_L2.flip n) hab
  · intro b hb
    refine ⟨SAP.P031.WH.W1.P.T6_L2.flip n b, ?_,
      SAP.P031.WH.W1.P.T6_L2.flip_involutive n b⟩
    simp only [neg, pos, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rw [SAP.P031.WH.W1.P.T6_L2.q_flip]
    linarith
