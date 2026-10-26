import AronowAudit.P031.Wave1.LargeSampleRefutationBlueprint

/-! Split a `2k`-digit vector into two blocks, then apply the
binary enumeration to each block. The equivalence transports arbitrary events,
so no regularity assumption on `E` is needed. -/

namespace AronowAudit.P031.Wave1.LargeSampleRefutation
noncomputable section
open scoped BigOperators Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

theorem n5_proof : N5 := by
  intro n E
  let c : Fin (hcK n) ⊕ Fin (hcK n) ≃ Fin (2 * hcK n) :=
    finSumFinEquiv.trans (finCongr (two_mul (hcK n)).symm)
  let b : (Fin (hcK n) → Fin 2) ≃ Fin (hcN n) :=
    finFunctionFinEquiv (m := 2) (n := hcK n)
  let e : (Fin (2 * hcK n) → Fin 2) ≃ Fin (hcN n) × Fin (hcN n) :=
    (((Equiv.arrowCongr c (Equiv.refl (Fin 2))).symm).trans
      (Equiv.sumArrowEquivProdArrow (Fin (hcK n)) (Fin (hcK n)) (Fin 2))).trans
        (Equiv.prodCongr b b)

  have hleft (v : Fin (2 * hcK n) → Fin 2) :
      hcDigits n (e v).1 = fun j => v (c (Sum.inl j)) := by
    change b.symm (b (fun j => v (c (Sum.inl j)))) = _
    exact b.symm_apply_apply _

  have hright (v : Fin (2 * hcK n) → Fin 2) :
      hcDigits n (e v).2 = fun j => v (c (Sum.inr j)) := by
    change b.symm (b (fun j => v (c (Sum.inr j)))) = _
    exact b.symm_apply_apply _

  have hsum (v : Fin (2 * hcK n) → Fin 2) :
      (∑ j, sgn2 (v j)) =
        (∑ j, sgn2 (hcDigits n (e v).1 j)) +
        (∑ j, sgn2 (hcDigits n (e v).2 j)) := by
    calc
      _ = ∑ j : Fin (hcK n) ⊕ Fin (hcK n), sgn2 (v (c j)) :=
        (c.sum_comp (fun j => sgn2 (v j))).symm
      _ = (∑ j : Fin (hcK n), sgn2 (v (c (Sum.inl j)))) +
          (∑ j : Fin (hcK n), sgn2 (v (c (Sum.inr j)))) :=
        Fintype.sum_sum_type _
      _ = _ := by rw [hleft, hright]

  have hstat (v : Fin (2 * hcK n) → Fin 2) :
      hcQ n (e v).1 + hcQ n (e v).2 =
        (∑ j, sgn2 (v j)) / (2 * ((n : ℝ) + 1)) := by
    unfold hcQ
    rw [hsum]
    exact (add_div _ _ _).symm

  have hcard :
      (Finset.univ.filter (fun v : Fin (2 * hcK n) → Fin 2 =>
        E ((∑ j, sgn2 (v j)) / (2 * ((n : ℝ) + 1))))).card =
      (Finset.univ.filter (fun ij : Fin (hcN n) × Fin (hcN n) =>
        E (hcQ n ij.1 + hcQ n ij.2))).card := by
    apply Finset.card_equiv e
    intro v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hstat v]
  exact congrArg (fun t : ℕ => (t : ℝ)) hcard.symm

end
end AronowAudit.P031.Wave1.LargeSampleRefutation
