import AronowAudit.P005.Wave1.InteractedExpansion.N6

set_option autoImplicit false
namespace AronowAudit.P005.Wave1.InteractedExpansion
open AronowAudit.P005 Finset Filter
open scoped BigOperators Topology
noncomputable section

theorem n10_proof : N10 := by
  intro h1 h4 h5 h7 h8 h9 n hn heven S hS
  have hc := balanced_cards n hn S hS
  have hs : Real.sqrt (spikeQ n) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (spikeQ_pos_of_S1 h1 n (by omega)))
  have hfit (A : Finset (Fin n)) (hA : 2 ≤ A.card) :
      mean A (spikeV n) - dot (xMean (spikePopulation n) A)
        (armBetaHat (spikePopulation n) A (spikeV n)) = armFit n A := by
    have hf := (h4 n (spikePopulation n) (spikeA n) (1 / (n : ℝ))
      (Real.sqrt (spikeQ n)) hs (fun _ _ => rfl) A (spikeV n)
      (ne_of_gt (h5 n hn A hA))).2
    rw [hf]
    unfold armFit
    ring
  have hinter : interactedATE (spikePopulation n) S =
      armFit n S - armFit n (control S) := by
    change mean S (spikeV n) - mean (control S) (spikeV n) -
      (dot (xMean (spikePopulation n) S) (armBetaHat (spikePopulation n) S (spikeV n)) -
      dot (xMean (spikePopulation n) (control S))
        (armBetaHat (spikePopulation n) (control S) (spikeV n))) = _
    linarith [hfit S hc.1, hfit (control S) hc.2]
  let z : Fin n := ⟨0, by omega⟩
  have hzval : z.val = 0 := rfl
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hbase : (n : ℝ) - 3 ≤ |interactedATE (spikePopulation n) S| := by
    rw [hinter]
    by_cases hz : z ∈ S
    · have hno : ∀ i ∈ control S, i.val ≠ 0 := by
        intro i hi hi0
        have hiz : i = z := Fin.ext (hi0.trans hzval.symm)
        exact (Finset.mem_sdiff.mp hi).2 (hiz.symm ▸ hz)
      rw [h7 n hn (control S) hno hc.2]
      have hb := h8 n hn S ⟨z, hz, hzval⟩ hc.1
      have ht := abs_sub_abs_le_abs_sub (n : ℝ) (armFit n S)
      rw [abs_of_nonneg hnR, abs_sub_comm (n : ℝ) (armFit n S)] at ht
      linarith
    · have hzC : z ∈ control S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz⟩
      have hno : ∀ i ∈ S, i.val ≠ 0 := by
        intro i hi hi0
        have hiz : i = z := Fin.ext (hi0.trans hzval.symm)
        exact hz (hiz ▸ hi)
      rw [h7 n hn S hno hc.1]
      have hb := h8 n hn (control S) ⟨z, hzC, hzval⟩ hc.2
      have ht := abs_sub_abs_le_abs_sub (n : ℝ) (armFit n (control S))
      rw [abs_of_nonneg hnR] at ht
      linarith
  have hzATE := (h9 n hn).1
  have hlead := (h9 n hn).2 S hS
  have ht := abs_sub_abs_le_abs_sub (interactedATE (spikePopulation n) S)
    (armLeading (spikePopulation n) S)
  unfold R
  rw [hzATE, sub_zero]
  linarith

end
end AronowAudit.P005.Wave1.InteractedExpansion
