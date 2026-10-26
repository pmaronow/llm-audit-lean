import AronowAudit.P004.Wave1.PairedWitness.PW7

namespace AronowAudit.P004.Wave1.PairedWitness

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators Classical

theorem pair_residualEffect_zero (N : ℕ) (i : Fin N) :
    residualEffect (fun _ => 1 / 2) (pairedTable N)
      (printedFits (fun _ => 1 / 2) (pairedTable N) (pairO N)) i = 0 := by
  by_cases hE : Even N
  · have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    rw [pw7_proof N hE hN]
    unfold residualEffect nodeEffect
    rw [pair_marginal hE i true, pair_marginal hE i false]
    norm_num [pairFit, bit]
  · have htable : pairedTable N = (fun _ _ => (0 : ℝ)) := by
      funext j z
      simp only [pairedTable, if_neg hE]
    have hmarginal : ∀ (j : Fin N) (a : Bool),
        marginal (fun _ => 1 / 2) (pairedTable N) j a = 0 := by
      intro j a
      rw [htable]
      simp [marginal, expect]
    have hfits : printedFits (fun _ => 1 / 2) (pairedTable N) (pairO N) =
        (fun _ _ => (0 : ℝ)) := by
      have hbeta : ∀ a : Bool,
          beta (fun _ => 1 / 2) (pairedTable N) (pairO N) a = 0 := by
        intro a
        have hrhs :
            (fun j : Fin 1 =>
              (∑ k : Fin N, marginal (fun _ => 1 / 2) (pairedTable N) k a *
                (1 / 2) * (1 - 1 / 2) * pairO N k j) / (N : ℝ)) = 0 := by
          funext j
          simp only [hmarginal, zero_mul, Finset.sum_const_zero, zero_div,
            Pi.zero_apply]
        unfold beta
        rw [hrhs, Matrix.mulVec_zero]
      funext j a
      unfold printedFits
      rw [hbeta]
      simp [dot]
    unfold residualEffect nodeEffect
    rw [hmarginal i true, hmarginal i false, hfits]
    norm_num

theorem pw8_proof : PW8 := by
  intro N B
  unfold printedHomophilyQ
  simp only [pair_residualEffect_zero, zero_mul, Finset.sum_const_zero, zero_div]

end
end AronowAudit.P004.Wave1.PairedWitness
