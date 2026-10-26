import AronowAudit.P004.Wave1.PairedWitness.PW10

/-! The printed variance equation shares the PW10 second moments.  Its additional
effect and mean-product terms vanish because every marginal equals its arm fit. -/

namespace AronowAudit.P004.Wave1.PairedWitness

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators Classical

namespace MomentCalculations

theorem residualEffect_zero {N : ℕ} (hE : Even N) (i : Fin N) :
    residualEffect (fun _ : Fin N => 1/2) (pairedTable N) (pairFit N) i = 0 := by
  unfold residualEffect nodeEffect
  rw [marginal_eq_fit hE i true, marginal_eq_fit hE i false]
  exact sub_self _

/-- The first marginal residual factor is zero in every signed term; the
literal `i` fit in the second factor is retained. -/
theorem signed_mean_neighborhood_sum {N : ℕ} (hE : Even N)
    (B : Fin N → Finset (Fin N)) :
    (∑ i, ∑ j ∈ (B i).erase i, ∑ a : Bool, ∑ b : Bool, armSign a * armSign b *
      (marginal (fun _ : Fin N => 1/2) (pairedTable N) i a - pairFit N i a) *
        (marginal (fun _ : Fin N => 1/2) (pairedTable N) j b - pairFit N i b)) = 0 := by
  simp only [marginal_eq_fit hE, sub_self, mul_zero, zero_mul, Finset.sum_const_zero]

end MomentCalculations

open MomentCalculations

theorem pw11_proof : PW11 := by
  intro N hE hN B
  have heq :
      printedVarianceFormula (fun _ : Fin N => 1/2) (pairedTable N) B (pairFit N) =
        printedSecondMomentBound (fun _ : Fin N => 1/2) (pairedTable N) B (pairFit N) := by
    unfold printedVarianceFormula printedSecondMomentBound
    simp only [residualEffect_zero hE, pow_two, zero_mul, sub_zero,
      signed_mean_neighborhood_sum hE B]
  rw [heq]
  exact pw10_proof N hE hN B

end
end AronowAudit.P004.Wave1.PairedWitness
