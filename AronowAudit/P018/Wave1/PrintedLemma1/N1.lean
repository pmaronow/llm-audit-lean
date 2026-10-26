import AronowAudit.P018.Wave1.PrintedLemma1Blueprint

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace AronowAudit.P018.Wave1.PrintedLemma1
open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
noncomputable section

theorem lagrange_sum {E : Type} [Fintype E] (x : E → ℝ) :
    (∑ d, ∑ f, (x d - x f)^2) =
      2 * ((Fintype.card E : ℝ) * ∑ d, x d ^ 2 - (∑ d, x d)^2) := by
  simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

def pairDyad {N : ℕ} (i j : Fin N) (hij : i < j) : Dyad N :=
  ⟨{i,j}, Finset.mem_powersetCard.mpr ⟨by simp, Finset.card_pair hij.ne⟩⟩

theorem pair_first {N : ℕ} (i j : Fin N) (hij : i < j) :
    firstUnit (pairDyad i j hij) = i := by
  simp [firstUnit, members, pairDyad, Finset.min'_eq_iff, hij.le]

theorem pair_second {N : ℕ} (i j : Fin N) (hij : i < j) :
    secondUnit (pairDyad i j hij) = j := by
  simp [secondUnit, members, pairDyad, Finset.max'_eq_iff, hij.le]

theorem n1_proof : N1 := by
  intro N hN ω hω hdet
  let i0 : Fin N := ⟨0, by omega⟩
  let i1 : Fin N := ⟨1, by omega⟩
  let i2 : Fin N := ⟨2, by omega⟩
  let d := pairDyad i0 i1 (by simp [i0, i1])
  let f := pairDyad i0 i2 (by simp [i0, i2])
  let x : Dyad N → ℝ := fun d => 2 + ω (firstUnit d) + ω (secondUnit d)
  have hg : (Fintype.card (Dyad N) : ℝ) * (∑ d, x d ^ 2) - (∑ d, x d)^2 = 0 := by
    simpa [Matrix.det_fin_two, sampleGram, Matrix.sum_apply, design, nonlinearKernel, outer, pow_two,
      x, Finset.sum_apply] using hdet
  have hz : (∑ d, ∑ f, (x d - x f)^2) = 0 := by rw [lagrange_sum, hg, mul_zero]
  have hbound : (x d - x f)^2 ≤ ∑ d, ∑ f, (x d - x f)^2 := by
    apply le_trans (Finset.single_le_sum (fun f _ => sq_nonneg (x d - x f))
      (Finset.mem_univ f))
    exact Finset.single_le_sum
      (f := fun d : Dyad N => ∑ f : Dyad N, (x d - x f)^2)
      (fun d _ => Finset.sum_nonneg (fun f _ => sq_nonneg (x d - x f)))
      (Finset.mem_univ d)
  have he : x d = x f := by nlinarith [sq_nonneg (x d - x f)]
  have hsame : ω i1 = ω i2 := by
    simpa [x, d, f, pair_first, pair_second] using he
  exact hω hsame
end
end AronowAudit.P018.Wave1.PrintedLemma1
