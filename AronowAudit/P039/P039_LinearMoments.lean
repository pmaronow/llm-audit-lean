import Mathlib
/-! Finite linear moment identities and rank of a left-inverse complement.
These are generic algebra and integration lemmas, with no distributional hypotheses beyond the displayed moments. -/
namespace AronowAudit.P039.LinearMoments
open MeasureTheory Matrix
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000

lemma integral_linear_zero {Ω I J : Type*} [MeasurableSpace Ω] [Fintype I] [Fintype J]
    (μ : Measure Ω) (ε : Ω → I → ℝ) (A : Matrix J I ℝ)
    (hi : ∀ i, Integrable (fun ω => ε ω i) μ)
    (he : ∀ i, (∫ ω, ε ω i ∂μ)=0) (j : J) :
    (∫ ω, (A*ᵥ ε ω) j ∂μ)=0 := by
  change (∫ ω, ∑ i, A j i*ε ω i ∂μ)=0
  rw [integral_finset_sum _ (fun i _ => (hi i).const_mul (A j i))]
  simp_rw [integral_const_mul,he,mul_zero]
  simp


lemma integral_linear_product {Ω I J : Type*} [MeasurableSpace Ω] [Fintype I] [Fintype J]
    (μ : Measure Ω) (ε : Ω → I → ℝ) (A : Matrix J I ℝ)
    (hij : ∀ i l, Integrable (fun ω => ε ω i*ε ω l) μ) (j k : J) :
    (∫ ω, (A*ᵥ ε ω) j*(A*ᵥ ε ω) k ∂μ)=
      ∑ i, ∑ l, A j i*A k l*(∫ ω, ε ω i*ε ω l ∂μ) := by
  classical
  have hf : (fun ω => (A*ᵥ ε ω) j*(A*ᵥ ε ω) k)=
      fun ω => ∑ i, ∑ l, (A j i*A k l)*(ε ω i*ε ω l) := by
    funext ω
    simp only [Matrix.mulVec,dotProduct]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hf,integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum]
    · simp_rw [integral_const_mul]
    · exact fun l _ => (hij i l).const_mul _
  · exact fun i _ => integrable_finset_sum _ (fun l _ => (hij i l).const_mul _)

lemma rank_complement_left_inverse {n k : ℕ}
    (Z : Matrix (Fin n) (Fin k) ℝ) (L : Matrix (Fin k) (Fin n) ℝ)
    (hL : L*Z=1) : (1-Z*L).rank = n-k := by
  let M := 1-Z*L
  have hZ : Function.Injective Z.mulVec := by
    intro a b hab
    have hh := congrArg (fun v => L*ᵥ v) hab
    simpa only [Matrix.mulVec_mulVec,hL,Matrix.one_mulVec] using hh
  have hMZ : M*Z=0 := by
    dsimp [M]
    rw [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,hL,Matrix.mul_one,sub_self]
  have hker : LinearMap.ker M.mulVecLin=LinearMap.range Z.mulVecLin := by
    ext v
    constructor
    · intro hv
      change M*ᵥ v=0 at hv
      refine ⟨L*ᵥ v,?_⟩
      have hh : v-(Z*L)*ᵥ v=0 := by
        simpa only [M,Matrix.sub_mulVec,Matrix.one_mulVec] using hv
      change Z*ᵥ (L*ᵥ v)=v
      rw [Matrix.mulVec_mulVec]
      exact (sub_eq_zero.mp hh).symm
    · rintro ⟨a,rfl⟩
      change M*ᵥ (Z*ᵥ a)=0
      rw [Matrix.mulVec_mulVec,hMZ,Matrix.zero_mulVec]
  have hr := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hzr : Module.finrank ℝ (LinearMap.range Z.mulVecLin)=k := by
    simpa using LinearMap.finrank_range_of_inj (f := Z.mulVecLin) hZ
  rw [hker,hzr] at hr
  have hr' : M.rank+k=n := by
    simpa only [Matrix.rank,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using hr
  change M.rank=n-k
  exact (Nat.add_sub_cancel M.rank k).symm.trans (congrArg (fun t : ℕ => t-k) hr')

end
end AronowAudit.P039.LinearMoments

