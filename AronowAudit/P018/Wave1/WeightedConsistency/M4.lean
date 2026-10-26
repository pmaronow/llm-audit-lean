import AronowAudit.P018.Wave1.WeightedConsistency.M3

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

theorem m4_proof : M4.{u} := by
  intro U _ k R X Y dir v C H hS hreg hmom hpop N d
  let β := popBeta R.μ X Y
  let ν := repeatedLaw R N
  have hxy (t : Fin (R.T N d)) (a : Fin k) :
      Integrable (fun ω => repeatedY R ω d t * repeatedX R ω d t a) ν :=
    (record_memLp R hS.1 hreg d t a).2.integrable_mul
      (record_memLp R hS.1 hreg d t a).1
  have hxx (t : Fin (R.T N d)) (a b : Fin k) :
      Integrable (fun ω => (repeatedX R ω d t a * repeatedX R ω d t b) * β b) ν :=
    ((record_memLp R hS.1 hreg d t a).1.integrable_mul
      (record_memLp R hS.1 hreg d t b).1).mul_const _
  have hid (t : Fin (R.T N d)) (a : Fin k) (ω : Fin N → U) :
      (repeatedY R ω d t - dot (repeatedX R ω d t) β) * repeatedX R ω d t a =
        repeatedY R ω d t * repeatedX R ω d t a -
          ∑ b, (repeatedX R ω d t a * repeatedX R ω d t b) * β b := by
    simp only [dot, sub_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hmean (t : Fin (R.T N d)) (a : Fin k) :
      (∫ ω, (repeatedY R ω d t - dot (repeatedX R ω d t) β) *
        repeatedX R ω d t a ∂ν) = 0 := by
    simp_rw [hid]
    rw [integral_sub (hxy t a) (integrable_finset_sum _ (fun b _ => hxx t a b)),
      integral_finset_sum _ (fun b _ => hxx t a b)]
    simp_rw [integral_mul_const]
    have hmxy := congrFun (hmom N d t).2 a
    have hmxx (b : Fin k) := congrFun (congrFun (hmom N d t).1 a) b
    change (∫ ω, repeatedY R ω d t * repeatedX R ω d t a ∂ν) = popR R.μ X Y a at hmxy
    change ∀ b, (∫ ω, repeatedX R ω d t a * repeatedX R ω d t b ∂ν) =
      popQ R.μ X a b at hmxx
    rw [hmxy]
    simp_rw [hmxx]
    have he : (popQ R.μ X).mulVec β = popR R.μ X Y := by
      unfold β popBeta
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hpop.1),
        Matrix.one_mulVec]
    exact sub_eq_zero.mpr (congrFun he a).symm
  ext a
  change (∫ ω, (recordWeightedBlockScore R (v N) β ω d) a ∂ν) = 0
  simp only [recordWeightedBlockScore, Finset.sum_apply, score, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc]
  rw [integral_finset_sum _ (fun t _ => ?_)]
  · simp_rw [integral_const_mul, hmean]
    simp
  · apply Integrable.const_mul
    simp_rw [hid]
    exact (hxy _ a).sub (integrable_finset_sum _ (fun b _ => hxx _ a b))

end
end AronowAudit.P018.Wave1.WeightedConsistency
