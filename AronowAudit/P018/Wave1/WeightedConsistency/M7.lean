import AronowAudit.P018.Wave1.WeightedConsistency.G7
import AronowAudit.P018.Wave1.WeightedConsistency.M0

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

theorem weighted_normal_equation {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (v : (d : Dyad N) → Fin (R.T N d) → ℝ)
    (β : Vec k) (ω : Fin N → U) :
    (∑ d : Dyad N, recordWeightedBlockScore R v β ω d) =
      recordWeightedXY R v ω - (recordWeightedGram R v ω).mulVec β := by
  ext a
  simp only [recordWeightedBlockScore, recordWeightedXY, recordWeightedGram,
    Finset.sum_apply, score, Pi.smul_apply, smul_eq_mul, Matrix.sum_mulVec,
    Matrix.smul_mulVec, Pi.sub_apply]
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro t ht
  change _ = _ - v d t * ((outer (repeatedX R ω d t) (repeatedX R ω d t)).mulVec β) a
  have hout : ((outer (repeatedX R ω d t) (repeatedX R ω d t)).mulVec β) a =
      repeatedX R ω d t a * dot (repeatedX R ω d t) β := by
    simp only [Matrix.mulVec, dotProduct, outer, dot, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [hout]
  ring

theorem m7_proof : M7.{u} := by
  intro _ _ U _ k R X Y dir v C H hS hpop hGram hScore
  letI instUnitProbability : IsProbabilityMeasure R.μ := hS.1.1
  letI instSamplesProbability : ∀ N, IsProbabilityMeasure (repeatedLaw R N) :=
    fun N => repeatedLaw_probability R hS.1 N
  let β := popBeta R.μ X Y
  let A := normGram R v
  let s := fun N (ω : Fin N → U) =>
    (Dreal N)⁻¹ • ∑ d : Dyad N, recordWeightedBlockScore R (v N) β ω d
  have hA : inProbability (repeatedLaw R) (fun N ω => A N ω - H) := by
    have hd : inProbability (repeatedLaw R)
        (fun N (_ : Fin N → U) => recordWeightedH R (v N) - H) :=
      inProbability_deterministic (repeatedLaw R) _
        (by convert hS.2.2.2.2.2.sub_const H using 1 <;> simp only [sub_self] <;> rfl)
    have hh := inProbability_add (repeatedLaw R) hGram hd
    simpa only [sub_add_sub_cancel] using hh
  have hHdet : H.det ≠ 0 := ne_of_gt hS.2.2.2.2.1.det_pos
  have hc : ContinuousAt (fun A : Mat k => A⁻¹) H := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hHdet
  have hi := inProbability_continuousAt (repeatedLaw R) hc hA
  have hprod : inProbability (repeatedLaw R)
      (fun N ω => (A N ω)⁻¹.mulVec (s N ω)) :=
    inProbability_product_null (repeatedLaw R) (fun (A : Mat k) (s : Vec k) => A.mulVec s) (k : ℝ)
      (Nat.cast_nonneg k) (norm_mulVec_le (k := k)) (fun N ω => (A N ω)⁻¹) H⁻¹ s hi hScore
  let φ : Mat k → Vec k := fun A => A⁻¹.mulVec (A.mulVec β) - β
  have hφcont : ContinuousAt φ H := by
    unfold φ
    have hm : Continuous (fun p : Mat k × Vec k => p.1.mulVec p.2) :=
      continuous_fst.matrix_mulVec continuous_snd
    have hinner : ContinuousAt (fun A : Mat k => A.mulVec β) H :=
      (continuous_id.matrix_mulVec continuous_const).continuousAt
    exact (hm.continuousAt.comp (hc.prodMk hinner)).sub continuousAt_const
  have hφzero : φ H = 0 := by
    dsimp [φ]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hHdet),
      Matrix.one_mulVec, sub_self]
  have hrest : inProbability (repeatedLaw R) (fun N ω => φ (A N ω)) := by
    have hh := inProbability_continuousAt (repeatedLaw R) hφcont hA
    simpa only [hφzero, sub_zero] using hh
  have hsum := inProbability_add (repeatedLaw R) hprod hrest
  apply inProbability_eventually_eq (repeatedLaw R) (f := fun N ω =>
    (A N ω)⁻¹.mulVec (s N ω) + φ (A N ω)) (g := fun N ω => recordWeightedOLS R (v N) ω - β) _ hsum
  filter_upwards [eventually_ge_atTop 2] with N hN ω
  have hD := Dreal_ne_zero hN
  have hscaled : (A N ω)⁻¹.mulVec ((Dreal N)⁻¹ • recordWeightedXY R (v N) ω) =
      recordWeightedOLS R (v N) ω := by
    dsimp [A, normGram, recordWeightedOLS]
    rw [matrix_inverse_scale_total _ _ (inv_ne_zero hD), inv_inv,
      Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
    simp only [mul_inv_cancel₀ hD, inv_mul_cancel₀ hD, one_smul]
  have hs : s N ω = (Dreal N)⁻¹ • recordWeightedXY R (v N) ω - (A N ω).mulVec β := by
    change (Dreal N)⁻¹ • (∑ d : Dyad N, recordWeightedBlockScore R (v N) β ω d) =
      (Dreal N)⁻¹ • recordWeightedXY R (v N) ω -
        ((Dreal N)⁻¹ • recordWeightedGram R (v N) ω).mulVec β
    simpa only [smul_sub, Matrix.smul_mulVec] using
      congrArg (fun z : Vec k => (Dreal N)⁻¹ • z) (weighted_normal_equation R (v N) β ω)
  rw [hs, Matrix.mulVec_sub, ← hscaled]
  dsimp [φ]
  abel

end
end AronowAudit.P018.Wave1.WeightedConsistency
