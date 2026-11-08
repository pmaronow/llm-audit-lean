import SAP.P018a.Defs.WholeW3
import SAP.P018a.Bridge
import AronowAudit.P018.Wave1.Gap.GLP0181B1
import AronowAudit.P018.Wave1.Gap.GLP0181B3
import AronowAudit.P018.Wave1.Gap.GP0181B2
import AronowAudit.P018.Wave1.Gap.GP0181B3

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018a.WH.W3
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise ENNReal
set_option maxHeartbeats 2000000

/-- Conditional expectation commutes with the finite sum of scores. -/
theorem conditionalScoreSum_eqW3 {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    conditionalScoreSumW3 (N := N) K =ᵐ[unitSampleLaw K N] residualMeanScoreSumW3 K := by
  let : IsProbabilityMeasure K.μ := hK.1
  let : IsProbabilityMeasure (unitSampleLaw K N) := by
    unfold unitSampleLaw
    infer_instance
  have ha (a : Fin k) :
      (fun ω => conditionalScoreSumW3 (N := N) K ω a) =ᵐ[unitSampleLaw K N]
        (fun ω => residualMeanScoreSumW3 K ω a) := by
    have hsum := condExp_finsetSum (μ := unitSampleLaw K N)
      (s := (univ : Finset (Dyad N)))
      (f := fun d ω => score (design K ω d) (epsilon K ω d) a)
      (fun d _ => (show MemLp _ 2 (unitSampleLaw K N) from
        AronowAudit.P018.Wave1.vc3_score_lp (Bridge.toKernel K) hK d a 2).integrable
          (by norm_num)) (designSigma K)
    have heach : ∀ᵐ ω ∂unitSampleLaw K N, ∀ d : Dyad N,
        (unitSampleLaw K N)[(fun z => score (design K z d) (epsilon K z d) a) |
          designSigma K] ω = score (design K ω d) (conditionalResidualMean K d ω) a :=
      ae_all_iff.mpr (fun d => AronowAudit.P018.Wave1.vc3_score_projection (Bridge.toKernel K) hK d a)
    filter_upwards [hsum, heach] with ω hω hd
    change (unitSampleLaw K N)[(fun z => (∑ d : Dyad N,
      score (design K z d) (epsilon K z d)) a) | designSigma K] ω = _
    simp only [Finset.sum_apply]
    have heq : (fun z => ∑ d : Dyad N, score (design K z d) (epsilon K z d) a) =
        ∑ d : Dyad N, fun z => score (design K z d) (epsilon K z d) a := by
      funext z
      simp only [Finset.sum_apply]
    rw [heq]
    simpa only [Finset.sum_apply, hd, residualMeanScoreSumW3] using hω
  filter_upwards [ae_all_iff.mpr ha] with ω hω
  exact funext hω

/-- Entrywise covariance respects almost-sure equality of its vector arguments. -/
theorem covMat_congrW3 {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) {f g f' g' : Ω → Vec k}
    (hf : f =ᵐ[P] f') (hg : g =ᵐ[P] g') : covMat P f g = covMat P f' g' := by
  ext a b
  have hfa : (fun ω => f ω a) =ᵐ[P] (fun ω => f' ω a) := hf.fun_comp (fun x => x a)
  have hgb : (fun ω => g ω b) =ᵐ[P] (fun ω => g' ω b) := hg.fun_comp (fun x => x b)
  simp only [covMat, covariance]
  rw [integral_congr_ae hfa, integral_congr_ae hgb]
  apply integral_congr_ae
  filter_upwards [hfa, hgb] with ω ha hb
  rw [ha, hb]

/-- The two definitions of the omitted variance agree. -/
theorem omittedVariance_eqW3 {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    omittedVarianceW3 (N := N) K = varMat (unitSampleLaw K N) (conditionalScoreSumW3 K) := by
  exact covMat_congrW3 _ (conditionalScoreSum_eqW3 K hK).symm
    (conditionalScoreSum_eqW3 K hK).symm

/-- Split the ordered overlap sum into its diagonal and distinct neighbors. -/
theorem diagonalNeighbors_eqW3 {k N : ℕ} (A : Dyad N → Dyad N → Mat k) :
    diagonalNeighborsW3 A = ∑ d, ∑ f, if overlap d f then A d f else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro d hd
  have hov : overlap d d := by
    change (members d ∩ members d).Nonempty
    rw [inter_self]
    exact card_pos.mp (by rw [members_card]; norm_num)
  simp only [neighbors, Finset.sum_filter]
  have heq (f : Dyad N) :
      (if overlap d f then A d f else 0) =
        (if f = d then A d d else 0) +
          (if f ≠ d ∧ overlap d f then A d f else 0) := by
    by_cases hf : f = d
    · subst f
      simp [hov]
    · by_cases ho : overlap d f <;> simp [hf, ho]
  simp_rw [heq, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', mem_univ, ite_true, overlap]
  rfl

/-- The scalar finite-N coefficients, exported from the limit calculation. -/
theorem finiteTarget_eqW3 {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) (N : ℕ) (hN : 2 ≤ N) :
    trueTarget K N = sandwich (populationGram K)⁻¹
      ((2/((N : ℝ)-1)) • scoreH K +
        (4*((N : ℝ)-2)/((N : ℝ)-1)) • projectionGamma K) := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := by linarith
  have hn1 : (N : ℝ)-1 ≠ 0 := by linarith
  have hc1 : (N : ℝ)/(Dreal N)^2 * Dreal N = 2/((N : ℝ)-1) := by
    unfold Dreal
    field_simp [hn0, hn1]
  have hc2 : (N : ℝ)/(Dreal N)^2 * ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)) =
      4*((N : ℝ)-2)/((N : ℝ)-1) := by
    unfold Dreal
    field_simp [hn0, hn1]
    ring
  have hv : varMat (unitSampleLaw K N) (scoreSum K) = correctedSigma K N :=
    AronowAudit.P018.Wave1.vc3_sparse_variance (Bridge.toKernel K) hK
  have hc : correctedSigma K N = (Dreal N) • scoreH K +
      ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)) • projectionGamma K :=
    AronowAudit.P018.Wave1.vc3_closed_covariance (Bridge.toKernel K) hK
  unfold trueTarget
  rw [hv, hc]
  simp only [sandwich, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_add, smul_smul, hc1, hc2]

/-- The unit-law projection covariance is symmetric, including at N=2. -/
theorem gamma_symmetricW3 {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) : (projectionGamma K).transpose = projectionGamma K := by
  ext a b
  simp only [projectionGamma, meanMat, outer, Matrix.transpose_apply]
  simp only [mul_comm]

/-- There is at least one dyad when N >= 2, and every record count is positive. -/
theorem repeatedL_posW3 {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedAtSize R N) (hN : 2 ≤ N) :
    0 < repeatedL R N := by
  classical
  let i : Fin N := ⟨0, by omega⟩
  let j : Fin N := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    dsimp only [i, j] at hv
    omega
  let d : Dyad N := ⟨{i, j}, by simp [dyads, Finset.mem_powersetCard, hij]⟩
  have hd : (0 : ℝ) < R.T N d := by exact_mod_cast hR.2.1 d
  exact lt_of_lt_of_le hd
    (Finset.single_le_sum (fun e _ => Nat.cast_nonneg (R.T N e)) (Finset.mem_univ d))

/-- Finite covariance algebra: disjoint independence sparsifies covariances;
only total centering is used for the full raw-moment formula. -/
theorem blockCovarianceW3 {Ω : Type*} [MeasurableSpace Ω] {k N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (q : Ω → Dyad N → Vec k)
    (hq : ∀ d a, MemLp (fun ω => q ω d a) 2 P)
    (hind : ∀ d f, ¬overlap d f → IndepFun (fun ω => q ω d) (fun ω => q ω f) P)
    (hmean : meanVec P (fun ω => ∑ d, q ω d) = 0) :
    blockCovarianceConclusionsW3 P q := by
  classical
  let S := fun ω => ∑ d : Dyad N, q ω d
  have hS (a : Fin k) : MemLp (fun ω => S ω a) 2 P := by
    simpa only [S, Finset.sum_apply] using memLp_finsetSum univ (fun d _ => hq d a)
  have hv : varMat P S = ∑ d : Dyad N, ∑ f : Dyad N,
      covMat P (fun ω => q ω d) (fun ω => q ω f) := by
    ext a b
    simpa only [varMat, Matrix.sum_apply, covMat, S, Finset.sum_apply] using
      covariance_fun_sum_fun_sum (fun d => hq d a) (fun f => hq f b)
  have hzero (d f : Dyad N) (hdf : ¬overlap d f) :
      covMat P (fun ω => q ω d) (fun ω => q ω f) = 0 := by
    ext a b
    exact ((hind d f hdf).comp (measurable_pi_apply a) (measurable_pi_apply b)).covariance_eq_zero
      (hq d a) (hq f b)
  have hsparse : varMat P S = sparseCovW3 P q := by
    rw [hv]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro f hf
    by_cases ho : overlap d f
    · simp [ho]
    · simp [ho, hzero d f ho]
  have hp (d f : Dyad N) : covMat P (fun ω => q ω d) (fun ω => q ω f) =
      meanMat P (fun ω => outer (q ω d) (q ω f)) -
        outer (meanVec P (fun ω => q ω d)) (meanVec P (fun ω => q ω f)) := by
    ext a b
    exact covariance_eq_sub (hq d a) (hq f b)
  have hcenter : sparseCovW3 P q = sparseRawW3 P q - sparseMeansW3 P q := by
    unfold sparseCovW3 sparseRawW3 sparseMeansW3
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro f hf
    by_cases ho : overlap d f <;> simp [ho, hp d f]
  have hfull : varMat P S = fullRawW3 P q := by
    ext a b
    have hm (a : Fin k) : (∫ ω, S ω a ∂P) = 0 :=
      congrArg (fun v : Vec k => v a) hmean
    change covariance (fun ω => S ω a) (fun ω => S ω b) P = _
    rw [covariance_eq_sub (hS a) (hS b), hm a, hm b, zero_mul, sub_zero]
    simp only [fullRawW3, Matrix.sum_apply, meanMat, outer, Pi.mul_apply]
    have heq : (fun ω => S ω a * S ω b) =
        fun ω => ∑ d : Dyad N, ∑ f : Dyad N, q ω d a * q ω f b := by
      funext ω
      simp only [S, Finset.sum_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    have hprod (d f : Dyad N) : Integrable (fun ω => q ω d a * q ω f b) P :=
      (hq d a).integrable_mul (hq f b)
    have hrow (d : Dyad N) : Integrable (fun ω => ∑ f : Dyad N, q ω d a * q ω f b) P :=
      integrable_finsetSum _ (fun f _ => hprod d f)
    rw [heq, integral_finsetSum _ (fun d _ => hrow d)]
    apply Finset.sum_congr rfl
    intro d hd
    exact integral_finsetSum _ (fun f _ => hprod d f)
  have heq : varMat P S = sparseRawW3 P q - sparseMeansW3 P q := hsparse.trans hcenter
  have hadd : sparseRawW3 P q = varMat P S + sparseMeansW3 P q := by
    rw [heq]
    abel
  refine ⟨hmean, hfull, hsparse, heq, hadd, ?_, ?_, ?_⟩
  · rw [hadd]
    exact add_eq_left
  · intro hz
    have hm : sparseMeansW3 P q = 0 := by
      have hout : outer (0 : Vec k) 0 = 0 := by ext a b; simp [outer]
      simp only [sparseMeansW3, hz, hout, ite_self, Finset.sum_const_zero]
    rw [hadd, hm, add_zero]
  · ext a
    have hm : (∫ ω, S ω a ∂P) = 0 := congrArg (fun v : Vec k => v a) hmean
    simp only [Finset.sum_apply, meanVec, Pi.zero_apply]
    rw [← integral_finsetSum _ (fun d _ => (hq d a).integrable (by norm_num))]
    simpa only [S, Finset.sum_apply] using hm

end SAP.P018a.WH.W3
