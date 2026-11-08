import SAP.P018a.WH.W2.Leaves
import AronowAudit.P018.P018_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

noncomputable section
namespace SAP.P018a.WH.W2.P.T12_L2

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open SAP.P018a
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

set_option maxRecDepth 4096
set_option maxHeartbeats 900000

theorem weighted_symmetric {U : Type u} [MeasurableSpace U]
    {k N : ℕ} (R : RepeatedKernel U k)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ) (ω : Fin N → U) :
    (recordWeightedGram R w ω).transpose = recordWeightedGram R w ω := by
  classical
  ext a b
  simp only [Matrix.transpose_apply, recordWeightedGram, Matrix.sum_apply,
    Matrix.smul_apply, outer, Matrix.of_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro t ht
  ring

theorem score_expansion {U : Type u} [MeasurableSpace U]
    {k N : ℕ} (R : RepeatedKernel U k)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k) (ω : Fin N → U) :
    (∑ d : Dyad N, recordWeightedBlockScore R w β ω d) =
      recordWeightedXY R w ω - (recordWeightedGram R w ω).mulVec β := by
  classical
  have hnormal :
      (∑ d : Dyad N, ∑ t : Fin (R.T N d),
        score (repeatedX R ω d t) (w d t * dot (repeatedX R ω d t) β)) =
      (recordWeightedGram R w ω).mulVec β := by
    simp only [recordWeightedGram, Matrix.sum_mulVec]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro t ht
    ext a
    simp only [score, Pi.smul_apply, smul_eq_mul, dot,
      Matrix.mulVec, dotProduct, Matrix.smul_apply, outer, Matrix.of_apply,
      Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [← hnormal]
  ext a
  simp only [recordWeightedBlockScore, recordWeightedXY, score,
    Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.sub_apply,
    mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem mean_mulVec {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} (G : Ω → Mat k)
    (hG : ∀ a b, MemLp (fun ω => G ω a b) ∞ μ) (β : Vec k) :
    meanVec μ (fun ω => (G ω).mulVec β) = (meanMat μ G).mulVec β := by
  classical
  ext a
  simp only [meanVec, meanMat, Matrix.mulVec, dotProduct]
  rw [integral_finsetSum _ (fun b _ =>
    ((hG a b).integrable (by simp)).mul_const (β b))]
  simp only [integral_mul_const]

theorem covariance_linear_map {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) ℝ) (q : Ω → Vec k)
    (hq : ∀ a, MemLp (fun ω => q ω a) 2 μ) :
    varMat μ (fun ω => A.mulVec (q ω)) = A * varMat μ q * A.transpose := by
  ext i j
  simp only [varMat, covMat, Matrix.mulVec, dotProduct]
  rw [ProbabilityTheory.covariance_fun_sum_fun_sum
    (fun a => (hq a).const_mul (A i a)) (fun b => (hq b).const_mul (A j b))]
  simp only [ProbabilityTheory.covariance_const_mul_left,
    ProbabilityTheory.covariance_const_mul_right, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [covMat]
  ring

theorem covariance_score_scale {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (q : Ω → Vec k) (a : ℝ) :
    varMat μ (fun ω => a • q ω) = (a^2) • varMat μ q := by
  ext i j
  simp only [varMat, covMat, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    ProbabilityTheory.covariance_const_mul_left,
    ProbabilityTheory.covariance_const_mul_right]
  ring

theorem finite_contract {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ}
    (G : Ω → Mat k) (b : Ω → Vec k)
    (hG : ∀ a b, MemLp (fun ω => G ω a b) ∞ μ)
    (hb : ∀ a, MemLp (fun ω => b ω a) ∞ μ)
    (hsym : ∀ ω, (G ω).transpose = G ω)
    (c : ℝ) (hc : c ≠ 0) (n : ℕ)
    (hH : (c⁻¹ • meanMat μ G).det ≠ 0) :
    let H := c⁻¹ • meanMat μ G
    let β := (meanMat μ G)⁻¹.mulVec (meanVec μ b)
    let S := fun ω => b ω - (G ω).mulVec β
    meanVec μ S = 0 ∧
    meanMat μ (fun ω => c⁻¹ • G ω) = H ∧
    ((n : ℝ) / c^2) • sandwich H⁻¹ (varMat μ S) =
      varMat μ (fun ω => H⁻¹.mulVec ((Real.sqrt n / c) • S ω)) ∧
    (∀ ω, (G ω).det ≠ 0 →
      Real.sqrt n • ((G ω)⁻¹.mulVec (b ω) - β) =
        (c⁻¹ • G ω)⁻¹.mulVec ((Real.sqrt n / c) • S ω)) := by
  classical
  let A : Mat k := meanMat μ G
  let H : Mat k := c⁻¹ • A
  let β : Vec k := A⁻¹.mulVec (meanVec μ b)
  let S : Ω → Vec k := fun ω => b ω - (G ω).mulVec β
  change meanVec μ S = 0 ∧
    meanMat μ (fun ω => c⁻¹ • G ω) = H ∧
    ((n : ℝ) / c^2) • sandwich H⁻¹ (varMat μ S) =
      varMat μ (fun ω => H⁻¹.mulVec ((Real.sqrt n / c) • S ω)) ∧
    (∀ ω, (G ω).det ≠ 0 →
      Real.sqrt n • ((G ω)⁻¹.mulVec (b ω) - β) =
        (c⁻¹ • G ω)⁻¹.mulVec ((Real.sqrt n / c) • S ω))
  have hA : IsUnit A.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply hH
    change (c⁻¹ • A).det = 0
    rw [Matrix.det_smul, hz, mul_zero]
  have hGβ (a : Fin k) : MemLp (fun ω => (G ω).mulVec β a) ∞ μ := by
    simpa only [Matrix.mulVec, dotProduct] using
      memLp_finsetSum (univ : Finset (Fin k))
        (fun j _ => (hG a j).mul_const (β j))
  have hS (a : Fin k) : MemLp (fun ω => S ω a) ∞ μ :=
    (hb a).sub (hGβ a)
  have hmean : meanVec μ S = meanVec μ b - A.mulVec β := by
    rw [← mean_mulVec μ G hG β]
    ext a
    exact integral_sub ((hb a).integrable (by simp))
      ((hGβ a).integrable (by simp))
  have hzero : meanVec μ S = 0 := by
    rw [hmean]
    dsimp only [β]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec, sub_self]
  have hAT : A.transpose = A := by
    ext a b
    change (∫ ω, G ω b a ∂μ) = ∫ ω, G ω a b ∂μ
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω =>
      congrArg (fun M : Mat k => M a b) (hsym ω))
  have hHT : H.transpose = H := by
    dsimp only [H]
    rw [Matrix.transpose_smul, hAT]
  have hIT : (H⁻¹).transpose = H⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hHT]
  have hcov : varMat μ (fun ω => H⁻¹.mulVec ((Real.sqrt n / c) • S ω)) =
      ((n : ℝ) / c^2) • sandwich H⁻¹ (varMat μ S) := by
    have hscaled (a : Fin k) :
        MemLp (fun ω => ((Real.sqrt n / c) • S ω) a) 2 μ := by
      have hS2 : MemLp (fun ω => S ω a) 2 μ := (hS a).mono_exponent (by simp)
      exact hS2.const_mul (Real.sqrt n / c)
    rw [covariance_linear_map μ H⁻¹ _ hscaled,
      covariance_score_scale μ S (Real.sqrt n / c), hIT]
    have hsquare : (Real.sqrt n / c)^2 = (n : ℝ) / c^2 := by
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    rw [hsquare]
    simp only [sandwich, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨hzero, AronowAudit.P018.meanMat_scale μ G c⁻¹, hcov.symm, ?_⟩
  intro ω hdet
  have hunit : IsUnit (G ω).det := isUnit_iff_ne_zero.mpr hdet
  have hscore : (G ω)⁻¹.mulVec (S ω) =
      (G ω)⁻¹.mulVec (b ω) - β := by
    dsimp only [S]
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  rw [AronowAudit.P018.matrix_inverse_scale (G ω) hunit c⁻¹ (inv_ne_zero hc),
    inv_inv, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, hscore]
  have hscalar : c * (Real.sqrt n / c) = Real.sqrt n := by
    field_simp [hc] <;> ring
  rw [hscalar]

theorem weighted_contract {U : Type u} [MeasurableSpace U]
    {k N : ℕ} (R : RepeatedKernel U k)
    (hR : WholeRecordRegular R N)
    (hL1 : SAP.P018a.WH.W2.T12_L1.{u})
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ)
    (c : ℝ) (hc : c ≠ 0)
    (hH : (c⁻¹ • meanMat (repeatedLaw R N) (recordWeightedGram R w)).det ≠ 0) :
    wholeRecordContract R w c := by
  letI : IsProbabilityMeasure R.μ := hR.1
  letI : IsProbabilityMeasure (repeatedLaw R N) := by
    dsimp only [repeatedLaw]
    infer_instance
  obtain ⟨hG, hb, _⟩ := hL1 R hR w
  have h := finite_contract (repeatedLaw R N)
    (recordWeightedGram R w) (recordWeightedXY R w) hG hb
    (weighted_symmetric R w) c hc N hH
  dsimp only at h ⊢
  have hfirst : meanVec (repeatedLaw R N) (fun ω => ∑ d : Dyad N,
      recordWeightedBlockScore R w (recordWeightedBeta R w) ω d) = 0 := by
    simpa only [score_expansion, recordWeightedBeta] using h.1
  refine ⟨hfirst, h.2.1, ?_, ?_⟩
  · simpa only [score_expansion, recordWeightedBeta] using h.2.2.1
  · intro ω hdet
    simpa only [score_expansion, recordWeightedBeta, recordWeightedOLS] using
      h.2.2.2 ω hdet

end SAP.P018a.WH.W2.P.T12_L2

theorem SAP.P018a.WH.W2.T12_L2_proof : SAP.P018a.WH.W2.T12_L2 := by
  intro hL1
  intro U hU k N R hR w c hc hH
  exact SAP.P018a.WH.W2.P.T12_L2.weighted_contract R hR hL1 w c hc hH
