import AronowAudit.P004.P004_Spatial
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace AronowAudit.P004.MatrixCompletion
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1000000

theorem PSD_iff_posSemidef {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℝ) :
    PSD Q ↔ Q.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨hs,hq⟩
    refine ⟨?_,fun x => ?_⟩
    · rw [Matrix.isHermitian_iff_isSymm]
      exact Matrix.IsSymm.ext (fun i j => hs j i)
    · simpa only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,Finset.mul_sum,mul_assoc] using hq x
  · rintro ⟨hs,hq⟩
    refine ⟨fun i j => hs.isSymm.apply j i,fun x => ?_⟩
    simpa only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,Finset.mul_sum,mul_assoc] using hq x

theorem weighted_kernel_psd {N : ℕ} (w : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i)
    (V : Matrix (Fin N) (Fin N) ℝ) : PSD (fun i j => ∑ k, w k*V i k*V j k) := by
  apply (PSD_iff_posSemidef _).mpr
  have hh := (Matrix.PosSemidef.diagonal hw).mul_mul_conjTranspose_same V
  have he : (fun i j => ∑ k, w k*V i k*V j k) = V * Matrix.diagonal w * V.conjTranspose := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply,star_trivial,Matrix.mul_diagonal]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  exact hh

theorem hadamard_psd {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℝ) (hQ : PSD Q) (e : Fin N → ℝ) :
    PSD (Matrix.of (fun i j => e i*e j*Q i j)) := by
  apply (PSD_iff_posSemidef _).mpr
  have hh := ((PSD_iff_posSemidef Q).mp hQ).mul_mul_conjTranspose_same (Matrix.diagonal e)
  convert hh using 1
  ext i j
  simp only [Matrix.of_apply,Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.diagonal_transpose,
    Matrix.diagonal_mul,Matrix.mul_diagonal]
  ring

theorem gram_inv_symmetric {N : ℕ} (z : Assignment N) :
    (((designMatrix z).transpose*designMatrix z)⁻¹).IsSymm := by
  apply Matrix.IsSymm.inv
  apply Matrix.IsSymm.ext
  intro a b
  simp only [Matrix.mul_apply,Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sandwich_psd {N : ℕ} (z : Assignment N) (e : Fin N → ℝ)
    (Q : Matrix (Fin N) (Fin N) ℝ) (hQ : PSD Q) : PSD (sandwich z e Q) := by
  have hE := (PSD_iff_posSemidef _).mp (hadamard_psd Q hQ e)
  have hX := hE.conjTranspose_mul_mul_same (designMatrix z)
  have hA := hX.mul_mul_conjTranspose_same (((designMatrix z).transpose*designMatrix z)⁻¹)
  apply (PSD_iff_posSemidef _).mpr
  simpa only [sandwich, Matrix.conjTranspose_eq_transpose_of_trivial,(gram_inv_symmetric z).eq] using hA

theorem kernel_variance_nonneg {N : ℕ} (z : Assignment N) (e : Fin N → ℝ)
    (Q : Matrix (Fin N) (Fin N) ℝ) (hQ : PSD Q) : 0 ≤ kernelVariance z e Q := by
  have hh := hQ.2 (fun i => lambda z i*e i)
  convert hh using 1
  unfold kernelVariance
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem kernel_variance_sub {N : ℕ} (z : Assignment N) (e : Fin N → ℝ)
    (Q K : Matrix (Fin N) (Fin N) ℝ) :
    kernelVariance z e (Q-K) = kernelVariance z e Q-kernelVariance z e K := by
  simp only [kernelVariance,Matrix.sub_apply,mul_sub,Finset.sum_sub_distrib]

theorem sandwich_sub {N : ℕ} (z : Assignment N) (e : Fin N → ℝ)
    (Q K : Matrix (Fin N) (Fin N) ℝ) :
    sandwich z e (Q-K) = sandwich z e Q-sandwich z e K := by
  have he : Matrix.of (fun i j => e i*e j*(Q-K) i j) =
      Matrix.of (fun i j => e i*e j*Q i j)-Matrix.of (fun i j => e i*e j*K i j) := by
    ext i j
    simp only [Matrix.of_apply,Matrix.sub_apply,mul_sub]
  simp only [sandwich,he,Matrix.mul_sub,Matrix.sub_mul]

theorem spectral_psd {N : ℕ} (values : Fin N → ℝ) (vectors : Matrix (Fin N) (Fin N) ℝ) :
    PSD (spectralKernel values vectors true) ∧
    PSD (spectralKernel values vectors true-spectralKernel values vectors false) := by
  refine ⟨weighted_kernel_psd _ (fun i => le_max_right _ _) vectors,?_⟩
  have he : spectralKernel values vectors true-spectralKernel values vectors false =
      fun i j => ∑ k, (max (values k) 0-values k)*vectors i k*vectors j k := by
    ext i j
    simp [spectralKernel,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]
  rw [he]
  exact weighted_kernel_psd _ (fun i => sub_nonneg.mpr (le_max_left _ _)) vectors

end
end AronowAudit.P004.MatrixCompletion

namespace AronowAudit.P004
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1000000

theorem sandwich_sum_identity {N : ℕ} (z : Assignment N) (e : Fin N → ℝ)
    (Q : Matrix (Fin N) (Fin N) ℝ) :
    sandwich z e Q =
      ((designMatrix z).transpose * designMatrix z)⁻¹ *
        Matrix.of (fun a b => ∑ i, ∑ j, designMatrix z i a * designMatrix z j b * e i * e j * Q i j) *
      ((designMatrix z).transpose * designMatrix z)⁻¹ := by
  have hi : (designMatrix z).transpose * Matrix.of (fun i j => e i*e j*Q i j)*designMatrix z =
      Matrix.of (fun a b => ∑ i, ∑ j, designMatrix z i a*designMatrix z j b*e i*e j*Q i j) := by
    ext a b
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.of_apply,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  dsimp only [sandwich]
  rw [hi]

theorem spectral_psd_order {N : ℕ} (values : Fin N → ℝ)
    (vectors : Matrix (Fin N) (Fin N) ℝ)
    (horth : vectors.transpose * vectors = 1)
    (z : Assignment N) (e : Fin N → ℝ)
    (h1 : 0 < armCount z true) (h0 : 0 < armCount z false) :
    let K := spectralKernel values vectors false
    let Q := spectralKernel values vectors true
    PSD Q ∧ PSD (Q-K) ∧ PSD (Matrix.of (fun i j => e i*e j*Q i j)) ∧
    PSD (Matrix.of (fun i j => e i*e j*(Q-K) i j)) ∧
    PSD (sandwich z e Q) ∧ PSD (sandwich z e Q-sandwich z e K) ∧
    max (kernelVariance z e K) 0 ≤ kernelVariance z e Q := by
  dsimp only
  obtain ⟨hQ,hD⟩ := MatrixCompletion.spectral_psd values vectors
  refine ⟨hQ,hD,MatrixCompletion.hadamard_psd _ hQ e,MatrixCompletion.hadamard_psd _ hD e,
    MatrixCompletion.sandwich_psd z e _ hQ,?_,?_⟩
  · rw [← MatrixCompletion.sandwich_sub]
    exact MatrixCompletion.sandwich_psd z e _ hD
  · apply max_le
    · have hh := MatrixCompletion.kernel_variance_nonneg z e _ hD
      rw [MatrixCompletion.kernel_variance_sub] at hh
      linarith
    · exact MatrixCompletion.kernel_variance_nonneg z e _ hQ

theorem capped_pd_interval {N : ℕ} (values : Fin N → ℝ)
    (vectors : Matrix (Fin N) (Fin N) ℝ) (horth : vectors.transpose * vectors = 1)
    (z : Assignment N) (e : Fin N → ℝ)
    (h1 : 0 < armCount z true) (h0 : 0 < armCount z false)
    (critical c err : ℝ) (hc : 0 ≤ critical ∧ critical ≤ c) :
    let K := spectralKernel values vectors false
    let Q := spectralKernel values vectors true
    let V := cappedVariance (kernelVariance z e Q) (adjustmentMu z Q)
    kernelVariance z e Q ≤ V ∧ max (kernelVariance z e K) 0 ≤ kernelVariance z e Q ∧
    (0 ≤ kernelVariance z e K → |err| ≤ critical*Real.sqrt (kernelVariance z e K) →
      |err| ≤ c*Real.sqrt V) := by
  dsimp only
  have hh := spectral_psd_order values vectors horth z e h1 h0
  have hn := MatrixCompletion.kernel_variance_nonneg z e _ hh.1
  have hcap := capped_variance_ge _ (adjustmentMu z (spectralKernel values vectors true)) hn
  refine ⟨hcap,hh.2.2.2.2.2.2,?_⟩
  intro hK herr
  have hKQ : kernelVariance z e (spectralKernel values vectors false) ≤
      kernelVariance z e (spectralKernel values vectors true) :=
    (le_max_left _ _).trans hh.2.2.2.2.2.2
  calc
    _ ≤ critical*Real.sqrt (kernelVariance z e (spectralKernel values vectors false)) := herr
    _ ≤ c*Real.sqrt (cappedVariance (kernelVariance z e (spectralKernel values vectors true))
        (adjustmentMu z (spectralKernel values vectors true))) :=
      mul_le_mul hc.2 (Real.sqrt_le_sqrt (hKQ.trans hcap)) (Real.sqrt_nonneg _) (hc.1.trans hc.2)

end
end AronowAudit.P004
