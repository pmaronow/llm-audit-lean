import SAP.P001a.WH.W1.Leaves
import AronowAudit.P015.P015_OLSCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 900000

open MeasureTheory ProbabilityTheory Filter Function
open scoped BigOperators ENNReal NNReal Topology Classical Matrix Matrix.Norms.Elementwise

noncomputable section

namespace SAP.P001a.WH.W1.P.T18_L4

lemma iid_scalar_slln_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ)
    (hiid : IID μ (fun i ω => (Z i ω, D i ω)))
    (g : (Fin p → ℝ) × ℝ → ℝ) (hg : Measurable g)
    (hgi : Integrable (fun ω => g (Z 0 ω, D 0 ω)) μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => (∑ i ∈ Finset.range n, g (Z i ω, D i ω)) / (n : ℝ))
      atTop (𝓝 (∫ ω, g (Z 0 ω, D 0 ω) ∂μ)) := by
  have hind : Pairwise (fun i j =>
      (fun ω => g (Z i ω, D i ω)) ⟂ᵢ[μ] (fun ω => g (Z j ω, D j ω))) := by
    intro i j hij
    exact (hiid.2.1.indepFun hij).comp hg hg
  have hident : ∀ i, IdentDistrib
      (fun ω => g (Z i ω, D i ω)) (fun ω => g (Z 0 ω, D 0 ω)) μ μ := by
    intro i
    exact (hiid.2.2 i).comp hg
  exact ProbabilityTheory.strong_law_ae_real
    (fun i ω => g (Z i ω, D i ω)) hgi hind hident

lemma iid_scalar_slln_cp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ)
    (hiid : IID μ (fun i ω => (Z i ω, D i ω)))
    (g : (Fin p → ℝ) × ℝ → ℝ) (hg : Measurable g)
    (hgi : Integrable (fun ω => g (Z 0 ω, D 0 ω)) μ) (c : ℝ)
    (hc : ∫ ω, g (Z 0 ω, D 0 ω) ∂μ = c) :
    CP μ (fun n ω => (∑ i ∈ Finset.range n, g (Z i ω, D i ω)) / (n : ℝ)) c := by
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun ω => (∑ i ∈ Finset.range n, g (Z i ω, D i ω)) / (n : ℝ)) μ := by
    intro n
    have hs : Measurable
        (fun ω => ∑ i ∈ Finset.range n, g (Z i ω, D i ω)) := by
      apply Finset.measurable_sum
      intro i hi
      exact hg.comp (hiid.1 i)
    exact (hs.div_const _).aestronglyMeasurable
  have hae := iid_scalar_slln_ae μ Z D hiid g hg hgi
  rw [hc] at hae
  have htm := tendstoInMeasure_of_tendsto_ae hmeas hae
  exact (AronowAudit.P001.Wave1.DecideB_cp_iff_tendstoInMeasure μ _ _).mpr htm

lemma cp_finite_coordinates {Ω I E : Type*} [MeasurableSpace Ω] [Fintype I]
    [PseudoMetricSpace E] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : ℕ → Ω → I → ℝ) (a : I → ℝ) (g : (I → ℝ) → E)
    (hf : ∀ i, CP μ (fun n ω => f n ω i) (a i))
    (hg : ContinuousAt g a) :
    CP μ (fun n ω => g (f n ω)) (g a) := by
  have hfi : ∀ i, TendstoInMeasure μ (fun n ω => f n ω i) atTop (fun _ => a i) := by
    intro i
    exact (AronowAudit.P001.Wave1.DecideB_cp_iff_tendstoInMeasure μ _ _).mp (hf i)
  have h := AronowAudit.P015.ConvergenceCompletion.finite_cmt μ f a g hfi hg
  exact (AronowAudit.P001.Wave1.DecideB_cp_iff_tendstoInMeasure μ _ _).mpr h

lemma measurable_matrix_transpose {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] (A : Ω → Matrix m n ℝ) (hA : Measurable A) :
    Measurable (fun ω => (A ω).transpose) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact (measurable_pi_apply i).comp
    ((measurable_pi_apply j).comp hA)

lemma measurable_matrix_mul {Ω m n k : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [Fintype k]
    (A : Ω → Matrix m n ℝ) (B : Ω → Matrix n k ℝ)
    (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun ω => A ω * B ω) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro k'
  simp only [Matrix.mul_apply]
  apply Finset.measurable_sum
  intro j hj
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)).mul
    ((measurable_pi_apply k').comp ((measurable_pi_apply j).comp hB))

lemma sample_beta_measurable {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ)
    (hiid : IID μ
      (fun i ω => (Z i ω, D i ω))) (n : ℕ) :
    Measurable (wholeBetaHat Z D n) := by
  have hrows : Measurable (wholeRows Z n) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (measurable_pi_apply j).comp (measurable_fst.comp (hiid.1 i))
  have hG : Measurable (fun ω => (wholeRows Z n ω).transpose * wholeRows Z n ω) := by
    apply Measurable.of_eval
    intro j
    apply Measurable.of_eval
    intro k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, wholeRows]
    apply Finset.measurable_sum
    intro i hi
    exact ((measurable_pi_apply j).comp (measurable_fst.comp (hiid.1 i))).mul
      ((measurable_pi_apply k).comp (measurable_fst.comp (hiid.1 i)))
  have hInv := SAP.P001a.WH.W1.measurable_matrix_inverse _ hG
  have hcross : Measurable (fun ω =>
      (wholeRows Z n ω).transpose.mulVec (fun i => D i ω)) := by
    apply Measurable.of_eval
    intro j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, wholeRows]
    apply Finset.measurable_sum
    intro i hi
    exact ((measurable_pi_apply j).comp (measurable_fst.comp (hiid.1 i))).mul
      (measurable_snd.comp (hiid.1 i))
  change Measurable (fun ω =>
    (((wholeRows Z n ω).transpose * wholeRows Z n ω)⁻¹).mulVec
      ((wholeRows Z n ω).transpose.mulVec (fun i => D i ω)))
  apply Measurable.of_eval
  intro j
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.measurable_sum
  intro k hk
  exact ((measurable_pi_apply k).comp ((measurable_pi_apply j).comp hInv)).mul
    ((measurable_pi_apply k).comp hcross)

lemma sample_hc0_measurable {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ)
    (hiid : IID μ
      (fun i ω => (Z i ω, D i ω))) (n : ℕ) :
    Measurable (wholeHC0 Z D n) := by
  have hrows : Measurable (wholeRows Z n) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (measurable_pi_apply j).comp (measurable_fst.comp (hiid.1 i))
  have hG : Measurable (fun ω => (wholeRows Z n ω).transpose * wholeRows Z n ω) := by
    apply Measurable.of_eval
    intro j
    apply Measurable.of_eval
    intro k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, wholeRows]
    apply Finset.measurable_sum
    intro i hi
    exact ((measurable_pi_apply j).comp (measurable_fst.comp (hiid.1 i))).mul
      ((measurable_pi_apply k).comp (measurable_fst.comp (hiid.1 i)))
  have hInv := SAP.P001a.WH.W1.measurable_matrix_inverse _ hG
  have hbeta : Measurable (wholeBetaHat Z D n) := sample_beta_measurable μ Z D hiid n
  have hr : Measurable (fun ω => fun i : Fin n =>
      D i ω - Z i ω ⬝ᵥ wholeBetaHat Z D n ω) := by
    apply Measurable.of_eval
    intro i
    have hz : Measurable (fun ω => Z i ω ⬝ᵥ wholeBetaHat Z D n ω) := by
      simp only [dotProduct]
      apply Finset.measurable_sum
      intro j hj
      exact ((measurable_pi_apply j).comp (measurable_fst.comp (hiid.1 i))).mul
        ((measurable_pi_apply j).comp hbeta)
    exact (measurable_snd.comp (hiid.1 i)).sub hz
  have hdiag : Measurable (fun ω => Matrix.diagonal (fun i : Fin n =>
      (D i ω - Z i ω ⬝ᵥ wholeBetaHat Z D n ω)^2)) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply, if_pos rfl]
      exact (measurable_pi_apply i).comp hr |>.pow_const 2
    · simp only [Matrix.diagonal_apply, if_neg hij]
      exact measurable_const
  have htranspose := measurable_matrix_transpose (wholeRows Z n) hrows
  have hprod := measurable_matrix_mul (fun ω => (wholeRows Z n ω).transpose)
    (fun ω => Matrix.diagonal (fun i : Fin n =>
      (D i ω - Z i ω ⬝ᵥ wholeBetaHat Z D n ω)^2)) htranspose hdiag
  have hmid : Measurable (fun ω =>
      (wholeRows Z n ω).transpose *
        Matrix.diagonal (fun i : Fin n =>
          (D i ω - Z i ω ⬝ᵥ wholeBetaHat Z D n ω)^2) * wholeRows Z n ω) := by
    exact measurable_matrix_mul _ (wholeRows Z n) hprod hrows
  change Measurable (fun ω =>
      ((wholeRows Z n ω).transpose * wholeRows Z n ω)⁻¹ *
        ((wholeRows Z n ω).transpose *
          Matrix.diagonal (fun i : Fin n =>
            (D i ω - Z i ω ⬝ᵥ wholeBetaHat Z D n ω)^2) * wholeRows Z n ω) *
        ((wholeRows Z n ω).transpose * wholeRows Z n ω)⁻¹)
  have hleft := measurable_matrix_mul _ _ hInv hmid
  exact measurable_matrix_mul _ _ hleft hInv

theorem prove {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (D : ℕ → Ω → ℝ) (hiid : IID μ (fun i ω => (Z i ω, D i ω)))
    (b : Fin p → ℝ) (h : WholeScoreMoments μ (Z 0) (D 0) b) :
    WholeGramLimits μ Z D b := by
  let Q : Matrix (Fin p) (Fin p) ℝ := wholeQ μ (Z 0)
  have hdetQ : Q.det ≠ 0 := isUnit_iff_ne_zero.mp h.rank
  let gG : Fin p → Fin p → (Fin p → ℝ) × ℝ → ℝ :=
    fun j k r => r.1 j * r.1 k
  let gS : Fin p → (Fin p → ℝ) × ℝ → ℝ :=
    fun j r => r.1 j * (r.2 - r.1 ⬝ᵥ b)
  let gM : Fin p → Fin p → (Fin p → ℝ) × ℝ → ℝ :=
    fun j k r => (r.1 j * (r.2 - r.1 ⬝ᵥ b)) *
      (r.1 k * (r.2 - r.1 ⬝ᵥ b))
  have hgG (j k : Fin p) : Measurable (gG j k) := by
    change Measurable (fun r : (Fin p → ℝ) × ℝ => r.1 j * r.1 k)
    fun_prop
  have hgS (j : Fin p) : Measurable (gS j) := by
    change Measurable (fun r : (Fin p → ℝ) × ℝ => r.1 j * (r.2 - r.1 ⬝ᵥ b))
    fun_prop
  have hgM (j k : Fin p) : Measurable (gM j k) := by
    change Measurable (fun r : (Fin p → ℝ) × ℝ =>
      (r.1 j * (r.2 - r.1 ⬝ᵥ b)) * (r.1 k * (r.2 - r.1 ⬝ᵥ b)))
    fun_prop
  have hGint (j k : Fin p) :
      Integrable (fun ω => gG j k (Z 0 ω, D 0 ω)) μ := by
    change Integrable ((fun ω => Z 0 ω j) * (fun ω => Z 0 ω k)) μ
    exact (h.secondZ j).integrable_mul (h.secondZ k)
  have hSint (j : Fin p) :
      Integrable (fun ω => gS j (Z 0 ω, D 0 ω)) μ := by
    simpa [gS, wholeResidual] using (h.secondScore j).integrable one_le_two
  have hMint (j k : Fin p) :
      Integrable (fun ω => gM j k (Z 0 ω, D 0 ω)) μ := by
    change Integrable
      ((fun ω => Z 0 ω j * wholeResidual (Z 0) (D 0) b ω) *
        (fun ω => Z 0 ω k * wholeResidual (Z 0) (D 0) b ω)) μ
    exact (h.secondScore j).integrable_mul (h.secondScore k)
  have hGramCP (j k : Fin p) :
      CP μ (fun n ω =>
        (∑ i ∈ Finset.range n, Z i ω j * Z i ω k) / (n : ℝ)) (Q j k) := by
    have hc : ∫ ω, gG j k (Z 0 ω, D 0 ω) ∂μ = Q j k := by
      simp [gG, Q, wholeQ]
    simpa [gG] using iid_scalar_slln_cp μ Z D hiid (gG j k) (hgG j k)
      (hGint j k) (Q j k) hc
  have hScoreCP (j : Fin p) :
      CP μ (fun n ω =>
        (∑ i ∈ Finset.range n, Z i ω j * wholeResidual (Z i) (D i) b ω) /
          (n : ℝ)) 0 := by
    have hc : ∫ ω, gS j (Z 0 ω, D 0 ω) ∂μ = 0 := by
      simpa [gS, wholeResidual, SAP.P001a.mean] using h.orthogonal j
    simpa [gS, wholeResidual] using iid_scalar_slln_cp μ Z D hiid (gS j)
      (hgS j) (hSint j) 0 hc
  have hMeatCP (j k : Fin p) :
      CP μ (fun n ω =>
        (∑ i ∈ Finset.range n,
          (wholeResidual (Z i) (D i) b ω)^2 * Z i ω j * Z i ω k) / (n : ℝ))
        (wholeOmega μ (Z 0) (D 0) b j k) := by
    have hc : ∫ ω, gM j k (Z 0 ω, D 0 ω) ∂μ =
        wholeOmega μ (Z 0) (D 0) b j k := by
      apply integral_congr_ae
      filter_upwards [] with ω
      simp [gM, wholeOmega, wholeResidual]
      ring
    simpa [gM, wholeResidual, pow_two, mul_comm, mul_left_comm, mul_assoc] using
      iid_scalar_slln_cp μ Z D hiid (gM j k) (hgM j k)
        (hMint j k) _ hc
  have hgram : CP μ (wholeEmpiricalQ Z) Q := by
    let f : ℕ → Ω → (Fin p × Fin p) → ℝ := fun n ω jk =>
      wholeEmpiricalQ Z n ω jk.1 jk.2
    let a : (Fin p × Fin p) → ℝ := fun jk => Q jk.1 jk.2
    let mat : ((Fin p × Fin p) → ℝ) → Matrix (Fin p) (Fin p) ℝ :=
      fun v j k => v (j, k)
    have hf : ∀ jk, CP μ (fun n ω => f n ω jk) (a jk) := by
      rintro ⟨j, k⟩
      simpa [f, a, wholeEmpiricalQ, Q] using hGramCP j k
    have hmatC : Continuous mat := by
      dsimp [mat]
      exact continuous_pi fun j => continuous_pi fun k => continuous_apply (j, k)
    have ht := cp_finite_coordinates μ f a mat hf (hmatC.continuousAt)
    change CP μ (fun n ω j k =>
      (∑ i ∈ Finset.range n, Z i ω j * Z i ω k) / (n : ℝ))
      (fun j k => Q j k)
    exact ht
  have hinverse : CP μ (fun n ω => (wholeEmpiricalQ Z n ω)⁻¹) Q⁻¹ := by
    let f : ℕ → Ω → (Fin p × Fin p) → ℝ := fun n ω jk =>
      wholeEmpiricalQ Z n ω jk.1 jk.2
    let a : (Fin p × Fin p) → ℝ := fun jk => Q jk.1 jk.2
    let mat : ((Fin p × Fin p) → ℝ) → Matrix (Fin p) (Fin p) ℝ :=
      fun v j k => v (j, k)
    have hf : ∀ jk, CP μ (fun n ω => f n ω jk) (a jk) := by
      rintro ⟨j, k⟩
      simpa [f, a, wholeEmpiricalQ, Q] using hGramCP j k
    have hmatC : Continuous mat := by
      dsimp [mat]
      exact continuous_pi fun j => continuous_pi fun k => continuous_apply (j, k)
    have ha : mat a = Q := by
      ext j k
      rfl
    let invMat : ((Fin p × Fin p) → ℝ) → Matrix (Fin p) (Fin p) ℝ :=
      fun v => Ring.inverse ((mat v).det) • (mat v).adjugate
    have hscalarInv : ContinuousAt (fun v => Ring.inverse ((mat v).det)) a := by
      have hs : ContinuousAt Ring.inverse Q.det := by
        simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hdetQ)
      apply hs.comp_of_eq (hmatC.matrix_det.continuousAt)
      simpa [ha]
    have hadj : ContinuousAt (fun v => (mat v).adjugate) a :=
      continuous_id.matrix_adjugate.continuousAt.comp_of_eq hmatC.continuousAt ha
    have hcomp' : ContinuousAt invMat a := by
      change ContinuousAt
        (fun v => Ring.inverse ((mat v).det) • (mat v).adjugate) a
      exact hscalarInv.smul hadj
    have ht := cp_finite_coordinates μ f a invMat hf hcomp'
    have hseq (n : ℕ) (ω : Ω) :
        invMat (f n ω) = (wholeEmpiricalQ Z n ω)⁻¹ := by
      have hmf : mat (f n ω) = wholeEmpiricalQ Z n ω := by
        ext j k
        rfl
      ext j k
      change (Ring.inverse ((mat (f n ω)).det) *
          (mat (f n ω)).adjugate j k) =
        (Ring.inverse ((wholeEmpiricalQ Z n ω).det) *
          (wholeEmpiricalQ Z n ω).adjugate j k)
      rw [hmf]
    have hlim : invMat a = Q⁻¹ := by
      ext j k
      simp [invMat, a, mat, ha, Matrix.inv_def]
    have heq : ∀ᶠ n in atTop,
        (fun ω => invMat (f n ω)) =ᵐ[μ] fun ω => (wholeEmpiricalQ Z n ω)⁻¹ := by
      filter_upwards [] with n
      exact Eventually.of_forall (hseq n)
    have hlimAE : (fun _ : Ω => invMat a) =ᵐ[μ] fun _ => Q⁻¹ :=
      Eventually.of_forall (fun _ => hlim)
    have htM := (AronowAudit.P001.Wave1.DecideB_cp_iff_tendstoInMeasure μ _ _).mp ht
    have htM' := TendstoInMeasure.congr' heq hlimAE htM
    exact (AronowAudit.P001.Wave1.DecideB_cp_iff_tendstoInMeasure μ _ _).mpr htM'
  have hScoreInt (j : Fin p) :
      Integrable (fun ω => Z 0 ω j * wholeResidual (Z 0) (D 0) b ω) μ :=
    (h.secondScore j).integrable one_le_two
  have hGramInt (j k : Fin p) :
      Integrable (fun ω => Z 0 ω j * Z 0 ω k) μ :=
    (h.secondZ j).integrable_mul (h.secondZ k)
  have hZDInt (j : Fin p) : Integrable (fun ω => Z 0 ω j * D 0 ω) μ := by
    have hs : Integrable (fun ω => ∑ k, (Z 0 ω j * Z 0 ω k) * b k) μ :=
      integrable_finset_sum Finset.univ (fun k _ => (hGramInt j k).mul_const (b k))
    have he : (fun ω => Z 0 ω j * D 0 ω) = fun ω =>
        Z 0 ω j * wholeResidual (Z 0) (D 0) b ω +
          ∑ k, (Z 0 ω j * Z 0 ω k) * b k := by
      funext ω
      simp only [wholeResidual, dotProduct]
      rw [mul_sub, Finset.mul_sum]
      ring
    rw [he]
    exact (hScoreInt j).add hs
  have hZDCP (j : Fin p) :
      CP μ (fun n ω =>
        (∑ i ∈ Finset.range n, Z i ω j * D i ω) / (n : ℝ))
        (∫ ω, Z 0 ω j * D 0 ω ∂μ) := by
    exact iid_scalar_slln_cp μ Z D hiid
      (fun r => r.1 j * r.2) (by fun_prop) (hZDInt j) _ rfl
  have hnormal : Q.mulVec b = fun j => ∫ ω, Z 0 ω j * D 0 ω ∂μ := by
    ext j
    simp only [Matrix.mulVec, dotProduct, Q, wholeQ]
    calc
      (∑ k, (∫ ω, Z 0 ω j * Z 0 ω k ∂μ) * b k) =
          ∫ ω, ∑ k, (Z 0 ω j * Z 0 ω k) * b k ∂μ := by
        calc
          _ = ∑ k, ∫ ω, (Z 0 ω j * Z 0 ω k) * b k ∂μ := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [integral_mul_const]
          _ = ∫ ω, ∑ k, (Z 0 ω j * Z 0 ω k) * b k ∂μ := by
            symm
            exact integral_finsetSum Finset.univ
              (fun k _ => (hGramInt j k).mul_const (b k))
      _ = ∫ ω, Z 0 ω j * D 0 ω ∂μ := by
        symm
        calc
          ∫ ω, Z 0 ω j * D 0 ω ∂μ =
              ∫ ω, (Z 0 ω j * wholeResidual (Z 0) (D 0) b ω +
                ∑ k, (Z 0 ω j * Z 0 ω k) * b k) ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with ω
            simp only [wholeResidual, dotProduct]
            rw [mul_sub, Finset.mul_sum]
            ring
          _ = (∫ ω, Z 0 ω j * wholeResidual (Z 0) (D 0) b ω ∂μ) +
                ∫ ω, ∑ k, (Z 0 ω j * Z 0 ω k) * b k ∂μ := by
            exact integral_add (hScoreInt j) (integrable_finset_sum Finset.univ
              (fun k _ => (hGramInt j k).mul_const (b k)))
          _ = ∫ ω, ∑ k, (Z 0 ω j * Z 0 ω k) * b k ∂μ := by
            have horth := h.orthogonal j
            change ∫ ω, Z 0 ω j * wholeResidual (Z 0) (D 0) b ω ∂μ = 0 at horth
            rw [horth]
            simp
  let m : Fin p → ℝ := fun j => ∫ ω, Z 0 ω j * D 0 ω ∂μ
  have hbEq : Q⁻¹.mulVec m = b := by
    letI : Invertible Q := Matrix.invertibleOfIsUnitDet Q h.rank
    exact Matrix.inv_mulVec_eq_vec hnormal.symm
  have hGols : ∀ j k, TendstoInMeasure μ
      (fun n ω => (∑ i : Fin n, Z i ω j * Z i ω k) / (n : ℝ)) atTop
      (fun _ => Q j k) := by
    intro j k
    have ht := (AronowAudit.P001.Wave1.DecideB_cp_iff_tendstoInMeasure μ _ _).mp
      (hGramCP j k)
    simpa only [← Fin.sum_univ_eq_sum_range] using ht
  have hYols : ∀ j, TendstoInMeasure μ
      (fun n ω => (∑ i : Fin n, Z i ω j * D i ω) / (n : ℝ)) atTop
      (fun _ => m j) := by
    intro j
    have ht := (AronowAudit.P001.Wave1.DecideB_cp_iff_tendstoInMeasure μ _ _).mp
      (hZDCP j)
    simpa only [← Fin.sum_univ_eq_sum_range, m] using ht
  have hbetaCoord := AronowAudit.P015.OLSCompletion.ols_moment_limit
    μ Z D Q m hdetQ hGols hYols
  have hBetaCP : CP μ (wholeBetaHat Z D) b := by
    let f : ℕ → Ω → Fin p → ℝ := fun n ω j => wholeBetaHat Z D n ω j
    have hf : ∀ j, TendstoInMeasure μ (fun n ω => f n ω j) atTop (fun _ => b j) := by
      intro j
      have ht := hbetaCoord j
      have heq : ∀ᶠ n in atTop,
          (fun ω => AronowAudit.P015.ols (wholeRows Z n ω) (fun i => D i ω) j) =ᵐ[μ]
            fun ω => wholeBetaHat Z D n ω j := by
        filter_upwards [] with n
        exact Eventually.of_forall (fun ω => rfl)
      have hlim : (fun _ : Ω => (Q⁻¹.mulVec m) j) =ᵐ[μ]
          fun _ => b j := Eventually.of_forall (fun _ => congrFun hbEq j)
      have ht' := TendstoInMeasure.congr' heq hlim ht
      simpa [f, wholeBetaHat, wholeRows, olsCoef, AronowAudit.P015.ols] using ht'
    have hvec := AronowAudit.P015.ConvergenceCompletion.finite_cmt
      μ f b (fun v => v) hf continuousAt_id
    exact (AronowAudit.P001.Wave1.DecideB_cp_iff_tendstoInMeasure μ _ _).mpr hvec
  have hmeat : CP μ
      (wholeMeat Z (fun i => wholeResidual (Z i) (D i) b))
      (wholeOmega μ (Z 0) (D 0) b) := by
    let f : ℕ → Ω → (Fin p × Fin p) → ℝ := fun n ω jk =>
      wholeMeat Z (fun i => wholeResidual (Z i) (D i) b) n ω jk.1 jk.2
    let a : (Fin p × Fin p) → ℝ := fun jk => wholeOmega μ (Z 0) (D 0) b jk.1 jk.2
    let mat : ((Fin p × Fin p) → ℝ) → Matrix (Fin p) (Fin p) ℝ :=
      fun v j k => v (j, k)
    have hf : ∀ jk, CP μ (fun n ω => f n ω jk) (a jk) := by
      rintro ⟨j, k⟩
      simpa [f, a, wholeMeat, wholeOmega] using hMeatCP j k
    have hmatC : Continuous mat := by
      dsimp [mat]
      exact continuous_pi fun j => continuous_pi fun k => continuous_apply (j, k)
    have ht := cp_finite_coordinates μ f a mat hf hmatC.continuousAt
    change CP μ (fun n ω j k =>
      (∑ i ∈ Finset.range n,
        (wholeResidual (Z i) (D i) b ω)^2 * Z i ω j * Z i ω k) / (n : ℝ))
      (fun j k => wholeOmega μ (Z 0) (D 0) b j k)
    exact ht
  have haeGram : ∀ᵐ ω ∂μ, Tendsto (fun n => wholeEmpiricalQ Z n ω)
      atTop (𝓝 Q) := by
    have hae : ∀ᵐ ω ∂μ, ∀ j k : Fin p,
        Tendsto (fun n =>
          (∑ i ∈ Finset.range n, Z i ω j * Z i ω k) / (n : ℝ)) atTop
          (𝓝 (Q j k)) := by
      rw [ae_all_iff]
      intro j
      rw [ae_all_iff]
      intro k
      exact iid_scalar_slln_ae μ Z D hiid (gG j k) (hgG j k) (hGint j k)
    filter_upwards [hae] with ω hω
    apply tendsto_pi_nhds.mpr
    intro j
    apply tendsto_pi_nhds.mpr
    intro k
    simpa [wholeEmpiricalQ, Q] using hω j k
  have hrank : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      IsUnit (wholeEmpiricalQ Z n ω).det := by
    filter_upwards [haeGram] with ω hω
    have hdetlim : Tendsto (fun n => (wholeEmpiricalQ Z n ω).det)
        atTop (𝓝 Q.det) :=
      (continuous_id.matrix_det.continuousAt.tendsto.comp hω)
    have hball : ∀ᶠ n in atTop,
        dist ((wholeEmpiricalQ Z n ω).det) Q.det < |Q.det| :=
      hdetlim.eventually (Metric.ball_mem_nhds _ (abs_pos.mpr hdetQ))
    filter_upwards [hball] with n hn
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hn' : |Q.det| < |Q.det| := by
      simpa [hz, Real.dist_eq, Real.norm_eq_abs] using hn
    exact (lt_irrefl _ hn')
  refine ⟨?_, ?_, ?_, ?_, hBetaCP, ?_, hrank⟩
  · intro n
    have hm : Measurable (wholeBetaHat Z D n) := sample_beta_measurable μ Z D hiid n
    simpa using hm
  · intro n
    have hm : Measurable (wholeHC0 Z D n) := sample_hc0_measurable μ Z D hiid n
    simpa using hm
  · exact hgram
  · simpa [Q] using hinverse
  · simpa [wholeMeat] using hmeat

end SAP.P001a.WH.W1.P.T18_L4

theorem SAP.P001a.WH.W1.T18_L4_proof : SAP.P001a.WH.W1.T18_L4 := by
  intro Ω inst μ hμ p Z D hiid b h
  exact SAP.P001a.WH.W1.P.T18_L4.prove μ Z D hiid b h
