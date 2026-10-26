import AronowAudit.P011.P011_Audit
import AronowAudit.P011.P011_DenseVarianceCompletion
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Spectral clipping, operator-norm bounds, and Frobenius projection inequalities. -/
namespace AronowAudit.P011.SpectralConfidence
noncomputable section
open scoped BigOperators Matrix Matrix.Norms.L2Operator
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem audit_psd_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    PSD M ↔ M.PosSemidef := by
  constructor
  · intro hM
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    constructor
    · ext i j; simpa using hM.1 j i
    · intro x
      simpa [quadratic,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc,mul_comm,mul_left_comm]
        using hM.2 x
  · intro hp
    constructor
    · intro i j
      have hh := congr_fun (congr_fun hp.1 j) i
      simpa using hh
    · intro x
      simpa [quadratic,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc,mul_comm,mul_left_comm]
        using hp.dotProduct_mulVec_nonneg x

theorem spectral_representation {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsHermitian) :
    M = (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      Matrix.diagonal hM.eigenvalues *
      (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
  simpa [Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial,Function.comp_def] using hM.spectral_theorem

theorem positive_part_difference_representation {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) :
    positivePart M - M =
      (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      Matrix.diagonal (fun i => max (hM.eigenvalues i) 0 - hM.eigenvalues i) *
      (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
  calc
    positivePart M - M = positivePart M -
        (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
          Matrix.diagonal hM.eigenvalues *
          (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ :=
      congrArg (fun N => positivePart M - N) (spectral_representation M hM)
    _ = _ := by
      rw [positivePart,dif_pos hM, ← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.diagonal_sub]

/-- The actual spectral clipping is a Loewner majorant of every symmetric matrix. -/
theorem positive_part_majorant {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsHermitian) : PSD (positivePart M - M) := by
  apply (audit_psd_iff _).mpr
  rw [positive_part_difference_representation M hM]
  simpa using
    (Matrix.PosSemidef.diagonal (fun i =>
      sub_nonneg.mpr (le_max_left (hM.eigenvalues i) 0))).mul_mul_conjTranspose_same
        (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)

/-- The positive and negative spectral parts have orthogonal ranges; their product is zero. -/
theorem positive_part_orthogonal {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsHermitian) : positivePart M * (positivePart M - M) = 0 := by
  let U : Matrix (Fin n) (Fin n) ℝ := hM.eigenvectorUnitary
  have hU : Uᵀ * U = 1 := by
    simpa [U,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self hM.eigenvectorUnitary
  have hp : positivePart M =
      U * Matrix.diagonal (fun i => max (hM.eigenvalues i) 0) * Uᵀ := by
    rw [positivePart,dif_pos hM]
  have hd : positivePart M - M =
      U * Matrix.diagonal (fun i => max (hM.eigenvalues i) 0 - hM.eigenvalues i) * Uᵀ :=
    positive_part_difference_representation M hM
  have hz : Matrix.diagonal (fun i => max (hM.eigenvalues i) 0) *
      Matrix.diagonal (fun i => max (hM.eigenvalues i) 0 - hM.eigenvalues i) =
      (0 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [Matrix.diagonal_mul_diagonal]
    have hf : (fun i => max (hM.eigenvalues i) 0 *
        (max (hM.eigenvalues i) 0 - hM.eigenvalues i)) = fun _ => 0 := by
      funext i
      by_cases hi : 0 ≤ hM.eigenvalues i
      · rw [max_eq_left hi]; ring
      · rw [max_eq_right (le_of_not_ge hi)]; ring
    rw [hf]
    exact Matrix.diagonal_zero
  rw [hd,hp]
  calc
    _ = U * Matrix.diagonal (fun i => max (hM.eigenvalues i) 0) * (Uᵀ * U) *
        Matrix.diagonal (fun i => max (hM.eigenvalues i) 0 - hM.eigenvalues i) * Uᵀ := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hU,Matrix.mul_one,Matrix.mul_assoc U, hz,Matrix.mul_zero,Matrix.zero_mul]

/-- Spectral clipping cannot enlarge the Euclidean operator norm. -/
theorem positive_part_operatorNorm_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsHermitian) : operatorNorm (positivePart M) ≤ operatorNorm M := by
  have hn : operatorNorm M = ‖hM.eigenvalues‖ := by
    change ‖M‖ = _
    conv_lhs => rw [spectral_representation M hM]
    simp only [← Matrix.conjTranspose_eq_transpose_of_trivial,
      ← Matrix.star_eq_conjTranspose, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal]
  have hp : operatorNorm (positivePart M) = ‖fun i => max (hM.eigenvalues i) 0‖ := by
    change ‖positivePart M‖ = _
    rw [positivePart,dif_pos hM]
    simp only [← Matrix.conjTranspose_eq_transpose_of_trivial,
      ← Matrix.star_eq_conjTranspose, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal]
  rw [hn,hp]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  calc
    ‖max (hM.eigenvalues i) 0‖ ≤ ‖hM.eigenvalues i‖ := by
      by_cases hi : 0 ≤ hM.eigenvalues i
      · rw [max_eq_left hi]
      · rw [max_eq_right (le_of_not_ge hi),norm_zero]; exact norm_nonneg _
    _ ≤ _ := norm_le_pi_norm _ i

theorem trace_psd_product_nonneg {n : ℕ} (X N : Matrix (Fin n) (Fin n) ℝ)
    (hX : PSD X) (hN : PSD N) : 0 ≤ Matrix.trace (X * N) := by
  have hXp := (audit_psd_iff X).mp hX
  have hNp := (audit_psd_iff N).mp hN
  let U : Matrix (Fin n) (Fin n) ℝ := hNp.1.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal hNp.1.eigenvalues
  have hs : N = U * D * Uᵀ := spectral_representation N hNp.1
  have hXU : (Uᵀ * X * U).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial]
      using hXp.conjTranspose_mul_mul_same U
  have hr : Matrix.trace (X * (U * D * Uᵀ)) =
      Matrix.trace ((Uᵀ * X * U) * D) := by
    calc
      _ = Matrix.trace ((X * U) * D * Uᵀ) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Uᵀ * (X * U) * D) :=
        Matrix.trace_mul_cycle (X * U) D Uᵀ
      _ = _ := by simp only [Matrix.mul_assoc]
  calc
    0 ≤ ∑ i, (Uᵀ * X * U) i i * hNp.1.eigenvalues i :=
      Finset.sum_nonneg fun i _ => mul_nonneg hXU.diag_nonneg (hNp.eigenvalues_nonneg i)
    _ = Matrix.trace ((Uᵀ * X * U) * D) := by
      simp [D, Matrix.trace, Matrix.mul_diagonal]
    _ = Matrix.trace (X * (U * D * Uᵀ)) := hr.symm
    _ = Matrix.trace (X * N) := congrArg (fun K => Matrix.trace (X * K)) hs.symm

theorem frobeniusSq_nonneg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ frobeniusSq M := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (M i j)

theorem frobeniusSq_eq_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    frobeniusSq M = 0 ↔ M = 0 := by
  constructor
  · intro h
    ext i j
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (M i j))).mp h i (Finset.mem_univ _)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg (M i j))).mp hi j (Finset.mem_univ _)
    exact sq_eq_zero_iff.mp hij
  · intro h
    simp [h,frobeniusSq]

theorem frobeniusSq_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    frobeniusSq (A+B) = frobeniusSq A + frobeniusSq B +
      2 * ∑ i, ∑ j, A i j * B i j := by
  calc
    _ = ∑ i, ∑ j, ((A i j)^2 + (B i j)^2 + 2*(A i j*B i j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [Matrix.add_apply]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, frobeniusSq]

theorem trace_mul_symmetric {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i j, B i j = B j i) :
    Matrix.trace (A*B) = ∑ i, ∑ j, A i j * B i j := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hB j i]

/-- The full projection identity for the actual spectral clipping. -/
theorem positive_part_frobenius_identity {n : ℕ}
    (M X : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) :
    frobeniusSq (X-M) = frobeniusSq (positivePart M-M) +
      frobeniusSq (X-positivePart M) +
      2*Matrix.trace (X*(positivePart M-M)) := by
  have hN := positive_part_majorant M hM
  have hf := frobeniusSq_add (X-positivePart M) (positivePart M-M)
  rw [sub_add_sub_cancel, ← trace_mul_symmetric _ _ hN.1] at hf
  rw [Matrix.sub_mul,Matrix.trace_sub,positive_part_orthogonal M hM,
    Matrix.trace_zero,sub_zero] at hf
  linarith

/-- Frobenius projection inequality, including its squared-error remainder. -/
theorem positive_part_frobenius_projection {n : ℕ}
    (M X : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) (hX : PSD X) :
    frobeniusSq (positivePart M-M) + frobeniusSq (X-positivePart M) ≤
      frobeniusSq (X-M) := by
  have htrace := trace_psd_product_nonneg X (positivePart M-M) hX (positive_part_majorant M hM)
  rw [positive_part_frobenius_identity M X hM]
  linarith

theorem positive_part_frobenius_nearest {n : ℕ}
    (M X : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) (hX : PSD X) :
    frobeniusSq (positivePart M-M) ≤ frobeniusSq (X-M) := by
  have h := positive_part_frobenius_projection M X hM hX
  have hn := frobeniusSq_nonneg (X-positivePart M)
  linarith

theorem positive_part_frobenius_unique {n : ℕ}
    (M X : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) (hX : PSD X)
    (hnearest : frobeniusSq (X-M) = frobeniusSq (positivePart M-M)) :
    X = positivePart M := by
  have h := positive_part_frobenius_projection M X hM hX
  have hn := frobeniusSq_nonneg (X-positivePart M)
  have hz : frobeniusSq (X-positivePart M) = 0 := by linarith
  exact sub_eq_zero.mp ((frobeniusSq_eq_zero _).mp hz)

/-- The absolute row-sum bound in the Euclidean operator norm. -/
theorem operatorNorm_le_abs_row_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, M i j = M j i) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ i, (∑ j, |M i j|) ≤ C) : operatorNorm M ≤ C := by
  have hl2norm (x : Fin n → ℝ) : ‖WithLp.toLp 2 x‖ = l2 x := by
    simp [EuclideanSpace.norm_eq,l2,Real.norm_eq_abs,sq_abs]
  have hl2nonneg (x : Fin n → ℝ) : 0 ≤ l2 x := Real.sqrt_nonneg _
  have hl2sq (x : Fin n → ℝ) : l2 x^2 = ∑ i, x i^2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i))
  have hcol (j : Fin n) : (∑ i, |M i j|) ≤ C := by
    calc
      _ = ∑ i, |M j i| := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hM i j]
      _ ≤ C := hrow j
  have hx (x : Fin n → ℝ) : l2 (M *ᵥ x) ≤ C * l2 x := by
    have hi (i : Fin n) : (M *ᵥ x) i ^ 2 ≤ C * ∑ j, |M i j| * x j ^ 2 := by
      have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
        (r := fun j => M i j * x j) (f := fun j => |M i j|)
        (g := fun j => |M i j| * x j ^ 2)
        (fun j _ => abs_nonneg (M i j))
        (fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
        (fun j _ => by rw [mul_pow, ←mul_assoc, ←pow_two, sq_abs])
      exact hh.trans (mul_le_mul_of_nonneg_right (hrow i)
        (Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))))
    have hs : (∑ i, (M *ᵥ x) i ^ 2) ≤ C ^ 2 * ∑ j, x j ^ 2 := by
      calc
        _ ≤ ∑ i, C * ∑ j, |M i j| * x j ^ 2 := Finset.sum_le_sum (fun i _ => hi i)
        _ = C * ∑ j, (∑ i, |M i j|) * x j ^ 2 := by
          rw [←Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.sum_mul]
        _ ≤ C * ∑ j, C * x j ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hC
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)
        _ = _ := by rw [←Finset.mul_sum]; ring
    apply (sq_le_sq₀ (hl2nonneg _) (mul_nonneg hC (hl2nonneg _))).mp
    simpa only [hl2sq,mul_pow] using hs
  change ‖(Matrix.toEuclideanLin M).toContinuousLinearMap‖ ≤ C
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have hxnorm : l2 (WithLp.ofLp x) = ‖x‖ := by rw [←hl2norm]
  have he : (Matrix.toEuclideanLin M).toContinuousLinearMap x =
      WithLp.toLp 2 (M *ᵥ WithLp.ofLp x) := by
    have hxx : x = WithLp.toLp 2 (WithLp.ofLp x) := by simp
    rw [hxx]
    simp only [LinearMap.coe_toContinuousLinearMap',Matrix.toEuclideanLin,
      Matrix.toLpLin_toLp,Matrix.toLin'_apply]
  rw [he,hl2norm]
  simpa only [hxnorm] using hx (WithLp.ofLp x)

theorem oracle_symmetric {n : ℕ} (A : Graph n) (i j : Fin n) :
    oracleMatrix A i j = oracleMatrix A j i := by
  simp only [oracleMatrix,Matrix.add_apply,Matrix.one_apply,adjacency]
  rw [A.property.1 i j]
  simp only [eq_comm]

theorem oracle_hermitian {n : ℕ} (A : Graph n) : (oracleMatrix A).IsHermitian := by
  ext i j
  simpa using oracle_symmetric A j i

theorem oracle_nonneg {n : ℕ} (A : Graph n) (i j : Fin n) :
    0 ≤ oracleMatrix A i j := by
  have hI : 0 ≤ (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  have hA : 0 ≤ adjacency A i j := by
    unfold adjacency
    split_ifs <;> norm_num
  exact add_nonneg hI hA

set_option backward.isDefEq.respectTransparency false in
theorem oracle_row_sum {n : ℕ} (A : Graph n) (i : Fin n) :
    (∑ j,oracleMatrix A i j) = (degree A i : ℝ)+1 := by
  classical
  unfold oracleMatrix adjacency degree
  simp only [Matrix.add_apply,Matrix.one_apply,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  push_cast
  ring

theorem oracle_operatorNorm_degree {n : ℕ} (A : Graph n) :
    operatorNorm (oracleMatrix A) ≤
      1 + ((Finset.univ.sup (fun i => degree A i) : ℕ) : ℝ) := by
  apply operatorNorm_le_abs_row_sum _ (oracle_symmetric A) _ (by positivity)
  intro i
  simp_rw [abs_of_nonneg (oracle_nonneg A i _)]
  rw [oracle_row_sum]
  have hd : degree A i ≤ Finset.univ.sup (fun j => degree A j) :=
    Finset.le_sup (Finset.mem_univ i)
  have hdr : (degree A i : ℝ) ≤ ((Finset.univ.sup (fun j => degree A j) : ℕ) : ℝ) := by
    exact_mod_cast hd
  linarith

/-- Five finite spectral properties of the positive part of an oracle matrix. -/
theorem positive_part_finite {n : ℕ} (A : Graph n) :
    PSD (positivePart (oracleMatrix A)) ∧
    PSD (positivePart (oracleMatrix A) - oracleMatrix A) ∧
    operatorNorm (positivePart (oracleMatrix A)) ≤
      1 + ((Finset.univ.sup (fun i => degree A i) : ℕ) : ℝ) ∧
    (∀ x, max (V1 A x) 0 ≤ VPositive A x) ∧
    (∀ M, PSD M → frobeniusSq (positivePart (oracleMatrix A)-oracleMatrix A) ≤
      frobeniusSq (M-oracleMatrix A)) := by
  have hA := oracle_hermitian A
  have hp := positive_part_psd (oracleMatrix A)
  have hd := positive_part_majorant (oracleMatrix A) hA
  refine ⟨hp,hd,(positive_part_operatorNorm_le _ hA).trans (oracle_operatorNorm_degree A),?_,?_⟩
  · intro x
    change max (V1 A x) 0 ≤ varianceForm (positivePart (oracleMatrix A)) x
    apply max_le
    · rw [←variance_form_oracle A x]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      have hh := hd.2 (centered x)
      have he : quadratic (positivePart (oracleMatrix A)-oracleMatrix A) (centered x) =
          quadratic (positivePart (oracleMatrix A)) (centered x) -
          quadratic (oracleMatrix A) (centered x) := by
        simp [quadratic,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]
      linarith
    · exact div_nonneg (hp.2 _) (sq_nonneg _)
  · intro M hM
    exact positive_part_frobenius_nearest _ M hA hM

/-- Uniqueness of the nearest PSD matrix to a graph oracle matrix. -/
theorem positive_part_nearest_unique {n : ℕ} (A : Graph n)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : PSD M)
    (hnearest : frobeniusSq (M-oracleMatrix A) =
      frobeniusSq (positivePart (oracleMatrix A)-oracleMatrix A)) :
    M = positivePart (oracleMatrix A) := by
  exact positive_part_frobenius_unique _ M (oracle_hermitian A) hM hnearest

/-- Asymptotic conservativeness for the positive part of the true-graph oracle matrix. -/
theorem positive_part_conservative (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) :
    Conservative F (fun k y => VPositive (F.model k).G (weighted (F.model k) y)) := by
  have hscaling := h
  rcases h with ⟨hNested,hc1,hc2,hc3,hc4,hDep,hBound,hDeg,hVar,hTheta⟩
  let M : ∀ k, Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ :=
    fun k => positivePart (oracleMatrix (F.model k).G)
  have hsym : ∀ k i j, M k i j = M k j i := by
    intro k
    exact (positive_part_psd _).1
  have hK : ∀ k, operatorNorm (M k) ≤ 1+c2 := by
    intro k
    apply (positive_part_operatorNorm_le _ (oracle_hermitian (F.model k).G)).trans
    apply operatorNorm_le_abs_row_sum _ (oracle_symmetric _) (1+c2) (by positivity)
    intro i
    simp_rw [abs_of_nonneg (oracle_nonneg (F.model k).G i _)]
    rw [oracle_row_sum]
    linarith [hDeg k i]
  have hPSD : ∀ k, PSD (M k) ∧ PSD (M k-oracleMatrix (F.model k).G) := by
    intro k
    exact ⟨positive_part_psd _,positive_part_majorant _ (oracle_hermitian _)⟩
  have hfinal := (deterministic_quadratic_expansion F c1 c2 c3 c4 (1+c2)
    hscaling M hsym hK).2.2 hPSD
  simpa only [M,VPositive] using hfinal.2

/-- PSD orthogonal positive/negative decompositions identify the actual clipping. -/
theorem positive_part_of_orthogonal_decomposition {n : ℕ}
    (M C : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian)
    (hC : PSD C) (hN : PSD (C-M)) (horth : C*(C-M) = 0) :
    C = positivePart M := by
  have hf := frobeniusSq_add (positivePart M-C) (C-M)
  rw [sub_add_sub_cancel, ← trace_mul_symmetric _ _ hN.1] at hf
  rw [Matrix.sub_mul,Matrix.trace_sub,horth,Matrix.trace_zero,sub_zero] at hf
  have ht := trace_psd_product_nonneg (positivePart M) (C-M) (positive_part_psd M) hN
  have hn := frobeniusSq_nonneg (positivePart M-C)
  have hnear := positive_part_frobenius_nearest M C hM hC
  have heq : frobeniusSq (C-M) = frobeniusSq (positivePart M-M) := by linarith
  exact positive_part_frobenius_unique M C hM hC heq

/-- The rational cycle certificate equals the canonical Mathlib-eigenbasis clipping. -/
theorem cycle_clipped_eq_positive_part :
    cycleClipped = positivePart (oracleMatrix cycleGraph) := by
  have hp : PSD cycleClipped := by
    apply (audit_psd_iff _).mpr
    have hd : (Matrix.diagonal (![3,1,1,0] : Fin 4 → ℝ)).PosSemidef :=
      Matrix.PosSemidef.diagonal (fun i => by fin_cases i <;> norm_num)
    simpa [cycleClipped] using hd.mul_mul_conjTranspose_same cycleEigenvectors
  have hn : PSD (cycleClipped-oracleMatrix cycleGraph) := by
    constructor
    · intro i j
      simp only [Matrix.sub_apply]
      rw [hp.1 i j,oracle_symmetric cycleGraph i j]
    · intro x
      have hq : quadratic (cycleClipped-oracleMatrix cycleGraph) x =
          quadratic cycleClipped x-quadratic (oracleMatrix cycleGraph) x := by
        simp [quadratic,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]
      rw [hq,cycle_spectral_certificate.2.2 x]
      nlinarith [sq_nonneg (x 0-x 1+x 2-x 3)]
  have horth : cycleClipped*(cycleClipped-oracleMatrix cycleGraph) = 0 := by
    let U := cycleEigenvectors
    let p : Fin 4 → ℝ := ![3,1,1,0]
    let q : Fin 4 → ℝ := ![3,1,1,-1]
    have hd : cycleClipped-oracleMatrix cycleGraph =
        U * Matrix.diagonal (fun i => p i-q i) * Uᵀ := by
      calc
        _ = cycleClipped - U * Matrix.diagonal q * Uᵀ :=
          congrArg (fun K => cycleClipped-K) cycle_spectral_certificate.2.1
        _ = _ := by
          rw [cycleClipped, ← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.diagonal_sub]
    have hz : Matrix.diagonal p * Matrix.diagonal (fun i => p i-q i) =
        (0 : Matrix (Fin 4) (Fin 4) ℝ) := by
      rw [Matrix.diagonal_mul_diagonal]
      have hf : (fun i => p i*(p i-q i)) = fun _ => 0 := by
        funext i
        fin_cases i <;> norm_num [p,q]
      rw [hf]
      exact Matrix.diagonal_zero
    rw [hd]
    change (U * Matrix.diagonal p * Uᵀ) *
      (U * Matrix.diagonal (fun i => p i-q i) * Uᵀ) = 0
    calc
      _ = U * Matrix.diagonal p * (Uᵀ*U) *
          Matrix.diagonal (fun i => p i-q i) * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = 0 := by
        rw [show Uᵀ*U=1 from cycle_spectral_certificate.1,Matrix.mul_one,
          Matrix.mul_assoc U,hz,Matrix.mul_zero,Matrix.zero_mul]
  exact positive_part_of_orthogonal_decomposition _ cycleClipped (oracle_hermitian cycleGraph)
    hp hn horth


theorem cycle_actual_positive_value :
    quadratic (positivePart (oracleMatrix cycleGraph)) (![0,1,-1,0] : Fin 4 → ℝ) = 1 := by
  rw [←cycle_clipped_eq_positive_part]
  exact cycle_majorant_certificate.2.2.2

end
end AronowAudit.P011.SpectralConfidence

namespace AronowAudit.P011
noncomputable section

theorem positive_part_finite {n : ℕ} (A : Graph n) :
    PSD (positivePart (oracleMatrix A)) ∧
    PSD (positivePart (oracleMatrix A) - oracleMatrix A) ∧
    operatorNorm (positivePart (oracleMatrix A)) ≤
      1 + ((Finset.univ.sup (fun i => degree A i) : ℕ) : ℝ) ∧
    (∀ x, max (V1 A x) 0 ≤ VPositive A x) ∧
    (∀ M, PSD M → frobeniusSq (positivePart (oracleMatrix A)-oracleMatrix A) ≤
      frobeniusSq (M-oracleMatrix A)) := by
  exact SpectralConfidence.positive_part_finite A

theorem positive_part_nearest_unique {n : ℕ} (A : Graph n)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : PSD M)
    (hnearest : frobeniusSq (M-oracleMatrix A) =
      frobeniusSq (positivePart (oracleMatrix A)-oracleMatrix A)) :
    M = positivePart (oracleMatrix A) := by
  exact SpectralConfidence.positive_part_nearest_unique A M hM hnearest

theorem positive_part_conservative (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) :
    Conservative F (fun k y => VPositive (F.model k).G (weighted (F.model k) y)) := by
  exact SpectralConfidence.positive_part_conservative F c1 c2 c3 c4 h

end
end AronowAudit.P011
