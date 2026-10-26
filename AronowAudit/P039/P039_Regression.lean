import Mathlib
import AronowAudit.P039.P039_LinearMoments
import AronowAudit.P039.P039_StudentCompletion

namespace AronowAudit.P039

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192

open scoped BigOperators Matrix NNReal
open MeasureTheory ProbabilityTheory

/-- Squared Euclidean length, the `‖c-Aβ‖²` least-squares
criterion (T3--T4; the paper prints no matrix notation). -/
noncomputable def squaredLength {n : ℕ} (v : Fin n → ℝ) : ℝ := dotProduct v v

/-- Full column rank, represented by injectivity of the design's coefficient
map; T3--T4's OLS setting and T7's nested-design hypotheses. -/
noncomputable def FullColumnRank {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ) : Prop :=
  Function.Injective A.mulVec

/-- Ordinary least-squares coefficient `(Aᵀ A)⁻¹ Aᵀ c`; deposited `lm` fits,
Figure 4 (p. 138) and Table 2 Panel A (pp. 136--137), as specified in T3/T7.
Full rank is required in theorems using this total matrix-inverse definition. -/
noncomputable def ols {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ) (c : Fin n → ℝ) : Fin p → ℝ :=
  (Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ c)

/-- Fitted residual `c-Aβ̂`, the "residuals from the composite models",
p. 138 (PDF p. 13); the paper's nonlinear fits are not identified with this
exact linear OLS definition. -/
noncomputable def olsResidual {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ) (c : Fin n → ℝ) : Fin n → ℝ :=
  c - A *ᵥ ols A c

/-- Error sum of squares, T3--T4 and T7's OLS setting (not printed as a formula). -/
noncomputable def olsSSE {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ) (c : Fin n → ℝ) : ℝ :=
  squaredLength (olsResidual A c)

/-- Conventional squared coefficient SE: SSE/(n-p) times the corresponding
inverse-Gram diagonal, T3--T4/T7; the parenthesized Table 2 entries are read
as conventional SEs based on the deposited `summary(lm)` script. -/
noncomputable def olsSESquared {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ)
    (c : Fin n → ℝ) (j : Fin p) : ℝ :=
  olsSSE A c / ((n : ℝ) - p) * (Aᵀ * A)⁻¹ j j

/-- Residual standard error `sqrt(SSE/(n-p))`, the conventional reading of
"RMSQ = Root mean squared error", Table 2 note, p. 137; T7 explicitly uses
this reading in its nested-fit calculation. -/
noncomputable def olsResidualStandardError {n p : ℕ}
    (A : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) : ℝ :=
  Real.sqrt (olsSSE A y / ((n : ℝ)-p))

/-- Conventional coefficient t statistic, T3--T4: coefficient divided by
the nonnegative square root of the conventional squared SE. Its statistical
interpretation requires a strictly positive denominator. -/
noncomputable def olsT {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ)
    (c : Fin n → ℝ) (j : Fin p) : ℝ :=
  ols A c j / Real.sqrt (olsSESquared A c j)

/-- The unqualified squared t ratio, β̂²/SE², used for exact arithmetic
in T3 and T4(e); all concrete SE² values below are strictly positive. -/
noncomputable def olsTSquared {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ)
    (c : Fin n → ℝ) (j : Fin p) : ℝ :=
  (ols A c j) ^ 2 / olsSESquared A c j

/-- A coefficient vector minimizes the Euclidean SSE over every coefficient
vector; this gives mathematical least-squares meaning to the normal-equation
certificates rather than treating computed coefficients as arbitrary numbers. -/
noncomputable def IsLeastSquares {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) (β : Fin p → ℝ) : Prop :=
  ∀ b, squaredLength (y - A *ᵥ β) ≤ squaredLength (y - A *ᵥ b)

/-- Finite nonnegativity lemma for the least-squares criteria in T3--T4/T7. -/
theorem squaredLength_nonnegative {n : ℕ} (v : Fin n → ℝ) : 0 ≤ squaredLength v := by
  unfold squaredLength dotProduct
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))


/-- Finite zero-criterion lemma: squared Euclidean length vanishes exactly
at the zero vector, used in uniqueness of all certified OLS fits. -/
theorem squaredLength_zero_iff {n : ℕ} (v : Fin n → ℝ) : squaredLength v = 0 ↔ v = 0 := by
  exact dotProduct_self_eq_zero


/-- Normal equations yield the Pythagorean SSE expansion, the finite
least-squares lemma behind the exact regression witnesses of T3 and T7. -/
theorem normal_equation_expansion {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) (β b : Fin p → ℝ) (h : Aᵀ *ᵥ (y - A *ᵥ β) = 0) :
    squaredLength (y - A *ᵥ b) =
      squaredLength (y - A *ᵥ β) + squaredLength (A *ᵥ (b - β)) := by
  have ho : dotProduct (y - A *ᵥ β) (A *ᵥ (b - β)) = 0 := by
    rw [← Matrix.dotProduct_transpose_mulVec, h]
    simp
  have hv : y - A *ᵥ b = (y - A *ᵥ β) - A *ᵥ (b - β) := by
    rw [Matrix.mulVec_sub]
    abel
  have he : ∀ rr vv : Fin n → ℝ, squaredLength (rr-vv) =
      squaredLength rr - 2*dotProduct rr vv + squaredLength vv := by
    intro rr vv
    unfold squaredLength
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm vv rr]
    ring
  rw [hv, he, ho]
  ring


/-- A full-rank normal-equation certificate gives the unique least-squares
minimizer, supporting the concrete computations in T3 and T7. -/
theorem normal_equation_unique {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) (β : Fin p → ℝ) (hA : FullColumnRank A)
    (h : Aᵀ *ᵥ (y - A *ᵥ β) = 0) :
    IsLeastSquares A y β ∧ ∀ b, IsLeastSquares A y b → b = β := by
  have hmin : IsLeastSquares A y β := by
    intro b
    rw [normal_equation_expansion A y β b h]
    exact le_add_of_nonneg_right (squaredLength_nonnegative _)
  refine ⟨hmin, ?_⟩
  intro b hb
  have he := normal_equation_expansion A y β b h
  have hn := squaredLength_nonnegative (A *ᵥ (b - β))
  have hz : squaredLength (A *ᵥ (b - β)) = 0 := by
    have := hb β
    linarith
  have hzv := (squaredLength_zero_iff _).mp hz
  have hd : b - β = 0 := hA (by simpa using hzv)
  exact sub_eq_zero.mp hd


/-- An explicit left inverse of the Gram matrix certifies full column rank
without any approximate rank calculation; used for T3 and T7. -/
theorem gram_certificate_full_rank {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ)
    (H : Matrix (Fin p) (Fin p) ℝ) (h : H * (Aᵀ * A) = 1) : FullColumnRank A := by
  have hl : Function.LeftInverse (fun v => H *ᵥ (Aᵀ *ᵥ v)) A.mulVec := by
    intro b
    change H *ᵥ (Aᵀ *ᵥ (A *ᵥ b)) = b
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, h, Matrix.one_mulVec]
  exact hl.injective


/-- The six-observation u vector, T3(i); not
one of the paper's election samples. -/
noncomputable def witnessU : Fin 6 → ℝ := ![1, -1, 0, 0, 0, 0]
/-- The six-observation v vector, T3(i). -/
noncomputable def witnessV : Fin 6 → ℝ := ![0, 0, 1, -1, 0, 0]
/-- The six-observation w vector, T3(i). -/
noncomputable def witnessW : Fin 6 → ℝ := ![0, 0, 0, 0, 1, -1]
/-- The response y=u+(3/2)v+w, T3(i), with all numbers explicit. -/
noncomputable def witnessY : Fin 6 → ℝ := ![1, -1, 3/2, -3/2, 1, -1]
/-- The first-stage design [1,u], T3(i). -/
noncomputable def witnessZ : Matrix (Fin 6) (Fin 2) ℝ := fun i j => ![1, witnessU i] j
/-- Residual-regression design [1,x], the procedure used for the line of
Figure 4 (p. 138); here applied to the six-observation witness. -/
noncomputable def residualLine {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin n) (Fin 2) ℝ :=
  fun i j => ![1, x i] j
/-- Append the tested regressor to the first-stage controls, [Z,x], T4(c). -/
noncomputable def fullDesign {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin (k+1)) ℝ :=
  fun i j => if hj : j.val < k then Z i ⟨j.val, hj⟩ else x i

/-- The projection Z(ZᵀZ)⁻¹Zᵀ, T3(i), T4(a). -/
noncomputable def controlProjection {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := Z * (Zᵀ * Z)⁻¹ * Zᵀ
/-- Residual maker I-P, T3(i), T4(a). -/
noncomputable def residualMaker {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := 1 - controlProjection Z

/-- Finite OLS lemma for T4(a)/T7(i): full column rank makes the real Gram
matrix invertible. This is proved from equality of the two kernels in Mathlib. -/
theorem full_rank_gram_unit {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (hZ : FullColumnRank Z) : IsUnit (Zᵀ * Z) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  have hk : LinearMap.ker (Zᵀ * Z).mulVecLin = ⊥ := by
    rw [Matrix.ker_mulVecLin_transpose_mul_self]
    exact LinearMap.ker_eq_bot.mpr hZ
  exact LinearMap.ker_eq_bot.mp hk


/-- T4(a), finite matrix part: the control and residual projections are
symmetric and idempotent. The residual maker annihilates the controls
and gives the OLS residual with its normal equations. -/
theorem ols_projection_identities {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (hZ : FullColumnRank Z) :
    (controlProjection Z)ᵀ = controlProjection Z ∧
    controlProjection Z * controlProjection Z = controlProjection Z ∧
    (residualMaker Z)ᵀ = residualMaker Z ∧
    residualMaker Z * residualMaker Z = residualMaker Z ∧ residualMaker Z * Z = 0 ∧
    ∀ y, residualMaker Z *ᵥ y = olsResidual Z y ∧ Zᵀ *ᵥ (residualMaker Z *ᵥ y) = 0 := by
  have hu := full_rank_gram_unit Z hZ
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have hi := Matrix.nonsing_inv_mul (Zᵀ*Z) hd
  have hsym : (controlProjection Z)ᵀ = controlProjection Z := by
    unfold controlProjection
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_nonsing_inv]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hpz : controlProjection Z * Z = Z := by
    calc
      _ = Z*((Zᵀ*Z)⁻¹*(Zᵀ*Z)) := by simp only [controlProjection, Matrix.mul_assoc]
      _ = Z := by rw [hi]; simp
  have hpp : controlProjection Z * controlProjection Z = controlProjection Z := by
    calc
      _ = Z*((Zᵀ*Z)⁻¹*(Zᵀ*Z))*(Zᵀ*Z)⁻¹*Zᵀ := by
        simp only [controlProjection, Matrix.mul_assoc]
      _ = controlProjection Z := by rw [hi]; simp [controlProjection]
  have hms : (residualMaker Z)ᵀ = residualMaker Z := by
    simp only [residualMaker, Matrix.transpose_sub, Matrix.transpose_one, hsym]
  have hmm : residualMaker Z * residualMaker Z = residualMaker Z := by
    simp only [residualMaker, sub_mul, mul_sub, one_mul, mul_one, hpp]
    abel
  have hmz : residualMaker Z * Z = 0 := by
    simp only [residualMaker, Matrix.sub_mul, Matrix.one_mul, hpz, sub_self]
  have hzm : Zᵀ * residualMaker Z = 0 := by
    have h := congrArg Matrix.transpose hmz
    simpa only [Matrix.transpose_mul, hms, Matrix.transpose_zero] using h
  refine ⟨hsym, hpp, hms, hmm, hmz, ?_⟩
  intro y
  constructor
  · simp only [residualMaker, controlProjection, olsResidual, ols, Matrix.sub_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  · rw [Matrix.mulVec_mulVec, hzm, Matrix.zero_mulVec]


/-- Finite least-squares existence and uniqueness for T4(c)/T7(i), without
distributional assumptions: every full-rank OLS coefficient is the unique
minimizer of the finite Euclidean SSE. -/
theorem full_rank_ols_unique {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) (hA : FullColumnRank A) :
    IsLeastSquares A y (ols A y) ∧ ∀ b, IsLeastSquares A y b → b=ols A y := by
  have hp := (ols_projection_identities A hA).2.2.2.2.2 y
  apply normal_equation_unique A y (ols A y) hA
  change Aᵀ *ᵥ olsResidual A y = 0
  rw [← hp.1]
  exact hp.2


/-- T7(i), finite variational lemma: nesting the two control spans can
only decrease the minimized residual sum of squares of the common income
regressor. The explicit minimizers can be supplied by full_rank_ols_unique. -/
theorem nested_minimum_squares {n k₁ k₂ : ℕ}
    (Z₁ : Matrix (Fin n) (Fin k₁) ℝ) (Z₂ : Matrix (Fin n) (Fin k₂) ℝ)
    (q : Fin n → ℝ) (a₁ : Fin k₁ → ℝ) (a₂ : Fin k₂ → ℝ)
    (hspan : ∀ a, ∃ b, Z₁ *ᵥ a = Z₂ *ᵥ b) (hmin : IsLeastSquares Z₂ q a₂) :
    squaredLength (q-Z₂ *ᵥ a₂) ≤ squaredLength (q-Z₁ *ᵥ a₁) := by
  obtain ⟨b, hb⟩ := hspan a₁
  rw [hb]
  exact hmin b


/-- T3(i): exact first-stage Gram matrix, inverse and residual vector. -/
theorem witness_baseline :
    witnessZᵀ * witnessZ = !![6, 0; 0, 2] ∧
    (witnessZᵀ * witnessZ)⁻¹ = !![(1/6 : ℝ), 0; 0, 1/2] ∧
    FullColumnRank witnessZ ∧
    ols witnessZ witnessY = ![0, 1] ∧
    olsResidual witnessZ witnessY = ![0, 0, (3/2 : ℝ), -3/2, 1, -1] ∧
    olsSSE witnessZ witnessY = (13/2 : ℝ) := by
  have hg : witnessZᵀ * witnessZ = !![6, 0; 0, 2] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [witnessZ, witnessU, Matrix.mul_apply, dotProduct, Fin.sum_univ_succ]
  have hi : !![(1/6 : ℝ), 0; 0, 1/2] * (witnessZᵀ * witnessZ) = 1 := by
    rw [hg]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  have hinv := Matrix.inv_eq_left_inv hi
  have hb : ols witnessZ witnessY = ![0, 1] := by
    ext i; fin_cases i <;>
      norm_num [ols, hinv, witnessZ, witnessU, witnessY, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hr : olsResidual witnessZ witnessY = ![0, 0, (3/2 : ℝ), -3/2, 1, -1] := by
    unfold olsResidual
    rw [hb]
    ext i; fin_cases i <;>
      norm_num [witnessZ, witnessU, witnessY, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  refine ⟨hg, hinv, gram_certificate_full_rank _ _ hi, hb, hr, ?_⟩
  unfold olsSSE
  rw [hr]
  norm_num [squaredLength, dotProduct, Fin.sum_univ_succ]


/-- T3(i): the residual-maker is symmetric, idempotent, has rank four,
and maps y to the explicitly computed first-stage residual. -/
theorem witness_residual_projection :
    (residualMaker witnessZ)ᵀ = residualMaker witnessZ ∧
    residualMaker witnessZ * residualMaker witnessZ = residualMaker witnessZ ∧
    (residualMaker witnessZ).rank = 4 ∧
    residualMaker witnessZ *ᵥ witnessY = olsResidual witnessZ witnessY := by
  have hp := ols_projection_identities witnessZ witness_baseline.2.2.1
  have hm := hp.2.2.2.1
  have hi : IsIdempotentElem (residualMaker witnessZ).mulVecLin := by
    change (residualMaker witnessZ).mulVecLin.comp (residualMaker witnessZ).mulVecLin = _
    rw [← Matrix.mulVecLin_mul, hm]
  have ht := (LinearMap.IsIdempotentElem.isProj_range _ hi).trace
  have ht' : (residualMaker witnessZ).trace = ((residualMaker witnessZ).rank : ℝ) := by
    have he : LinearMap.trace ℝ (Fin 6 → ℝ) (residualMaker witnessZ).mulVecLin =
        (residualMaker witnessZ).trace := by
      rw [← Matrix.toLin'_apply', Matrix.trace_toLin'_eq]
    exact he.symm.trans ht
  have hval : (residualMaker witnessZ).trace = (4 : ℝ) := by
    norm_num [residualMaker, controlProjection, witness_baseline.2.1, witnessZ,
      witnessU, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ]
  have hrank : (residualMaker witnessZ).rank = 4 := by
    exact_mod_cast (ht'.symm.trans hval)
  exact ⟨hp.2.2.1, hm, hrank, (hp.2.2.2.2.2 witnessY).1⟩


/-- Closed form of the two-sided t4 tail for t≥0, T3(iii).
This analytic formula defines the nominal
p-value; no density-integration theorem is assumed. -/
noncomputable def studentFourTail (t : ℝ) : ℝ :=
  let z := t / Real.sqrt (4 + t^2)
  1 - (3/2 : ℝ)*z + (1/2 : ℝ)*z^3
/-- Closed form of the two-sided t3 tail for t≥0, T3(iii). -/
noncomputable def studentThreeTail (t : ℝ) : ℝ :=
  let q := t / Real.sqrt 3
  1 - (2 / Real.pi) * (Real.arctan q + q / (1+q^2))

/-- T3(iii): the nominal residual-line p-value is strictly below 0.05,
while the full-model p-value is strictly above 0.05. Both are the closed-form
tails specified in the target, evaluated at the computed positive t values. -/
theorem residual_test_five_percent_disagreement :
    studentFourTail 3 = 1 - 45 / (13 * Real.sqrt 13) ∧
    studentFourTail 3 < (1/20 : ℝ) ∧
    studentThreeTail (3 * Real.sqrt 3 / 2) =
      1/2 - 2/Real.pi * (Real.arctan (1/5) + 6/13) ∧
    (1/20 : ℝ) < studentThreeTail (3 * Real.sqrt 3 / 2) := by
  have hs13 : (Real.sqrt 13)^2 = (13 : ℝ) := Real.sq_sqrt (by norm_num)
  have hp13 : 0 < Real.sqrt (13 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hc13 : (Real.sqrt 13)^3 = (13 : ℝ)*Real.sqrt 13 := by
    rw [pow_succ, hs13]
  have hfour : studentFourTail 3 = 1-45/(13*Real.sqrt 13) := by
    unfold studentFourTail
    norm_num
    field_simp
    nlinarith [hc13]
  have hbound : 247 * Real.sqrt (13 : ℝ) < 900 := by
    by_contra hn
    have he : (900/247 : ℝ) ≤ Real.sqrt 13 := by linarith
    have hsq : (900/247 : ℝ)^2 ≤ (Real.sqrt 13)^2 :=
      (sq_le_sq₀ (by norm_num) hp13.le).2 he
    nlinarith
  have hreject : studentFourTail 3 < (1/20 : ℝ) := by
    rw [hfour]
    have hfrac : (19/20 : ℝ) < 45/(13*Real.sqrt 13) := by
      apply (lt_div_iff₀ (by positivity)).2
      nlinarith
    linarith
  have hp3 : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hq : (3*Real.sqrt 3/2)/Real.sqrt 3 = (3/2 : ℝ) := by
    field_simp
  have ha : Real.pi/4 + Real.arctan (1/5 : ℝ) = Real.arctan (3/2 : ℝ) := by
    have h := Real.arctan_add (x := (1 : ℝ)) (y := (1/5 : ℝ)) (by norm_num)
    norm_num [Real.arctan_one] at h
    exact h
  have hthree : studentThreeTail (3*Real.sqrt 3/2) =
      1/2 - 2/Real.pi * (Real.arctan (1/5) + 6/13) := by
    unfold studentThreeTail
    rw [hq]
    dsimp only
    rw [← ha]
    norm_num
    field_simp
    <;> ring
  have hangle : Real.arctan (1/5 : ℝ) < (1/5 : ℝ) := Real.arctan_lt_self (by norm_num)
  have hrec : 2/Real.pi < (2/3 : ℝ) := by
    apply (div_lt_div_iff₀ Real.pi_pos (by norm_num)).2
    nlinarith [Real.pi_gt_three]
  have hmul : 2/Real.pi * (Real.arctan (1/5)+6/13) <
      (2/3 : ℝ)*(1/5+6/13) := by
    calc
      _ ≤ 2/Real.pi * ((1/5 : ℝ)+6/13) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ < _ := mul_lt_mul_of_pos_right hrec (by norm_num)
  refine ⟨hfour, hreject, hthree, ?_⟩
  rw [hthree]
  linarith


/-- T3(ii): exact residual-line OLS fit with x=v.
The design is full rank, the stated minimizer is unique, residual/SSE/SE²
and t² are exact, with 4 residual degrees of freedom. -/
theorem residual_orthogonal_witness_fit :
    FullColumnRank (residualLine witnessV) ∧
    ols (residualLine witnessV) (olsResidual witnessZ witnessY) = ![(0/1 : ℝ), (3/2 : ℝ)] ∧
    olsResidual (residualLine witnessV) (olsResidual witnessZ witnessY) = ![(0/1 : ℝ), (0/1 : ℝ), (0/1 : ℝ), (0/1 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] ∧
    olsSSE (residualLine witnessV) (olsResidual witnessZ witnessY) = (2/1 : ℝ) ∧
    olsSESquared (residualLine witnessV) (olsResidual witnessZ witnessY) 1 = (1/4 : ℝ) ∧
    olsTSquared (residualLine witnessV) (olsResidual witnessZ witnessY) 1 = (9/1 : ℝ) ∧
    IsLeastSquares (residualLine witnessV) (olsResidual witnessZ witnessY) ![(0/1 : ℝ), (3/2 : ℝ)] ∧
    ∀ b, IsLeastSquares (residualLine witnessV) (olsResidual witnessZ witnessY) b → b=![(0/1 : ℝ), (3/2 : ℝ)] := by
  rw [witness_baseline.2.2.2.2.1]
  have hg : (residualLine witnessV)ᵀ * (residualLine witnessV) = !![(6/1 : ℝ), (0/1 : ℝ); (0/1 : ℝ), (2/1 : ℝ)] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [fullDesign, residualLine, witnessZ, witnessU, witnessV, witnessW, witnessY, Matrix.mul_apply, Fin.sum_univ_succ]
  have hi : !![(1/6 : ℝ), (0/1 : ℝ); (0/1 : ℝ), (1/2 : ℝ)] * ((residualLine witnessV)ᵀ * (residualLine witnessV)) = 1 := by
    rw [hg]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  have hinv := Matrix.inv_eq_left_inv hi
  have hb : ols (residualLine witnessV) ![(0/1 : ℝ), (0/1 : ℝ), (3/2 : ℝ), (-3/2 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] = ![(0/1 : ℝ), (3/2 : ℝ)] := by
    unfold ols
    rw [hinv]
    ext i; fin_cases i <;>
      norm_num [fullDesign, residualLine, witnessZ, witnessU, witnessV, witnessW, witnessY, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hr : olsResidual (residualLine witnessV) ![(0/1 : ℝ), (0/1 : ℝ), (3/2 : ℝ), (-3/2 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] = ![(0/1 : ℝ), (0/1 : ℝ), (0/1 : ℝ), (0/1 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] := by
    unfold olsResidual
    rw [hb]
    ext i; fin_cases i <;>
      norm_num [fullDesign, residualLine, witnessZ, witnessU, witnessV, witnessW, witnessY, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hs : olsSSE (residualLine witnessV) ![(0/1 : ℝ), (0/1 : ℝ), (3/2 : ℝ), (-3/2 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] = (2/1 : ℝ) := by
    unfold olsSSE
    rw [hr]
    norm_num [squaredLength, dotProduct, Fin.sum_univ_succ]
  have hse : olsSESquared (residualLine witnessV) ![(0/1 : ℝ), (0/1 : ℝ), (3/2 : ℝ), (-3/2 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] 1 = (1/4 : ℝ) := by
    unfold olsSESquared
    rw [hs, hinv]
    norm_num
  have ht : olsTSquared (residualLine witnessV) ![(0/1 : ℝ), (0/1 : ℝ), (3/2 : ℝ), (-3/2 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] 1 = (9/1 : ℝ) := by
    unfold olsTSquared
    rw [hb, hse]
    norm_num
  have hn : (residualLine witnessV)ᵀ *ᵥ (![(0/1 : ℝ), (0/1 : ℝ), (3/2 : ℝ), (-3/2 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)]-(residualLine witnessV) *ᵥ ![(0/1 : ℝ), (3/2 : ℝ)]) = 0 := by
    rw [← hb]
    change (residualLine witnessV)ᵀ *ᵥ olsResidual (residualLine witnessV) ![(0/1 : ℝ), (0/1 : ℝ), (3/2 : ℝ), (-3/2 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] = 0
    rw [hr]
    ext i; fin_cases i <;>
      norm_num [fullDesign, residualLine, witnessZ, witnessU, witnessV, witnessW, witnessY, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hf := gram_certificate_full_rank _ _ hi
  have hu := normal_equation_unique _ _ _ hf hn
  simp only [div_one] at *
  exact ⟨hf, hb, hr, hs, hse, ht, hu⟩


/-- T3(ii): exact full-model OLS fit with x=v.
The design is full rank, the stated minimizer is unique, residual/SSE/SE²
and t² are exact, with 3 residual degrees of freedom. -/
theorem full_orthogonal_witness_fit :
    FullColumnRank (fullDesign witnessZ witnessV) ∧
    ols (fullDesign witnessZ witnessV) witnessY = ![(0/1 : ℝ), (1/1 : ℝ), (3/2 : ℝ)] ∧
    olsResidual (fullDesign witnessZ witnessV) witnessY = ![(0/1 : ℝ), (0/1 : ℝ), (0/1 : ℝ), (0/1 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] ∧
    olsSSE (fullDesign witnessZ witnessV) witnessY = (2/1 : ℝ) ∧
    olsSESquared (fullDesign witnessZ witnessV) witnessY 2 = (1/3 : ℝ) ∧
    olsTSquared (fullDesign witnessZ witnessV) witnessY 2 = (27/4 : ℝ) ∧
    IsLeastSquares (fullDesign witnessZ witnessV) witnessY ![(0/1 : ℝ), (1/1 : ℝ), (3/2 : ℝ)] ∧
    ∀ b, IsLeastSquares (fullDesign witnessZ witnessV) witnessY b → b=![(0/1 : ℝ), (1/1 : ℝ), (3/2 : ℝ)] := by
  have hA : (fullDesign witnessZ witnessV) = !![(1 : ℝ), 1, 0; 1, -1, 0; 1, 0, 1; 1, 0, -1; 1, 0, 0; 1, 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [fullDesign, witnessZ, witnessU, witnessV]
  have hc : (fullDesign witnessZ witnessV)ᵀ *ᵥ witnessY = ![(0 : ℝ), 2, 3] := by
    ext i; fin_cases i <;>
      norm_num [hA, witnessY, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have hg : (fullDesign witnessZ witnessV)ᵀ * (fullDesign witnessZ witnessV) = !![(6/1 : ℝ), (0/1 : ℝ), (0/1 : ℝ); (0/1 : ℝ), (2/1 : ℝ), (0/1 : ℝ); (0/1 : ℝ), (0/1 : ℝ), (2/1 : ℝ)] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [fullDesign, residualLine, witnessZ, witnessU, witnessV, witnessW, witnessY, Matrix.mul_apply, Fin.sum_univ_succ]
  have hi : !![(1/6 : ℝ), (0/1 : ℝ), (0/1 : ℝ); (0/1 : ℝ), (1/2 : ℝ), (0/1 : ℝ); (0/1 : ℝ), (0/1 : ℝ), (1/2 : ℝ)] * ((fullDesign witnessZ witnessV)ᵀ * (fullDesign witnessZ witnessV)) = 1 := by
    rw [hg]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  have hinv := Matrix.inv_eq_left_inv hi
  have hb : ols (fullDesign witnessZ witnessV) witnessY = ![(0/1 : ℝ), (1/1 : ℝ), (3/2 : ℝ)] := by
    unfold ols
    rw [hinv, hc]
    ext i; fin_cases i <;>
      norm_num [hA, witnessY, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hr : olsResidual (fullDesign witnessZ witnessV) witnessY = ![(0/1 : ℝ), (0/1 : ℝ), (0/1 : ℝ), (0/1 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] := by
    unfold olsResidual
    rw [hb]
    ext i; fin_cases i <;>
      norm_num [hA, witnessY, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hs : olsSSE (fullDesign witnessZ witnessV) witnessY = (2/1 : ℝ) := by
    unfold olsSSE
    rw [hr]
    norm_num [squaredLength, dotProduct, Fin.sum_univ_succ]
  have hse : olsSESquared (fullDesign witnessZ witnessV) witnessY 2 = (1/3 : ℝ) := by
    unfold olsSESquared
    rw [hs, hinv]
    norm_num
  have ht : olsTSquared (fullDesign witnessZ witnessV) witnessY 2 = (27/4 : ℝ) := by
    unfold olsTSquared
    rw [hb, hse]
    norm_num
  have hn : (fullDesign witnessZ witnessV)ᵀ *ᵥ (witnessY-(fullDesign witnessZ witnessV) *ᵥ ![(0/1 : ℝ), (1/1 : ℝ), (3/2 : ℝ)]) = 0 := by
    rw [← hb]
    change (fullDesign witnessZ witnessV)ᵀ *ᵥ olsResidual (fullDesign witnessZ witnessV) witnessY = 0
    rw [hr]
    ext i; fin_cases i <;>
      norm_num [hA, witnessY, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hf := gram_certificate_full_rank _ _ hi
  have hu := normal_equation_unique _ _ _ hf hn
  simp only [div_one] at *
  exact ⟨hf, hb, hr, hs, hse, ht, hu⟩


/-- T3(iv): exact residual-line OLS fit with x=u+v.
The design is full rank, the stated minimizer is unique, residual/SSE/SE²
and t² are exact, with 4 residual degrees of freedom. -/
theorem residual_correlated_witness_fit :
    FullColumnRank (residualLine (witnessU+witnessV)) ∧
    ols (residualLine (witnessU+witnessV)) (olsResidual witnessZ witnessY) = ![(0/1 : ℝ), (3/4 : ℝ)] ∧
    olsResidual (residualLine (witnessU+witnessV)) (olsResidual witnessZ witnessY) = ![(-3/4 : ℝ), (3/4 : ℝ), (3/4 : ℝ), (-3/4 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] ∧
    olsSSE (residualLine (witnessU+witnessV)) (olsResidual witnessZ witnessY) = (17/4 : ℝ) ∧
    olsSESquared (residualLine (witnessU+witnessV)) (olsResidual witnessZ witnessY) 1 = (17/64 : ℝ) ∧
    olsTSquared (residualLine (witnessU+witnessV)) (olsResidual witnessZ witnessY) 1 = (36/17 : ℝ) ∧
    IsLeastSquares (residualLine (witnessU+witnessV)) (olsResidual witnessZ witnessY) ![(0/1 : ℝ), (3/4 : ℝ)] ∧
    ∀ b, IsLeastSquares (residualLine (witnessU+witnessV)) (olsResidual witnessZ witnessY) b → b=![(0/1 : ℝ), (3/4 : ℝ)] := by
  rw [witness_baseline.2.2.2.2.1]
  have hg : (residualLine (witnessU+witnessV))ᵀ * (residualLine (witnessU+witnessV)) = !![(6/1 : ℝ), (0/1 : ℝ); (0/1 : ℝ), (4/1 : ℝ)] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [fullDesign, residualLine, witnessZ, witnessU, witnessV, witnessW, witnessY, Matrix.mul_apply, Fin.sum_univ_succ]
  have hi : !![(1/6 : ℝ), (0/1 : ℝ); (0/1 : ℝ), (1/4 : ℝ)] * ((residualLine (witnessU+witnessV))ᵀ * (residualLine (witnessU+witnessV))) = 1 := by
    rw [hg]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  have hinv := Matrix.inv_eq_left_inv hi
  have hb : ols (residualLine (witnessU+witnessV)) ![(0/1 : ℝ), (0/1 : ℝ), (3/2 : ℝ), (-3/2 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] = ![(0/1 : ℝ), (3/4 : ℝ)] := by
    unfold ols
    rw [hinv]
    ext i; fin_cases i <;>
      norm_num [fullDesign, residualLine, witnessZ, witnessU, witnessV, witnessW, witnessY, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hr : olsResidual (residualLine (witnessU+witnessV)) ![(0/1 : ℝ), (0/1 : ℝ), (3/2 : ℝ), (-3/2 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] = ![(-3/4 : ℝ), (3/4 : ℝ), (3/4 : ℝ), (-3/4 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] := by
    unfold olsResidual
    rw [hb]
    ext i; fin_cases i <;>
      norm_num [fullDesign, residualLine, witnessZ, witnessU, witnessV, witnessW, witnessY, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hs : olsSSE (residualLine (witnessU+witnessV)) ![(0/1 : ℝ), (0/1 : ℝ), (3/2 : ℝ), (-3/2 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] = (17/4 : ℝ) := by
    unfold olsSSE
    rw [hr]
    norm_num [squaredLength, dotProduct, Fin.sum_univ_succ]
  have hse : olsSESquared (residualLine (witnessU+witnessV)) ![(0/1 : ℝ), (0/1 : ℝ), (3/2 : ℝ), (-3/2 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] 1 = (17/64 : ℝ) := by
    unfold olsSESquared
    rw [hs, hinv]
    norm_num
  have ht : olsTSquared (residualLine (witnessU+witnessV)) ![(0/1 : ℝ), (0/1 : ℝ), (3/2 : ℝ), (-3/2 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] 1 = (36/17 : ℝ) := by
    unfold olsTSquared
    rw [hb, hse]
    norm_num
  have hn : (residualLine (witnessU+witnessV))ᵀ *ᵥ (![(0/1 : ℝ), (0/1 : ℝ), (3/2 : ℝ), (-3/2 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)]-(residualLine (witnessU+witnessV)) *ᵥ ![(0/1 : ℝ), (3/4 : ℝ)]) = 0 := by
    rw [← hb]
    change (residualLine (witnessU+witnessV))ᵀ *ᵥ olsResidual (residualLine (witnessU+witnessV)) ![(0/1 : ℝ), (0/1 : ℝ), (3/2 : ℝ), (-3/2 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] = 0
    rw [hr]
    ext i; fin_cases i <;>
      norm_num [fullDesign, residualLine, witnessZ, witnessU, witnessV, witnessW, witnessY, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hf := gram_certificate_full_rank _ _ hi
  have hu := normal_equation_unique _ _ _ hf hn
  simp only [div_one] at *
  exact ⟨hf, hb, hr, hs, hse, ht, hu⟩


/-- T3(iv): exact full-model OLS fit with x=u+v.
The design is full rank, the stated minimizer is unique, residual/SSE/SE²
and t² are exact, with 3 residual degrees of freedom. -/
theorem full_correlated_witness_fit :
    FullColumnRank (fullDesign witnessZ (witnessU+witnessV)) ∧
    ols (fullDesign witnessZ (witnessU+witnessV)) witnessY = ![(0/1 : ℝ), (-1/2 : ℝ), (3/2 : ℝ)] ∧
    olsResidual (fullDesign witnessZ (witnessU+witnessV)) witnessY = ![(0/1 : ℝ), (0/1 : ℝ), (0/1 : ℝ), (0/1 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] ∧
    olsSSE (fullDesign witnessZ (witnessU+witnessV)) witnessY = (2/1 : ℝ) ∧
    olsSESquared (fullDesign witnessZ (witnessU+witnessV)) witnessY 2 = (1/3 : ℝ) ∧
    olsTSquared (fullDesign witnessZ (witnessU+witnessV)) witnessY 2 = (27/4 : ℝ) ∧
    IsLeastSquares (fullDesign witnessZ (witnessU+witnessV)) witnessY ![(0/1 : ℝ), (-1/2 : ℝ), (3/2 : ℝ)] ∧
    ∀ b, IsLeastSquares (fullDesign witnessZ (witnessU+witnessV)) witnessY b → b=![(0/1 : ℝ), (-1/2 : ℝ), (3/2 : ℝ)] := by
  have hA : (fullDesign witnessZ (witnessU+witnessV)) = !![(1 : ℝ), 1, 1; 1, -1, -1; 1, 0, 1; 1, 0, -1; 1, 0, 0; 1, 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [fullDesign, witnessZ, witnessU, witnessV]
  have hc : (fullDesign witnessZ (witnessU+witnessV))ᵀ *ᵥ witnessY = ![(0 : ℝ), 2, 5] := by
    ext i; fin_cases i <;>
      norm_num [hA, witnessY, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have hg : (fullDesign witnessZ (witnessU+witnessV))ᵀ * (fullDesign witnessZ (witnessU+witnessV)) = !![(6/1 : ℝ), (0/1 : ℝ), (0/1 : ℝ); (0/1 : ℝ), (2/1 : ℝ), (2/1 : ℝ); (0/1 : ℝ), (2/1 : ℝ), (4/1 : ℝ)] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [fullDesign, residualLine, witnessZ, witnessU, witnessV, witnessW, witnessY, Matrix.mul_apply, Fin.sum_univ_succ]
  have hi : !![(1/6 : ℝ), (0/1 : ℝ), (0/1 : ℝ); (0/1 : ℝ), (1/1 : ℝ), (-1/2 : ℝ); (0/1 : ℝ), (-1/2 : ℝ), (1/2 : ℝ)] * ((fullDesign witnessZ (witnessU+witnessV))ᵀ * (fullDesign witnessZ (witnessU+witnessV))) = 1 := by
    rw [hg]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  have hinv := Matrix.inv_eq_left_inv hi
  have hb : ols (fullDesign witnessZ (witnessU+witnessV)) witnessY = ![(0/1 : ℝ), (-1/2 : ℝ), (3/2 : ℝ)] := by
    unfold ols
    rw [hinv, hc]
    ext i; fin_cases i <;>
      norm_num [hA, witnessY, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hr : olsResidual (fullDesign witnessZ (witnessU+witnessV)) witnessY = ![(0/1 : ℝ), (0/1 : ℝ), (0/1 : ℝ), (0/1 : ℝ), (1/1 : ℝ), (-1/1 : ℝ)] := by
    unfold olsResidual
    rw [hb]
    ext i; fin_cases i <;>
      norm_num [hA, witnessY, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hs : olsSSE (fullDesign witnessZ (witnessU+witnessV)) witnessY = (2/1 : ℝ) := by
    unfold olsSSE
    rw [hr]
    norm_num [squaredLength, dotProduct, Fin.sum_univ_succ]
  have hse : olsSESquared (fullDesign witnessZ (witnessU+witnessV)) witnessY 2 = (1/3 : ℝ) := by
    unfold olsSESquared
    rw [hs, hinv]
    norm_num
  have ht : olsTSquared (fullDesign witnessZ (witnessU+witnessV)) witnessY 2 = (27/4 : ℝ) := by
    unfold olsTSquared
    rw [hb, hse]
    norm_num
  have hn : (fullDesign witnessZ (witnessU+witnessV))ᵀ *ᵥ (witnessY-(fullDesign witnessZ (witnessU+witnessV)) *ᵥ ![(0/1 : ℝ), (-1/2 : ℝ), (3/2 : ℝ)]) = 0 := by
    rw [← hb]
    change (fullDesign witnessZ (witnessU+witnessV))ᵀ *ᵥ olsResidual (fullDesign witnessZ (witnessU+witnessV)) witnessY = 0
    rw [hr]
    ext i; fin_cases i <;>
      norm_num [hA, witnessY, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hf := gram_certificate_full_rank _ _ hi
  have hu := normal_equation_unique _ _ _ hf hn
  simp only [div_one] at *
  exact ⟨hf, hb, hr, hs, hse, ht, hu⟩


/-- T3(ii),(iv): the same explicit six-observation design gives unequal t²
even when slope and residuals agree, and unequal slopes when x=u+v. These
are exact counterexamples to identifying a raw residual line with the
conditional coefficient test; the nominal reference dfs are four and three. -/
theorem regression_procedure_counterexample :
    FullColumnRank witnessZ ∧ FullColumnRank (residualLine witnessV) ∧
    FullColumnRank (fullDesign witnessZ witnessV) ∧
    FullColumnRank (residualLine (witnessU+witnessV)) ∧
    FullColumnRank (fullDesign witnessZ (witnessU+witnessV)) ∧
    olsTSquared (residualLine witnessV) (olsResidual witnessZ witnessY) 1 = 9 ∧
    olsTSquared (fullDesign witnessZ witnessV) witnessY 2 = (27/4 : ℝ) ∧
    olsTSquared (residualLine witnessV) (olsResidual witnessZ witnessY) 1 ≠
      olsTSquared (fullDesign witnessZ witnessV) witnessY 2 ∧
    ols (residualLine (witnessU+witnessV)) (olsResidual witnessZ witnessY) 1 = (3/4 : ℝ) ∧
    ols (fullDesign witnessZ (witnessU+witnessV)) witnessY 2 = (3/2 : ℝ) ∧
    ols (residualLine (witnessU+witnessV)) (olsResidual witnessZ witnessY) 1 ≠
      ols (fullDesign witnessZ (witnessU+witnessV)) witnessY 2 := by
  refine ⟨witness_baseline.2.2.1, residual_orthogonal_witness_fit.1,
    full_orthogonal_witness_fit.1, residual_correlated_witness_fit.1,
    full_correlated_witness_fit.1, ?_⟩
  rw [residual_orthogonal_witness_fit.2.2.2.2.2.1,
    full_orthogonal_witness_fit.2.2.2.2.2.1,
    residual_correlated_witness_fit.2.1, full_correlated_witness_fit.2.1]
  norm_num


/-- T3(iv): x=u+v has residualized squared length two and raw squared
length four; the raw slope 3/4 is exactly (3/2) times that ratio. -/
theorem correlated_regressor_residual_ratio :
    dotProduct (witnessU+witnessV) (residualMaker witnessZ *ᵥ (witnessU+witnessV)) = 2 ∧
    squaredLength (witnessU+witnessV) = 4 ∧ (3/4 : ℝ) = (3/2 : ℝ)*2/4 := by
  norm_num [squaredLength, residualMaker, controlProjection, witness_baseline.2.1,
    witnessZ, witnessU, witnessV, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]


/-- T3(ii),(iii): the actual conventional t statistics of the explicit,
full-rank six-observation fits are 3 and 3 sqrt(3)/2; their nominal tails
therefore disagree at the 5% level. This connects the analytic inequalities
to the fitted designs and responses, not just to isolated numerical tails. -/
theorem regression_five_percent_counterexample :
    FullColumnRank witnessZ ∧ FullColumnRank (residualLine witnessV) ∧
    FullColumnRank (fullDesign witnessZ witnessV) ∧
    olsT (residualLine witnessV) (olsResidual witnessZ witnessY) 1 = 3 ∧
    olsT (fullDesign witnessZ witnessV) witnessY 2 = 3*Real.sqrt 3/2 ∧
    studentFourTail (olsT (residualLine witnessV) (olsResidual witnessZ witnessY) 1) < (1/20 : ℝ) ∧
    (1/20 : ℝ) < studentThreeTail (olsT (fullDesign witnessZ witnessV) witnessY 2) := by
  have hr : olsT (residualLine witnessV) (olsResidual witnessZ witnessY) 1 = 3 := by
    unfold olsT
    rw [residual_orthogonal_witness_fit.2.1, residual_orthogonal_witness_fit.2.2.2.2.1]
    norm_num
  have hf : olsT (fullDesign witnessZ witnessV) witnessY 2 = 3*Real.sqrt 3/2 := by
    unfold olsT
    rw [full_orthogonal_witness_fit.2.1, full_orthogonal_witness_fit.2.2.2.2.1]
    norm_num
    ring
  refine ⟨witness_baseline.2.2.1, residual_orthogonal_witness_fit.1,
    full_orthogonal_witness_fit.1, hr, hf, ?_, ?_⟩
  · rw [hr]; exact residual_test_five_percent_disagreement.2.1
  · rw [hf]; exact residual_test_five_percent_disagreement.2.2.2


/-- T4(d), scalar finite lemma: once 0<S_M≤S_c is established, the raw slope
is attenuated, signs agree, equality has exactly the stated alternatives,
and the full-model SSE is no larger. This does not replace the matrix theorem. -/
theorem residual_attenuation_algebra (sm sc c R : ℝ) (hm : 0 < sm) (hmc : sm ≤ sc) :
    c/sc = (c/sm)*sm/sc ∧
    (0<c/sc ↔ 0<c/sm) ∧ (c/sc<0 ↔ c/sm<0) ∧
    |c/sc| ≤ |c/sm| ∧
    (c/sc=c/sm ↔ c=0 ∨ sm=sc) ∧
    R-c^2/sm ≤ R-c^2/sc := by
  have hc : 0 < sc := lt_of_lt_of_le hm hmc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · field_simp
  · simp [div_pos_iff, hm, hc, not_lt_of_ge hm.le, not_lt_of_ge hc.le]
  · simp [div_neg_iff, hm, hc, not_lt_of_ge hm.le, not_lt_of_ge hc.le]
  · rw [abs_div, abs_div, abs_of_pos hm, abs_of_pos hc]
    exact div_le_div_of_nonneg_left (abs_nonneg c) hm hmc
  · rw [div_eq_div_iff hc.ne' hm.ne']
    have he : c*sm=c*sc ↔ c*(sm-sc)=0 := by constructor <;> intro h <;> nlinarith
    rw [he, mul_eq_zero, sub_eq_zero]
  · exact sub_le_sub_left (div_le_div_of_nonneg_left (sq_nonneg c) hm hmc) R


/-- T4(e), scalar finite lemma: the two t² formulas retain their distinct
dfs; after dividing by their respective dfs, the residual-line value is
at most the full-model value. Equality of residualized and centered x gives
the exact df scaling of the squared statistics. -/
theorem residual_t_squared_algebra (sm sc c R dr df : ℝ)
    (hm : 0 < sm) (hmc : sm ≤ sc) (hf : 0 < R-c^2/sm)
    (hdr : 0 < dr) (hdf : 0 < df) :
    (c/sc)^2 / ((R-c^2/sc)/(dr*sc)) = dr*c^2/(sc*R-c^2) ∧
    (c/sm)^2 / ((R-c^2/sm)/(df*sm)) = df*c^2/(sm*R-c^2) ∧
    (dr*c^2/(sc*R-c^2))/dr ≤ (df*c^2/(sm*R-c^2))/df ∧
    (sm=sc → dr*c^2/(sc*R-c^2) = (dr/df)*(df*c^2/(sm*R-c^2))) := by
  have hc : 0 < sc := lt_of_lt_of_le hm hmc
  have hR : 0 < R := by
    have hh : 0 ≤ c^2/sm := div_nonneg (sq_nonneg c) hm.le
    linarith
  have hdm : 0 < sm*R-c^2 := by
    have hh := (div_lt_iff₀ hm).mp (show c^2/sm < R by linarith)
    nlinarith
  have hdc : 0 < sc*R-c^2 := by
    have hh := mul_le_mul_of_nonneg_right hmc hR.le
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp
    <;> ring
  · field_simp
    <;> ring
  · have he₁ : (dr*c^2/(sc*R-c^2))/dr = c^2/(sc*R-c^2) := by field_simp
    have he₂ : (df*c^2/(sm*R-c^2))/df = c^2/(sm*R-c^2) := by field_simp
    rw [he₁, he₂]
    apply div_le_div_of_nonneg_left (sq_nonneg c) hdm
    have hh := mul_le_mul_of_nonneg_right hmc hR.le
    linarith
  · intro he
    rw [he]
    field_simp


/-- T7(i), scalar finite lemma: positive residualized-regressor sums of
squares ordered R₂≤R₁ yield SE₁/s₁≤SE₂/s₂ and the stated SE upper bound
when SE_j=s_j/sqrt(R_j). The inverse-Gram identification is stated separately. -/
theorem nested_standard_error_scalar (R₁ R₂ s₁ s₂ : ℝ)
    (h₁ : 0<R₁) (h₂ : 0<R₂) (hR : R₂≤R₁) (hs₁ : 0<s₁) (hs₂ : 0<s₂) :
    (s₁/Real.sqrt R₁)/s₁ ≤ (s₂/Real.sqrt R₂)/s₂ ∧
    s₁/Real.sqrt R₁ ≤ (s₂/Real.sqrt R₂)*s₁/s₂ := by
  have hp₁ : 0 < Real.sqrt R₁ := Real.sqrt_pos.2 h₁
  have hp₂ : 0 < Real.sqrt R₂ := Real.sqrt_pos.2 h₂
  have hsq : Real.sqrt R₂ ≤ Real.sqrt R₁ := Real.sqrt_le_sqrt hR
  have hb : (1 : ℝ)/Real.sqrt R₁ ≤ 1/Real.sqrt R₂ :=
    div_le_div_of_nonneg_left (by norm_num) hp₂ hsq
  have he₁ : (s₁/Real.sqrt R₁)/s₁ = 1/Real.sqrt R₁ := by field_simp
  have he₂ : (s₂/Real.sqrt R₂)/s₂ = 1/Real.sqrt R₂ := by field_simp
  refine ⟨by rw [he₁, he₂]; exact hb, ?_⟩
  calc
    _ = s₁*(1/Real.sqrt R₁) := by ring
    _ ≤ s₁*(1/Real.sqrt R₂) := mul_le_mul_of_nonneg_left hb hs₁.le
    _ = (s₂/Real.sqrt R₂)*s₁/s₂ := by field_simp


namespace FiniteCompletion
open scoped BigOperators Matrix
noncomputable section

theorem fullDesign_snoc {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (q : Fin n → ℝ) (a : Fin k → ℝ) (t : ℝ) :
    fullDesign Z q *ᵥ Fin.snoc a t = Z *ᵥ a + t • q := by
  ext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, fullDesign]
  ring

theorem controls_full_rank {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (q : Fin n → ℝ) (hA : FullColumnRank (fullDesign Z q)) : FullColumnRank Z := by
  intro a b hab
  have h : Fin.snoc a (0:ℝ) = Fin.snoc b 0 := hA (by simp only [fullDesign_snoc, zero_smul, add_zero]; exact hab)
  funext j
  simpa using congrFun h j.castSucc

theorem residual_normal {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (q : Fin n → ℝ) (hZ : FullColumnRank Z) :
    Zᵀ *ᵥ olsResidual Z q = 0 := by
  have h := (ols_projection_identities Z hZ).2.2.2.2.2 q
  rw [← h.1]
  exact h.2

theorem residual_dot {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (q : Fin n → ℝ) (hZ : FullColumnRank Z) :
    dotProduct q (olsResidual Z q) = olsSSE Z q := by
  have ho : dotProduct (Z *ᵥ ols Z q) (olsResidual Z q) = 0 := by
    rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec, residual_normal Z q hZ]
    simp
  have he : q = olsResidual Z q + Z *ᵥ ols Z q := by unfold olsResidual; abel
  calc
    _ = dotProduct (olsResidual Z q + Z *ᵥ ols Z q) (olsResidual Z q) :=
      congrArg (fun v => dotProduct v (olsResidual Z q)) he
    _ = _ := by rw [add_dotProduct, ho, add_zero]; rfl

theorem residual_positive {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (q : Fin n → ℝ) (hA : FullColumnRank (fullDesign Z q)) : 0 < olsSSE Z q := by
  apply lt_of_le_of_ne (squaredLength_nonnegative _)
  intro hz
  have hr : olsResidual Z q = 0 := (squaredLength_zero_iff _).mp hz.symm
  have hb : fullDesign Z q *ᵥ Fin.snoc (-ols Z q) 1 = 0 := by
    rw [fullDesign_snoc]
    simpa [olsResidual, Matrix.mulVec_neg, sub_eq_add_neg, add_comm] using hr
  have hv : Fin.snoc (-ols Z q) (1:ℝ) = 0 := hA (by simpa using hb)
  have hl := congrFun hv (Fin.last k)
  simpa using hl

theorem inverse_gram_last {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (q : Fin n → ℝ) (hA : FullColumnRank (fullDesign Z q)) :
    ((fullDesign Z q)ᵀ * fullDesign Z q)⁻¹ (Fin.last k) (Fin.last k) = 1 / olsSSE Z q := by
  let A := fullDesign Z q
  let b : Fin (k+1) → ℝ := Fin.snoc (-ols Z q) (1:ℝ)
  let R := olsSSE Z q
  have hZ := controls_full_rank Z q hA
  have hR : 0 < R := residual_positive Z q hA
  have hab : A *ᵥ b = olsResidual Z q := by
    dsimp [A,b]
    rw [fullDesign_snoc]
    simp [olsResidual, Matrix.mulVec_neg, sub_eq_add_neg, add_comm]
  have hat : Aᵀ *ᵥ olsResidual Z q = Pi.single (Fin.last k) R := by
    ext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa [A, Matrix.mulVec, dotProduct, fullDesign, R] using residual_dot Z q hZ
    · have hh := congrFun (residual_normal Z q hZ) j
      simpa [A, Matrix.mulVec, dotProduct, fullDesign] using hh
  have hu := full_rank_gram_unit A hA
  have hi := Matrix.nonsing_inv_mul (Aᵀ*A) ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have hb : (Aᵀ*A)⁻¹ *ᵥ Pi.single (Fin.last k) R = b := by
    rw [← hat, ← hab, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hi, Matrix.one_mulVec]
  have hl := congrFun hb (Fin.last k)
  have he : (Aᵀ*A)⁻¹ (Fin.last k) (Fin.last k) * R = 1 := by
    change dotProduct (fun j => (Aᵀ*A)⁻¹ (Fin.last k) j) (Pi.single (Fin.last k) R) = b (Fin.last k) at hl
    rw [dotProduct_single] at hl
    simpa [b] using hl
  exact (eq_div_iff hR.ne').mpr he

end
end FiniteCompletion

namespace FiniteCompletion
open scoped BigOperators Matrix
noncomputable section

theorem se_decomposition {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (q y : Fin n → ℝ) (hA : FullColumnRank (fullDesign Z q)) :
    Real.sqrt (olsSESquared (fullDesign Z q) y (Fin.last k)) =
      Real.sqrt (olsSSE (fullDesign Z q) y / ((n : ℝ)-k-1)) / Real.sqrt (olsSSE Z q) := by
  unfold olsSESquared
  rw [inverse_gram_last Z q hA]
  have he : (n:ℝ)-(k+1:ℕ) = (n:ℝ)-k-1 := by push_cast; ring
  rw [he, mul_one_div]
  exact Real.sqrt_div' _ (residual_positive Z q hA).le

theorem nested_standard_error_bound_completed {n k₁ k₂ : ℕ}
    (Z₁ : Matrix (Fin n) (Fin k₁) ℝ) (Z₂ : Matrix (Fin n) (Fin k₂) ℝ)
    (q y : Fin n → ℝ)
    (hspan : ∀ a, ∃ b, Z₁ *ᵥ a = Z₂ *ᵥ b)
    (h₁ : FullColumnRank (fullDesign Z₁ q))
    (h₂ : FullColumnRank (fullDesign Z₂ q))
    (hn₁ : k₁+1 < n) (hn₂ : k₂+1 < n)
    (hs₁ : 0 < olsSSE (fullDesign Z₁ q) y)
    (hs₂ : 0 < olsSSE (fullDesign Z₂ q) y) :
    let R₁ := olsSSE Z₁ q
    let R₂ := olsSSE Z₂ q
    let s₁ := Real.sqrt (olsSSE (fullDesign Z₁ q) y / ((n : ℝ)-k₁-1))
    let s₂ := Real.sqrt (olsSSE (fullDesign Z₂ q) y / ((n : ℝ)-k₂-1))
    let se₁ := Real.sqrt (olsSESquared (fullDesign Z₁ q) y (Fin.last k₁))
    let se₂ := Real.sqrt (olsSESquared (fullDesign Z₂ q) y (Fin.last k₂))
    (∃ a, IsLeastSquares Z₁ q a ∧ squaredLength (q-Z₁ *ᵥ a) = R₁) ∧
    (∃ a, IsLeastSquares Z₂ q a ∧ squaredLength (q-Z₂ *ᵥ a) = R₂) ∧
    0 < R₁ ∧ 0 < R₂ ∧ R₂ ≤ R₁ ∧
    ((fullDesign Z₁ q)ᵀ * fullDesign Z₁ q)⁻¹ (Fin.last k₁) (Fin.last k₁) = 1/R₁ ∧
    ((fullDesign Z₂ q)ᵀ * fullDesign Z₂ q)⁻¹ (Fin.last k₂) (Fin.last k₂) = 1/R₂ ∧
    se₁ = s₁ / Real.sqrt R₁ ∧ se₂ = s₂ / Real.sqrt R₂ ∧
    se₁/s₁ ≤ se₂/s₂ ∧ se₁ ≤ se₂*s₁/s₂ := by
  dsimp only
  have hZ₁ := controls_full_rank Z₁ q h₁
  have hZ₂ := controls_full_rank Z₂ q h₂
  have hm₁ := (full_rank_ols_unique Z₁ q hZ₁).1
  have hm₂ := (full_rank_ols_unique Z₂ q hZ₂).1
  have hR₁ := residual_positive Z₁ q h₁
  have hR₂ := residual_positive Z₂ q h₂
  have hR := nested_minimum_squares Z₁ Z₂ q (ols Z₁ q) (ols Z₂ q) hspan hm₂
  change olsSSE Z₂ q ≤ olsSSE Z₁ q at hR
  have hd₁ : 0 < (n:ℝ)-k₁-1 := by
    have h : (k₁:ℝ)+1 < n := by exact_mod_cast hn₁
    linarith
  have hd₂ : 0 < (n:ℝ)-k₂-1 := by
    have h : (k₂:ℝ)+1 < n := by exact_mod_cast hn₂
    linarith
  have hss₁ := Real.sqrt_pos.mpr (div_pos hs₁ hd₁)
  have hss₂ := Real.sqrt_pos.mpr (div_pos hs₂ hd₂)
  have hsform₁ := se_decomposition Z₁ q y h₁
  have hsform₂ := se_decomposition Z₂ q y h₂
  refine ⟨⟨ols Z₁ q, hm₁, rfl⟩, ⟨ols Z₂ q, hm₂, rfl⟩, hR₁, hR₂, hR,
    inverse_gram_last Z₁ q h₁, inverse_gram_last Z₂ q h₂, hsform₁, hsform₂, ?_⟩
  rw [hsform₁, hsform₂]
  exact nested_standard_error_scalar _ _ _ _ hR₁ hR₂ hR hss₁ hss₂

end
end FiniteCompletion

section FullNestedBound
open scoped BigOperators Matrix
noncomputable section

/-- Full T7(i): the regressor geometry is independent of the outcome;
positive outcome residual errors are needed only for normalized-SE comparisons. -/
theorem nested_standard_error_bound_full {n k₁ k₂ : ℕ}
    (Z₁ : Matrix (Fin n) (Fin k₁) ℝ) (Z₂ : Matrix (Fin n) (Fin k₂) ℝ)
    (q : Fin n → ℝ)
    (hspan : ∀ a, ∃ b, Z₁ *ᵥ a = Z₂ *ᵥ b)
    (h₁ : FullColumnRank (fullDesign Z₁ q))
    (h₂ : FullColumnRank (fullDesign Z₂ q))
    (hn₁ : k₁+1 < n) (hn₂ : k₂+1 < n) :
    let R₁ := olsSSE Z₁ q
    let R₂ := olsSSE Z₂ q
    (∃ a, IsLeastSquares Z₁ q a ∧ squaredLength (q-Z₁ *ᵥ a) = R₁) ∧
    (∃ a, IsLeastSquares Z₂ q a ∧ squaredLength (q-Z₂ *ᵥ a) = R₂) ∧
    0 < R₁ ∧ 0 < R₂ ∧ R₂ ≤ R₁ ∧
    ((fullDesign Z₁ q)ᵀ * fullDesign Z₁ q)⁻¹ (Fin.last k₁) (Fin.last k₁) = 1/R₁ ∧
    ((fullDesign Z₂ q)ᵀ * fullDesign Z₂ q)⁻¹ (Fin.last k₂) (Fin.last k₂) = 1/R₂ ∧
    (∀ y, 0 < olsSSE (fullDesign Z₁ q) y → 0 < olsSSE (fullDesign Z₂ q) y →
      let s₁ := Real.sqrt (olsSSE (fullDesign Z₁ q) y / ((n : ℝ)-k₁-1))
      let s₂ := Real.sqrt (olsSSE (fullDesign Z₂ q) y / ((n : ℝ)-k₂-1))
      let se₁ := Real.sqrt (olsSESquared (fullDesign Z₁ q) y (Fin.last k₁))
      let se₂ := Real.sqrt (olsSESquared (fullDesign Z₂ q) y (Fin.last k₂))
      se₁ = s₁ / Real.sqrt R₁ ∧ se₂ = s₂ / Real.sqrt R₂ ∧
      se₁/s₁ ≤ se₂/s₂ ∧ se₁ ≤ se₂*s₁/s₂) := by
  dsimp only
  have hm₁ := (full_rank_ols_unique Z₁ q (FiniteCompletion.controls_full_rank Z₁ q h₁)).1
  have hm₂ := (full_rank_ols_unique Z₂ q (FiniteCompletion.controls_full_rank Z₂ q h₂)).1
  refine ⟨⟨ols Z₁ q, hm₁, rfl⟩, ⟨ols Z₂ q, hm₂, rfl⟩,
    FiniteCompletion.residual_positive Z₁ q h₁, FiniteCompletion.residual_positive Z₂ q h₂,
    nested_minimum_squares Z₁ Z₂ q (ols Z₁ q) (ols Z₂ q) hspan hm₂,
    FiniteCompletion.inverse_gram_last Z₁ q h₁, FiniteCompletion.inverse_gram_last Z₂ q h₂, ?_⟩
  intro y hs₁ hs₂
  have h := FiniteCompletion.nested_standard_error_bound_completed Z₁ Z₂ q y hspan h₁ h₂ hn₁ hn₂ hs₁ hs₂
  dsimp only at h
  rcases h with ⟨_,_,_,_,_,_,_,he₁,he₂,hb₁,hb₂⟩
  exact ⟨he₁,he₂,hb₁,hb₂⟩

end
end FullNestedBound


namespace RegressionCompletion
open scoped BigOperators Matrix
noncomputable section

theorem fullDesign_init {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (x : Fin n → ℝ) (b : Fin (k+1) → ℝ) :
    fullDesign Z x *ᵥ b = Z *ᵥ Fin.init b + b (Fin.last k) • x := by
  rw [← Fin.snoc_init_self b]
  simpa using FiniteCompletion.fullDesign_snoc Z x (Fin.init b) (b (Fin.last k))

theorem fullDesign_full_rank {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (x : Fin n → ℝ) (hZ : FullColumnRank Z) (hx : ¬ ∃ a, Z *ᵥ a = x) :
    FullColumnRank (fullDesign Z x) := by
  intro a b hab
  have he := sub_eq_zero.mpr hab
  rw [← Matrix.mulVec_sub, fullDesign_init] at he
  have ht : (a-b) (Fin.last k) = 0 := by
    by_contra ht
    apply hx
    refine ⟨(-(a-b) (Fin.last k))⁻¹ • Fin.init (a-b), ?_⟩
    rw [Matrix.mulVec_smul]
    have hz : Z *ᵥ Fin.init (a-b) = -((a-b) (Fin.last k) • x) := eq_neg_of_add_eq_zero_left he
    rw [hz]
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
    field_simp
    <;> ring
  have hi : Fin.init (a-b) = 0 := hZ (by simpa [ht] using he)
  have hd : a-b=0 := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · exact ht
    · simpa [Fin.init] using congrFun hi j
  exact sub_eq_zero.mp hd

theorem symmetric_dot {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : Mᵀ=M) (u v : Fin n → ℝ) :
    dotProduct u (M *ᵥ v) = dotProduct (M *ᵥ u) v := by
  rw [← Matrix.dotProduct_transpose_mulVec,hM]
  exact dotProduct_comm _ _

theorem residual_quadratic {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (hZ : FullColumnRank Z) (x : Fin n → ℝ) :
    squaredLength (residualMaker Z *ᵥ x) = dotProduct x (residualMaker Z *ᵥ x) := by
  have hs := (ols_projection_identities Z hZ).2.2.1
  have hi := (ols_projection_identities Z hZ).2.2.2.1
  unfold squaredLength
  rw [← symmetric_dot _ hs, Matrix.mulVec_mulVec, hi]

theorem residual_intercept {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (hZ : FullColumnRank Z) (h1 : ∃ c, Z *ᵥ c = fun _ => 1) :
    residualMaker Z *ᵥ (fun _ => (1:ℝ)) = 0 := by
  obtain ⟨c,hc⟩ := h1
  rw [← hc,Matrix.mulVec_mulVec,(ols_projection_identities Z hZ).2.2.2.2.1,Matrix.zero_mulVec]

theorem residual_mean_zero {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (hZ : FullColumnRank Z) (h1 : ∃ c, Z *ᵥ c = fun _ => 1) (y : Fin n → ℝ) :
    (∑ i, (residualMaker Z *ᵥ y) i)=0 := by
  have h := symmetric_dot (residualMaker Z) (ols_projection_identities Z hZ).2.2.1 (fun _ => 1) y
  rw [residual_intercept Z hZ h1] at h
  simpa [dotProduct] using h

theorem residual_centered {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (hZ : FullColumnRank Z) (h1 : ∃ c, Z *ᵥ c = fun _ => 1) (x : Fin n → ℝ) :
    residualMaker Z *ᵥ (x - ((∑ i,x i)/(n:ℝ)) • (fun _ => 1)) = residualMaker Z *ᵥ x := by
  rw [Matrix.mulVec_sub,Matrix.mulVec_smul,residual_intercept Z hZ h1,smul_zero,sub_zero]

end
end RegressionCompletion

namespace RegressionCompletion
open scoped BigOperators Matrix
noncomputable section

theorem squaredLength_sub_smul {n : ℕ} (u v : Fin n → ℝ) (a : ℝ) :
    squaredLength (u-a • v) = squaredLength u - 2*a*dotProduct u v + a^2*squaredLength v := by
  unfold squaredLength
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm v u]
  ring

theorem projection_orthogonal {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (hZ : FullColumnRank Z) (v : Fin n → ℝ) :
    dotProduct (controlProjection Z *ᵥ v) (residualMaker Z *ᵥ v) = 0 := by
  have hp := ols_projection_identities Z hZ
  have hz : controlProjection Z * residualMaker Z = 0 := by
    rw [residualMaker,Matrix.mul_sub,Matrix.mul_one,hp.2.1,sub_self]
  rw [← symmetric_dot _ hp.1,Matrix.mulVec_mulVec,hz,Matrix.zero_mulVec]
  simp

theorem projection_decomposition {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (v : Fin n → ℝ) : v = controlProjection Z *ᵥ v + residualMaker Z *ᵥ v := by
  rw [residualMaker,Matrix.sub_mulVec,Matrix.one_mulVec]
  abel

theorem projection_pythagoras {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (hZ : FullColumnRank Z) (v : Fin n → ℝ) :
    squaredLength v = squaredLength (controlProjection Z *ᵥ v) + squaredLength (residualMaker Z *ᵥ v) := by
  have he := projection_decomposition Z v
  calc
    _ = squaredLength (controlProjection Z *ᵥ v + residualMaker Z *ᵥ v) := congrArg squaredLength he
    _ = _ := by
      unfold squaredLength
      rw [add_dotProduct,dotProduct_add,dotProduct_add,projection_orthogonal Z hZ,
        dotProduct_comm (residualMaker Z *ᵥ v) (controlProjection Z *ᵥ v),projection_orthogonal Z hZ]
      ring

theorem centered_geometry {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (x : Fin n → ℝ) (hZ : FullColumnRank Z) (h1 : ∃ c, Z *ᵥ c = fun _ => 1)
    (hx : ¬ ∃ a, Z *ᵥ a=x) :
    let P := controlProjection Z
    let M := residualMaker Z
    let xc := x-((∑ i,x i)/(n:ℝ)) • (fun _ => 1)
    let sm := dotProduct x (M *ᵥ x)
    let sc := squaredLength xc
    sc = sm + squaredLength (P *ᵥ xc) ∧ 0 < sm ∧ sm ≤ sc ∧
    (sm=sc ↔ P *ᵥ xc=0) := by
  dsimp only
  have he := projection_pythagoras Z hZ (x-((∑ i,x i)/(n:ℝ)) • (fun _ => 1))
  rw [residual_centered Z hZ h1,residual_quadratic Z hZ] at he
  have hp : 0 < dotProduct x (residualMaker Z *ᵥ x) := by
    rw [(ols_projection_identities Z hZ).2.2.2.2.2 x |>.1,FiniteCompletion.residual_dot Z x hZ]
    exact FiniteCompletion.residual_positive Z x (fullDesign_full_rank Z x hZ hx)
  refine ⟨by linarith, hp, ?_, ?_⟩
  · linarith [squaredLength_nonnegative (controlProjection Z *ᵥ (x-((∑ i,x i)/(n:ℝ)) • (fun _ => 1)))]
  · rw [← squaredLength_zero_iff]
    constructor <;> intro h <;> linarith

theorem centered_residual_dot {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (hZ : FullColumnRank Z) (h1 : ∃ c, Z *ᵥ c = fun _ => 1) (x y : Fin n → ℝ) :
    dotProduct (x-((∑ i,x i)/(n:ℝ)) • (fun _ => 1)) (residualMaker Z *ᵥ y) =
      dotProduct x (residualMaker Z *ᵥ y) := by
  rw [sub_dotProduct,smul_dotProduct]
  have hz : dotProduct (fun _ => (1:ℝ)) (residualMaker Z *ᵥ y) = 0 := by
    simpa [dotProduct] using residual_mean_zero Z hZ h1 y
  rw [hz,smul_zero,sub_zero]

theorem projection_zero_iff_columns {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (hZ : FullColumnRank Z) (v : Fin n → ℝ) :
    controlProjection Z *ᵥ v = 0 ↔ ∀ j, dotProduct v (fun i => Z i j)=0 := by
  have hp := ols_projection_identities Z hZ
  have hn : Zᵀ *ᵥ (residualMaker Z *ᵥ v)=0 := (hp.2.2.2.2.2 v).2
  constructor
  · intro hz j
    have he : residualMaker Z *ᵥ v=v := by
      rw [residualMaker,Matrix.sub_mulVec,Matrix.one_mulVec,hz,sub_zero]
    rw [he] at hn
    have hh := congrFun hn j
    simpa [Matrix.mulVec,dotProduct,mul_comm] using hh
  · intro hz
    have hh : Zᵀ *ᵥ v=0 := by
      ext j
      simpa [Matrix.mulVec,dotProduct,mul_comm] using hz j
    unfold controlProjection
    rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,hh]
    simp

end
end RegressionCompletion

namespace RegressionCompletion
open scoped BigOperators Matrix
noncomputable section

theorem full_fit {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (x y : Fin n → ℝ) (hZ : FullColumnRank Z) (hx : ¬ ∃ a, Z *ᵥ a=x) :
    let A := fullDesign Z x
    let r := residualMaker Z *ᵥ y
    let v := residualMaker Z *ᵥ x
    let sm := dotProduct x v
    let c := dotProduct x r
    FullColumnRank A ∧ (∃! β, IsLeastSquares A y β) ∧
    ols A y = Fin.snoc (ols Z (y-(c/sm) • x)) (c/sm) ∧
    ols A y (Fin.last k) = c/sm ∧
    olsResidual A y = r-(c/sm) • v ∧
    olsSSE A y = squaredLength r-c^2/sm ∧
    (Aᵀ*A)⁻¹ (Fin.last k) (Fin.last k) = 1/sm := by
  dsimp only
  let M := residualMaker Z
  let A := fullDesign Z x
  let r := M *ᵥ y
  let v := M *ᵥ x
  let sm := dotProduct x v
  let c := dotProduct x r
  let b := c/sm
  let β : Fin (k+1) → ℝ := Fin.snoc (ols Z (y-b • x)) b
  have hA := fullDesign_full_rank Z x hZ hx
  have hsm : sm=olsSSE Z x := by
    dsimp [sm,v,M]
    rw [(ols_projection_identities Z hZ).2.2.2.2.2 x |>.1]
    exact FiniteCompletion.residual_dot Z x hZ
  have hsp : 0 < sm := by rw [hsm]; exact FiniteCompletion.residual_positive Z x hA
  have hβres : y-A *ᵥ β=r-b • v := by
    dsimp [A,β]
    rw [FiniteCompletion.fullDesign_snoc]
    have he : y-(Z *ᵥ ols Z (y-b • x)+b • x) = olsResidual Z (y-b • x) := by
      unfold olsResidual
      abel
    rw [he,← (ols_projection_identities Z hZ).2.2.2.2.2 (y-b • x) |>.1]
    rw [Matrix.mulVec_sub,Matrix.mulVec_smul]
  have hzr : Zᵀ *ᵥ r=0 := (ols_projection_identities Z hZ).2.2.2.2.2 y |>.2
  have hzv : Zᵀ *ᵥ v=0 := (ols_projection_identities Z hZ).2.2.2.2.2 x |>.2
  have hz : Zᵀ *ᵥ (r-b • v)=0 := by
    rw [Matrix.mulVec_sub,Matrix.mulVec_smul,hzr,hzv]
    simp
  have hn : Aᵀ *ᵥ (y-A *ᵥ β)=0 := by
    rw [hβres]
    ext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · have hh : dotProduct x (r-b • v)=0 := by
        rw [dotProduct_sub,dotProduct_smul]
        change c-b*sm=0
        dsimp [b]
        field_simp <;> ring
      simpa [A,Matrix.mulVec,dotProduct,fullDesign] using hh
    · have hh := congrFun hz j
      simpa [A,Matrix.mulVec,dotProduct,fullDesign] using hh
  have hu := normal_equation_unique A y β hA hn
  have hcoef : ols A y=β := hu.2 _ (full_rank_ols_unique A y hA).1
  have hres : olsResidual A y=r-b • v := by
    unfold olsResidual
    rw [hcoef,hβres]
  have hcross : dotProduct r v=c := by
    have hp := ols_projection_identities Z hZ
    calc
      dotProduct r v = dotProduct y (M *ᵥ (M *ᵥ x)) :=
        (symmetric_dot M hp.2.2.1 y (M *ᵥ x)).symm
      _ = dotProduct y (M *ᵥ x) := by rw [Matrix.mulVec_mulVec,hp.2.2.2.1]
      _ = dotProduct (M *ᵥ y) x := symmetric_dot M hp.2.2.1 y x
      _ = c := dotProduct_comm _ _
  have hvnorm : squaredLength v=sm := residual_quadratic Z hZ x
  refine ⟨hA, ⟨β,hu.1,fun a ha => hu.2 a ha⟩, hcoef, ?_, hres, ?_, ?_⟩
  · simpa [β] using congrFun hcoef (Fin.last k)
  · change squaredLength (olsResidual A y)=squaredLength r-c^2/sm
    rw [hres,squaredLength_sub_smul,hcross,hvnorm]
    dsimp [b]
    field_simp
    <;> ring
  · rw [FiniteCompletion.inverse_gram_last Z x hA,← hsm]

end
end RegressionCompletion

namespace RegressionCompletion
open scoped BigOperators Matrix
noncomputable section

def onesDesign (n : ℕ) : Matrix (Fin n) (Fin 1) ℝ := fun _ _ => 1

theorem ones_mul {n : ℕ} (a : Fin 1 → ℝ) :
    onesDesign n *ᵥ a = a 0 • (fun _ => (1:ℝ)) := by
  ext i
  simp [onesDesign,Matrix.mulVec,dotProduct]

theorem ones_rank {n : ℕ} (hn : 0<n) : FullColumnRank (onesDesign n) := by
  intro a b hab
  have he := congrFun hab ⟨0,hn⟩
  simp only [ones_mul,Pi.smul_apply,smul_eq_mul,mul_one] at he
  ext j
  fin_cases j
  exact he

theorem ones_ols {n : ℕ} (hn : 0<n) (u : Fin n → ℝ) :
    ols (onesDesign n) u = fun _ => (∑ i,u i)/(n:ℝ) := by
  let m := (∑ i,u i)/(n:ℝ)
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hnormal : (onesDesign n)ᵀ *ᵥ (u-onesDesign n *ᵥ (fun _ => m))=0 := by
    rw [ones_mul]
    ext j
    simp only [onesDesign,Matrix.transpose_apply,Matrix.mulVec,dotProduct,Pi.sub_apply,
      Pi.smul_apply,smul_eq_mul,mul_one,one_mul,Pi.zero_apply,Finset.sum_sub_distrib,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    dsimp [m]
    field_simp
    <;> ring
  exact (normal_equation_unique _ u _ (ones_rank hn) hnormal).2 _
    (full_rank_ols_unique _ u (ones_rank hn)).1

theorem ones_residual {n : ℕ} (hn : 0<n) (u : Fin n → ℝ) :
    residualMaker (onesDesign n) *ᵥ u = u-((∑ i,u i)/(n:ℝ)) • (fun _ => 1) := by
  rw [(ols_projection_identities _ (ones_rank hn)).2.2.2.2.2 u |>.1]
  unfold olsResidual
  rw [ones_ols hn,ones_mul]

theorem ones_full {n : ℕ} (x : Fin n → ℝ) :
    fullDesign (onesDesign n) x = residualLine x := by
  ext i j
  fin_cases j <;> simp [fullDesign,onesDesign,residualLine]

end
end RegressionCompletion

namespace RegressionCompletion
open scoped BigOperators Matrix
noncomputable section

theorem raw_fit {n : ℕ} (x r : Fin n → ℝ) (hn : 0<n)
    (hr : (∑ i,r i)=0)
    (hsc : 0 < squaredLength (x-((∑ i,x i)/(n:ℝ)) • (fun _ => 1))) :
    let xb := (∑ i,x i)/(n:ℝ)
    let xc := x-xb • (fun _ => 1)
    let sc := squaredLength xc
    let c := dotProduct x r
    let a := c/sc
    ols (residualLine x) r = ![-a*xb,a] ∧
    IsLeastSquares (residualLine x) r ![-a*xb,a] ∧
    olsResidual (residualLine x) r = r-a • xc ∧
    olsSSE (residualLine x) r = squaredLength r-c^2/sc ∧
    ((residualLine x)ᵀ*residualLine x)⁻¹ 1 1 = 1/sc := by
  dsimp only
  let C := onesDesign n
  let xb := (∑ i,x i)/(n:ℝ)
  let xc := x-xb • (fun _ => (1:ℝ))
  let sc := squaredLength xc
  let c := dotProduct x r
  let a := c/sc
  have hC : FullColumnRank C := ones_rank hn
  have hMx : residualMaker C *ᵥ x=xc := ones_residual hn x
  have hMr : residualMaker C *ᵥ r=r := by
    rw [ones_residual hn r,hr]
    simp
  have hsm : dotProduct x (residualMaker C *ᵥ x)=sc := by
    rw [← residual_quadratic C hC,hMx]
  have hx : ¬ ∃ b,C *ᵥ b=x := by
    rintro ⟨b,hb⟩
    have hz : residualMaker C *ᵥ x=0 := by
      rw [← hb,Matrix.mulVec_mulVec,(ols_projection_identities C hC).2.2.2.2.1]
      simp
    rw [hMx] at hz
    have hz' : sc=0 := by simp [sc,hz,squaredLength,dotProduct]
    linarith
  have hf := full_fit C x r hC hx
  dsimp only at hf
  rw [hMr,hMx,show dotProduct x xc=sc from by simpa [hMx] using hsm] at hf
  rw [ones_full] at hf
  obtain ⟨hA,hu,hcoef,hlast,hres,hsse,hinv⟩ := hf
  have hcoef' : ols (residualLine x) r = ![-a*xb,a] := by
    rw [hcoef,ones_ols hn]
    ext j
    fin_cases j
    · simp only [Fin.snoc,Fin.lastCases,Fin.isValue,Fin.val_zero,Fin.mk_one,
        Matrix.cons_val_zero,Matrix.head_cons]
      change (∑ i,(r-a • x) i)/(n:ℝ) = -a*xb
      simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_sub_distrib,
        ← Finset.mul_sum,hr]
      dsimp [xb]
      ring
    · change Fin.snoc (α := fun _ => ℝ) (fun _ : Fin 1 => (∑ i,(r-a • x) i)/(n:ℝ)) a (Fin.last 1) = a
      exact Fin.snoc_last (α := fun _ : Fin 2 => ℝ) a (fun _ : Fin 1 => (∑ i,(r-a • x) i)/(n:ℝ))
  refine ⟨hcoef',?_,hres,hsse,?_⟩
  · rw [← hcoef']
    exact (full_rank_ols_unique _ r hA).1
  · exact hinv

end
end RegressionCompletion

namespace RegressionCompletion
noncomputable section
 theorem signed_t_scale (b E dr df : ℝ) (hE : 0<E) (hdr : 0<dr) (hdf : 0<df) :
    b/Real.sqrt (E/dr) = Real.sqrt (dr/df)*(b/Real.sqrt (E/df)) := by
  rw [Real.sqrt_div hE.le,Real.sqrt_div hE.le,Real.sqrt_div hdr.le]
  have he := (Real.sqrt_pos.mpr hE).ne'
  have hr := (Real.sqrt_pos.mpr hdr).ne'
  have hf := (Real.sqrt_pos.mpr hdf).ne'
  field_simp
  <;> ring
end
end RegressionCompletion

namespace RegressionCompletion
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2000000
theorem corrected_residual_regression_completed {n k : ℕ}
    (Z : Matrix (Fin n) (Fin k) ℝ) (x y : Fin n → ℝ)
    (hZ : FullColumnRank Z) (h1 : ∃ c, Z *ᵥ c = fun _ => 1)
    (hx : ¬ ∃ c, Z *ᵥ c = x) (hn : k+1 < n) :
    let P := controlProjection Z
    let M := residualMaker Z
    let r := M *ᵥ y
    let xbar := (∑ i, x i) / n
    let xc := x - xbar • (fun _ => (1 : ℝ))
    let sm := dotProduct x (M *ᵥ x)
    let sc := squaredLength xc
    let c := dotProduct x r
    let a := c/sc
    let b := c/sm
    let sr := squaredLength r - c^2/sc
    let sf := squaredLength r - c^2/sm
    Pᵀ = P ∧ P*P = P ∧ Mᵀ = M ∧ M*M = M ∧ M*Z = 0 ∧
    (∑ i, r i) = 0 ∧ M *ᵥ xc = M *ᵥ x ∧
    dotProduct xc r = c ∧ c = dotProduct x (M *ᵥ y) ∧
    sc = sm + squaredLength (P *ᵥ xc) ∧ 0 < sm ∧ sm ≤ sc ∧
    (sm = sc ↔ P *ᵥ xc = 0) ∧
    (P *ᵥ xc = 0 ↔ ∀ j, dotProduct xc (fun i => Z i j) = 0) ∧
    ols (residualLine x) r = ![-a*xbar, a] ∧
    IsLeastSquares (residualLine x) r ![-a*xbar, a] ∧
    olsSSE (residualLine x) r = sr ∧
    (∃! β, IsLeastSquares (fullDesign Z x) y β) ∧
    ols (fullDesign Z x) y (Fin.last k) = b ∧
    olsSSE (fullDesign Z x) y = sf ∧
    a = b*sm/sc ∧ (0<a ↔ 0<b) ∧ (a<0 ↔ b<0) ∧ |a| ≤ |b| ∧
    (a=b ↔ b=0 ∨ P *ᵥ xc = 0) ∧ sf ≤ sr ∧
    olsSESquared (residualLine x) r 1 = sr / (((n : ℝ)-2)*sc) ∧
    olsSESquared (fullDesign Z x) y (Fin.last k) = sf / (((n : ℝ)-k-1)*sm) ∧
    (0 < sf →
      olsTSquared (residualLine x) r 1 = ((n : ℝ)-2)*c^2/(sc*squaredLength r-c^2) ∧
      olsTSquared (fullDesign Z x) y (Fin.last k) =
        ((n : ℝ)-k-1)*c^2/(sm*squaredLength r-c^2) ∧
      olsTSquared (residualLine x) r 1 / ((n : ℝ)-2) ≤
        olsTSquared (fullDesign Z x) y (Fin.last k) / ((n : ℝ)-k-1) ∧
      (P *ᵥ xc = 0 → a=b ∧
        olsResidual (residualLine x) r = olsResidual (fullDesign Z x) y ∧
        olsT (residualLine x) r 1 =
          Real.sqrt (((n : ℝ)-2)/((n : ℝ)-k-1)) * olsT (fullDesign Z x) y (Fin.last k) ∧
        (2 ≤ k → olsT (fullDesign Z x) y (Fin.last k) ≠ 0 →
          |olsT (fullDesign Z x) y (Fin.last k)| < |olsT (residualLine x) r 1|))) := by
  classical
  dsimp only
  let P := controlProjection Z
  let M := residualMaker Z
  let r := M *ᵥ y
  let xbar := (∑ i,x i)/(n:ℝ)
  let xc := x-xbar • (fun _ => (1:ℝ))
  let sm := dotProduct x (M *ᵥ x)
  let sc := squaredLength xc
  let c := dotProduct x r
  let a := c/sc
  let b := c/sm
  let sr := squaredLength r-c^2/sc
  let sf := squaredLength r-c^2/sm
  let dr := (n:ℝ)-2
  let df := (n:ℝ)-k-1
  have hp := ols_projection_identities Z hZ
  obtain ⟨hdecomp,hm,hmc,heq⟩ := centered_geometry Z x hZ h1 hx
  change 0<sm at hm
  change sm ≤ sc at hmc
  change sm=sc ↔ P *ᵥ xc=0 at heq
  have hc : 0<sc := lt_of_lt_of_le hm hmc
  have hmean : (∑ i,r i)=0 := residual_mean_zero Z hZ h1 y
  have hn0 : 0<n := by omega
  have hk : 1≤k := by
    by_contra h
    have hk0 : k=0 := by omega
    subst k
    obtain ⟨u,hu⟩ := h1
    have hi := congrFun hu ⟨0,hn0⟩
    norm_num [Matrix.mulVec,dotProduct] at hi
  have hnreal : (k:ℝ)+1<(n:ℝ) := by exact_mod_cast hn
  have hkreal : (1:ℝ)≤(k:ℝ) := by exact_mod_cast hk
  have hdr : 0<dr := by dsimp [dr]; linarith
  have hdf : 0<df := by dsimp [df]; linarith
  obtain ⟨hcoefr,hminr,hresr,hsser,hinvr⟩ := raw_fit x r hn0 hmean hc
  obtain ⟨hA,hu,hcoeff,hlast,hresf,hssef,hinvf⟩ := full_fit Z x y hZ hx
  change ols (residualLine x) r = ![-a*xbar,a] at hcoefr
  change olsResidual (residualLine x) r = r-a • xc at hresr
  change olsSSE (residualLine x) r = sr at hsser
  change ((residualLine x)ᵀ*residualLine x)⁻¹ 1 1=1/sc at hinvr
  change ols (fullDesign Z x) y (Fin.last k)=b at hlast
  change olsResidual (fullDesign Z x) y=r-b • (M *ᵥ x) at hresf
  change olsSSE (fullDesign Z x) y=sf at hssef
  change ((fullDesign Z x)ᵀ*fullDesign Z x)⁻¹ (Fin.last k) (Fin.last k)=1/sm at hinvf
  have har : ols (residualLine x) r 1=a := by rw [hcoefr]; simp
  have hser : olsSESquared (residualLine x) r 1=sr/(dr*sc) := by
    unfold olsSESquared
    rw [hsser,hinvr]
    change sr/dr*(1/sc)=sr/(dr*sc)
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hsef : olsSESquared (fullDesign Z x) y (Fin.last k)=sf/(df*sm) := by
    unfold olsSESquared
    rw [hssef,hinvf]
    simp only [Nat.cast_add,Nat.cast_one]
    change sf/((n:ℝ)-((k:ℝ)+1))*(1/sm)=sf/(df*sm)
    have he : (n:ℝ)-((k:ℝ)+1)=df := by dsimp [df]; ring
    rw [he]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hslope := residual_attenuation_algebra sm sc c (squaredLength r) hm hmc
  have hbzero : b=0 ↔ c=0 := by simp only [b,div_eq_zero_iff,ne_of_gt hm,or_false]
  have hab : a=b ↔ b=0 ∨ P *ᵥ xc=0 :=
    hslope.2.2.2.2.1.trans (or_congr hbzero.symm heq)
  refine ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.1,hmean,
    residual_centered Z hZ h1 x,centered_residual_dot Z hZ h1 x y,rfl,
    hdecomp,hm,hmc,heq,projection_zero_iff_columns Z hZ xc,hcoefr,hminr,hsser,
    hu,hlast,hssef,hslope.1,hslope.2.1,hslope.2.2.1,hslope.2.2.2.1,hab,
    hslope.2.2.2.2.2,hser,hsef,?_⟩
  intro hsf
  have ht := residual_t_squared_algebra sm sc c (squaredLength r) dr df hm hmc hsf hdr hdf
  have htr : olsTSquared (residualLine x) r 1=dr*c^2/(sc*squaredLength r-c^2) := by
    unfold olsTSquared
    rw [har,hser]
    exact ht.1
  have htf : olsTSquared (fullDesign Z x) y (Fin.last k)=df*c^2/(sm*squaredLength r-c^2) := by
    unfold olsTSquared
    rw [hlast,hsef]
    exact ht.2.1
  refine ⟨htr,htf,?_,?_⟩
  · rw [htr,htf]
    exact ht.2.2.1
  · intro hP
    have he : sm=sc := heq.mpr hP
    have hab' : a=b := hab.mpr (Or.inr hP)
    have hxc : xc=M *ᵥ x := by
      have hh : xc=M *ᵥ xc := by
        dsimp [M]
        rw [residualMaker,Matrix.sub_mulVec,Matrix.one_mulVec,hP,sub_zero]
      exact hh.trans (residual_centered Z hZ h1 x)
    have hres : olsResidual (residualLine x) r=olsResidual (fullDesign Z x) y := by
      rw [hresr,hresf,hab',hxc]
    have hsr : sr=sf := by dsimp [sr,sf]; rw [he]
    have hE : 0<sf/sm := div_pos hsf hm
    have hscale : olsT (residualLine x) r 1 =
        Real.sqrt (dr/df)*olsT (fullDesign Z x) y (Fin.last k) := by
      unfold olsT
      rw [har,hlast,hser,hsef]
      change a/Real.sqrt (sr/(dr*sc))=Real.sqrt (dr/df)*(b/Real.sqrt (sf/(df*sm)))
      rw [hab',hsr,← he]
      have h1 : sf/(dr*sm)=(sf/sm)/dr := by ring
      have h2 : sf/(df*sm)=(sf/sm)/df := by ring
      rw [h1,h2]
      exact signed_t_scale b (sf/sm) dr df hE hdr hdf
    refine ⟨hab',hres,hscale,?_⟩
    intro hk2 htne
    have hk2r : (2:ℝ)≤(k:ℝ) := by exact_mod_cast hk2
    have hdfdr : df<dr := by dsimp [df,dr]; linarith
    have hrat : 1<dr/df := (lt_div_iff₀ hdf).mpr (by simpa using hdfdr)
    have hfac : 1<Real.sqrt (dr/df) := by
      simpa using Real.sqrt_lt_sqrt (show (0:ℝ)≤1 by norm_num) hrat
    rw [hscale,abs_mul,abs_of_pos (lt_trans zero_lt_one hfac)]
    nlinarith [abs_pos.mpr htne]

end
end RegressionCompletion

/-- T4(a)--(e), general corrected linear-regression statement. All designs
have full column rank, contain an intercept, x is outside the controls' span,
and n>k+1. The conclusions retain the unique OLS fits, both SSEs, attenuation,
both conventional t formulas and the distinct residual degrees of freedom.
This exact statement is about linear OLS; the paper's nonlinear B2/B3 fits
are only an approximate application, T4(g), not asserted by this theorem. -/
theorem corrected_residual_regression {n k : ℕ}
    (Z : Matrix (Fin n) (Fin k) ℝ) (x y : Fin n → ℝ)
    (hZ : FullColumnRank Z) (h1 : ∃ c, Z *ᵥ c = fun _ => 1)
    (hx : ¬ ∃ c, Z *ᵥ c = x) (hn : k+1 < n) :
    let P := controlProjection Z
    let M := residualMaker Z
    let r := M *ᵥ y
    let xbar := (∑ i, x i) / n
    let xc := x - xbar • (fun _ => (1 : ℝ))
    let sm := dotProduct x (M *ᵥ x)
    let sc := squaredLength xc
    let c := dotProduct x r
    let a := c/sc
    let b := c/sm
    let sr := squaredLength r - c^2/sc
    let sf := squaredLength r - c^2/sm
    Pᵀ = P ∧ P*P = P ∧ Mᵀ = M ∧ M*M = M ∧ M*Z = 0 ∧
    (∑ i, r i) = 0 ∧ M *ᵥ xc = M *ᵥ x ∧
    dotProduct xc r = c ∧ c = dotProduct x (M *ᵥ y) ∧
    sc = sm + squaredLength (P *ᵥ xc) ∧ 0 < sm ∧ sm ≤ sc ∧
    (sm = sc ↔ P *ᵥ xc = 0) ∧
    (P *ᵥ xc = 0 ↔ ∀ j, dotProduct xc (fun i => Z i j) = 0) ∧
    ols (residualLine x) r = ![-a*xbar, a] ∧
    IsLeastSquares (residualLine x) r ![-a*xbar, a] ∧
    olsSSE (residualLine x) r = sr ∧
    (∃! β, IsLeastSquares (fullDesign Z x) y β) ∧
    ols (fullDesign Z x) y (Fin.last k) = b ∧
    olsSSE (fullDesign Z x) y = sf ∧
    a = b*sm/sc ∧ (0<a ↔ 0<b) ∧ (a<0 ↔ b<0) ∧ |a| ≤ |b| ∧
    (a=b ↔ b=0 ∨ P *ᵥ xc = 0) ∧ sf ≤ sr ∧
    olsSESquared (residualLine x) r 1 = sr / (((n : ℝ)-2)*sc) ∧
    olsSESquared (fullDesign Z x) y (Fin.last k) = sf / (((n : ℝ)-k-1)*sm) ∧
    (0 < sf →
      olsTSquared (residualLine x) r 1 = ((n : ℝ)-2)*c^2/(sc*squaredLength r-c^2) ∧
      olsTSquared (fullDesign Z x) y (Fin.last k) =
        ((n : ℝ)-k-1)*c^2/(sm*squaredLength r-c^2) ∧
      olsTSquared (residualLine x) r 1 / ((n : ℝ)-2) ≤
        olsTSquared (fullDesign Z x) y (Fin.last k) / ((n : ℝ)-k-1) ∧
      (P *ᵥ xc = 0 → a=b ∧
        olsResidual (residualLine x) r = olsResidual (fullDesign Z x) y ∧
        olsT (residualLine x) r 1 =
          Real.sqrt (((n : ℝ)-2)/((n : ℝ)-k-1)) * olsT (fullDesign Z x) y (Fin.last k) ∧
        (2 ≤ k → olsT (fullDesign Z x) y (Fin.last k) ≠ 0 →
          |olsT (fullDesign Z x) y (Fin.last k)| < |olsT (residualLine x) r 1|))) := by
  exact RegressionCompletion.corrected_residual_regression_completed Z x y hZ h1 hx hn


/-- Student t law as an independent-standard-Gaussian ratio, the definition
given in T3: numerator N(0,1), denominator sqrt(sum of ν independent normal
squares / ν). This uses the explicit product measure, not a named axiom. -/
noncomputable def studentLaw (ν : ℕ) : Measure ℝ :=
  (Measure.pi (fun _ : Fin (ν+1) => gaussianReal 0 1)).map
    (fun z => z 0 / Real.sqrt ((∑ i ∈ Finset.univ.erase (0 : Fin (ν+1)), (z i)^2) / ν))

/-- The chi-square law of ν degrees of freedom as the sum of squares of ν
independent standard normals, T3(v). -/
noncomputable def chiSquaredLaw (ν : ℕ) : Measure ℝ :=
  (Measure.pi (fun _ : Fin ν => gaussianReal 0 1)).map (fun z => ∑ i, (z i)^2)


/-- Covariance matrix via population means and expectations, T4(f).
This is a distributional OLS definition, not an assumption made by the
empirical paper itself. -/
noncomputable def vectorCovariance {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ε : Ω → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ ω, (ε ω i - ∫ η, ε η i ∂μ) * (ε ω j - ∫ η, ε η j ∂μ) ∂μ

namespace CovarianceCompletion
open Matrix
noncomputable section
set_option maxHeartbeats 2000000

lemma residual_rank {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (hZ : FullColumnRank Z) : (residualMaker Z).rank = n-k := by
  let L := (Zᵀ*Z)⁻¹*Zᵀ
  have hL : L*Z=1 := by
    dsimp [L]
    rw [Matrix.mul_assoc]
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (full_rank_gram_unit Z hZ))
  simpa only [residualMaker,controlProjection,Matrix.mul_assoc] using
    LinearMoments.rank_complement_left_inverse Z L hL

lemma control_dimension_pos {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (h1 : ∃ c, Z*ᵥ c=fun _ => 1) (hn : 0<n) : 0<k := by
  by_contra hk
  have hk0 : k=0 := by omega
  subst k
  obtain ⟨a,ha⟩ := h1
  have hh := congrFun ha (⟨0,hn⟩ : Fin n)
  norm_num [Matrix.mulVec,dotProduct] at hh

lemma linear_covariance {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ}
    (μ : Measure Ω) (ε : Ω → Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (σ : ℝ) (hi : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hij : ∀ i j, Integrable (fun ω => ε ω i*ε ω j) μ)
    (he : ∀ i, (∫ ω, ε ω i ∂μ)=0)
    (hc : vectorCovariance μ ε=σ^2 • (1 : Matrix (Fin n) (Fin n) ℝ)) :
    vectorCovariance μ (fun ω => A*ᵥ ε ω)=σ^2 • (A*Aᵀ) := by
  have hz := LinearMoments.integral_linear_zero μ ε A hi he
  have hcoeff (p q : Fin n) : (∫ ω, ε ω p*ε ω q ∂μ)=σ^2*(if p=q then 1 else 0) := by
    have hh := congrArg (fun B : Matrix (Fin n) (Fin n) ℝ => B p q) hc
    simpa only [vectorCovariance,he,sub_zero,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply] using hh
  ext i j
  change (∫ ω, ((A*ᵥ ε ω) i-(∫ η,(A*ᵥ ε η) i ∂μ))*
    ((A*ᵥ ε ω) j-(∫ η,(A*ᵥ ε η) j ∂μ)) ∂μ)=_
  simp only [hz,sub_zero]
  rw [LinearMoments.integral_linear_product μ ε A hij i j]
  simp_rw [hcoeff]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  change (∑ p, A i p*A j p*σ^2)=σ^2*(∑ p, A i p*A j p)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

lemma residual_covariance_core {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (γ : Fin k → ℝ) (ε : Ω → Fin n → ℝ) (σ : ℝ)
    (hZ : FullColumnRank Z) (h1 : ∃ c, Z*ᵥ c=fun _ => 1) (hn : k+1<n)
    (hi : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hij : ∀ i j, Integrable (fun ω => ε ω i*ε ω j) μ)
    (he : ∀ i, (∫ ω, ε ω i ∂μ)=0)
    (hc : vectorCovariance μ ε=σ^2 • (1 : Matrix (Fin n) (Fin n) ℝ)) :
    let M := residualMaker Z
    let r := fun ω => M*ᵥ (Z*ᵥ γ+ε ω)
    (∀ ω, r ω=M*ᵥ ε ω) ∧ vectorCovariance μ r=σ^2 • M ∧ M.rank=n-k ∧
    (0<σ → (vectorCovariance μ r).rank=n-k ∧
      vectorCovariance μ r≠σ^2 • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  dsimp only
  let M := residualMaker Z
  have hp := ols_projection_identities Z hZ
  have hr (ω : Ω) : M*ᵥ (Z*ᵥ γ+ε ω)=M*ᵥ ε ω := by
    rw [Matrix.mulVec_add,Matrix.mulVec_mulVec,hp.2.2.2.2.1,Matrix.zero_mulVec,zero_add]
  have hcov : vectorCovariance μ (fun ω => M*ᵥ (Z*ᵥ γ+ε ω))=σ^2 • M := by
    simp_rw [hr]
    rw [linear_covariance μ ε M σ hi hij he hc,hp.2.2.1,hp.2.2.2.1]
  have hrank : M.rank=n-k := residual_rank Z hZ
  refine ⟨hr,hcov,hrank,?_⟩
  intro hσ
  have hsq : σ^2≠0 := pow_ne_zero _ hσ.ne'
  have hscalar (B : Matrix (Fin n) (Fin n) ℝ) : (σ^2 • B).rank=B.rank :=
    Matrix.rank_smul_of_mem_nonZeroDivisors B (mem_nonZeroDivisors_of_ne_zero hsq)
  rw [hcov,hscalar,hrank]
  refine ⟨rfl,?_⟩
  intro heq
  have hh := congrArg Matrix.rank heq
  rw [hscalar M,hscalar 1,Matrix.rank_one,Fintype.card_fin,hrank] at hh
  have hk := control_dimension_pos Z h1 (by omega)
  omega

lemma signed_t_scale_nonnegative (b E dr df : ℝ) (hE : 0≤E) (hdr : 0<dr) (hdf : 0<df) :
    b/Real.sqrt (E/dr)=Real.sqrt (dr/df)*(b/Real.sqrt (E/df)) := by
  rcases lt_or_eq_of_le hE with hE|hE
  · exact RegressionCompletion.signed_t_scale b E dr df hE hdr hdf
  · rw [←hE]
    simp

lemma orthogonal_t_scale {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (x y : Fin n → ℝ) (hZ : FullColumnRank Z) (h1 : ∃ c, Z*ᵥ c=fun _ => 1)
    (hx : ¬∃ c, Z*ᵥ c=x) (hn : k+1<n)
    (horth : controlProjection Z*ᵥ (x-((∑i,x i)/(n:ℝ)) • (fun _ => 1))=0) :
    olsT (residualLine x) (residualMaker Z*ᵥ y) 1=
      Real.sqrt (((n:ℝ)-2)/((n:ℝ)-k-1))*olsT (fullDesign Z x) y (Fin.last k) := by
  let M := residualMaker Z
  let r := M*ᵥ y
  let xc := x-((∑i,x i)/(n:ℝ)) • (fun _ => (1:ℝ))
  let sm := dotProduct x (M*ᵥ x)
  let sc := squaredLength xc
  let c := dotProduct x r
  let a := c/sc
  let b := c/sm
  let sr := squaredLength r-c^2/sc
  let sf := squaredLength r-c^2/sm
  let dr := (n:ℝ)-2
  let df := (n:ℝ)-k-1
  have hh := corrected_residual_regression Z x y hZ h1 hx hn
  dsimp only at hh
  have hm : 0<sm := hh.2.2.2.2.2.2.2.2.2.2.1
  have heq0 : sm=sc ↔ controlProjection Z*ᵥ xc=0 := hh.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcoefr : ols (residualLine x) r = ![-a*((∑i,x i)/(n:ℝ)),a] := hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlast : ols (fullDesign Z x) y (Fin.last k)=b := hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hssef : olsSSE (fullDesign Z x) y=sf := hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hser : olsSESquared (residualLine x) r 1=sr/(dr*sc) := hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsef : olsSESquared (fullDesign Z x) y (Fin.last k)=sf/(df*sm) := hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have heq : sm=sc := heq0.mpr horth
  have hab : a=b := by dsimp [a,b]; rw [heq]
  have har : ols (residualLine x) r 1=a := by rw [hcoefr]; simp
  have hsr : sr=sf := by dsimp [sr,sf]; rw [heq]
  have hsf0 : 0 ≤ sf := by rw [←hssef]; exact squaredLength_nonnegative _
  have hE : 0 ≤ sf/sm := div_nonneg hsf0 hm.le
  have hk := control_dimension_pos Z h1 (by omega)
  have hnreal : (k:ℝ)+1<(n:ℝ) := by exact_mod_cast hn
  have hkreal : (1:ℝ)≤k := by exact_mod_cast hk
  have hdr : 0<dr := by dsimp [dr]; linarith
  have hdf : 0<df := by dsimp [df]; linarith
  unfold olsT
  rw [har,hlast,hser,hsef]
  change a/Real.sqrt (sr/(dr*sc))=Real.sqrt (dr/df)*(b/Real.sqrt (sf/(df*sm)))
  rw [hab,hsr,←heq]
  have h1' : sf/(dr*sm)=(sf/sm)/dr := by ring
  have h2' : sf/(df*sm)=(sf/sm)/df := by ring
  rw [h1',h2']
  exact signed_t_scale_nonnegative b (sf/sm) dr df hE hdr hdf

lemma measurable_olsT {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ) (i : Fin p) :
    Measurable (fun y => olsT A y i) := by
  unfold olsT olsSESquared olsSSE olsResidual squaredLength ols
  fun_prop [Matrix.mulVec, dotProduct]

lemma residual_law {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ) (x : Fin n → ℝ)
    (γ : Fin k → ℝ) (ε : Ω → Fin n → ℝ)
    (hZ : FullColumnRank Z) (h1 : ∃ c, Z *ᵥ c = fun _ => 1)
    (hx : ¬ ∃ c, Z *ᵥ c = x) (hn : k+1 < n)
    (hi : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hk : 2 ≤ k)
    (horth : controlProjection Z *ᵥ (x-((∑i,x i)/(n:ℝ)) • (fun _ => 1))=0)
    (hlaw : μ.map (fun ω => olsT (fullDesign Z x) (Z*ᵥ γ+ε ω) (Fin.last k)) =
      studentLaw (n-k-1)) :
    μ.map (fun ω => olsT (residualLine x) (residualMaker Z*ᵥ (Z*ᵥ γ+ε ω)) 1) =
      (studentLaw (n-k-1)).map (fun t => Real.sqrt (((n:ℝ)-2)/((n:ℝ)-k-1))*t) ∧
    μ.map (fun ω => olsT (residualLine x) (residualMaker Z*ᵥ (Z*ᵥ γ+ε ω)) 1) ≠
      studentLaw (n-2) := by
  let tf := fun ω => olsT (fullDesign Z x) (Z*ᵥ γ+ε ω) (Fin.last k)
  let scale := fun t : ℝ => Real.sqrt (((n:ℝ)-2)/((n:ℝ)-k-1))*t
  have htf : AEMeasurable tf μ := by
    apply (measurable_olsT (fullDesign Z x) (Fin.last k)).comp_aemeasurable
    apply aemeasurable_pi_lambda
    intro i
    exact aemeasurable_const.add (hi i).aemeasurable
  have hs : Measurable scale := by fun_prop
  have hmap : μ.map (fun ω => olsT (residualLine x) (residualMaker Z*ᵥ (Z*ᵥ γ+ε ω)) 1) =
      (studentLaw (n-k-1)).map scale := by
    simp_rw [orthogonal_t_scale Z x _ hZ h1 hx hn horth]
    change μ.map (scale ∘ tf) = _
    rw [← AEMeasurable.map_map_of_aemeasurable hs.aemeasurable htf,hlaw]
  refine ⟨hmap, ?_⟩
  rw [hmap]
  have hν : 0 < n-k-1 := by omega
  have hlt : n-k-1 < n-2 := by omega
  have hcast : ((n-k-1 : ℕ):ℝ) = (n:ℝ)-k-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n-k),Nat.cast_sub (by omega : k ≤ n)]
    norm_num
  have hcast' : ((n-2 : ℕ):ℝ) = (n:ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    norm_num
  have hh := StudentCompletion.scaled_ratioLaw_ne hν hlt
  change (StudentCompletion.ratioLaw (n-k-1)).map scale ≠ StudentCompletion.ratioLaw (n-2)
  have hscl : scale = (fun t : ℝ => Real.sqrt (((n-2 : ℕ):ℝ)/((n-k-1 : ℕ):ℝ))*t) := by
    funext t
    dsimp [scale]
    rw [hcast,hcast']
  rw [hscl]
  exact hh

end
end CovarianceCompletion

/-- T4(f): residual covariance is σ²M. For σ>0 it has rank n-k and
differs from σ²I; for σ=0 it is zero.
The distributional comparison takes the full-model t law as an explicit
hypothesis; no such law is assumed for the nonlinear fits of the paper. -/
theorem corrected_residual_covariance_and_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n k : ℕ}
    (Z : Matrix (Fin n) (Fin k) ℝ) (x : Fin n → ℝ) (γ : Fin k → ℝ)
    (ε : Ω → Fin n → ℝ) (σ : ℝ)
    (hZ : FullColumnRank Z) (h1 : ∃ c, Z *ᵥ c = fun _ => 1)
    (hx : ¬ ∃ c, Z *ᵥ c = x) (hn : k+1 < n)
    (hi : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hij : ∀ i j, Integrable (fun ω => ε ω i * ε ω j) μ)
    (he : ∀ i, (∫ ω, ε ω i ∂μ) = 0)
    (hc : vectorCovariance μ ε = σ^2 • (1 : Matrix (Fin n) (Fin n) ℝ)) :
    let M := residualMaker Z
    let r := fun ω => M *ᵥ (Z *ᵥ γ + ε ω)
    let xc := x - ((∑ i, x i) / n) • (fun _ => (1 : ℝ))
    let tf := fun ω => olsT (fullDesign Z x) (Z *ᵥ γ + ε ω) (Fin.last k)
    let tr := fun ω => olsT (residualLine x) (r ω) 1
    (∀ ω, r ω = M *ᵥ ε ω) ∧
    vectorCovariance μ r = σ^2 • M ∧ M.rank = n-k ∧
    (0 < σ → (vectorCovariance μ r).rank = n-k ∧
      vectorCovariance μ r ≠ σ^2 • (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    (2 ≤ k → controlProjection Z *ᵥ xc = 0 → μ.map tf = studentLaw (n-k-1) →
      μ.map tr = (studentLaw (n-k-1)).map
        (fun t => Real.sqrt (((n : ℝ)-2)/((n : ℝ)-k-1))*t) ∧
      μ.map tr ≠ studentLaw (n-2)) := by
  dsimp only
  have hcore := CovarianceCompletion.residual_covariance_core μ Z γ ε σ hZ h1 hn hi hij he hc
  dsimp only at hcore
  refine ⟨hcore.1,hcore.2.1,hcore.2.2.1,hcore.2.2.2,?_⟩
  intro hk horth hlaw
  exact CovarianceCompletion.residual_law μ Z x γ ε hZ h1 hx hn hi hk horth hlaw


/-- T7(i): exact general nested-OLS correction. The controls' spans are
nested, the appended common regressor gives two full-rank designs, and both
have positive residual standard error. Residualizing q identifies the
inverse-Gram q diagonal and yields the required normalized-SE inequality. -/
theorem nested_standard_error_bound {n k₁ k₂ : ℕ}
    (Z₁ : Matrix (Fin n) (Fin k₁) ℝ) (Z₂ : Matrix (Fin n) (Fin k₂) ℝ)
    (q y : Fin n → ℝ)
    (hspan : ∀ a, ∃ b, Z₁ *ᵥ a = Z₂ *ᵥ b)
    (h₁ : FullColumnRank (fullDesign Z₁ q))
    (h₂ : FullColumnRank (fullDesign Z₂ q))
    (hn₁ : k₁+1 < n) (hn₂ : k₂+1 < n)
    (hs₁ : 0 < olsSSE (fullDesign Z₁ q) y)
    (hs₂ : 0 < olsSSE (fullDesign Z₂ q) y) :
    let R₁ := olsSSE Z₁ q
    let R₂ := olsSSE Z₂ q
    let s₁ := Real.sqrt (olsSSE (fullDesign Z₁ q) y / ((n : ℝ)-k₁-1))
    let s₂ := Real.sqrt (olsSSE (fullDesign Z₂ q) y / ((n : ℝ)-k₂-1))
    let se₁ := Real.sqrt (olsSESquared (fullDesign Z₁ q) y (Fin.last k₁))
    let se₂ := Real.sqrt (olsSESquared (fullDesign Z₂ q) y (Fin.last k₂))
    (∃ a, IsLeastSquares Z₁ q a ∧ squaredLength (q-Z₁ *ᵥ a) = R₁) ∧
    (∃ a, IsLeastSquares Z₂ q a ∧ squaredLength (q-Z₂ *ᵥ a) = R₂) ∧
    0 < R₁ ∧ 0 < R₂ ∧ R₂ ≤ R₁ ∧
    ((fullDesign Z₁ q)ᵀ * fullDesign Z₁ q)⁻¹ (Fin.last k₁) (Fin.last k₁) = 1/R₁ ∧
    ((fullDesign Z₂ q)ᵀ * fullDesign Z₂ q)⁻¹ (Fin.last k₂) (Fin.last k₂) = 1/R₂ ∧
    se₁ = s₁ / Real.sqrt R₁ ∧ se₂ = s₂ / Real.sqrt R₂ ∧
    se₁/s₁ ≤ se₂/s₂ ∧ se₁ ≤ se₂*s₁/s₂ := by
  exact FiniteCompletion.nested_standard_error_bound_completed Z₁ Z₂ q y hspan h₁ h₂ hn₁ hn₂ hs₁ hs₂


/-- T7(ii), finite arithmetic core: any normalized SEs satisfying the
nested-OLS inequality and the four closed printed rounding intervals lead
to a contradiction. The general matrix-to-inequality lemma is separate. -/
theorem printed_standard_error_incompatible (se₁ se₂ s₁ s₂ : ℝ)
    (hse₁ : 1.35 ≤ se₁) (hse₂ : 0 ≤ se₂) (hse₂u : se₂ ≤ 0.965)
    (hs₁ : 0 ≤ s₁) (hs₁u : s₁ ≤ 4.625) (hs₂ : 4.695 ≤ s₂)
    (hbound : se₁ ≤ se₂*s₁/s₂) : False := by
  have hp : 0 < s₂ := by linarith
  have hb : se₁*s₂ ≤ se₂*s₁ := (le_div_iff₀ hp).mp hbound
  have hu : se₂*s₁ ≤ (0.965 : ℝ)*4.625 := by
    exact mul_le_mul hse₂u hs₁u hs₁ (by norm_num)
  have hl : (1.35 : ℝ)*4.695 ≤ se₁*s₂ :=
    mul_le_mul hse₁ hs₂ (by norm_num) (by linarith)
  norm_num at hu hl
  linarith


/-- T7(ii), the complete universal incompatibility claim: no two nested,
full-rank A1/A2 OLS fits on 17 observations can simultaneously have the four
printed conventional SE/RMSQ entries, even throughout their closed rounding
intervals. The general inverse-Gram/residual-geometry theorem supplies the normalized-SE
inequality, which combines with the scalar rounding contradiction. -/
theorem printed_nested_standard_errors_impossible
    (Z₁ : Matrix (Fin 17) (Fin 2) ℝ) (Z₂ : Matrix (Fin 17) (Fin 3) ℝ)
    (q y : Fin 17 → ℝ)
    (hspan : ∀ a, ∃ b, Z₁ *ᵥ a = Z₂ *ᵥ b)
    (h₁ : FullColumnRank (fullDesign Z₁ q))
    (h₂ : FullColumnRank (fullDesign Z₂ q))
    (hse₁ : Real.sqrt (olsSESquared (fullDesign Z₁ q) y 2) ∈
      Set.Icc (1.35 : ℝ) 1.45)
    (hse₂ : Real.sqrt (olsSESquared (fullDesign Z₂ q) y 3) ∈
      Set.Icc (0.955 : ℝ) 0.965)
    (hs₁ : olsResidualStandardError (fullDesign Z₁ q) y ∈
      Set.Icc (4.615 : ℝ) 4.625)
    (hs₂ : olsResidualStandardError (fullDesign Z₂ q) y ∈
      Set.Icc (4.695 : ℝ) 4.705) : False := by
  have hp₁ : 0 < olsSSE (fullDesign Z₁ q) y := by
    have ht : 0 < olsResidualStandardError (fullDesign Z₁ q) y := by
      exact lt_of_lt_of_le (by norm_num) hs₁.1
    unfold olsResidualStandardError at ht
    have hv := Real.sqrt_pos.mp ht
    norm_num at hv
    linarith
  have hp₂ : 0 < olsSSE (fullDesign Z₂ q) y := by
    have ht : 0 < olsResidualStandardError (fullDesign Z₂ q) y := by
      exact lt_of_lt_of_le (by norm_num) hs₂.1
    unfold olsResidualStandardError at ht
    have hv := Real.sqrt_pos.mp ht
    norm_num at hv
    linarith
  have h := nested_standard_error_bound Z₁ Z₂ q y hspan h₁ h₂
    (by decide) (by decide) hp₁ hp₂
  dsimp only at h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hb⟩
  have hbound : Real.sqrt (olsSESquared (fullDesign Z₁ q) y 2) ≤
      Real.sqrt (olsSESquared (fullDesign Z₂ q) y 3) *
        olsResidualStandardError (fullDesign Z₁ q) y /
        olsResidualStandardError (fullDesign Z₂ q) y := by
    norm_num [olsResidualStandardError] at hb ⊢
    exact hb
  exact printed_standard_error_incompatible _ _ _ _ hse₁.1
    (Real.sqrt_nonneg _) hse₂.2 (Real.sqrt_nonneg _) hs₁.2 hs₂.1 hbound

/-- T7(ii): exact bound 0.965*4.625/4.695=7141/7512<0.951, with
the precise positive gap from the smallest number printing as 1.4. -/
theorem printed_standard_error_exact_gap :
    (0.965 : ℝ)*4.625/4.695 = 7141/7512 ∧
    (7141/7512 : ℝ) < 0.951 ∧
    (27/20 : ℝ) - 7141/7512 = 15001/37560 ∧ (0 : ℝ) < 15001/37560 := by
  norm_num




/-- The seventeen deposited rows (1948,1952,...,2012) of incmargin, q1415,
term, hwar4.8, rel.xtrm, copied exactly from T7's decimal strings. The paper
defines "incumbent party vote margin" on p. 128 and q1415/fatigue/war in
the Table 2 specifications, p. 136. These are given derived inputs, not a
formal verification of their construction from raw data. -/
noncomputable def tableTwoInputs : Matrix (Fin 17) (Fin 5) ℝ :=
  !![(112/25 : ℝ), (1934828833/500000000 : ℝ), (16/1 : ℝ), (0/1 : ℝ), (119984289/500000000 : ℝ);
    (-217/20 : ℝ), (2417476109/1000000000 : ℝ), (20/1 : ℝ), (1904152679/10000000 : ℝ), (1374649/15625000 : ℝ);
    (77/5 : ℝ), (72046309/125000000 : ℝ), (4/1 : ℝ), (0/1 : ℝ), (-51046667/1000000000 : ℝ);
    (-17/100 : ℝ), (336587/20000000 : ℝ), (8/1 : ℝ), (0/1 : ℝ), (-53180451/1000000000 : ℝ);
    (1129/50 : ℝ), (3258883307/1000000000 : ℝ), (4/1 : ℝ), (474421501/500000000 : ℝ), (-318262019/1000000000 : ℝ);
    (-7/10 : ℝ), (1398802867/1000000000 : ℝ), (8/1 : ℝ), (91018219/625000 : ℝ), (54862857/250000000 : ℝ);
    (463/20 : ℝ), (303629933/125000000 : ℝ), (4/1 : ℝ), (0/1 : ℝ), (-455834851/1000000000 : ℝ);
    (-103/50 : ℝ), (628281/800000 : ℝ), (8/1 : ℝ), (2086606979/1000000000 : ℝ), (25423097/500000000 : ℝ);
    (-487/50 : ℝ), (-207120123/250000000 : ℝ), (4/1 : ℝ), (0/1 : ℝ), (-19407/31250 : ℝ);
    (1821/100 : ℝ), (1283325533/500000000 : ℝ), (4/1 : ℝ), (0/1 : ℝ), (273800291/1000000000 : ℝ);
    (193/25 : ℝ), (189045253/125000000 : ℝ), (8/1 : ℝ), (0/1 : ℝ), (173195729/1000000000 : ℝ);
    (-139/25 : ℝ), (77430623/100000000 : ℝ), (12/1 : ℝ), (0/1 : ℝ), (192515613/1000000000 : ℝ);
    (851/100 : ℝ), (283826897/250000000 : ℝ), (4/1 : ℝ), (0/1 : ℝ), (-146050087/1000000000 : ℝ);
    (51/100 : ℝ), (837710937/500000000 : ℝ), (8/1 : ℝ), (0/1 : ℝ), (-42411239/250000000 : ℝ);
    (123/50 : ℝ), (32470207/31250000 : ℝ), (4/1 : ℝ), (3860627651/1000000000 : ℝ), (62372671/250000000 : ℝ);
    (-727/100 : ℝ), (-349851591/500000000 : ℝ), (8/1 : ℝ), (1398476601/100000000 : ℝ), (-119001519/1000000000 : ℝ);
    (96/25 : ℝ), (86756221/250000000 : ℝ), (4/1 : ℝ), (24/5 : ℝ), (40330327/1000000000 : ℝ)]

/-- The incmargin outcome of Table 2 Panel A (p. 128 definition), deposited
in the first column of T7's fixed input table. -/
noncomputable def tableTwoOutcome : Fin 17 → ℝ := fun i => tableTwoInputs i 0

/-- Column A1 design of Table 2, pp. 136--137: intercept, income and
fatigue. -/
noncomputable def tableA1 : Matrix (Fin 17) (Fin 3) ℝ := fun i j => ![(1 : ℝ), tableTwoInputs i 1, tableTwoInputs i 2] j
/-- Exact Gram certificate for the deposited A1 design, T7(iii). -/
noncomputable def gramA1 : Matrix (Fin 3) (Fin 3) ℝ := !![(17/1 : ℝ), (22274347101/1000000000 : ℝ), (128/1 : ℝ);
    (22274347101/1000000000 : ℝ), (56191363635337591927/1000000000000000000 : ℝ), (24895450589/125000000 : ℝ);
    (128/1 : ℝ), (24895450589/125000000 : ℝ), (1312/1 : ℝ)]
/-- Exact inverse-Gram certificate for the deposited A1 design, T7(iii).
Its product with the Gram matrix is the identity. -/
noncomputable def inverseGramA1 : Matrix (Fin 3) (Fin 3) ℝ := !![(1064278988990160375165/4470670631662545158236 : ℝ), (-29148453073250000000/1117667657915636289559 : ℝ), (-344531910510220578343/17882682526650180632944 : ℝ);
    (-29148453073250000000/1117667657915636289559 : ℝ), (46250000000000000000/1117667657915636289559 : ℝ), (-4177069149812500000/1117667657915636289559 : ℝ);
    (-344531910510220578343/17882682526650180632944 : ℝ), (-4177069149812500000/1117667657915636289559 : ℝ), (229553321512455979279/71530730106600722531776 : ℝ)]
/-- Exact right-hand side of A1's normal equations, T7(iii). -/
noncomputable def rhsA1 : Fin 3 → ℝ := ![(7051/100 : ℝ), (20887037112487/100000000000 : ℝ), (2746/25 : ℝ)]
/-- Exact A1 coefficient vector, T7(iii).
The entries satisfy the normal equations for the design and outcome. -/
noncomputable def coefficientsA1 : Fin 3 → ℝ := ![(2061423620329160546377923/223533531583127257911800 : ℝ), (7146187962914975000000/1117667657915636289559 : ℝ), (-1597443326895646253537849/894134126332509031647200 : ℝ)]

/-- T7(iii): the deposited A1 design has full column rank, the stated
coefficient vector satisfies the OLS definition and normal equations, and
the exact SSE and squared income SE have the stated rational values. -/
theorem table_A1_exact_fit :
    tableA1ᵀ * tableA1 = gramA1 ∧
    inverseGramA1 * gramA1 = 1 ∧
    FullColumnRank tableA1 ∧
    ols tableA1 tableTwoOutcome = coefficientsA1 ∧
    tableA1ᵀ *ᵥ (tableTwoOutcome - tableA1 *ᵥ coefficientsA1) = 0 ∧
    olsSSE tableA1 tableTwoOutcome = (669081239978677801524669051/2235335315831272579118000 : ℝ) ∧
    olsSESquared tableA1 tableTwoOutcome 1 = (7736251837253462080128985902187500000000000/8744266954854366478686864008983610246901367 : ℝ) := by
  have hg : tableA1ᵀ * tableA1 = gramA1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [tableA1, tableTwoInputs, gramA1, Matrix.mul_apply, Fin.sum_univ_succ]
  have hi : inverseGramA1 * gramA1 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [inverseGramA1, gramA1, Matrix.mul_apply, Fin.sum_univ_succ]
  have hil : inverseGramA1 * (tableA1ᵀ * tableA1) = 1 := by rw [hg]; exact hi
  have hinv : (tableA1ᵀ * tableA1)⁻¹ = inverseGramA1 := Matrix.inv_eq_left_inv hil
  have hty : tableA1ᵀ *ᵥ tableTwoOutcome = rhsA1 := by
    ext i; fin_cases i <;>
      norm_num [tableA1, tableTwoInputs, tableTwoOutcome, rhsA1, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hb : ols tableA1 tableTwoOutcome = coefficientsA1 := by
    unfold ols
    rw [hinv, hty]
    ext i; fin_cases i <;>
      norm_num [inverseGramA1, rhsA1, coefficientsA1, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hnormal : tableA1ᵀ *ᵥ (tableTwoOutcome-tableA1 *ᵥ coefficientsA1) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hg, hty]
    ext i; fin_cases i <;>
      norm_num [gramA1, rhsA1, coefficientsA1, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hs : olsSSE tableA1 tableTwoOutcome = (669081239978677801524669051/2235335315831272579118000 : ℝ) := by
    unfold olsSSE olsResidual
    rw [hb]
    norm_num [squaredLength, tableA1, tableTwoInputs, tableTwoOutcome, coefficientsA1,
      Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  refine ⟨hg, hi, gram_certificate_full_rank _ _ hil, hb, hnormal, hs, ?_⟩
  unfold olsSESquared
  rw [hs, hinv]
  norm_num [inverseGramA1]


/-- T7(iii): A1's exact certificate is the unique least-squares minimizer,
so the correction concerns the actual OLS fit of the fixed input rows. -/
theorem table_A1_unique_minimizer :
    IsLeastSquares tableA1 tableTwoOutcome coefficientsA1 ∧
    ∀ b, IsLeastSquares tableA1 tableTwoOutcome b → b = coefficientsA1 := by
  have h := table_A1_exact_fit
  exact normal_equation_unique _ _ _ h.2.2.1 h.2.2.2.2.1


/-- T7(iii): the exact A1 income coefficient lies in the rounding interval
for the corrected 6.39 in Table 2. -/
theorem table_A1_coefficient_rounding :
    (6.385 : ℝ) ≤ ols tableA1 tableTwoOutcome 1 ∧
    ols tableA1 tableTwoOutcome 1 < 6.395 := by
  rw [table_A1_exact_fit.2.2.2.1]
  norm_num [coefficientsA1]


/-- Column A2 design of Table 2, pp. 136--137: intercept, income and
fatigue, war fatalities. -/
noncomputable def tableA2 : Matrix (Fin 17) (Fin 4) ℝ := fun i j => ![(1 : ℝ), tableTwoInputs i 1, tableTwoInputs i 2, tableTwoInputs i 3] j
/-- Exact Gram certificate for the deposited A2 design, T7(iii). -/
noncomputable def gramA2 : Matrix (Fin 4) (Fin 4) ℝ := !![(17/1 : ℝ), (22274347101/1000000000 : ℝ), (128/1 : ℝ), (180862630971/500000000 : ℝ);
    (22274347101/1000000000 : ℝ), (56191363635337591927/1000000000000000000 : ℝ), (24895450589/125000000 : ℝ), (166163407087136723917/250000000000000000 : ℝ);
    (128/1 : ℝ), (24895450589/125000000 : ℝ), (1312/1 : ℝ), (1285086856931/250000000 : ℝ);
    (180862630971/500000000 : ℝ), (166163407087136723917/250000000000000000 : ℝ), (1285086856931/250000000 : ℝ), (28852298026797981773173/500000000000000000 : ℝ)]
/-- Exact inverse-Gram certificate for the deposited A2 design, T7(iii).
Its product with the Gram matrix is the identity. -/
noncomputable def inverseGramA2 : Matrix (Fin 4) (Fin 4) ℝ := !![(78862331612291980327451396327214859407064613/296887231059390189791731950374739324942216354 : ℝ), (-1239014374721653685225668604737552500000000/49481205176565031631955325062456554157036059 : ℝ), (-15250704789727539031697536657708827510597805/593774462118780379583463900749478649884432708 : ℝ), (135271334301711092139996948421627000000000/148443615529695094895865975187369662471108177 : ℝ);
    (-1239014374721653685225668604737552500000000/49481205176565031631955325062456554157036059 : ℝ), (2049512234685310922589560500000000000000000/49481205176565031631955325062456554157036059 : ℝ), (-196900609401460031735370121123203750000000/49481205176565031631955325062456554157036059 : ℝ), (1700117562225489614011000000000000000000/49481205176565031631955325062456554157036059 : ℝ);
    (-15250704789727539031697536657708827510597805/593774462118780379583463900749478649884432708 : ℝ), (-196900609401460031735370121123203750000000/49481205176565031631955325062456554157036059 : ℝ), (1396292878548449824344524762988715757368409/296887231059390189791731950374739324942216354 : ℝ), (-31487298550813897482575965955611750000000/148443615529695094895865975187369662471108177 : ℝ);
    (135271334301711092139996948421627000000000/148443615529695094895865975187369662471108177 : ℝ), (1700117562225489614011000000000000000000/49481205176565031631955325062456554157036059 : ℝ), (-31487298550813897482575965955611750000000/148443615529695094895865975187369662471108177 : ℝ), (4470670631662545158236000000000000000000/148443615529695094895865975187369662471108177 : ℝ)]
/-- Exact right-hand side of A2's normal equations, T7(iii). -/
noncomputable def rhsA2 : Fin 4 → ℝ := ![(7051/100 : ℝ), (20887037112487/100000000000 : ℝ), (2746/25 : ℝ), (-111227985112891/50000000000 : ℝ)]
/-- Exact A2 coefficient vector, T7(iii).
The entries satisfy the normal equations for the design and outcome. -/
noncomputable def coefficientsA2 : Fin 4 → ℝ := ![(25684156229514428563777695313037499225923245817/2968872310593901897917319503747393249422163540 : ℝ), (315309901567374756223272228924480076940000000/49481205176565031631955325062456554157036059 : ℝ), (-6137053209578193764329374573380726129631314269/3711090388242377372396649379684241561777704425 : ℝ), (-2800544261937919072726551897176219660000000/148443615529695094895865975187369662471108177 : ℝ)]

/-- T7(iii): the deposited A2 design has full column rank, the stated
coefficient vector satisfies the OLS definition and normal equations, and
the exact SSE and squared income SE have the stated rational values. -/
theorem table_A2_exact_fit :
    tableA2ᵀ * tableA2 = gramA2 ∧
    inverseGramA2 * gramA2 = 1 ∧
    FullColumnRank tableA2 ∧
    ols tableA2 tableTwoOutcome = coefficientsA2 ∧
    tableA2ᵀ *ᵥ (tableTwoOutcome - tableA2 *ᵥ coefficientsA2) = 0 ∧
    olsSSE tableA2 tableTwoOutcome = (213389270031088993406358428750520859232201897223397/742218077648475474479329875936848312355540885000 : ℝ) ∧
    olsSESquared tableA2 tableTwoOutcome 1 = (87468783935856889968959076916547418567045954314277345968916000934001709403700000000000000/95487196963287717244789952652591939943572286312594988431258935890666000674446137223807759 : ℝ) := by
  have hg : tableA2ᵀ * tableA2 = gramA2 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [tableA2, tableTwoInputs, gramA2, Matrix.mul_apply, Fin.sum_univ_succ]
  have hi : inverseGramA2 * gramA2 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [inverseGramA2, gramA2, Matrix.mul_apply, Fin.sum_univ_succ]
  have hil : inverseGramA2 * (tableA2ᵀ * tableA2) = 1 := by rw [hg]; exact hi
  have hinv : (tableA2ᵀ * tableA2)⁻¹ = inverseGramA2 := Matrix.inv_eq_left_inv hil
  have hty : tableA2ᵀ *ᵥ tableTwoOutcome = rhsA2 := by
    ext i; fin_cases i <;>
      norm_num [tableA2, tableTwoInputs, tableTwoOutcome, rhsA2, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hb : ols tableA2 tableTwoOutcome = coefficientsA2 := by
    unfold ols
    rw [hinv, hty]
    ext i; fin_cases i <;>
      norm_num [inverseGramA2, rhsA2, coefficientsA2, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hnormal : tableA2ᵀ *ᵥ (tableTwoOutcome-tableA2 *ᵥ coefficientsA2) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hg, hty]
    ext i; fin_cases i <;>
      norm_num [gramA2, rhsA2, coefficientsA2, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hs : olsSSE tableA2 tableTwoOutcome = (213389270031088993406358428750520859232201897223397/742218077648475474479329875936848312355540885000 : ℝ) := by
    unfold olsSSE olsResidual
    rw [hb]
    norm_num [squaredLength, tableA2, tableTwoInputs, tableTwoOutcome, coefficientsA2,
      Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  refine ⟨hg, hi, gram_certificate_full_rank _ _ hil, hb, hnormal, hs, ?_⟩
  unfold olsSESquared
  rw [hs, hinv]
  norm_num [inverseGramA2]


/-- T7(iii): A2's exact certificate is the unique least-squares minimizer,
so the correction concerns the actual OLS fit of the fixed input rows. -/
theorem table_A2_unique_minimizer :
    IsLeastSquares tableA2 tableTwoOutcome coefficientsA2 ∧
    ∀ b, IsLeastSquares tableA2 tableTwoOutcome b → b = coefficientsA2 := by
  have h := table_A2_exact_fit
  exact normal_equation_unique _ _ _ h.2.2.1 h.2.2.2.2.1


/-- T7(iii): the exact A2 income coefficient lies in the rounding interval
for the corrected 6.37 in Table 2. -/
theorem table_A2_coefficient_rounding :
    (6.365 : ℝ) ≤ ols tableA2 tableTwoOutcome 1 ∧
    ols tableA2 tableTwoOutcome 1 < 6.375 := by
  rw [table_A2_exact_fit.2.2.2.1]
  norm_num [coefficientsA2]


/-- Column A3 design of Table 2, pp. 136--137: intercept, income and
fatigue, war fatalities, and relative extremism. -/
noncomputable def tableA3 : Matrix (Fin 17) (Fin 5) ℝ := fun i j => ![(1 : ℝ), tableTwoInputs i 1, tableTwoInputs i 2, tableTwoInputs i 3, tableTwoInputs i 4] j
/-- Exact Gram certificate for the deposited A3 design, T7(iii). -/
noncomputable def gramA3 : Matrix (Fin 5) (Fin 5) ℝ := !![(17/1 : ℝ), (22274347101/1000000000 : ℝ), (128/1 : ℝ), (180862630971/500000000 : ℝ), (-40646817/100000000 : ℝ);
    (22274347101/1000000000 : ℝ), (56191363635337591927/1000000000000000000 : ℝ), (24895450589/125000000 : ℝ), (166163407087136723917/250000000000000000 : ℝ), (848156779439308911/1000000000000000000 : ℝ);
    (128/1 : ℝ), (24895450589/125000000 : ℝ), (1312/1 : ℝ), (1285086856931/250000000 : ℝ), (1152045359/250000000 : ℝ);
    (180862630971/500000000 : ℝ), (166163407087136723917/250000000000000000 : ℝ), (1285086856931/250000000 : ℝ), (28852298026797981773173/500000000000000000 : ℝ), (24003737119460923291/500000000000000000 : ℝ);
    (-40646817/100000000 : ℝ), (848156779439308911/1000000000000000000 : ℝ), (1152045359/250000000 : ℝ), (24003737119460923291/500000000000000000 : ℝ), (543209621800141297/500000000000000000 : ℝ)]
/-- Exact inverse-Gram certificate for the deposited A3 design, T7(iii).
Its product with the Gram matrix is the identity. -/
noncomputable def inverseGramA3 : Matrix (Fin 5) (Fin 5) ℝ := !![(82338956538638989696278690468373247034797257396400809607513693/263545025594799089766460841230799927145443792347888343866175781 : ℝ), (-2777024895194139847461368627424659827362246935349240000000000/87848341864933029922153613743599975715147930782629447955391927 : ℝ), (-15783460161245936548154975572968532741689521148468529099655767/527090051189598179532921682461599854290887584695776687732351562 : ℝ), (232467466336626311870035348319406057448788252657119000000000/263545025594799089766460841230799927145443792347888343866175781 : ℝ), (20170411806100145199272081424308558958792422645788779000000000/87848341864933029922153613743599975715147930782629447955391927 : ℝ);
    (-2777024895194139847461368627424659827362246935349240000000000/87848341864933029922153613743599975715147930782629447955391927 : ℝ), (3719744731245302902274768025019627921906944000000000000000000/87848341864933029922153613743599975715147930782629447955391927 : ℝ), (-297021775846677777312510059204071862534120979229935000000000/87848341864933029922153613743599975715147930782629447955391927 : ℝ), (3378395885337343062109757946975066914623000000000000000000/87848341864933029922153613743599975715147930782629447955391927 : ℝ), (-2832384437959485648083391652225064936484715000000000000000000/87848341864933029922153613743599975715147930782629447955391927 : ℝ);
    (-15783460161245936548154975572968532741689521148468529099655767/527090051189598179532921682461599854290887584695776687732351562 : ℝ), (-297021775846677777312510059204071862534120979229935000000000/87848341864933029922153613743599975715147930782629447955391927 : ℝ), (10733512582473787677446420252747376150424315496594727657959821/2108360204758392718131686729846399417163550338783106750929406248 : ℝ), (-55201974641604264148521540715188221282458287050810750000000/263545025594799089766460841230799927145443792347888343866175781 : ℝ), (-1836189029063668748517896049361057910717313413487991500000000/87848341864933029922153613743599975715147930782629447955391927 : ℝ);
    (232467466336626311870035348319406057448788252657119000000000/263545025594799089766460841230799927145443792347888343866175781 : ℝ), (3378395885337343062109757946975066914623000000000000000000/87848341864933029922153613743599975715147930782629447955391927 : ℝ), (-55201974641604264148521540715188221282458287050810750000000/263545025594799089766460841230799927145443792347888343866175781 : ℝ), (7941972223900175023734708669273900992012000000000000000000/263545025594799089766460841230799927145443792347888343866175781 : ℝ), (-12579218353503464057576660917862181679568000000000000000000/87848341864933029922153613743599975715147930782629447955391927 : ℝ);
    (20170411806100145199272081424308558958792422645788779000000000/87848341864933029922153613743599975715147930782629447955391927 : ℝ), (-2832384437959485648083391652225064936484715000000000000000000/87848341864933029922153613743599975715147930782629447955391927 : ℝ), (-1836189029063668748517896049361057910717313413487991500000000/87848341864933029922153613743599975715147930782629447955391927 : ℝ), (-12579218353503464057576660917862181679568000000000000000000/87848341864933029922153613743599975715147930782629447955391927 : ℝ), (98962410353130063263910650124913108314072118000000000000000000/87848341864933029922153613743599975715147930782629447955391927 : ℝ)]
/-- Exact right-hand side of A3's normal equations, T7(iii). -/
noncomputable def rhsA3 : Fin 5 → ℝ := ![(7051/100 : ℝ), (20887037112487/100000000000 : ℝ), (2746/25 : ℝ), (-111227985112891/50000000000 : ℝ), (-704815468797/100000000000 : ℝ)]
/-- Exact A3 coefficient vector, T7(iii).
The entries satisfy the normal equations for the design and outcome. -/
noncomputable def coefficientsA3 : Fin 5 → ℝ := ![(56378680668760324252433213339653942088949112019789364103424592173/6588625639869977244161521030769998178636094808697208596654394525 : ℝ), (560959205595590684404193874010188762669512981839878401170000000/87848341864933029922153613743599975715147930782629447955391927 : ℝ), (-17342663386991901794850512124376610236356646928578241142225864371/10541801023791963590658433649231997085817751693915533754647031240 : ℝ), (-4956573971418376117599707529401755107347693844013013020000000/263545025594799089766460841230799927145443792347888343866175781 : ℝ), (-40591609457254980209769484284745347505452605434070339820000000/87848341864933029922153613743599975715147930782629447955391927 : ℝ)]

/-- T7(iii): the deposited A3 design has full column rank, the stated
coefficient vector satisfies the OLS definition and normal equations, and
the exact SSE and squared income SE have the stated rational values. -/
theorem table_A3_exact_fit :
    tableA3ᵀ * tableA3 = gramA3 ∧
    inverseGramA3 * gramA3 = 1 ∧
    FullColumnRank tableA3 ∧
    ols tableA3 tableTwoOutcome = coefficientsA3 ∧
    tableA3ᵀ *ᵥ (tableTwoOutcome - tableA3 *ᵥ coefficientsA3) = 0 ∧
    olsSSE tableA3 tableTwoOutcome = (47324877916940352665959680919248539485953157846602969430940354614258/164715640996749431104038025769249954465902370217430214916359863125 : ℝ) ∧
    olsSESquared tableA3 tableTwoOutcome 1 = (23471528705115474983107983048961605510619198926004247005168593424390887734336184946568093765880721396385547673600000000000000/23151993505254435772914763438131578987685805911938751506612621633148375489001684195882614005985122017451222715967416530319987 : ℝ) := by
  have hg : tableA3ᵀ * tableA3 = gramA3 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [tableA3, tableTwoInputs, gramA3, Matrix.mul_apply, Fin.sum_univ_succ]
  have hi : inverseGramA3 * gramA3 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [inverseGramA3, gramA3, Matrix.mul_apply, Fin.sum_univ_succ]
  have hil : inverseGramA3 * (tableA3ᵀ * tableA3) = 1 := by rw [hg]; exact hi
  have hinv : (tableA3ᵀ * tableA3)⁻¹ = inverseGramA3 := Matrix.inv_eq_left_inv hil
  have hty : tableA3ᵀ *ᵥ tableTwoOutcome = rhsA3 := by
    ext i; fin_cases i <;>
      norm_num [tableA3, tableTwoInputs, tableTwoOutcome, rhsA3, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hb : ols tableA3 tableTwoOutcome = coefficientsA3 := by
    unfold ols
    rw [hinv, hty]
    ext i; fin_cases i <;>
      norm_num [inverseGramA3, rhsA3, coefficientsA3, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hnormal : tableA3ᵀ *ᵥ (tableTwoOutcome-tableA3 *ᵥ coefficientsA3) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hg, hty]
    ext i; fin_cases i <;>
      norm_num [gramA3, rhsA3, coefficientsA3, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  have hs : olsSSE tableA3 tableTwoOutcome = (47324877916940352665959680919248539485953157846602969430940354614258/164715640996749431104038025769249954465902370217430214916359863125 : ℝ) := by
    unfold olsSSE olsResidual
    rw [hb]
    norm_num [squaredLength, tableA3, tableTwoInputs, tableTwoOutcome, coefficientsA3,
      Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  refine ⟨hg, hi, gram_certificate_full_rank _ _ hil, hb, hnormal, hs, ?_⟩
  unfold olsSESquared
  rw [hs, hinv]
  norm_num [inverseGramA3]


/-- T7(iii): A3's exact certificate is the unique least-squares minimizer,
so the correction concerns the actual OLS fit of the fixed input rows. -/
theorem table_A3_unique_minimizer :
    IsLeastSquares tableA3 tableTwoOutcome coefficientsA3 ∧
    ∀ b, IsLeastSquares tableA3 tableTwoOutcome b → b = coefficientsA3 := by
  have h := table_A3_exact_fit
  exact normal_equation_unique _ _ _ h.2.2.1 h.2.2.2.2.1


/-- T7(iii): the exact A3 income coefficient lies in the rounding interval
for the corrected 6.39 in Table 2. -/
theorem table_A3_coefficient_rounding :
    (6.385 : ℝ) ≤ ols tableA3 tableTwoOutcome 1 ∧
    ols tableA3 tableTwoOutcome 1 < 6.395 := by
  rw [table_A3_exact_fit.2.2.2.1]
  norm_num [coefficientsA3]


/-- T7(iii): the squared A1 income SE lies in [0.935²,0.945²); since the
conventional SE is a nonnegative square root, it rounds to 0.94. -/
theorem table_A1_standard_error_rounding :
    (0.935 : ℝ)^2 ≤ olsSESquared tableA1 tableTwoOutcome 1 ∧
    olsSESquared tableA1 tableTwoOutcome 1 < (0.945 : ℝ)^2 ∧
    (0.935 : ℝ) ≤ Real.sqrt (olsSESquared tableA1 tableTwoOutcome 1) ∧
    Real.sqrt (olsSESquared tableA1 tableTwoOutcome 1) < (0.945 : ℝ) := by
  have h := table_A1_exact_fit.2.2.2.2.2.2
  rw [h]
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · apply (Real.le_sqrt' (by norm_num)).2
    norm_num
  · apply (Real.sqrt_lt' (by norm_num)).2
    norm_num




end AronowAudit.P039

