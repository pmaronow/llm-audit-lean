import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

namespace AronowAudit.P037
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false

/-- Main p. 568: "robust SEs under a normal approximation"; SI p. 13:
"the model is fit with OLS regression". The coefficient map A=(X'X)⁻¹X'.
Full column rank is explicitly required in results using this map. -/
noncomputable def schoolOLSMap {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ) :=
  (X.transpose * X)⁻¹ * X.transpose

/-- T18: H=XA, e=y-XAy.
X comprises the nonaliased school-regression columns. -/
noncomputable def schoolHat {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ) :=
  X * schoolOLSMap X

/-- Residuals of the school OLS regression, SI Eqs. (5),(6). -/
noncomputable def schoolResidual {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) ℝ) (y : Fin n → ℝ) :=
  y - X.mulVec ((schoolOLSMap X).mulVec y)

/-- T18(a), released script 4: HC0, with no n/(n-k) or leverage factor,
V=A diag(e_i²) A'. The paper names robust SEs without naming HC0. -/
noncomputable def schoolHC0 {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) ℝ) (y : Fin n → ℝ) :=
  schoolOLSMap X * Matrix.diagonal (fun i => (schoolResidual X y i)^2) *
    (schoolOLSMap X).transpose


/-- Conditional moments with X,y fixed: componentwise integrals over a
probability law of bootstrap multipliers or model errors; continuous laws,
including the coded standard normals, are allowed. -/
noncomputable def inferenceMean {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (v : Ω → Fin k → ℝ) : Fin k → ℝ :=
  fun j => ∫ ω, v ω j ∂μ

/-- Covariance is the centered second moment, not an assumed matrix. -/
noncomputable def inferenceCov {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (v : Ω → Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun j l => ∫ ω, (v ω j - inferenceMean μ v j) *
    (v ω l - inferenceMean μ v l) ∂μ

/-! Finite linear-moment and symmetric-projection algebra for inference. -/
namespace InferenceCompletion
open MeasureTheory
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

theorem gram_unit {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ)
    (hX : Function.Injective X.mulVec) : IsUnit (X.transpose*X).det := by
  apply (Matrix.isUnit_iff_isUnit_det (X.transpose*X)).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  change Function.Injective ((X.transpose*X).mulVecLin : _ → _)
  rw [← LinearMap.ker_eq_bot,Matrix.ker_mulVecLin_transpose_mul_self]
  exact LinearMap.ker_eq_bot.mpr hX

theorem left_inverse {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ)
    (hX : Function.Injective X.mulVec) : schoolOLSMap X * X = 1 := by
  unfold schoolOLSMap
  rw [Matrix.mul_assoc,Matrix.nonsing_inv_mul _ (gram_unit X hX)]

theorem hat_symmetric {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ) :
    (schoolHat X).transpose = schoolHat X := by
  simp only [schoolHat,schoolOLSMap,Matrix.transpose_mul,Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv,Matrix.mul_assoc]

theorem hat_idempotent {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ)
    (hX : Function.Injective X.mulVec) : schoolHat X * schoolHat X = schoolHat X := by
  unfold schoolHat
  rw [Matrix.mul_assoc,←Matrix.mul_assoc (schoolOLSMap X),left_inverse X hX,
    Matrix.one_mul]

theorem integrable_mulVec {Ω : Type*} [MeasurableSpace Ω] {n k : ℕ}
    (μ : Measure Ω) (A : Matrix (Fin k) (Fin n) ℝ) (v : Ω → Fin n → ℝ)
    (h1 : ∀ i, Integrable (fun ω => v ω i) μ) (j : Fin k) :
    Integrable (fun ω => A.mulVec (v ω) j) μ := by
  simpa only [Matrix.mulVec,dotProduct] using
    integrable_finsetSum Finset.univ (fun i _ => (h1 i).const_mul (A j i))

theorem integral_mulVec {Ω : Type*} [MeasurableSpace Ω] {n k : ℕ}
    (μ : Measure Ω) (A : Matrix (Fin k) (Fin n) ℝ) (v : Ω → Fin n → ℝ)
    (h1 : ∀ i, Integrable (fun ω => v ω i) μ) (j : Fin k) :
    (∫ ω, A.mulVec (v ω) j ∂μ) = ∑ i, A j i*(∫ ω, v ω i ∂μ) := by
  rw [show (fun ω => A.mulVec (v ω) j) = (fun ω => ∑ i,A j i*v ω i) from rfl,
    integral_finsetSum _ (fun i _ => (h1 i).const_mul (A j i))]
  simp only [integral_const_mul]

theorem integral_mulVec_product {Ω : Type*} [MeasurableSpace Ω] {n k l : ℕ}
    (μ : Measure Ω) (A : Matrix (Fin k) (Fin n) ℝ) (B : Matrix (Fin l) (Fin n) ℝ)
    (v : Ω → Fin n → ℝ) (h2 : ∀ i j,Integrable (fun ω => v ω i*v ω j) μ)
    (a : Fin k) (b : Fin l) :
    (∫ ω,A.mulVec (v ω) a*B.mulVec (v ω) b ∂μ) =
      ∑ i,∑ j,(A a i*B b j)*(∫ ω,v ω i*v ω j ∂μ) := by
  have he : (fun ω => A.mulVec (v ω) a*B.mulVec (v ω) b) =
      (fun ω => ∑ i,∑ j,(A a i*B b j)*(v ω i*v ω j)) := by
    funext ω
    simp only [Matrix.mulVec,dotProduct,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl;intro i _
    apply Finset.sum_congr rfl;intro j _
    ring
  rw [he,integral_finsetSum _ (fun i _ => integrable_finset_sum _
    (fun j _ => (h2 i j).const_mul (A a i*B b j)))]
  apply Finset.sum_congr rfl;intro i _
  rw [integral_finsetSum _ (fun j _ => (h2 i j).const_mul (A a i*B b j))]
  simp only [integral_const_mul]

theorem affine_moments {Ω : Type*} [MeasurableSpace Ω] {n k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Fin k → ℝ)
    (A : Matrix (Fin k) (Fin n) ℝ) (v : Ω → Fin n → ℝ) (s : ℝ)
    (h1 : ∀ i,Integrable (fun ω => v ω i) μ)
    (h2 : ∀ i j,Integrable (fun ω => v ω i*v ω j) μ)
    (hmean : inferenceMean μ v=0)
    (hmom : ∀ i j,(∫ ω,v ω i*v ω j ∂μ)=if i=j then s else 0) :
    inferenceMean μ (fun ω => b+A.mulVec (v ω))=b ∧
    inferenceCov μ (fun ω => b+A.mulVec (v ω))=s • (A*A.transpose) := by
  have hm : ∀ i,(∫ ω,v ω i ∂μ)=0 := fun i => congrFun hmean i
  have hfirst : inferenceMean μ (fun ω => b+A.mulVec (v ω))=b := by
    ext j
    change (∫ ω,b j+A.mulVec (v ω) j ∂μ)=b j
    rw [integral_add (integrable_const _) (integrable_mulVec μ A v h1 j),
      integral_const,integral_mulVec μ A v h1]
    simp [hm]
  refine ⟨hfirst,?_⟩
  ext j l
  unfold inferenceCov
  rw [hfirst]
  simp only [Pi.add_apply,add_sub_cancel_left]
  rw [integral_mulVec_product μ A A v h2 j l]
  simp_rw [hmom]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true,
    Matrix.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl;intro i _
  ring

theorem wild_completed {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) ℝ) (y : Fin n → ℝ)
    (hX : Function.Injective X.mulVec) (v : Ω → Fin n → ℝ)
    (h1 : ∀ i, Integrable (fun ω => v ω i) μ)
    (h2 : ∀ i j, Integrable (fun ω => v ω i*v ω j) μ)
    (hmean : inferenceMean μ v = 0)
    (hmom : ∀ i j,(∫ ω,v ω i*v ω j ∂μ)=if i=j then 1 else 0) :
    let b := (schoolOLSMap X).mulVec y
    let bs := fun ω => (schoolOLSMap X).mulVec
      (X.mulVec b+fun i => schoolResidual X y i*v ω i)
    (∀ ω,bs ω=b+(schoolOLSMap X).mulVec (fun i => schoolResidual X y i*v ω i)) ∧
    inferenceMean μ bs=b ∧ inferenceCov μ bs=schoolHC0 X y := by
  dsimp
  let b := (schoolOLSMap X).mulVec y
  let M : Matrix (Fin k) (Fin n) ℝ := fun j i => schoolOLSMap X j i*schoolResidual X y i
  have heq : (fun ω => (schoolOLSMap X).mulVec
      (X.mulVec b+fun i => schoolResidual X y i*v ω i)) =
      (fun ω => b+M.mulVec (v ω)) := by
    funext ω
    rw [Matrix.mulVec_add,Matrix.mulVec_mulVec,left_inverse X hX,Matrix.one_mulVec]
    congr 1
    ext j
    simp only [Matrix.mulVec,dotProduct,M]
    apply Finset.sum_congr rfl;intro i _
    ring
  have hM := affine_moments μ b M v 1 h1 h2 hmean hmom
  have hCov : M*M.transpose=schoolHC0 X y := by
    ext j l
    change (∑ i,(schoolOLSMap X j i*schoolResidual X y i)*
      (schoolOLSMap X l i*schoolResidual X y i)) =
      ((schoolOLSMap X*Matrix.diagonal (fun i => (schoolResidual X y i)^2))*
        (schoolOLSMap X).transpose) j l
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal,Matrix.transpose_apply]
    apply Finset.sum_congr rfl;intro i _
    ring
  refine ⟨?_,?_,?_⟩
  · intro ω
    change (schoolOLSMap X).mulVec (X.mulVec b+_) = b+_
    rw [Matrix.mulVec_add,Matrix.mulVec_mulVec,left_inverse X hX,Matrix.one_mulVec]
  · rw [heq]
    exact hM.1
  · rw [heq,hM.2,one_smul,hCov]

theorem leverage_completed {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ)
    (hX : Function.Injective X.mulVec) (hn : 0<n) :
    (schoolHat X).transpose=schoolHat X ∧
    schoolHat X*schoolHat X=schoolHat X ∧
    (∀ i,0≤schoolHat X i i ∧ schoolHat X i i≤1) ∧
    (∑ i,schoolHat X i i)=(k:ℝ) ∧
    (∑ i,schoolHat X i i)/(n:ℝ)=(k:ℝ)/n := by
  have hs := hat_symmetric X
  have hi := hat_idempotent X hX
  have hsq : ∀ i,schoolHat X i i=∑ j,(schoolHat X i j)^2 := by
    intro i
    have h := congrFun (congrFun hi i) i
    rw [Matrix.mul_apply] at h
    have hsym : ∀ j,schoolHat X j i=schoolHat X i j := fun j =>
      congrFun (congrFun hs i) j
    simpa only [hsym,pow_two] using h.symm
  have hb : ∀ i,0≤schoolHat X i i ∧ schoolHat X i i≤1 := by
    intro i
    have h0 : 0≤schoolHat X i i := by rw [hsq];exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hle : (schoolHat X i i)^2≤schoolHat X i i := by
      calc
        _ ≤ ∑ j,(schoolHat X i j)^2 :=
          Finset.single_le_sum (fun j _ => sq_nonneg (schoolHat X i j)) (Finset.mem_univ i)
        _ = _ := (hsq i).symm
    exact ⟨h0,by nlinarith⟩
  have ht : (∑ i,schoolHat X i i)=(k:ℝ) := by
    change (schoolHat X).trace=(k:ℝ)
    rw [schoolHat,Matrix.trace_mul_comm,left_inverse X hX]
    simp
  exact ⟨hs,hi,hb,ht,by rw [ht]⟩

theorem integrable_mulVec_product {Ω : Type*} [MeasurableSpace Ω] {n k l : ℕ}
    (μ : Measure Ω) (A : Matrix (Fin k) (Fin n) ℝ) (B : Matrix (Fin l) (Fin n) ℝ)
    (v : Ω → Fin n → ℝ) (h2 : ∀ i j,Integrable (fun ω => v ω i*v ω j) μ)
    (a : Fin k) (b : Fin l) :
    Integrable (fun ω => A.mulVec (v ω) a*B.mulVec (v ω) b) μ := by
  have he : (fun ω => A.mulVec (v ω) a*B.mulVec (v ω) b) =
      (fun ω => ∑ i,∑ j,(A a i*B b j)*(v ω i*v ω j)) := by
    funext ω
    simp only [Matrix.mulVec,dotProduct,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl;intro i _
    apply Finset.sum_congr rfl;intro j _
    ring
  rw [he]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (h2 i j).const_mul (A a i*B b j)))

theorem residual_model {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ)
    (hX : Function.Injective X.mulVec) (β : Fin k → ℝ) (u : Fin n → ℝ) :
    schoolResidual X (X.mulVec β+u) = (1-schoolHat X).mulVec u := by
  unfold schoolResidual schoolHat
  rw [Matrix.mulVec_add,Matrix.mulVec_mulVec,left_inverse X hX,Matrix.one_mulVec,
    Matrix.mulVec_add,Matrix.sub_mulVec,Matrix.one_mulVec,←Matrix.mulVec_mulVec]
  ext i
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

theorem ols_covariance_matrix {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ)
    (hX : Function.Injective X.mulVec) :
    schoolOLSMap X*(schoolOLSMap X).transpose=(X.transpose*X)⁻¹ := by
  unfold schoolOLSMap
  simp only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_nonsing_inv]
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc X.transpose X _,
    Matrix.mul_nonsing_inv _ (gram_unit X hX),Matrix.mul_one]

theorem symmetric_projection_rows {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hs : P.transpose=P) (hi : P*P=P) : ∀ i,∑ j,(P i j)^2=P i i := by
  intro i
  have h := congrFun (congrFun hi i) i
  rw [Matrix.mul_apply] at h
  have hsym : ∀ j,P j i=P i j := fun j => congrFun (congrFun hs i) j
  simpa only [hsym,pow_two] using h

theorem sandwich_entry {n k : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (d : Fin n → ℝ) (j l : Fin k) :
    (A*Matrix.diagonal d*A.transpose) j l=∑ i,(A j i*A l i)*d i := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply]
  apply Finset.sum_congr rfl;intro i _;ring

theorem hc0_completed {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) ℝ) (hX : Function.Injective X.mulVec)
    (β : Fin k → ℝ) (σ2 : ℝ) (hσ : 0≤σ2) (u : Ω → Fin n → ℝ)
    (h1 : ∀ i,Integrable (fun ω => u ω i) μ)
    (h2 : ∀ i j,Integrable (fun ω => u ω i*u ω j) μ)
    (hmean : inferenceMean μ u=0)
    (hmom : ∀ i j,(∫ ω,u ω i*u ω j ∂μ)=if i=j then σ2 else 0) :
    let y := fun ω => X.mulVec β+u ω
    let A := schoolOLSMap X
    let H := schoolHat X
    let V := inferenceCov μ (fun ω => A.mulVec (y ω))
    let EV : Matrix (Fin k) (Fin k) ℝ := fun j l => ∫ ω,schoolHC0 X (y ω) j l ∂μ
    (∀ ω,schoolResidual X (y ω)=(1-H).mulVec (u ω)) ∧
    (∀ i,(∫ ω,(schoolResidual X (y ω) i)^2 ∂μ)=σ2*(1-H i i)) ∧
    V=σ2 • (A*A.transpose) ∧ V=σ2 • (X.transpose*X)⁻¹ ∧
    EV=σ2 • (A*Matrix.diagonal (fun i => 1-H i i)*A.transpose) ∧
    V-EV=σ2 • (A*Matrix.diagonal (fun i => H i i)*A.transpose) ∧
    (∀ t,0≤dotProduct t ((V-EV).mulVec t)) := by
  dsimp
  let A := schoolOLSMap X
  let H := schoolHat X
  let R := 1-H
  have hres : ∀ ω,schoolResidual X (X.mulVec β+u ω)=R.mulVec (u ω) :=
    fun ω => residual_model X hX β (u ω)
  have hs : R.transpose=R := by simp only [R,H,Matrix.transpose_sub,Matrix.transpose_one,hat_symmetric]
  have hi : R*R=R := by
    dsimp only [R]
    simp only [sub_mul,mul_sub,one_mul,mul_one,show H*H=H from hat_idempotent X hX]
    abel
  have he2 : ∀ i,(∫ ω,(schoolResidual X (X.mulVec β+u ω) i)^2 ∂μ)=σ2*(1-H i i) := by
    intro i
    simp_rw [hres,pow_two]
    rw [integral_mulVec_product μ R R u h2 i i]
    simp_rw [hmom]
    simp only [mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
    rw [show (∑ j,R i j*R i j*σ2)=σ2*(∑ j,(R i j)^2) by
      rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro j _;ring,
      symmetric_projection_rows R hs hi i]
    simp [R,Matrix.sub_apply,Matrix.one_apply]
  have hcov : inferenceCov μ (fun ω => A.mulVec (X.mulVec β+u ω))=
      σ2 • (A*A.transpose) := by
    have he : (fun ω => A.mulVec (X.mulVec β+u ω))=(fun ω => β+A.mulVec (u ω)) := by
      funext ω
      rw [Matrix.mulVec_add,Matrix.mulVec_mulVec,left_inverse X hX,Matrix.one_mulVec]
    rw [he]
    exact (affine_moments μ β A u σ2 h1 h2 hmean hmom).2
  let EV : Matrix (Fin k) (Fin k) ℝ := fun j l => ∫ ω,schoolHC0 X (X.mulVec β+u ω) j l ∂μ
  have hev : EV =
      σ2 • (A*Matrix.diagonal (fun i => 1-H i i)*A.transpose) := by
    ext j l
    have he : (fun ω => schoolHC0 X (X.mulVec β+u ω) j l) =
        (fun ω => ∑ i,(A j i*A l i)*(schoolResidual X (X.mulVec β+u ω) i)^2) := by
      funext ω
      simp only [schoolHC0,sandwich_entry,A]
    change (∫ ω,schoolHC0 X (X.mulVec β+u ω) j l ∂μ)=_
    rw [he,integral_finsetSum _ (fun i _ => by
      have h := (integrable_mulVec_product μ R R u h2 i i).const_mul (A j i*A l i)
      simpa only [←pow_two,←hres] using h)]
    simp only [integral_const_mul,he2,Matrix.smul_apply,smul_eq_mul,sandwich_entry]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl;intro i _;ring
  have hdiff : inferenceCov μ (fun ω => A.mulVec (X.mulVec β+u ω))-
      EV=
      σ2 • (A*Matrix.diagonal (fun i => H i i)*A.transpose) := by
    rw [hcov,hev,←smul_sub]
    congr 1
    ext j l
    change (A*A.transpose) j l-(A*Matrix.diagonal (fun i => 1-H i i)*A.transpose) j l =
      (A*Matrix.diagonal (fun i => H i i)*A.transpose) j l
    rw [sandwich_entry,sandwich_entry,Matrix.mul_apply]
    simp only [Matrix.transpose_apply,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl;intro i _;ring
  refine ⟨hres,he2,hcov,?_,hev,hdiff,?_⟩
  · rw [hcov,ols_covariance_matrix X hX]
  · intro t
    rw [hdiff,Matrix.smul_mulVec,dotProduct_smul]
    apply mul_nonneg hσ
    have ht : dotProduct t ((A*Matrix.diagonal (fun i => H i i)*A.transpose).mulVec t)=
        ∑ i,H i i*((A.transpose.mulVec t) i)^2 := by
      rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,
        ←Matrix.mulVec_transpose]
      simp only [dotProduct]
      apply Finset.sum_congr rfl;intro i _
      have hd : (Matrix.diagonal (fun j => H j j)).mulVec (A.transpose.mulVec t) i =
          H i i*(A.transpose.mulVec t i) := by
        simp [Matrix.mulVec,dotProduct,Matrix.diagonal_apply]
      rw [hd]
      ring
    rw [ht]
    apply Finset.sum_nonneg
    intro i _
    have hh : 0≤H i i := by
      rw [←symmetric_projection_rows H (hat_symmetric X) (hat_idempotent X hX) i]
      exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
    exact mul_nonneg hh (sq_nonneg _)

end
end InferenceCompletion

/-- T18(b): raw residual multipliers with zero means and identity second
moments reproduce HC0 exactly. These moment assumptions cover independent
standard normals; no bootstrap calibration or exact test size is asserted. -/
theorem wild_bootstrap_is_hc0 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) ℝ) (y : Fin n → ℝ)
    (hX : Function.Injective X.mulVec) (v : Ω → Fin n → ℝ)
    (h1 : ∀ i, Integrable (fun ω => v ω i) μ)
    (h2 : ∀ i j, Integrable (fun ω => v ω i*v ω j) μ)
    (hmean : inferenceMean μ v = 0)
    (hmom : ∀ i j, (∫ ω, v ω i*v ω j ∂μ) = if i=j then 1 else 0) :
    let b := (schoolOLSMap X).mulVec y
    let bs := fun ω => (schoolOLSMap X).mulVec
      (X.mulVec b + fun i => schoolResidual X y i*v ω i)
    (∀ ω, bs ω = b + (schoolOLSMap X).mulVec
      (fun i => schoolResidual X y i*v ω i)) ∧
    inferenceMean μ bs = b ∧ inferenceCov μ bs = schoolHC0 X y := by
  exact InferenceCompletion.wild_completed μ X y hX v h1 h2 hmean hmom

/-- T18(c): the full-rank OLS hat matrix is a symmetric projection;
its diagonal is in [0,1], its trace is k, and (for n>0) mean leverage is k/n. -/
theorem school_leverage_facts {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ)
    (hX : Function.Injective X.mulVec) (hn : 0 < n) :
    (schoolHat X).transpose = schoolHat X ∧
    schoolHat X * schoolHat X = schoolHat X ∧
    (∀ i, 0 ≤ schoolHat X i i ∧ schoolHat X i i ≤ 1) ∧
    (∑ i, schoolHat X i i) = (k:ℝ) ∧
    (∑ i, schoolHat X i i)/(n:ℝ) = (k:ℝ)/n := by
  exact InferenceCompletion.leverage_completed X hX hn

/-- T18(d): under an independent homoskedastic benchmark,
the expected HC0 shortfall is σ² A diag(h) A', a positive semidefinite matrix.
Zero error means and σ²I second moments suffice; this is not an assumption
of the paper's randomization interpretation. -/
theorem hc0_homoskedastic_shortfall {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) ℝ) (hX : Function.Injective X.mulVec)
    (β : Fin k → ℝ) (σ2 : ℝ) (hσ : 0 ≤ σ2) (u : Ω → Fin n → ℝ)
    (h1 : ∀ i, Integrable (fun ω => u ω i) μ)
    (h2 : ∀ i j, Integrable (fun ω => u ω i*u ω j) μ)
    (hmean : inferenceMean μ u = 0)
    (hmom : ∀ i j, (∫ ω, u ω i*u ω j ∂μ) = if i=j then σ2 else 0) :
    let y := fun ω => X.mulVec β + u ω
    let A := schoolOLSMap X
    let H := schoolHat X
    let V := inferenceCov μ (fun ω => A.mulVec (y ω))
    let EV : Matrix (Fin k) (Fin k) ℝ := fun j l => ∫ ω, schoolHC0 X (y ω) j l ∂μ
    (∀ ω, schoolResidual X (y ω) = (1-H).mulVec (u ω)) ∧
    (∀ i, (∫ ω, (schoolResidual X (y ω) i)^2 ∂μ) = σ2*(1-H i i)) ∧
    V = σ2 • (A*A.transpose) ∧ V = σ2 • (X.transpose*X)⁻¹ ∧
    EV = σ2 • (A*Matrix.diagonal (fun i => 1-H i i)*A.transpose) ∧
    V-EV = σ2 • (A*Matrix.diagonal (fun i => H i i)*A.transpose) ∧
    (∀ t, 0 ≤ dotProduct t ((V-EV).mulVec t)) := by
  exact InferenceCompletion.hc0_completed μ X hX β σ2 hσ u h1 h2 hmean hmom

/-- T18(d), finite row lemma: the leverage-weighted HC0 expectation ratio
is 1 minus a nonnegative weighted leverage; equality requires all active
leverage entries to be zero. The positive row norm excludes division by zero. -/
theorem hc0_row_bias_factor {n : ℕ} (a h : Fin n → ℝ)
    (hh : ∀ i, 0 ≤ h i ∧ h i ≤ 1) (ha : 0 < ∑ i, (a i)^2) :
    (∑ i, (a i)^2*(1-h i))/(∑ i, (a i)^2) =
      1-(∑ i, (a i)^2*h i)/(∑ i, (a i)^2) ∧
    (∑ i, (a i)^2*(1-h i))/(∑ i, (a i)^2) ≤ 1 ∧
    ((∑ i, (a i)^2*(1-h i))/(∑ i, (a i)^2) = 1 ↔
      ∀ i, a i ≠ 0 → h i = 0) := by
  have hs : (∑ i, (a i)^2*(1-h i)) =
      (∑ i, (a i)^2)-(∑ i, (a i)^2*h i) := by
    simp [mul_sub, Finset.sum_sub_distrib]
  have hn : 0 ≤ ∑ i, (a i)^2*h i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (hh i).1)
  have hid : (∑ i, (a i)^2*(1-h i))/(∑ i, (a i)^2) =
      1-(∑ i, (a i)^2*h i)/(∑ i, (a i)^2) := by
    rw [hs, sub_div, div_self (ne_of_gt ha)]
  refine ⟨hid, ?_, ?_⟩
  · rw [hid]; exact sub_le_self _ (div_nonneg hn ha.le)
  · rw [hid]
    constructor
    · intro heq i hai
      have hz : (∑ i, (a i)^2*h i) = 0 := by
        have : (∑ i, (a i)^2*h i)/(∑ i, (a i)^2) = 0 := by linarith
        exact (div_eq_zero_iff).mp this |>.resolve_right (ne_of_gt ha)
      have hi : (a i)^2*h i ≤ ∑ j, (a j)^2*h j :=
        Finset.single_le_sum (fun j _ => mul_nonneg (sq_nonneg _) (hh j).1)
          (Finset.mem_univ i)
      have hp : 0 < (a i)^2 := sq_pos_of_ne_zero hai
      rw [hz] at hi
      nlinarith [(hh i).1]
    · intro heq
      have hz : (∑ i, (a i)^2*h i) = 0 := by
        apply Finset.sum_eq_zero; intro i _
        by_cases hai : a i=0
        · simp [hai]
        · simp [heq i hai]
      rw [hz]; simp

/-- Fig. 2 caption, main p. 569: "conditional average potential outcome"
and "95% confidence intervals ... heteroskedasticity-robust SEs".
The averaged prediction row is evaluated with the covariance of the same fit. -/
noncomputable def predictionVariance {k : ℕ}
    (V : Matrix (Fin k) (Fin k) ℝ) (l : Fin k → ℝ) : ℝ :=
  dotProduct l (V.mulVec l)


/-- T24(c): a predicted treatment mean has control-level variance plus
contrast variance plus twice the covariance; equality with contrast variance
has the stated necessary and sufficient condition. -/
theorem prediction_mean_contrast_variance {k : ℕ}
    (V : Matrix (Fin k) (Fin k) ℝ) (hV : V.transpose=V)
    (l0 d : Fin k → ℝ) :
    predictionVariance V (l0+d) = predictionVariance V l0 +
      predictionVariance V d + 2*dotProduct l0 (V.mulVec d) ∧
    (predictionVariance V (l0+d) = predictionVariance V d ↔
      predictionVariance V l0 + 2*dotProduct l0 (V.mulVec d)=0) := by
  have hsym : dotProduct d (V.mulVec l0) = dotProduct l0 (V.mulVec d) := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    have hij : V j i=V i j := by simpa using congrFun (congrFun hV i) j
    rw [hij]; ring
  have h : predictionVariance V (l0+d) = predictionVariance V l0 +
      predictionVariance V d + 2*dotProduct l0 (V.mulVec d) := by
    simp only [predictionVariance, Matrix.mulVec_add, dotProduct_add,
      add_dotProduct, hsym]
    ring
  exact ⟨h, by rw [h]; constructor <;> intro he <;> linarith⟩

/-- T23: six groups of identical rows, with multiplicities 14,14,7,7,7,7.
This count representation is exactly 56 observations, not six unweighted
observations. It contains no empirical respondent records. -/
def bandMultiplicity : Fin 6 → ℝ := ![14,14,7,7,7,7]
def bandTreatment : Fin 6 → ℝ := ![0,0,1,1,1,1]
noncomputable def bandComposition : Fin 6 → ℝ := ![0,0,0,0,1/5,1/5]
noncomputable def bandOutcome : Fin 6 → ℝ := ![0,1/5,1/10,3/10,2/5,3/5]
noncomputable def bandRow (i : Fin 6) : Fin 3 → ℝ :=
  ![1,bandTreatment i,bandTreatment i*bandComposition i]
noncomputable def bandCoefficient : Fin 3 → ℝ := ![1/10,1/10,3/2]
noncomputable def bandInverseGram : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1/28,-1/28,0; -1/28,3/28,-5/14; 0,-5/14,25/7]
noncomputable def bandCovariance : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1/2800,-1/2800,0; -1/2800,3/2800,-1/280; 0,-1/280,1/28]
noncomputable def bandGram : Matrix (Fin 3) (Fin 3) ℝ :=
  fun j l => ∑ i, bandMultiplicity i*bandRow i j*bandRow i l
noncomputable def bandRhs : Fin 3 → ℝ :=
  fun j => ∑ i, bandMultiplicity i*bandRow i j*bandOutcome i
noncomputable def bandMeat : Matrix (Fin 3) (Fin 3) ℝ :=
  fun j l => ∑ i, bandMultiplicity i*(bandOutcome i-dotProduct (bandRow i) bandCoefficient)^2*
    bandRow i j*bandRow i l

/-- T23(i),(ii): explicit inverse and normal-equation certificates for
the full 56-row OLS fit, and its actual grouped HC0 sandwich covariance. -/
theorem band_ols_hc0_certificate :
    (∑ i, bandMultiplicity i)=56 ∧
    (∑ i, bandMultiplicity i*bandTreatment i)=28 ∧
    bandInverseGram*bandGram=1 ∧
    bandGram.mulVec bandCoefficient=bandRhs ∧
    (∀ i, |bandOutcome i-dotProduct (bandRow i) bandCoefficient|=1/10) ∧
    bandInverseGram*bandMeat*bandInverseGram.transpose=bandCovariance := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [bandMultiplicity, Fin.sum_univ_succ]
  · norm_num [bandMultiplicity, bandTreatment, Fin.sum_univ_succ]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [bandInverseGram, bandGram, bandMultiplicity, bandRow,
        bandTreatment, bandComposition, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i; fin_cases i <;>
      norm_num [bandGram, bandRhs, bandMultiplicity, bandRow, bandTreatment,
        bandComposition, bandOutcome, bandCoefficient, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]
  · intro i; fin_cases i <;>
      norm_num [bandOutcome, bandRow, bandTreatment, bandComposition,
        bandCoefficient, dotProduct, Fin.sum_univ_succ]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [bandInverseGram, bandMeat, bandCovariance, bandMultiplicity,
        bandRow, bandTreatment, bandComposition, bandOutcome, bandCoefficient,
        Matrix.mul_apply, Matrix.vecMul, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]

/-- T23(iii)--(v): in this fitted data set the robust variances of the
two means are 1/2800, the treatment-band contrast variance is 1/1400,
and the code's control residual-variance/56 is 1/5400. The two variances
used by the code differ from those of the quantities drawn. -/
theorem band_counterexample_values :
    dotProduct (![1,0,0] : Fin 3 → ℝ) bandCoefficient=1/10 ∧
    dotProduct (![1,1,1/10] : Fin 3 → ℝ) bandCoefficient=7/20 ∧
    predictionVariance bandCovariance ![1,0,0]=1/2800 ∧
    predictionVariance bandCovariance ![1,1,1/10]=1/2800 ∧
    predictionVariance bandCovariance ![0,1,1/10]=1/1400 ∧
    dotProduct (![1,0,0] : Fin 3 → ℝ) (bandCovariance.mulVec ![0,1,1/10])=-1/2800 ∧
    ((28/100:ℝ)/27)/56=1/5400 ∧
    (1/1400:ℝ)>1/2800 ∧ (1/5400:ℝ)<1/2800 ∧
    (1/5400:ℝ)/(1/2800)=14/27 ∧ ((28/100:ℝ)/27)/28≠1/2800 := by
  norm_num [predictionVariance, bandCovariance, bandCoefficient,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-! Exact invertible shear for recentering an interaction regression. -/
namespace RefitCompletion
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

theorem map_reparam {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ)
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : IsUnit S.det) :
    schoolOLSMap (X*S)=S⁻¹*schoolOLSMap X := by
  have hg : (X*S).transpose*(X*S)=S.transpose*(X.transpose*X)*S := by
    simp only [Matrix.transpose_mul,Matrix.mul_assoc]
  unfold schoolOLSMap
  rw [hg,Matrix.mul_inv_rev,Matrix.mul_inv_rev,Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc S.transpose⁻¹ S.transpose X.transpose,
    Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_transpose _ hS),Matrix.one_mul]

theorem prediction_reparam {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ)
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : IsUnit S.det) (y : Fin n → ℝ) :
    (X*S).mulVec ((schoolOLSMap (X*S)).mulVec y)=X.mulVec ((schoolOLSMap X).mulVec y) := by
  rw [map_reparam X S hS,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
  congr 1
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hS,Matrix.one_mulVec]

theorem residual_reparam {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ)
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : IsUnit S.det) (y : Fin n → ℝ) :
    schoolResidual (X*S) y=schoolResidual X y := by
  unfold schoolResidual
  rw [prediction_reparam X S hS]

theorem hc0_reparam {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ)
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : IsUnit S.det) (y : Fin n → ℝ) :
    schoolHC0 (X*S) y=S⁻¹*schoolHC0 X y*S⁻¹.transpose := by
  unfold schoolHC0
  rw [map_reparam X S hS,residual_reparam X S hS,Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

def design {n p : ℕ} (T C : Fin n → ℝ) (z : Matrix (Fin n) (Fin p) ℝ) :
    Matrix (Fin n) (Fin (3+p)) ℝ := fun i j =>
  if h0 : j.val=0 then 1 else if h1 : j.val=1 then T i else if h2 : j.val=2 then T i*C i
  else z i ⟨j.val-3,by omega⟩

theorem design_shear {n p : ℕ} (T C : Fin n → ℝ)
    (z : Matrix (Fin n) (Fin p) ℝ) (c : ℝ) :
    design T (fun i => C i-c) z = design T C z*
      Matrix.transvection (⟨1,by omega⟩ : Fin (3+p)) ⟨2,by omega⟩ (-c) := by
  ext i j
  by_cases hj : j=(⟨2,by omega⟩ : Fin (3+p))
  · subst j
    rw [Matrix.mul_transvection_apply_same]
    norm_num [design]
    ring
  · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ hj]
    have hjv : j.val≠2 := by intro h;apply hj;exact Fin.ext h
    simp [design,hjv]

theorem hc0_symmetric {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ) (y : Fin n → ℝ) :
    (schoolHC0 X y).transpose=schoolHC0 X y := by
  simp only [schoolHC0,Matrix.transpose_mul,Matrix.transpose_transpose,
    Matrix.diagonal_transpose,Matrix.mul_assoc]

theorem shear_right_entry {q : ℕ} (i j : Fin q) (c : ℝ)
    (M : Matrix (Fin q) (Fin q) ℝ) (a : Fin q) :
    (M*(Matrix.transvection i j c).transpose) a i=M a i+c*M a j := by
  change ((M*(Matrix.transvection i j c).transpose).transpose) i a = _
  rw [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transvection_mul_apply_same]
  rfl

theorem completed {n p : ℕ} (T C : Fin n → ℝ) (z : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) (c : ℝ) :
    let X : Matrix (Fin n) (Fin (3+p)) ℝ := fun i j =>
      if h0 : j.val=0 then 1 else if h1 : j.val=1 then T i else if h2 : j.val=2 then T i*C i
      else z i ⟨j.val-3,by omega⟩
    let Xc : Matrix (Fin n) (Fin (3+p)) ℝ := fun i j =>
      if h0 : j.val=0 then 1 else if h1 : j.val=1 then T i else if h2 : j.val=2 then T i*(C i-c)
      else z i ⟨j.val-3,by omega⟩
    let b := (schoolOLSMap X).mulVec y
    let bc := (schoolOLSMap Xc).mulVec y
    let V := schoolHC0 X y
    Function.Injective X.mulVec →
      Xc.mulVec bc=X.mulVec b ∧ schoolResidual Xc y=schoolResidual X y ∧
      bc ⟨1,by omega⟩=b ⟨1,by omega⟩+c*b ⟨2,by omega⟩ ∧
      schoolHC0 Xc y ⟨1,by omega⟩ ⟨1,by omega⟩=
        V ⟨1,by omega⟩ ⟨1,by omega⟩+
        2*c*V ⟨1,by omega⟩ ⟨2,by omega⟩+
        c^2*V ⟨2,by omega⟩ ⟨2,by omega⟩ := by
  let X := design T C z
  let Xc := design T (fun i => C i-c) z
  let a : Fin (3+p) := ⟨1,by omega⟩
  let b : Fin (3+p) := ⟨2,by omega⟩
  let S := Matrix.transvection a b (-c)
  let R := Matrix.transvection a b c
  change Function.Injective X.mulVec →
    Xc.mulVec ((schoolOLSMap Xc).mulVec y)=X.mulVec ((schoolOLSMap X).mulVec y) ∧
    schoolResidual Xc y=schoolResidual X y ∧
    (schoolOLSMap Xc).mulVec y a=(schoolOLSMap X).mulVec y a+c*(schoolOLSMap X).mulVec y b ∧
    schoolHC0 Xc y a a=schoolHC0 X y a a+2*c*schoolHC0 X y a b+c^2*schoolHC0 X y b b
  intro _hX
  have hab : a≠b := by intro h;have := congrArg Fin.val h;norm_num [a,b] at this
  have hS : IsUnit S.det := by
    dsimp only [S]
    rw [Matrix.det_transvection_of_ne a b hab]
    exact isUnit_one
  have hinv : S⁻¹=R := by
    apply Matrix.inv_eq_left_inv
    dsimp only [S,R]
    rw [Matrix.transvection_mul_transvection_same a b hab]
    simp
  have hXc : Xc=X*S := design_shear T C z c
  have hmap : schoolOLSMap Xc=R*schoolOLSMap X := by rw [hXc,map_reparam X S hS,hinv]
  refine ⟨?_,?_,?_,?_⟩
  · rw [hXc]
    exact prediction_reparam X S hS y
  · rw [hXc]
    exact residual_reparam X S hS y
  · rw [hmap,←Matrix.mulVec_mulVec]
    dsimp only [R]
    rw [Matrix.transvection,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.single_mulVec]
    simp
  · rw [hXc,hc0_reparam X S hS y,hinv]
    dsimp only [R]
    rw [shear_right_entry,Matrix.transvection_mul_apply_same,
      Matrix.transvection_mul_apply_same]
    have hsym : schoolHC0 X y b a=schoolHC0 X y a b :=
      congrFun (congrFun (hc0_symmetric X y) a) b
    rw [hsym]
    ring

end
end RefitCompletion

/-- T24(a),(d): for an interaction model with arbitrary fixed nuisance
columns, recentering TC to T(C-c) preserves predictions and residuals;
the new treatment coefficient and its HC0 variance are the contrast,
not the treatment group's predicted mean. All refits use the same schools. -/
theorem centered_refit_is_contrast {n p : ℕ}
    (T C : Fin n → ℝ) (z : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) (c : ℝ) :
    let X : Matrix (Fin n) (Fin (3+p)) ℝ := fun i j =>
      if h0 : j.val=0 then 1 else if h1 : j.val=1 then T i else if h2 : j.val=2 then T i*C i
      else z i ⟨j.val-3, by omega⟩
    let Xc : Matrix (Fin n) (Fin (3+p)) ℝ := fun i j =>
      if h0 : j.val=0 then 1 else if h1 : j.val=1 then T i else if h2 : j.val=2 then T i*(C i-c)
      else z i ⟨j.val-3, by omega⟩
    let b := (schoolOLSMap X).mulVec y
    let bc := (schoolOLSMap Xc).mulVec y
    let V := schoolHC0 X y
    Function.Injective X.mulVec →
      Xc.mulVec bc=X.mulVec b ∧ schoolResidual Xc y=schoolResidual X y ∧
      bc ⟨1, by omega⟩=b ⟨1, by omega⟩+c*b ⟨2, by omega⟩ ∧
      schoolHC0 Xc y ⟨1, by omega⟩ ⟨1, by omega⟩=
        V ⟨1, by omega⟩ ⟨1, by omega⟩+
        2*c*V ⟨1, by omega⟩ ⟨2, by omega⟩+
        c^2*V ⟨2, by omega⟩ ⟨2, by omega⟩ := by
  exact RefitCompletion.completed T C z y c

/-- T23(iv): the centered 56-school design at c=.1, with exactly the
same multiplicities as the original data. Its treatment column estimates
the contrast; the coefficient is .25, not the level .35. -/
noncomputable def bandCenteredRow (i : Fin 6) : Fin 3 → ℝ :=
  ![1,bandTreatment i,bandTreatment i*(bandComposition i-1/10)]
noncomputable def bandCenteredCoefficient : Fin 3 → ℝ := ![1/10,1/4,3/2]
noncomputable def bandCenteredInverse : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1/28,-1/28,0;-1/28,1/14,0;0,0,25/7]

/-- The Gram matrix and HC0 meat of the centered, multiplicity-weighted fit. -/
noncomputable def bandCenteredGram : Matrix (Fin 3) (Fin 3) ℝ :=
  fun j l => ∑ i, bandMultiplicity i*bandCenteredRow i j*bandCenteredRow i l
noncomputable def bandCenteredMeat : Matrix (Fin 3) (Fin 3) ℝ :=
  fun j l => ∑ i, bandMultiplicity i*(bandOutcome i-
    dotProduct (bandCenteredRow i) bandCenteredCoefficient)^2*
      bandCenteredRow i j*bandCenteredRow i l

/-- T23(iv): inverse, normal-equation, residual and actual HC0 variance
certificates for the centered refit. This completes the concrete connection
between the code's refit SE and the wrong treatment-level band. -/
theorem band_centered_refit_certificate :
    bandCenteredInverse*bandCenteredGram=1 ∧
    bandCenteredGram.mulVec bandCenteredCoefficient=(fun j => ∑ i,
      bandMultiplicity i*bandCenteredRow i j*bandOutcome i) ∧
    (∀ i, dotProduct (bandCenteredRow i) bandCenteredCoefficient=
      dotProduct (bandRow i) bandCoefficient) ∧
    (bandCenteredInverse*bandCenteredMeat*bandCenteredInverse.transpose) 1 1=1/1400 := by
  refine ⟨?_,?_,?_,?_⟩
  · ext j l; fin_cases j <;> fin_cases l <;>
      norm_num [bandCenteredGram,bandCenteredInverse,bandCenteredRow,bandMultiplicity,
        bandTreatment,bandComposition,Matrix.mul_apply,Fin.sum_univ_succ]
  · ext j; fin_cases j <;>
      norm_num [bandCenteredGram,bandCenteredCoefficient,bandCenteredRow,bandMultiplicity,
        bandTreatment,bandComposition,bandOutcome,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  · intro i; fin_cases i <;>
      norm_num [bandCenteredCoefficient,bandCenteredRow,bandRow,bandCoefficient,
        bandTreatment,bandComposition,dotProduct,Fin.sum_univ_succ]
  · norm_num [bandCenteredMeat,bandCenteredInverse,bandCenteredRow,bandCenteredCoefficient,
      bandMultiplicity,bandTreatment,bandComposition,bandOutcome,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]


/-- T24(a): the averaged prediction rows l0=(1,0,0,zbar) and
l1(c)=(1,1,c,zbar), with coefficients ordered (alpha,tau,beta,eta).
The sum type is simply a finite indexing of the three model columns and
the nuisance columns; it represents the same row as concatenation. -/
theorem interaction_prediction_rows {p : ℕ} (zbar : Fin p → ℝ)
    (b : (Fin 3 ⊕ Fin p) → ℝ) (c : ℝ) :
    dotProduct (Sum.elim (![1,0,0] : Fin 3 → ℝ) zbar) b=
      b (.inl 0)+(∑ j, zbar j*b (.inr j)) ∧
    dotProduct (Sum.elim (![1,1,c] : Fin 3 → ℝ) zbar) b=
      b (.inl 0)+b (.inl 1)+c*b (.inl 2)+(∑ j, zbar j*b (.inr j)) ∧
    dotProduct (Sum.elim (![1,1,c] : Fin 3 → ℝ) zbar) b-
      dotProduct (Sum.elim (![1,0,0] : Fin 3 → ℝ) zbar) b=
        b (.inl 1)+c*b (.inl 2) := by
  simp only [dotProduct,Fintype.sum_sum_type,Fin.sum_univ_succ]
  norm_num
  ring

end AronowAudit.P037

