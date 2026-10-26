import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

namespace AronowAudit.P037
open scoped BigOperators
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

/-- SI p. 19: ξhat(d_k)=argmin Σ_{D_i=d_k}(1/π_i(d_k))[y_i-g(x_i,ξ)]².
The predicate keeps the actual least-squares objective; a minimizer is not
replaced by an arbitrary vector satisfying assumed numerical outputs. -/
def regressionMinimum {I K : Type*} [Fintype I] [Fintype K]
    (w : I → ℝ) (X : Matrix I K ℝ) (Y : I → ℝ) (b : K → ℝ) : Prop :=
  ∀ c : K → ℝ, (∑ i, w i*(Y i-X.mulVec b i)^2)≤
    (∑ i, w i*(Y i-X.mulVec c i)^2)

/-- T28,T34: actual WLS coefficient map (X'WX)⁻¹X'W.
Positive weights/full rank are explicit hypotheses of the general results. -/
noncomputable def regressionMap {I K : Type*} [Fintype I] [Fintype K] [DecidableEq K]
    (w : I → ℝ) (X : Matrix I K ℝ) : Matrix K I ℝ :=
  (X.transpose*Matrix.diagonal w*X)⁻¹*X.transpose*Matrix.diagonal w

/-- T28(a), released script 3: joint design with four exposure intercepts
and shared covariate slopes; it is distinct from the printed separate fits. -/
def pooledExposureRow {I : Type*} {p : ℕ} (D : I → Fin 4)
    (x : I → Fin p → ℝ) : Matrix I (Fin (4+p)) ℝ := fun i j =>
  if h : j.val<4 then (if D i=⟨j.val,h⟩ then 1 else 0)
  else x i ⟨j.val-4, by omega⟩

/-- T28(b): the separate linear regression has its own intercept and
covariate slopes in each exposure. Weights are masked by observed exposure. -/
def separateExposureRow {I : Type*} {p : ℕ} (x : I → Fin p → ℝ)
    : Matrix I (Fin (1+p)) ℝ := fun i j =>
  if h : j.val=0 then 1 else x i ⟨j.val-1, by omega⟩

/-- T28,T42: augmented residual-plus-prediction average over the same
fixed set A, here indexed by I. N=card I is the actual averaging denominator. -/
noncomputable def augmentedExposureMean {I : Type*} [Fintype I]
    (D : I → Fin 4) (w Y fitted : I → ℝ) (k : Fin 4) : ℝ :=
  (∑ i, ((if D i=k then w i*(Y i-fitted i) else 0)+fitted i))/(Fintype.card I:ℝ)

namespace RegressionCompletion
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem normal_of_minimum {I K : Type*} [Fintype I] [Fintype K]
    (w : I → ℝ) (X : Matrix I K ℝ) (Y : I → ℝ) (b : K → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hb : regressionMinimum w X Y b) :
    ∀ j, (∑ i, w i * (Y i-X.mulVec b i) * X i j) = 0 := by
  classical
  intro j
  let A := ∑ i, w i * (Y i-X.mulVec b i) * X i j
  let B := ∑ i, w i * (X i j)^2
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
  have hquad (t : ℝ) : 0 ≤ t^2*B-2*t*A := by
    let c : K → ℝ := fun k => b k + if k=j then t else 0
    have hpred (i : I) : X.mulVec c i = X.mulVec b i + t*X i j := by
      simp [c, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib,
        mul_ite, Finset.sum_ite_eq', mul_comm]
    have h := hb c
    have heq : (∑ i, w i*(Y i-X.mulVec c i)^2) =
        (∑ i, w i*(Y i-X.mulVec b i)^2) + (t^2*B-2*t*A) := by
      simp only [hpred]
      calc
        _ = ∑ i, (w i*(Y i-X.mulVec b i)^2 +
            t^2*(w i*(X i j)^2) - (2*t)*(w i*(Y i-X.mulVec b i)*X i j)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
          dsimp only [A, B]
          ring
    rw [heq] at h
    linarith
  have hden : B+1 ≠ 0 := by linarith
  have h := mul_nonneg (hquad (A/(B+1))) (sq_nonneg (B+1))
  have heq : ((A/(B+1))^2*B-2*(A/(B+1))*A)*(B+1)^2 = -A^2*(B+2) := by
    field_simp
    ring
  rw [heq] at h
  have hs : A^2=0 := by nlinarith [sq_nonneg A, mul_nonneg hB (sq_nonneg A)]
  exact sq_eq_zero_iff.mp hs

theorem pooled_prediction {I : Type*} [Fintype I] {p : ℕ}
    (D : I → Fin 4) (x : I → Fin p → ℝ) (b : Fin (4+p) → ℝ) (i : I) :
    (pooledExposureRow D x).mulVec b i =
      b ((D i).castAdd p) + ∑ j, x i j*b ⟨4+j.val, by omega⟩ := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, pooledExposureRow]
  simp
  apply Finset.sum_congr rfl
  intro j _
  congr 1

theorem separate_prediction {I : Type*} [Fintype I] {p : ℕ}
    (x : I → Fin p → ℝ) (b : Fin (1+p) → ℝ) (i : I) :
    (separateExposureRow x).mulVec b i =
      b ⟨0, by omega⟩ + ∑ j, x i j*b ⟨1+j.val, by omega⟩ := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, separateExposureRow]
  simp
  congr 1

end RegressionCompletion

open RegressionCompletion

/-- T28(a)--(c): positive-weight full-rank joint and separate argmins
have zero weighted residual sums within every exposure. Their augmented
means are the average predictions; pooled contrasts are intercept differences.
This theorem uses the same weights in residual corrections and fitting. -/
theorem pooled_and_separate_mean_identities {I : Type*} [Fintype I]
    {p : ℕ} (hI : 0<Fintype.card I) (D : I → Fin 4)
    (w Y : I → ℝ) (hw : ∀ i, 0<w i) (x : I → Fin p → ℝ)
    (b : Fin (4+p) → ℝ) (s : Fin 4 → Fin (1+p) → ℝ)
    (hpooled : Function.Injective (Matrix.mulVec (pooledExposureRow D x)))
    (hseparate : ∀ k, Function.Injective
      (fun v => fun i : {i : I // D i=k} => (Matrix.mulVec (separateExposureRow x)) v i.val))
    (hb : regressionMinimum w (pooledExposureRow D x) Y b)
    (hs : ∀ k, regressionMinimum (fun i => if D i=k then w i else 0)
      (separateExposureRow x) Y (s k)) :
    let pooledPred := fun k i => b (k.castAdd p) + ∑ j, x i j*b ⟨4+j.val, by omega⟩
    let separatePred := fun k i => s k ⟨0, by omega⟩+
      ∑ j, x i j*s k ⟨1+j.val, by omega⟩
    (∀ k, (∑ i, if D i=k then w i*(Y i-pooledPred k i) else 0)=0 ∧
      (∑ i, if D i=k then w i*(Y i-separatePred k i) else 0)=0) ∧
    (∀ k, augmentedExposureMean D w Y (pooledPred k) k=
      (∑ i, pooledPred k i)/(Fintype.card I:ℝ) ∧
      augmentedExposureMean D w Y (separatePred k) k=
        (∑ i, separatePred k i)/(Fintype.card I:ℝ)) ∧
    (∀ k l, ((∑ i, pooledPred k i)/(Fintype.card I:ℝ))-
      ((∑ i, pooledPred l i)/(Fintype.card I:ℝ))=b (k.castAdd p)-b (l.castAdd p)) := by
  intro pooledPred separatePred
  have hp := normal_of_minimum w (pooledExposureRow D x) Y b (fun i => (hw i).le) hb
  have hsep (k : Fin 4) := normal_of_minimum (fun i => if D i=k then w i else 0)
    (separateExposureRow x) Y (s k)
    (fun i => by split_ifs; exact (hw i).le; rfl) (hs k)
  have hres (k : Fin 4) :
      (∑ i, if D i=k then w i*(Y i-pooledPred k i) else 0)=0 ∧
      (∑ i, if D i=k then w i*(Y i-separatePred k i) else 0)=0 := by
    constructor
    · have h := hp (k.castAdd p)
      have heq : (∑ i, w i*(Y i-(pooledExposureRow D x).mulVec b i)*
          pooledExposureRow D x i (k.castAdd p)) =
          ∑ i, if D i=k then w i*(Y i-pooledPred k i) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [pooled_prediction]
        by_cases hi : D i=k
        · simp [pooledExposureRow, hi, pooledPred]
        · simp [pooledExposureRow, hi]
      rw [heq] at h
      exact h
    · have h := hsep k ⟨0, by omega⟩
      simpa [separate_prediction, separateExposureRow, separatePred, ite_mul] using h
  refine ⟨hres, ?_, ?_⟩
  · intro k
    constructor
    · unfold augmentedExposureMean
      rw [Finset.sum_add_distrib, (hres k).1, zero_add]
    · unfold augmentedExposureMean
      rw [Finset.sum_add_distrib, (hres k).2, zero_add]
  · intro k l
    have hn : (Fintype.card I:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hI)
    dsimp only [pooledPred]
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    field_simp
    ring

/-- Finite WLS lemma for T28(d): positive weights and
full-rank designs make these stationary points the unique WLS minima.
Zero masked weights are allowed if equality of fits on positive-weight
rows still determines the coefficients. -/
theorem regression_unique_of_normal {I K : Type*} [Fintype I] [Fintype K]
    (w : I → ℝ) (X : Matrix I K ℝ) (Y : I → ℝ) (b : K → ℝ)
    (hw : ∀ i, 0≤w i)
    (hnormal : ∀ j, (∑ i, w i*(Y i-X.mulVec b i)*X i j)=0)
    (hfit : ∀ c, (∀ i, 0<w i → X.mulVec c i=X.mulVec b i) → c=b) :
    ∀ c, regressionMinimum w X Y c ↔ c=b := by
  have cross (c : K → ℝ) :
      (∑ i, w i*(Y i-X.mulVec b i)*(X.mulVec c i-X.mulVec b i))=0 := by
    calc
      _ = ∑ i, ∑ j, (w i*(Y i-X.mulVec b i)*X i j)*(c j-b j) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Matrix.mulVec, dotProduct]
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ j, (∑ i, w i*(Y i-X.mulVec b i)*X i j)*(c j-b j) := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ = 0 := by simp [hnormal]
  have gap (c : K → ℝ) :
      (∑ i, w i*(Y i-X.mulVec c i)^2)=
      (∑ i, w i*(Y i-X.mulVec b i)^2)+
      (∑ i, w i*(X.mulVec c i-X.mulVec b i)^2) := by
    calc
      _ = ∑ i, (w i*(Y i-X.mulVec b i)^2+
          w i*(X.mulVec c i-X.mulVec b i)^2-
          2*(w i*(Y i-X.mulVec b i)*(X.mulVec c i-X.mulVec b i))) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, cross, mul_zero, sub_zero]
  have nonneg (c : K → ℝ) : 0≤∑ i, w i*(X.mulVec c i-X.mulVec b i)^2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
  have minimum : regressionMinimum w X Y b := by
    intro c
    rw [gap c]
    exact le_add_of_nonneg_right (nonneg c)
  intro c
  constructor
  · intro hc
    have hle := hc b
    rw [gap c] at hle
    have hz : (∑ i, w i*(X.mulVec c i-X.mulVec b i)^2)=0 := by
      linarith [nonneg c]
    apply hfit c
    intro i hi
    have ht : w i*(X.mulVec c i-X.mulVec b i)^2=0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => mul_nonneg (hw i) (sq_nonneg _))).mp hz i (Finset.mem_univ i)
    have hs := (mul_eq_zero.mp ht).resolve_left hi.ne'
    have hd : X.mulVec c i-X.mulVec b i=0 := (sq_eq_zero_iff).mp hs
    exact sub_eq_zero.mp hd
  · rintro rfl
    exact minimum

/-- T28(d),(e), correcting SI p. 19:
with one covariate and positive within-exposure Sxx, every separate WLS
minimizer and every joint WLS minimizer equals the displayed coefficient
formula. The equivalences also assert existence and uniqueness. Their
standardized prediction difference is (b_k-beta)(xbar-xbar_w,k). -/
theorem one_covariate_regression_formulas {I : Type*} [Fintype I]
    (hI : 0<Fintype.card I) (D : I → Fin 4) (w x Y : I → ℝ)
    (hw : ∀ i, 0<w i) :
    let W := fun k => ∑ i, if D i=k then w i else 0
    let xb := fun k => (∑ i, if D i=k then w i*x i else 0)/W k
    let yb := fun k => (∑ i, if D i=k then w i*Y i else 0)/W k
    let Sxx := fun k => ∑ i, if D i=k then w i*(x i-xb k)^2 else 0
    let Sxy := fun k => ∑ i, if D i=k then w i*(x i-xb k)*(Y i-yb k) else 0
    let bk := fun k => Sxy k/Sxx k
    let beta := (∑ k : Fin 4, Sxy k)/(∑ k : Fin 4, Sxx k)
    let xbar := (∑ i, x i)/(Fintype.card I:ℝ)
    (∀ k, 0<Sxx k) →
      (∀ k c, regressionMinimum (fun i => if D i=k then w i else 0)
        (fun i => ![1,x i]) Y c ↔ c=![yb k-bk k*xb k,bk k]) ∧
      (∀ c, regressionMinimum w (pooledExposureRow D (fun i => ![x i])) Y c ↔
        c=![yb 0-beta*xb 0,yb 1-beta*xb 1,yb 2-beta*xb 2,yb 3-beta*xb 3,beta]) ∧
      (∀ k, (yb k-bk k*xb k+bk k*xbar)-(yb k-beta*xb k+beta*xbar)=
        (bk k-beta)*(xbar-xb k))  := by
  intro W xb yb Sxx Sxy bk beta xbar hxx
  let q := fun k i => if D i=k then w i else 0
  have qnonneg : ∀ k i, 0≤q k i := by
    intro k i
    dsimp [q]
    split_ifs
    · exact (hw i).le
    · exact le_refl 0
  have group (k : Fin 4) : ∃ i, D i=k := by
    by_contra hn
    have hz : Sxx k=0 := by
      dsimp [Sxx]
      apply Finset.sum_eq_zero
      intro i _
      exact if_neg (fun hi => hn ⟨i,hi⟩)
    linarith [hxx k]
  have hW (k : Fin 4) : 0<W k := by
    obtain ⟨i,hi⟩ := group k
    have hle := Finset.single_le_sum (fun j (_ : j∈(Finset.univ : Finset I)) => qnonneg k j)
      (Finset.mem_univ i)
    have hqi : q k i=w i := by simp [q,hi]
    rw [hqi] at hle
    exact lt_of_lt_of_le (hw i) hle
  have Wq (k : Fin 4) : (∑ i, q k i)=W k := rfl
  have Xq (k : Fin 4) : (∑ i, q k i*x i)=W k*xb k := by
    simp only [q, ite_mul, zero_mul]
    dsimp [xb]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (hW k).ne']
  have Yq (k : Fin 4) : (∑ i, q k i*Y i)=W k*yb k := by
    simp only [q, ite_mul, zero_mul]
    dsimp [yb]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (hW k).ne']
  have XXq (k : Fin 4) : (∑ i, q k i*(x i-xb k)^2)=Sxx k := by
    simp only [q, ite_mul, zero_mul]
    rfl
  have XYq (k : Fin 4) : (∑ i, q k i*(x i-xb k)*(Y i-yb k))=Sxy k := by
    simp only [q, ite_mul, zero_mul]
    rfl
  have CX (k : Fin 4) : (∑ i, q k i*(x i-xb k))=0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [Xq, Wq]
    ring
  have CY (k : Fin 4) : (∑ i, q k i*(Y i-yb k))=0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [Yq, Wq]
    ring
  have R0 (k : Fin 4) (t : ℝ) :
      (∑ i, q k i*(Y i-(yb k-t*xb k)-x i*t))=0 := by
    calc
      _ = (∑ i, q k i*(Y i-yb k))-t*(∑ i, q k i*(x i-xb k)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [CY, CX]; ring
  have R1 (k : Fin 4) (t : ℝ) :
      (∑ i, q k i*(Y i-(yb k-t*xb k)-x i*t)*x i)=Sxy k-t*Sxx k := by
    calc
      _ = (∑ i, q k i*(x i-xb k)*(Y i-yb k))-
          t*(∑ i, q k i*(x i-xb k)^2)+
          xb k*(∑ i, q k i*(Y i-yb k))-
          (t*xb k)*(∑ i, q k i*(x i-xb k)) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [XYq, XXq, CY, CX]; ring
  have rank (k : Fin 4) (u v : ℝ) (h : ∀ i, D i=k → u+x i*v=0) :
      u=0 ∧ v=0 := by
    have hz : (∑ i, q k i*(x i-xb k)*(u+x i*v))=0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : D i=k
      · rw [h i hi, mul_zero]
      · simp [q,hi]
    have he : (∑ i, q k i*(x i-xb k)*(u+x i*v))=v*Sxx k := by
      calc
        _ = u*(∑ i, q k i*(x i-xb k))+
            v*(∑ i, q k i*(x i-xb k)^2)+
            (v*xb k)*(∑ i, q k i*(x i-xb k)) := by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [CX, XXq]; ring
    rw [he] at hz
    have hv : v=0 := (mul_eq_zero.mp hz).resolve_right (hxx k).ne'
    obtain ⟨i,hi⟩ := group k
    have hu := h i hi
    simp only [hv, mul_zero, add_zero] at hu
    exact ⟨hu,hv⟩
  have separate_pred (c : Fin 2 → ℝ) (i : I) :
      (Matrix.mulVec (fun i => ![1,x i]) c) i=c 0+x i*c 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have separate (k : Fin 4) :
      ∀ c, regressionMinimum (q k) (fun i => ![1,x i]) Y c ↔
        c=![yb k-bk k*xb k,bk k] := by
    apply regression_unique_of_normal
    · exact qnonneg k
    · intro j
      fin_cases j
      · simp only [separate_pred]
        change (∑ i, q k i*(Y i-(yb k-bk k*xb k+x i*bk k))*1)=0
        simpa only [mul_one, sub_add_eq_sub_sub] using R0 k (bk k)
      · simp only [separate_pred]
        change (∑ i, q k i*(Y i-(yb k-bk k*xb k+x i*bk k))*x i)=0
        simp only [sub_add_eq_sub_sub]
        rw [R1]
        dsimp [bk]
        rw [div_mul_cancel₀ _ (hxx k).ne', sub_self]
    · intro c hc
      have hr := rank k (c 0-(yb k-bk k*xb k)) (c 1-bk k) (by
        intro i hi
        have hqi : 0<q k i := by simpa [q,hi] using hw i
        have he := hc i hqi
        simp only [separate_pred, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons] at he
        linarith)
      ext j
      fin_cases j
      · change c 0=yb k-bk k*xb k
        exact sub_eq_zero.mp hr.1
      · change c 1=bk k
        exact sub_eq_zero.mp hr.2
  let fit : Fin 5 → ℝ :=
    ![yb 0-beta*xb 0,yb 1-beta*xb 1,yb 2-beta*xb 2,yb 3-beta*xb 3,beta]
  have fit_alpha (k : Fin 4) : fit k.castSucc=yb k-beta*xb k := by
    fin_cases k <;> rfl
  have fit_beta : fit 4=beta := rfl
  have pooled_pred (c : Fin 5 → ℝ) (i : I) :
      (pooledExposureRow D (fun i => ![x i])).mulVec c i=
        c (D i).castSucc+x i*c 4 := by
    generalize hd : D i=d
    fin_cases d <;>
      simp [pooledExposureRow, hd, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have pooled_col (k : Fin 4) (i : I) :
      pooledExposureRow D (fun i => ![x i]) i k.castSucc=
        if D i=k then 1 else 0 := by
    fin_cases k <;> simp [pooledExposureRow]
  have pooled_x (i : I) : pooledExposureRow D (fun i => ![x i]) i 4=x i := by
    simp [pooledExposureRow]
  have partition (f : Fin 4 → I → ℝ) :
      (∑ i, w i*f (D i) i)=∑ k : Fin 4, ∑ i, q k i*f k i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    generalize hd : D i=d
    fin_cases d <;> simp [q, hd, Fin.sum_univ_succ]
  have pooled_normal (j : Fin 5) :
      (∑ i, w i*(Y i-(pooledExposureRow D (fun i => ![x i])).mulVec fit i)*
        pooledExposureRow D (fun i => ![x i]) i j)=0 := by
    by_cases hj : j.val<4
    · let k : Fin 4 := ⟨j.val,hj⟩
      have he : j=k.castSucc := by apply Fin.ext; rfl
      rw [he]
      simp only [pooled_pred, fit_alpha, fit_beta, pooled_col]
      calc
        _ = ∑ i, q k i*(Y i-(yb k-beta*xb k)-x i*beta) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : D i=k
          · simp [q, hi, sub_add_eq_sub_sub]
          · simp [q, hi]
        _ = 0 := R0 k beta
    · have he : j=4 := by apply Fin.ext; have := j.isLt; omega
      rw [he]
      simp only [pooled_pred, fit_alpha, fit_beta, pooled_x, sub_add_eq_sub_sub]
      have hp := partition (fun k i => (Y i-(yb k-beta*xb k)-x i*beta)*x i)
      simp only [← mul_assoc] at hp
      rw [hp]
      simp only [R1, Finset.sum_sub_distrib, ← Finset.mul_sum]
      have ht : 0<∑ k : Fin 4, Sxx k :=
        lt_of_lt_of_le (hxx 0) (Finset.single_le_sum
          (fun k _ => (hxx k).le) (Finset.mem_univ 0))
      dsimp [beta]
      rw [div_mul_cancel₀ _ ht.ne', sub_self]
  have pooled_unique : ∀ c,
      regressionMinimum w (pooledExposureRow D (fun i => ![x i])) Y c ↔ c=fit := by
    apply regression_unique_of_normal w _ Y fit (fun i => (hw i).le) pooled_normal
    intro c hc
    have hr (k : Fin 4) : c k.castSucc-(yb k-beta*xb k)=0 ∧ c 4-beta=0 := by
      apply rank k
      intro i hi
      have he := hc i (hw i)
      simp only [pooled_pred, fit_alpha, fit_beta] at he
      rw [hi] at he
      linarith
    ext j
    by_cases hj : j.val<4
    · let k : Fin 4 := ⟨j.val,hj⟩
      have he : j=k.castSucc := by apply Fin.ext; rfl
      rw [he, fit_alpha]
      exact sub_eq_zero.mp (hr k).1
    · have he : j=4 := by apply Fin.ext; have := j.isLt; omega
      rw [he,fit_beta]
      exact sub_eq_zero.mp (hr 0).2
  refine ⟨separate, pooled_unique, ?_⟩
  intro k
  ring


/-- T28(e), the exact difference between separate and pooled predictions.
This algebraic component does not assume a numerical fit is an argmin. -/
theorem separate_pooled_prediction_difference (yb bk beta xb xbar : ℝ) :
    (yb-bk*xb+bk*xbar)-(yb-beta*xb+beta*xbar)=(bk-beta)*(xbar-xb) := by ring

/-- T27's twelve synthetic units, indexed by (exposure,within-group unit).
Every unit's potential outcomes are x at C,S,NI and 2x at I. -/
noncomputable def regression12X (i : Fin 4 × Fin 3) : ℝ := (i.1.val:ℝ)+(i.2.val:ℝ)
noncomputable def regression12Potential (i : Fin 4 × Fin 3) (k : Fin 4) : ℝ :=
  (if k=3 then 2 else 1)*regression12X i
noncomputable def regression12Y (i : Fin 4 × Fin 3) : ℝ := regression12Potential i i.1
noncomputable def regression12Pooled (weights : Fin 4 → ℝ) : Fin 5 → ℝ :=
  let beta := (weights 0+weights 1+weights 2+2*weights 3)/(∑ k, weights k)
  ![1-beta,2-2*beta,3-3*beta,8-4*beta,beta]
noncomputable def regression12Mean (b : Fin 5 → ℝ) (k : Fin 4) : ℝ :=
  b k.castSucc+(5/2)*b 4

/-- T27(ii),(vi): actual data normal-equation certificates for each
pooled candidate. Within-exposure residual corrections vanish in both cases. -/
theorem regression12_normal_certificates :
    (∀ weights ∈ ({(![4,4,4,4] : Fin 4 → ℝ),![2,8,8,4]} : Set (Fin 4 → ℝ)),
      (∀ k : Fin 4, (∑ j : Fin 3, weights k*(regression12Y (k,j)-
        (regression12Pooled weights k.castSucc+
          regression12X (k,j)*regression12Pooled weights 4)))=0) ∧
      (∑ i : Fin 4 × Fin 3, weights i.1*regression12X i*(regression12Y i-
        (regression12Pooled weights i.1.castSucc+
          regression12X i*regression12Pooled weights 4)))=0) := by
  intro weights hw
  rcases hw with rfl | rfl <;> constructor
  · intro k; fin_cases k <;> norm_num [regression12Pooled,regression12Y,
      regression12Potential,regression12X,Fin.sum_univ_succ]
  · norm_num [Fintype.sum_prod_type,regression12Pooled,regression12Y,
      regression12Potential,regression12X,Fin.sum_univ_succ]
  · intro k; fin_cases k <;> norm_num [regression12Pooled,regression12Y,
      regression12Potential,regression12X,Fin.sum_univ_succ]
  · norm_num [Fintype.sum_prod_type,regression12Pooled,regression12Y,
      regression12Potential,regression12X,Fin.sum_univ_succ]

namespace RegressionCompletion
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem regression12_separate_minimum (weights : Fin 4 → ℝ)
    (hw : ∀ k, 0 ≤ weights k) (k : Fin 4) :
    regressionMinimum (fun i : Fin 4 × Fin 3 => if i.1=k then weights k else 0)
      (fun i => ![1,regression12X i]) regression12Y ![0,if k=3 then 2 else 1] := by
  intro c
  have hz : (∑ i : Fin 4 × Fin 3, (if i.1=k then weights k else 0) *
      (regression12Y i-(Matrix.mulVec (fun i => ![1,regression12X i]))
        ![0,if k=3 then 2 else 1] i)^2)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i.1=k
    · simp [hi, regression12Y, regression12Potential, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, mul_comm]
    · simp [hi]
  rw [hz]
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · change 0 ≤ if i.1=k then weights k else 0
    split_ifs
    · exact hw k
    · rfl
  · exact sq_nonneg _

theorem regression12_pooled_unique (weights : Fin 4 → ℝ)
    (hset : weights ∈ ({(![4,4,4,4] : Fin 4 → ℝ),![2,8,8,4]} : Set (Fin 4 → ℝ))) :
    ∀ c, regressionMinimum (fun i : Fin 4 × Fin 3 => weights i.1)
      (pooledExposureRow (fun i : Fin 4 × Fin 3 => i.1) (fun i => ![regression12X i]))
      regression12Y c ↔ c=regression12Pooled weights := by
  have hw : ∀ k, 0 < weights k := by
    intro k
    rcases hset with rfl | rfl <;> fin_cases k <;> norm_num
  have pred (v : Fin 5 → ℝ) (i : Fin 4 × Fin 3) :
      (pooledExposureRow (fun i : Fin 4 × Fin 3 => i.1)
        (fun i => ![regression12X i])).mulVec v i =
        v i.1.castSucc+regression12X i*v 4 := by
    generalize hi : i.1=k
    fin_cases k <;> simp [pooledExposureRow, Matrix.mulVec, dotProduct, hi,
      Fin.sum_univ_succ]
  have cert := regression12_normal_certificates weights hset
  apply regression_unique_of_normal (fun i : Fin 4 × Fin 3 => weights i.1)
    (pooledExposureRow (fun i : Fin 4 × Fin 3 => i.1) (fun i => ![regression12X i]))
    regression12Y (regression12Pooled weights) (fun i => (hw i.1).le)
  · intro j
    simp only [pred]
    fin_cases j
    · simpa [pooledExposureRow, Fintype.sum_prod_type, Fin.sum_univ_succ] using cert.1 0
    · simpa [pooledExposureRow, Fintype.sum_prod_type, Fin.sum_univ_succ] using cert.1 1
    · simpa [pooledExposureRow, Fintype.sum_prod_type, Fin.sum_univ_succ] using cert.1 2
    · simpa [pooledExposureRow, Fintype.sum_prod_type, Fin.sum_univ_succ] using cert.1 3
    · simpa [pooledExposureRow, mul_assoc, mul_left_comm, mul_comm] using cert.2
  · intro c hc
    have he (k : Fin 4) (j : Fin 3) := hc (k,j) (hw k)
    simp only [pred] at he
    have h0 := he 0 0
    have h1 := he 0 1
    norm_num [regression12X] at h0 h1
    have hlast : c 4=regression12Pooled weights 4 := by linarith
    ext j
    by_cases hj : j.val<4
    · let k : Fin 4 := ⟨j.val,hj⟩
      have hidx : j=k.castSucc := by apply Fin.ext; rfl
      have h := he k 0
      rw [hlast] at h
      rw [hidx]
      linarith
    · have hidx : j=(4:Fin 5) := by
        apply Fin.ext
        change j.val=4
        have := j.isLt
        omega
      simpa only [hidx] using hlast

end RegressionCompletion

/-- T27, full comparison of the actual argmin estimators for both the
equal-probability and school/seed weights. Separate fits are exact potential
outcome lines; the pooled I-minus-NI contrasts are 15/4 and 42/11, respectively,
rather than the separate-fit contrast 5/2. -/
theorem separate_pooled_regression_counterexample :
    (∑ i : Fin 4 × Fin 3, regression12X i)/12=5/2 ∧
    (∀ weights ∈ ({(![4,4,4,4] : Fin 4 → ℝ),![2,8,8,4]} : Set (Fin 4 → ℝ)),
      (∀ k, regressionMinimum (fun i : Fin 4 × Fin 3 => if i.1=k then weights k else 0)
        (fun i => ![1,regression12X i]) regression12Y ![0,if k=3 then 2 else 1]) ∧
      (∀ b, regressionMinimum (fun i => weights i.1)
        (pooledExposureRow (fun i : Fin 4 × Fin 3 => i.1) (fun i => ![regression12X i]))
        regression12Y b ↔ b=regression12Pooled weights)) ∧
    regression12Pooled ![4,4,4,4]=![-1/4,-1/2,-3/4,3,5/4] ∧
    regression12Pooled ![2,8,8,4]=![-2/11,-4/11,-6/11,36/11,13/11] ∧
    (∀ k, regression12Mean (regression12Pooled ![4,4,4,4]) k=
      (![23/8,21/8,19/8,49/8] : Fin 4 → ℝ) k) ∧
    (∀ k, regression12Mean (regression12Pooled ![2,8,8,4]) k=
      (![61/22,57/22,53/22,137/22] : Fin 4 → ℝ) k) ∧
    (15/4:ℝ)≠5/2 ∧ (42/11:ℝ)≠5/2 ∧
    (1/4:ℝ)^12>0 ∧ (1/20:ℝ)*(1/4)*(1/4)*(1/2)=1/640 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [regression12X, Fintype.sum_prod_type, Fin.sum_univ_succ]
  · intro weights hw
    constructor
    · have hpos : ∀ k, 0 ≤ weights k := by
        intro k
        rcases hw with rfl | rfl <;> fin_cases k <;> norm_num
      exact regression12_separate_minimum weights hpos
    · exact regression12_pooled_unique weights hw
  · ext j; fin_cases j <;> norm_num [regression12Pooled, Fin.sum_univ_succ]
  · ext j; fin_cases j <;> norm_num [regression12Pooled, Fin.sum_univ_succ]
  · intro k; fin_cases k <;> norm_num [regression12Mean, regression12Pooled, Fin.sum_univ_succ]
  · intro k; fin_cases k <;> norm_num [regression12Mean, regression12Pooled, Fin.sum_univ_succ]
  all_goals norm_num

/-- T34(c), finite core identity: a left-inverse coefficient map refits
an imputed outcome r+Hθ to Lr+θ. The full-rank WLS implication L H=I
is stated separately, so it is not smuggled in as a replacement for rank. -/
theorem linear_residual_refit_shift {n k : ℕ}
    (H : Matrix (Fin n) (Fin k) ℝ) (L : Matrix (Fin k) (Fin n) ℝ)
    (hLH : L*H=1) (r : Fin n → ℝ) (θ : Fin k → ℝ) :
    L.mulVec (r+H.mulVec θ)=L.mulVec r+θ := by
  rw [Matrix.mulVec_add,Matrix.mulVec_mulVec,hLH,Matrix.one_mulVec]

namespace RegressionCompletion
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem weighted_gram_unit {I K : Type*} [Fintype I] [Fintype K]
    [DecidableEq K] (w : I → ℝ) (X : Matrix I K ℝ)
    (hw : ∀ i, 0 < w i) (hX : Function.Injective X.mulVec) :
    IsUnit (X.transpose * Matrix.diagonal w * X).det := by
  let G := X.transpose * Matrix.diagonal w * X
  have hker (v : K → ℝ) (hv : G.mulVec v=0) : v=0 := by
    have he : dotProduct v (G.mulVec v) = ∑ i, w i*(X.mulVec v i)^2 := by
      dsimp only [G]
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose]
      simp only [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hv] at he
    have hz : (∑ i, w i*(X.mulVec v i)^2)=0 := by simpa using he.symm
    have hfit : X.mulVec v = 0 := by
      ext i
      have ht := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => mul_nonneg (hw i).le (sq_nonneg (X.mulVec v i)))).mp hz i
        (Finset.mem_univ i)
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp ht).resolve_left (hw i).ne')
    apply hX
    simpa using hfit
  apply (Matrix.isUnit_iff_isUnit_det G).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro a b hab
  have hd : G.mulVec (a-b)=0 := by rw [Matrix.mulVec_sub, hab, sub_self]
  exact sub_eq_zero.mp (hker _ hd)

theorem weighted_left_inverse {I K : Type*} [Fintype I] [Fintype K]
    [DecidableEq K] (w : I → ℝ) (X : Matrix I K ℝ)
    (hw : ∀ i, 0 < w i) (hX : Function.Injective X.mulVec) :
    regressionMap w X * X = 1 := by
  calc
    regressionMap w X * X = (X.transpose * Matrix.diagonal w * X)⁻¹ *
        (X.transpose * Matrix.diagonal w * X) := by
      simp only [regressionMap, Matrix.mul_assoc]
    _ = 1 := Matrix.nonsing_inv_mul _ (weighted_gram_unit w X hw hX)

theorem finite_variance_add_const {Ω : Type*} [Fintype Ω]
    (prob f : Ω → ℝ) (ht : ∑ z, prob z=1) (c : ℝ) :
    (∑ z, prob z*(f z+c)^2)-(∑ z, prob z*(f z+c))^2 =
      (∑ z, prob z*(f z)^2)-(∑ z, prob z*f z)^2 := by
  have hfirst : (∑ z, prob z*(f z+c))=(∑ z, prob z*f z)+c := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, ht, one_mul]
  have hsecond : (∑ z, prob z*(f z+c)^2)=
      (∑ z, prob z*(f z)^2)+(2*c)*(∑ z, prob z*f z)+c^2 := by
    calc
      _ = ∑ z, (prob z*(f z)^2+(2*c)*(prob z*f z)+prob z*c^2) := by
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
          ht, one_mul]
  rw [hfirst, hsecond]
  ring

end RegressionCompletion

/-- T34(a)--(c): fixed controls, fixed averaging population and positive
weights at every assignment make residual refits exactly the printed
constant-effects imputation, including means/contrasts and their variances. -/
theorem same_controls_residual_imputation {Ω : Type*} [Fintype Ω]
    {n p : ℕ} (hn : 0<n) (D0 : Fin n → Fin 4) (D : Ω → Fin n → Fin 4)
    (C : Matrix (Fin n) (Fin p) ℝ) (w0 : Fin n → ℝ) (w : Ω → Fin n → ℝ)
    (hw0 : ∀ i, 0<w0 i) (hw : ∀ z i, 0<w z i)
    (hX0 : Function.Injective (Matrix.mulVec (pooledExposureRow D0 C)))
    (hX : ∀ z, Function.Injective (Matrix.mulVec (pooledExposureRow (D z) C)))
    (y : Fin n → ℝ) (prob : Ω → ℝ) (hp : ∀ z, 0≤prob z) (ht : ∑ z, prob z=1) :
    let b0 := (regressionMap w0 (pooledExposureRow D0 C)).mulVec y
    let row := fun k => pooledExposureRow (fun _ : Unit => k)
      (fun _ j => (∑ i, C i j)/(n:ℝ)) ()
    let m := fun k => dotProduct (row k) b0
    let residual := y-(Matrix.mulVec (pooledExposureRow D0 C)) b0
    let imputed := fun z i => y i+m (D z i)-m (D0 i)
    let L := fun z => regressionMap (w z) (pooledExposureRow (D z) C)
    (∀ k l, m k-m l=b0 (k.castAdd p)-b0 (l.castAdd p)) ∧
    (∀ z, (L z*pooledExposureRow (D z) C)=1 ∧
      (L z).mulVec (imputed z)=(L z).mulVec residual+b0) ∧
    (∀ z k, dotProduct (row k) ((L z).mulVec (imputed z))=
      dotProduct (row k) ((L z).mulVec residual)+m k) ∧
    (∀ k l,
      (let a := fun z => dotProduct (row k-row l) ((L z).mulVec (imputed z))
       let b := fun z => dotProduct (row k-row l) ((L z).mulVec residual)
       (∑ z, prob z*(a z)^2)-(∑ z, prob z*a z)^2=
       (∑ z, prob z*(b z)^2)-(∑ z, prob z*b z)^2)) := by
  intro b0 row m residual imputed L
  have hrow (v : Fin (4+p) → ℝ) (k : Fin 4) :
      dotProduct (row k) v = v (k.castAdd p) +
        ∑ j, ((∑ i, C i j)/(n:ℝ))*v ⟨4+j.val, by omega⟩ := by
    exact pooled_prediction (fun _ : Unit => k)
      (fun _ j => (∑ i, C i j)/(n:ℝ)) v ()
  have hmean (k l : Fin 4) : m k-m l=b0 (k.castAdd p)-b0 (l.castAdd p) := by
    change dotProduct (row k) b0-dotProduct (row l) b0=_
    rw [hrow, hrow]
    ring
  have hleft (z : Ω) : L z*pooledExposureRow (D z) C=1 :=
    weighted_left_inverse (w z) _ (hw z) (hX z)
  have himpute (z : Ω) : imputed z=residual+(pooledExposureRow (D z) C).mulVec b0 := by
    ext i
    change y i+m (D z i)-m (D0 i) =
      y i-(pooledExposureRow D0 C).mulVec b0 i+(pooledExposureRow (D z) C).mulVec b0 i
    change y i+m (D z i)-m (D0 i) =
      y i-(pooledExposureRow D0 (fun i j => C i j)).mulVec b0 i+
        (pooledExposureRow (D z) (fun i j => C i j)).mulVec b0 i
    rw [pooled_prediction, pooled_prediction]
    linarith [hmean (D z i) (D0 i)]
  have hfit (z : Ω) : (L z).mulVec (imputed z)=(L z).mulVec residual+b0 := by
    rw [himpute, Matrix.mulVec_add, Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
  refine ⟨hmean, fun z => ⟨hleft z,hfit z⟩, ?_, ?_⟩
  · intro z k
    rw [hfit, dotProduct_add]
  · intro k l
    have he (z : Ω) : dotProduct (row k-row l) ((L z).mulVec (imputed z)) =
        dotProduct (row k-row l) ((L z).mulVec residual)+(m k-m l) := by
      rw [hfit, dotProduct_add]
      simp only [sub_dotProduct]
      rfl
    dsimp only
    simp_rw [he]
    exact finite_variance_add_const prob _ ht _

/-- T33's 96-state exact design: six exposed-pair choices and four
independent orientation bits. Unit indices are (pair,first/second). -/
def controlPair (z : Fin 6) : Finset (Fin 4) := ![{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}] z
noncomputable def pairReferentRate : Fin 4 → ℝ := ![1/10,1/5,3/10,2/5]
def controlExposure (z : Fin 6 × (Fin 4 → Bool)) (i : Fin 4 × Fin 2) : Fin 4 :=
  if i.1∈controlPair z.1 then
    (if (z.2 i.1)==decide (i.2=0) then 3 else 2)
  else if (z.2 i.1)==decide (i.2=0) then 0 else 1
noncomputable def controlMass (z : Fin 6 × (Fin 4 → Bool)) : ℝ :=
  (1/6)*∏ j, if j∈controlPair z.1 then
    (if z.2 j then pairReferentRate j else 1-pairReferentRate j) else 1/2
noncomputable def controlPiI (i : Fin 4 × Fin 2) : ℝ :=
  (1/2)*(if i.2=0 then pairReferentRate i.1 else 1-pairReferentRate i.1)
noncomputable def controlPi (i : Fin 4 × Fin 2) (k : Fin 4) : ℝ :=
  if k=0 ∨ k=1 then 1/4 else if k=2 then 1/2-controlPiI i else controlPiI i
def controlObserved (i : Fin 4 × Fin 2) : Fin 4 :=
  if i.1.val<2 then (if i.2=0 then 3 else 2) else if i.2=0 then 0 else 1
noncomputable def controlY (i : Fin 4 × Fin 2) : ℝ := ![![0,2],![1,0],![3,1],![2,4]] i.1 i.2
noncomputable def controlFullRow (D : (Fin 4 × Fin 2) → Fin 4) : Matrix (Fin 4 × Fin 2) (Fin 5) ℝ :=
  pooledExposureRow D (fun i => ![controlPiI i])
noncomputable def controlWeight (D : (Fin 4 × Fin 2) → Fin 4) (i : Fin 4 × Fin 2) : ℝ :=
  1/controlPi i (D i)
noncomputable def controlPoint : Fin 5 → ℝ :=
  (regressionMap (controlWeight controlObserved) (controlFullRow controlObserved)).mulVec controlY
noncomputable def controlPointMean (k : Fin 4) : ℝ := controlPoint k.castSucc+controlPoint 4/4
noncomputable def controlResidual : (Fin 4 × Fin 2) → ℝ :=
  controlY-(controlFullRow controlObserved).mulVec controlPoint
noncomputable def controlContrast (z : Fin 6 × (Fin 4 → Bool)) (full : Bool)
    (Y : (Fin 4 × Fin 2) → ℝ) : ℝ :=
  if full then
    let b := (regressionMap (controlWeight (controlExposure z)) (controlFullRow (controlExposure z))).mulVec Y
    b 3-b 2
  else
    let X : Matrix (Fin 4 × Fin 2) (Fin 4) ℝ := fun i k => if controlExposure z i=k then 1 else 0
    let b := (regressionMap (controlWeight (controlExposure z)) X).mulVec Y
    b 3-b 2
noncomputable def controlVariance (f : (Fin 6 × (Fin 4 → Bool)) → ℝ) : ℝ :=
  (∑ z, controlMass z*(f z)^2)-(∑ z, controlMass z*f z)^2
noncomputable def controlFullVarianceCertificate : ℝ :=
  1574066925743604937750798623088231315086040632174801225920729815316988109390788379330079414475192929 /
  171796363313262196427951740421954806512514436622177625713808591915692887084446808987770465290240000
noncomputable def controlCollapsedVarianceCertificate : ℝ := 1453114769225810453/621302156766720000


/-- T33(v): exact comparison of the rational variance certificates.
The theorem bounds and distinguishes these constants; it does not identify
them with variances computed from the actual refits. -/
theorem collapsed_controls_certificate_inequalities :
    9<controlFullVarianceCertificate ∧ controlFullVarianceCertificate<37/4 ∧
    2<controlCollapsedVarianceCertificate ∧ controlCollapsedVarianceCertificate<5/2 ∧
    controlCollapsedVarianceCertificate≠controlFullVarianceCertificate := by
  norm_num [controlFullVarianceCertificate,controlCollapsedVarianceCertificate]

/-- T27(E2): the hierarchical six-school synthetic design. Exactly three
schools are treated; independent Boolean R/N draws select one from each
eligible pair. Focal student (C,j) is in school j; the other exposure groups
are the three focal students in schools 3,4,5. No focal student is eligible. -/
def regression12School (i : Fin 4 × Fin 3) : Fin 6 :=
  if h : i.1=0 then ⟨i.2.val, by omega⟩ else ⟨i.1.val+2, by omega⟩
def regression12HierarchicalExposure (schools : Finset (Fin 6))
    (seeds : Fin 6 → Bool × Bool) (i : Fin 4 × Fin 3) : Fin 4 :=
  if regression12School i∉schools then 0 else
    if (seeds (regression12School i)).1 then 3 else
    if (seeds (regression12School i)).2 then 2 else 1

/-- T27(E2): "The first three have one focal
student each ... the last three have three focal students each"; every
school also has R,r,N,n and two noneligible helpers. -/
def regression12SchoolSize (s : Fin 6) : ℕ := if s.val<3 then 7 else 9

/-- The complete synthetic student population in T27(E2), with each
student indexed by its school and local roster position. Positions 0,1,2,3
are R,r,N,n; 4,5 are helpers; positions at least 6 are focal students. -/
abbrev Regression12Student := Σ s : Fin 6, Fin (regression12SchoolSize s)

/-- T27(E2): "Each focal student nominates R and N.
Both helpers nominate R. No other nominations occur." This is the directed
nomination graph; the exposure graph takes either nomination direction. -/
noncomputable def regression12Nomination (s : Fin 6)
    (i j : Fin (regression12SchoolSize s)) : Bool :=
  decide (((6 : ℕ) ≤ i.val ∧ (j.val=0 ∨ j.val=2)) ∨
    ((i.val=4 ∨ i.val=5) ∧ j.val=0))

/-- Directed indegree of the T27(E2) graph, for SI p. 17's definition
"indegree in the top decile of student's school". -/
noncomputable def regression12Indegree (s : Fin 6) (j : Fin (regression12SchoolSize s)) : ℕ :=
  (Finset.univ.filter (fun i => regression12Nomination s i j=true)).card

/-- T27(E2): "the interpolated 90th percentile lies
strictly between the indegrees of N and R". Type-7 interpolation uses
h=9(n-1)/10 in the sorted roster, as in the released referent classifier. -/
noncomputable def regression12Ninety (s : Fin 6) : ℝ :=
  let sorted := (List.ofFn (regression12Indegree s)).mergeSort (·≤·)
  let h := 9*(regression12SchoolSize s-1)
  ((10-h%10:ℕ):ℝ)/10*(sorted.getD (h/10) 0:ℝ)+
    ((h%10:ℕ):ℝ)/10*(sorted.getD (h/10+1) 0:ℝ)

/-- T27(E2)'s fixed-count seed draws: one of {R,r} and independently
one of {N,n}, each equiprobable. Boolean pairs encode these four equally
likely choices. Latent draws in control schools are ignored by exposure. -/
def regression12SeedSet (s : Fin 6) (b : Bool × Bool)
    : Finset (Fin (regression12SchoolSize s)) :=
  {⟨if b.1 then 0 else 1, by unfold regression12SchoolSize; split_ifs <;> omega⟩,
   ⟨if b.2 then 2 else 3, by unfold regression12SchoolSize; split_ifs <;> omega⟩}

/-- The twelve focal students of T27's data table embedded in the full
school rosters. Covariates/potential outcomes are regression12X/Potential. -/
def regression12FocalStudent (i : Fin 4 × Fin 3) : Regression12Student :=
  ⟨regression12School i, ⟨6+(if i.1=0 then 0 else i.2.val), by
    unfold regression12SchoolSize regression12School
    split_ifs <;> simp_all <;> omega⟩⟩

/-- T27(E2)'s exposures computed from the nomination graph, the actual
two-of-four seed set, and the indegree percentile. SI p. 17 labels are
C,S,NI,I,D=0,1,2,3,4; directly treated students are outside the four-exposure
population. Peers are related by either direction of nomination (T26). -/
noncomputable def regression12StudentExposure (schools : Finset (Fin 6))
    (seeds : Fin 6 → Bool × Bool) (u : Regression12Student) : Fin 5 :=
  if u.1∉schools then 0 else
  if u.2∈regression12SeedSet u.1 (seeds u.1) then 4 else
  if ∃ v ∈ regression12SeedSet u.1 (seeds u.1),
      (regression12Nomination u.1 u.2 v=true ∨ regression12Nomination u.1 v u.2=true) ∧
      regression12Ninety u.1<(regression12Indegree u.1 v:ℝ) then 3 else
  if ∃ v ∈ regression12SeedSet u.1 (seeds u.1),
      regression12Nomination u.1 u.2 v=true ∨ regression12Nomination u.1 v u.2=true
    then 2 else 1

/-- Exact marginal probability in T27(E2): three of six schools are
uniformly treated, and the two independent pair draws are uniform in each
school. Summing latent draws in control schools marginalizes them out. -/
noncomputable def regression12StudentProb (u : Regression12Student) (k : Fin 5) : ℝ :=
  ∑ schools ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
    ∑ seeds : Fin 6 → Bool × Bool,
      (1/(20*4^6):ℝ)*(if regression12StudentExposure schools seeds u=k then 1 else 0)

/-- T27(E2): "R has indegree two greater than N" and the "interpolated 90th percentile lies strictly between" them. This certificate computes the indegrees and percentile from the actual directed graph. -/
theorem regression12_graph_certificate :
    (∀ s j, regression12Indegree s j=
      if j.val=0 then regression12SchoolSize s-4 else
      if j.val=2 then regression12SchoolSize s-6 else 0) ∧
    (∀ s, regression12Ninety s=if s.val<3 then 9/5 else 17/5) := by
  have hu7 : (Finset.univ : Finset (Fin 7))={0,1,2,3,4,5,6} := by
    ext i; fin_cases i <;> simp
  have hu9 : (Finset.univ : Finset (Fin 9))={0,1,2,3,4,5,6,7,8} := by
    ext i; fin_cases i <;> simp
  have cr7 : ((Finset.univ : Finset (Fin 7)).filter
      (fun i => (6 : ℕ) ≤ i.val ∨ i.val=4 ∨ i.val=5)).card=3 := by
    have h : (Finset.univ : Finset (Fin 7)).filter
        (fun i => (6 : ℕ) ≤ i.val ∨ i.val=4 ∨ i.val=5)={4,5,6} := by
      ext i; fin_cases i <;> norm_num
    rw [h]; norm_num
  have cn7 : ((Finset.univ : Finset (Fin 7)).filter (fun i => (6 : ℕ) ≤ i.val)).card=1 := by
    have h : (Finset.univ : Finset (Fin 7)).filter (fun i => (6 : ℕ) ≤ i.val)={6} := by
      ext i; fin_cases i <;> norm_num
    rw [h]; norm_num
  have cr9 : ((Finset.univ : Finset (Fin 9)).filter
      (fun i => (6 : ℕ) ≤ i.val ∨ i.val=4 ∨ i.val=5)).card=5 := by
    have h : (Finset.univ : Finset (Fin 9)).filter
        (fun i => (6 : ℕ) ≤ i.val ∨ i.val=4 ∨ i.val=5)={4,5,6,7,8} := by
      ext i; fin_cases i <;> norm_num
    rw [h]; norm_num
  have cn9 : ((Finset.univ : Finset (Fin 9)).filter (fun i => (6 : ℕ) ≤ i.val)).card=3 := by
    have h : (Finset.univ : Finset (Fin 9)).filter (fun i => (6 : ℕ) ≤ i.val)={6,7,8} := by
      ext i; fin_cases i <;> norm_num
    rw [h]; norm_num
  have hd : ∀ s j, regression12Indegree s j=
      if j.val=0 then regression12SchoolSize s-4 else
      if j.val=2 then regression12SchoolSize s-6 else 0 := by
    intro s
    fin_cases s <;> intro j <;> fin_cases j <;>
      norm_num [regression12Indegree, regression12Nomination, regression12SchoolSize]
    all_goals first | exact cr7 | exact cn7 | exact cr9 | exact cn9
  have hs7 : (List.ofFn (fun j : Fin 7 => if j.val=0 then 3 else
      if j.val=2 then 1 else (0:ℕ))).mergeSort (·≤·)=[0,0,0,0,0,1,3] := by
    norm_num [List.ofFn_succ, List.mergeSort_eq_insertionSort,
      List.insertionSort, List.orderedInsert]
  have hs9 : (List.ofFn (fun j : Fin 9 => if j.val=0 then 5 else
      if j.val=2 then 3 else (0:ℕ))).mergeSort (·≤·)=[0,0,0,0,0,0,0,3,5] := by
    norm_num [List.ofFn_succ, List.mergeSort_eq_insertionSort,
      List.insertionSort, List.orderedInsert]
  have hd_fun (s : Fin 6) : regression12Indegree s=
      (fun j => if j.val=0 then regression12SchoolSize s-4 else
        if j.val=2 then regression12SchoolSize s-6 else 0) := funext (hd s)
  have hs (s : Fin 6) : (List.ofFn (regression12Indegree s)).mergeSort (·≤·)=
      if s.val<3 then [0,0,0,0,0,1,3] else [0,0,0,0,0,0,0,3,5] := by
    rw [hd_fun]
    fin_cases s <;> first | exact hs7 | exact hs9
  refine ⟨hd, ?_⟩
  intro s
  unfold regression12Ninety
  rw [hs]
  fin_cases s <;> norm_num [regression12SchoolSize]

/-- T27(E2)(iv): "R alone is a top-decile referent." The two-element seed sets choose one from each pair; focal students embed injectively, and their graph-derived exposures equal the projected school/seed exposure mapping. -/
theorem regression12_graph_exposures :
    (∀ s j, regression12Ninety s<(regression12Indegree s j:ℝ) ↔ j.val=0) ∧
    (∀ s b, (regression12SeedSet s b).card=2 ∧
      ((regression12SeedSet s b).filter (fun j => j.val<2)).card=1 ∧
      ((regression12SeedSet s b).filter (fun j => 2≤j.val ∧ j.val<4)).card=1) ∧
    Function.Injective regression12FocalStudent ∧
    (∀ schools seeds i,
      regression12StudentExposure schools seeds (regression12FocalStudent i)=
        (regression12HierarchicalExposure schools seeds i).castSucc) := by
  have href : ∀ s j, regression12Ninety s<(regression12Indegree s j:ℝ) ↔ j.val=0 := by
    intro s j
    rw [regression12_graph_certificate.1, regression12_graph_certificate.2]
    fin_cases s <;> fin_cases j <;> norm_num [regression12SchoolSize]
  have seedsize : ∀ s b, (regression12SeedSet s b).card=2 ∧
      ((regression12SeedSet s b).filter (fun j => j.val<2)).card=1 ∧
      ((regression12SeedSet s b).filter (fun j => 2≤j.val ∧ j.val<4)).card=1 := by
    intro s b
    rcases b with ⟨r,n⟩
    cases r <;> cases n <;>
      norm_num [regression12SeedSet, Fin.ext_iff, Finset.filter_insert, Finset.filter_singleton]
  have hinj : Function.Injective regression12FocalStudent := by
    rintro ⟨k,j⟩ ⟨l,h⟩ he
    have hs := congrArg (fun u : Regression12Student => u.1.val) he
    have hp := congrArg (fun u : Regression12Student => u.2.val) he
    have hkbound := k.isLt
    have hlbound := l.isLt
    have hjbound := j.isLt
    have hhbound := h.isLt
    by_cases hk : k=0 <;> by_cases hl : l=0 <;>
      simp [regression12FocalStudent, regression12School, hk, hl] at hs hp
    all_goals apply Prod.ext <;> apply Fin.ext <;> simp only [Prod.fst, Prod.snd] <;> omega
  have row (s : Fin 6) (j : Fin (regression12SchoolSize s))
      (hj : (6:ℕ)≤j.val) (schools : Finset (Fin 6)) (bits : Fin 6 → Bool × Bool) :
      regression12StudentExposure schools bits ⟨s,j⟩=
        if s∉schools then 0 else if (bits s).1 then 3 else if (bits s).2 then 2 else 1 := by
    have h0 : j.val≠0 := by omega
    have h1 : j.val≠1 := by omega
    have h2 : j.val≠2 := by omega
    have h3 : j.val≠3 := by omega
    have h4 : j.val≠4 := by omega
    have h5 : j.val≠5 := by omega
    have hnot : j∉regression12SeedSet s (bits s) := by
      simp only [regression12SeedSet, Finset.mem_insert, Finset.mem_singleton]
      intro he
      rcases he with he | he
      · have hval := congrArg Fin.val he
        simp only [Fin.val_mk] at hval
        split_ifs at hval <;> omega
      · have hval := congrArg Fin.val he
        simp only [Fin.val_mk] at hval
        split_ifs at hval <;> omega
    simp only [regression12StudentExposure, hnot, ite_false]
    cases hb : bits s with
    | mk r n =>
      cases r <;> cases n <;>
        simp [regression12SeedSet, href, regression12Nomination,
          hb, hj, h0, h1, h2, h3, h4, h5]
  refine ⟨href, seedsize, hinj, ?_⟩
  intro schools seeds i
  have hj : (6:ℕ)≤(regression12FocalStudent i).2.val := by
    simp [regression12FocalStudent]
  change regression12StudentExposure schools seeds
    ⟨regression12School i, (regression12FocalStudent i).2⟩=_
  rw [row (regression12School i) (regression12FocalStudent i).2 hj schools seeds]
  unfold regression12HierarchicalExposure
  split_ifs <;> rfl
/-- Finite product-law lemma for T27(E2)(iv): the "one of R,r and one of N,n, independently and uniformly" law has 4^5 latent assignments per prescribed pair draw in one school. This is a fiber-count identity for arbitrary real summands. -/
theorem regression12_seed_marginal (s : Fin 6) (f : Bool × Bool → ℝ) :
    (∑ bits : Fin 6 → Bool × Bool, f (bits s))=1024*(∑ b, f b) := by
  have count (b : Bool × Bool) :
      ((Finset.univ : Finset (Fin 6 → Bool × Bool)).filter (fun bits => bits s=b)).card=1024 := by
    have h := Fintype.card_filter_piFinset_const_eq_of_mem
      (Finset.univ : Finset (Bool × Bool)) s (Finset.mem_univ b)
    norm_num only [Fintype.piFinset_univ, Finset.card_univ, Fintype.card_prod,
      Fintype.card_bool, Fintype.card_fin, Nat.reduceMul, Nat.reduceSub, Nat.reducePow] at h
    exact h
  calc
    _ = ∑ b : Bool × Bool, ∑ bits ∈ (Finset.univ : Finset (Fin 6 → Bool × Bool)).filter
        (fun bits => bits s=b), f b :=
      (Finset.sum_fiberwise' Finset.univ (fun bits : Fin 6 → Bool × Bool => bits s) f).symm
    _ = ∑ b, (1024:ℝ)*f b := by
      simp only [Finset.sum_const, nsmul_eq_mul, count]
      norm_num
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- T27(E2): "exactly three of the six schools" are treated uniformly. Exactly ten of the twenty supported treated-school sets contain any specified school. -/
theorem regression12_treated_school_count (s : Fin 6) :
    (((Finset.univ : Finset (Fin 6)).powersetCard 3).filter (fun schools => s∈schools)).card=10 := by
  have h := Finset.card_filter_powersetCard_subset {s}
    (Finset.univ : Finset (Fin 6)) 3 (Finset.subset_univ _) (by simp)
  norm_num at h
  exact h

/-- T27(E2)(iv): focal "marginal exposure probabilities" are (1/2,1/8,1/8,1/4). Proved for the existing projected mapping by counting school subsets and one-coordinate fibers, without enumerating all seed schedules. -/
theorem regression12_focal_probabilities :
    ∀ i : Fin 4 × Fin 3, ∀ k : Fin 4,
      (∑ schools ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        ∑ seeds : Fin 6 → Bool × Bool,
          (1/(20*4^6):ℝ)*(if regression12HierarchicalExposure schools seeds i=k then 1 else 0))=
        (![1/2,1/8,1/8,1/4] : Fin 4 → ℝ) k := by
  intro i k
  let s := regression12School i
  have inner (schools : Finset (Fin 6)) :
      (∑ seeds : Fin 6 → Bool × Bool,
        (1/(20*4^6):ℝ)*(if regression12HierarchicalExposure schools seeds i=k then 1 else 0))=
      if s∈schools then (![0,1/80,1/80,1/40] : Fin 4 → ℝ) k else
        if k=0 then 1/20 else 0 := by
    unfold regression12HierarchicalExposure
    rw [regression12_seed_marginal s (fun b => (1/(20*4^6):ℝ)*
      (if (if s∉schools then (0:Fin 4) else if b.1 then 3 else if b.2 then 2 else 1)=k
        then 1 else 0))]
    by_cases ht : s∈schools <;> fin_cases k <;>
      norm_num [ht, Fintype.sum_prod_type, Fintype.sum_bool]
  have hc : (((Finset.univ : Finset (Fin 6)).powersetCard 3).filter
      (fun schools => s∈schools)).card=10 := regression12_treated_school_count s
  have hn : (((Finset.univ : Finset (Fin 6)).powersetCard 3).filter
      (fun schools => s∉schools)).card=10 := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 6)).powersetCard 3)
      (fun schools : Finset (Fin 6) => s∈schools)
    rw [hc] at h
    norm_num [Nat.choose] at h
    omega
  simp_rw [inner]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, hc, hn]
  fin_cases k <;> norm_num

/-- T27(E2)(iv): the displayed school/exposure realization has probability "(1/20)(1/4)(1/4)(1/2)=1/640". Its seed schedules form an explicitly counted product set. -/
theorem regression12_realization_probability :
    (∑ seeds : Fin 6 → Bool × Bool,
      (1/(20*4^6):ℝ)*(if (∀ i : Fin 4 × Fin 3,
        regression12HierarchicalExposure {3,4,5} seeds i=i.1) then 1 else 0))=1/640 := by
  have event (bits : Fin 6 → Bool × Bool) :
      (∀ i : Fin 4 × Fin 3, regression12HierarchicalExposure {3,4,5} bits i=i.1) ↔
      bits 3=(false,false) ∧ bits 4=(false,true) ∧ (bits 5).1=true := by
    constructor
    · intro h
      have h3 := h (1,0)
      have h4 := h (2,0)
      have h5 := h (3,0)
      generalize hb3 : bits 3=b3
      rcases b3 with ⟨r3,n3⟩
      cases r3 <;> cases n3 <;>
        simp_all [regression12HierarchicalExposure, regression12School]
      all_goals generalize hb4 : bits 4=b4
      all_goals rcases b4 with ⟨r4,n4⟩
      all_goals cases r4 <;> cases n4 <;>
        simp_all [regression12HierarchicalExposure, regression12School]
      all_goals generalize hb5 : bits 5=b5
      all_goals rcases b5 with ⟨r5,n5⟩
      all_goals cases r5 <;> cases n5 <;>
        simp_all [regression12HierarchicalExposure, regression12School]
    · rintro ⟨h3,h4,h5⟩ ⟨k,j⟩
      fin_cases k <;> fin_cases j <;>
        simp [regression12HierarchicalExposure, regression12School, h3,h4,h5]
  let B : Fin 6 → Finset (Bool × Bool) := fun s =>
    if s=3 then {(false,false)} else if s=4 then {(false,true)} else
    if s=5 then {(true,false),(true,true)} else Finset.univ
  have bittrue (b : Bool × Bool) : b∈({(true,false),(true,true)} : Finset (Bool × Bool)) ↔
      b.1=true := by
    rcases b with ⟨r,n⟩
    cases r <;> cases n <;> simp
  have allowed (bits : Fin 6 → Bool × Bool) :
      (∀ s, bits s∈B s) ↔ bits 3=(false,false) ∧ bits 4=(false,true) ∧ (bits 5).1=true := by
    simp [Fin.forall_fin_succ, B, bittrue]
  have hf : ((Finset.univ : Finset (Fin 6 → Bool × Bool)).filter
      (fun bits => ∀ i : Fin 4 × Fin 3, regression12HierarchicalExposure {3,4,5} bits i=i.1))=
      Fintype.piFinset B := by
    ext bits
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    exact (event bits).trans (allowed bits).symm
  have hc : (Fintype.piFinset B).card=128 := by
    rw [Fintype.card_piFinset]
    norm_num [B, Fin.prod_univ_succ]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, hf]
  simp only [Finset.sum_const, nsmul_eq_mul, hc]
  norm_num

/-- T27(E2)(iv): the complete nomination graph
has R as its sole referent in each school; the actual pair draws give the
four focal probabilities (1/2,1/8,1/8,1/4). Precisely the twelve focal
students have positive probability of all four exposures. The displayed
school/exposure realization has exact probability 1/640. -/
theorem regression12_hierarchical_design :
    (∀ s j, regression12Indegree s j=
      if j.val=0 then regression12SchoolSize s-4 else
      if j.val=2 then regression12SchoolSize s-6 else 0) ∧
    (∀ s, regression12Ninety s=if s.val<3 then 9/5 else 17/5) ∧
    (∀ s j, regression12Ninety s<(regression12Indegree s j:ℝ) ↔ j.val=0) ∧
    (∀ s b, (regression12SeedSet s b).card=2 ∧
      ((regression12SeedSet s b).filter (fun j => j.val<2)).card=1 ∧
      ((regression12SeedSet s b).filter (fun j => 2≤j.val ∧ j.val<4)).card=1) ∧
    Function.Injective regression12FocalStudent ∧
    (∀ schools seeds i,
      regression12StudentExposure schools seeds (regression12FocalStudent i)=
        (regression12HierarchicalExposure schools seeds i).castSucc) ∧
    (∀ i : Fin 4 × Fin 3, ∀ k : Fin 4,
      regression12StudentProb (regression12FocalStudent i) k.castSucc=
        (![1/2,1/8,1/8,1/4] : Fin 4 → ℝ) k) ∧
    (∀ u : Regression12Student,
      (∀ k : Fin 4, 0<regression12StudentProb u k.castSucc ∧
        regression12StudentProb u k.castSucc<1) ↔
      ∃ i : Fin 4 × Fin 3, u=regression12FocalStudent i) ∧
    (∑ seeds : Fin 6 → Bool × Bool,
      (1/(20*4^6):ℝ)*(if (∀ i : Fin 4 × Fin 3,
        regression12StudentExposure {3,4,5} seeds (regression12FocalStudent i)=i.1.castSucc)
        then 1 else 0))=1/640  := by
  have hgraph := regression12_graph_certificate
  have hrows := regression12_graph_exposures
  have castEq (k l : Fin 4) : k.castSucc=l.castSucc ↔ k=l := by
    constructor
    · intro h
      apply Fin.ext
      exact congrArg (fun v : Fin 5 => v.val) h
    · rintro rfl
      rfl
  have hprob (i : Fin 4 × Fin 3) (k : Fin 4) :
      regression12StudentProb (regression12FocalStudent i) k.castSucc=
        (![1/2,1/8,1/8,1/4] : Fin 4 → ℝ) k := by
    calc
      _ = ∑ schools ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
          ∑ seeds : Fin 6 → Bool × Bool,
            (1/(20*4^6):ℝ)*(if regression12HierarchicalExposure schools seeds i=k then 1 else 0) := by
        simp only [regression12StudentProb, hrows.2.2.2, castEq]
      _ = _ := regression12_focal_probabilities i k
  have image (u : Regression12Student) :
      (∃ i : Fin 4 × Fin 3, u=regression12FocalStudent i) ↔ (6:ℕ)≤u.2.val := by
    constructor
    · rintro ⟨i,rfl⟩
      simp [regression12FocalStudent]
    · intro hu
      rcases u with ⟨s,j⟩
      fin_cases s <;> fin_cases j <;> norm_num at hu
      all_goals first
        | exact ⟨(0,0),rfl⟩ | exact ⟨(0,1),rfl⟩ | exact ⟨(0,2),rfl⟩
        | exact ⟨(1,0),rfl⟩ | exact ⟨(1,1),rfl⟩ | exact ⟨(1,2),rfl⟩
        | exact ⟨(2,0),rfl⟩ | exact ⟨(2,1),rfl⟩ | exact ⟨(2,2),rfl⟩
        | exact ⟨(3,0),rfl⟩ | exact ⟨(3,1),rfl⟩ | exact ⟨(3,2),rfl⟩
  have neverNI (u : Regression12Student) (hu : u.2.val<6)
      (schools : Finset (Fin 6)) (bits : Fin 6 → Bool × Bool) :
      regression12StudentExposure schools bits u≠2 := by
    have seedval (v : Fin (regression12SchoolSize u.1))
        (hv : v∈regression12SeedSet u.1 (bits u.1)) : v.val<4 := by
      simp only [regression12SeedSet, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> dsimp only [Fin.val_mk] <;> split_ifs <;> norm_num
    have onlyR (v : Fin (regression12SchoolSize u.1))
        (hv : v∈regression12SeedSet u.1 (bits u.1))
        (he : regression12Nomination u.1 u.2 v=true ∨
          regression12Nomination u.1 v u.2=true) : v.val=0 := by
      have hvs := seedval v hv
      simp only [regression12Nomination, decide_eq_true_eq] at he
      omega
    by_cases ht : u.1∉schools
    · simp [regression12StudentExposure,ht]
    by_cases hs : u.2∈regression12SeedSet u.1 (bits u.1)
    · simp [regression12StudentExposure,ht,hs]
    by_cases hr : ∃ v ∈ regression12SeedSet u.1 (bits u.1),
        (regression12Nomination u.1 u.2 v=true ∨ regression12Nomination u.1 v u.2=true) ∧
        regression12Ninety u.1<(regression12Indegree u.1 v:ℝ)
    · simp [regression12StudentExposure,ht,hs,hr]
    have hp : ¬∃ v ∈ regression12SeedSet u.1 (bits u.1),
        regression12Nomination u.1 u.2 v=true ∨ regression12Nomination u.1 v u.2=true := by
      rintro ⟨v,hv,he⟩
      exact hr ⟨v,hv,he,(hrows.1 u.1 v).mpr (onlyR v hv he)⟩
    simp [regression12StudentExposure,ht,hs,hr,hp]
  have population (u : Regression12Student) :
      (∀ k : Fin 4, 0<regression12StudentProb u k.castSucc ∧
        regression12StudentProb u k.castSucc<1) ↔
      ∃ i : Fin 4 × Fin 3, u=regression12FocalStudent i := by
    constructor
    · intro h
      by_contra hn
      have hu : u.2.val<6 := by
        exact lt_of_not_ge (fun hi => hn ((image u).mpr hi))
      have hz : regression12StudentProb u 2=0 := by
        simp [regression12StudentProb, neverNI u hu]
      have hp := (h 2).1
      change 0<regression12StudentProb u 2 at hp
      rw [hz] at hp
      exact (lt_irrefl 0) hp
    · rintro ⟨i,rfl⟩ k
      rw [hprob]
      fin_cases k <;> norm_num
  refine ⟨hgraph.1,hgraph.2,hrows.1,hrows.2.1,hrows.2.2.1,hrows.2.2.2,
    hprob,population,?_⟩
  simpa only [hrows.2.2.2,castEq] using regression12_realization_probability


end AronowAudit.P037

