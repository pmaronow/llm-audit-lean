/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Actual all-order sigmoid derivatives, finite signed Taylor remainders,
and all-degree error lower bounds. No additional theorem hypotheses.
The partial-fraction identity is proved in P015_LogisticPartialFraction.
-/
import AronowAudit.P015.P015_LogisticPartialFraction
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Real.Pi.Bounds
import AronowAudit.P015.P015_TaylorUniformCompletion
namespace AronowAudit.P015.LogisticTaylorCompletion
open Complex Real Filter Set LogisticPartialFraction
open scoped Topology
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

def pole (n : ℕ) : ℝ := Real.pi*(2*n+1)
lemma pole_pos (n : ℕ) : 0<pole n := by dsimp [pole];positivity
lemma pole_ge_one (n : ℕ) : 1≤pole n := by
  have hp := Real.pi_gt_three
  have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
  dsimp [pole]
  nlinarith
lemma sub_pole_ne (x : ℝ) (n : ℕ) : (x:ℂ)-Complex.I*pole n≠0 := by
  intro he
  have hi := congrArg Complex.im he
  simp at hi
  exact (pole_pos n).ne' (by linarith)
lemma add_pole_ne (x : ℝ) (n : ℕ) : (x:ℂ)+Complex.I*pole n≠0 := by
  intro he
  have hi := congrArg Complex.im he
  simp at hi
  exact (pole_pos n).ne' hi

def termD (m : ℕ) (z : ℂ) (n : ℕ) : ℂ :=
  (-1:ℂ)^m*(m.factorial:ℂ)*
    (((z-Complex.I*pole n)⁻¹)^(m+1)+((z+Complex.I*pole n)⁻¹)^(m+1))
def realD (m : ℕ) (x : ℝ) (n : ℕ) : ℝ := (termD m (x:ℂ) n).re

lemma derivative_termD (m : ℕ) (x : ℝ) (n : ℕ) :
    HasDerivAt (fun z : ℂ=>termD m z n) (termD (m+1) x n) (x:ℂ) := by
  have h₁ := (((hasDerivAt_id (x:ℂ)).sub_const (Complex.I*pole n)).inv
    (sub_pole_ne x n)).pow (m+1)
  have h₂ := (((hasDerivAt_id (x:ℂ)).add_const (Complex.I*pole n)).inv
    (add_pole_ne x n)).pow (m+1)
  have hh := (h₁.add h₂).const_mul ((-1:ℂ)^m*(m.factorial:ℂ))
  convert! hh using 1
  dsimp only [termD,id_eq,Pi.inv_apply,Pi.pow_apply]
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    pow_succ,Nat.add_sub_cancel]
  field_simp
  <;> ring

lemma derivative_realD (m : ℕ) (x : ℝ) (n : ℕ) :
    HasDerivAt (fun y : ℝ=>realD m y n) (realD (m+1) x n) x :=
  (derivative_termD m x n).real_of_complex

lemma realD_zero (x : ℝ) (n : ℕ) : realD 0 x n=term x n := by
  have he : termD 0 (x:ℂ) n=(term x n:ℂ) := by
    simp only [termD,pow_zero,Nat.factorial_zero,Nat.cast_one,one_mul,zero_add,pow_one]
    change ((x:ℂ)-Complex.I*pole n)⁻¹+((x:ℂ)+Complex.I*pole n)⁻¹=
      ((2*x/((pole n)^2+x^2):ℝ):ℂ)
    push_cast
    have hd : ((pole n:ℂ)^2+(x:ℂ)^2)≠0 := by
      have hh : 0<(pole n)^2+x^2 := denominator_pos x n
      exact_mod_cast hh.ne'
    field_simp [sub_pole_ne x n,add_pole_ne x n,hd]
    <;> ring_nf
    <;> simp [Complex.I_sq]
    <;> ring

  exact congrArg Complex.re he

lemma inverse_pole_bound (x : ℝ) (n : ℕ) :
    ‖((x:ℂ)-Complex.I*pole n)⁻¹‖≤(pole n)⁻¹ ∧
    ‖((x:ℂ)+Complex.I*pole n)⁻¹‖≤(pole n)⁻¹ := by
  constructor
  · rw [norm_inv]
    apply inv_anti₀ (pole_pos n)
    simpa [abs_of_pos (pole_pos n)] using Complex.abs_im_le_norm ((x:ℂ)-Complex.I*pole n)
  · rw [norm_inv]
    apply inv_anti₀ (pole_pos n)
    simpa [abs_of_pos (pole_pos n)] using Complex.abs_im_le_norm ((x:ℂ)+Complex.I*pole n)

lemma termD_bound (m : ℕ) (hm : 1≤m) (x : ℝ) (n : ℕ) :
    ‖termD m (x:ℂ) n‖≤2*(m.factorial:ℝ)*term 1 n := by
  have hp : 0<pole n := pole_pos n
  have hp1 : 1≤pole n := pole_ge_one n
  have hpow : (pole n)⁻¹^(m+1)≤(pole n)⁻¹^2 :=
    pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hp1) (by omega)
  have hsmall : (pole n)⁻¹^2≤term 1 n := by
    dsimp [term]
    change (pole n)⁻¹^2≤2*1/((pole n)^2+1^2)
    rw [inv_pow,←one_div]
    apply (div_le_div_iff₀ (by positivity : 0<(pole n)^2) (by positivity)).mpr
    nlinarith
  calc
    ‖termD m (x:ℂ) n‖ ≤ (m.factorial:ℝ)*
      (‖((x:ℂ)-Complex.I*pole n)⁻¹‖^(m+1)+‖((x:ℂ)+Complex.I*pole n)⁻¹‖^(m+1)) := by
      simp only [termD,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,Complex.norm_natCast]
      gcongr
      simpa only [norm_pow] using norm_add_le ((((x:ℂ)-Complex.I*pole n)⁻¹)^(m+1)) ((((x:ℂ)+Complex.I*pole n)⁻¹)^(m+1))
    _ ≤ (m.factorial:ℝ)*((pole n)⁻¹^(m+1)+(pole n)⁻¹^(m+1)) := by
      gcongr
      · exact (inverse_pole_bound x n).1
      · exact (inverse_pole_bound x n).2
    _ ≤ 2*(m.factorial:ℝ)*term 1 n := by
      nlinarith [Nat.cast_nonneg (α:=ℝ) m.factorial]

lemma realD_summable (m : ℕ) (x : ℝ) : Summable (realD m x) := by
  rcases m with _|m
  · convert (hasSum_partial_fractions x).summable using 1
    exact funext (realD_zero x)
  · apply Summable.of_norm_bounded ((hasSum_partial_fractions 1).summable.mul_left (2*((m+1).factorial:ℝ)))
    intro n
    exact (Complex.abs_re_le_norm _).trans (termD_bound (m+1) (by omega) x n)

lemma derivative_sum (m : ℕ) (x : ℝ) : HasDerivAt (fun y : ℝ=>∑' n,realD m y n)
    (∑' n,realD (m+1) x n) x := by
  apply hasDerivAt_tsum
    ((hasSum_partial_fractions 1).summable.mul_left (2*((m+1).factorial:ℝ)))
    (fun n y=>derivative_realD m y n) ?_ (realD_summable m 0)
  intro n y
  exact (Complex.abs_re_le_norm _).trans (termD_bound (m+1) (by omega) y n)


lemma iterated_sigmoid_succ (m : ℕ) :
    iteratedDeriv (m+1) Real.sigmoid = (fun x=>∑' n,realD (m+1) x n) := by
  induction m with
  | zero =>
    funext x
    rw [iteratedDeriv_one]
    have hh := (derivative_sum 0 x).add_const (1/2)
    have hh' : HasDerivAt Real.sigmoid (∑' n,realD 1 x n) x := by
      convert hh using 1
      ext y
      rw [tsum_congr (realD_zero y),(hasSum_partial_fractions y).tsum_eq]
      ring
    exact hh'.deriv

  | succ m ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    exact (derivative_sum (m+1) x).deriv

lemma realD_even (m n : ℕ) : realD (2*m) 0 n=0 := by
  simp [realD,termD,neg_inv,neg_pow,pow_add,pow_mul,neg_one_sq]
lemma realD_odd (m n : ℕ) : realD (2*m+1) 0 n=
    (-1:ℝ)^m*((2*m+1).factorial:ℝ)*2/(pole n)^(2*m+2) := by
  have hI : ((Complex.I*(pole n:ℂ))⁻¹)^2= -((pole n:ℂ)⁻¹)^2 := by
    simp [mul_inv,mul_pow,Complex.I_sq]
  have he : termD (2*m+1) 0 n=
      (((-1:ℝ)^m*((2*m+1).factorial:ℝ)*2/(pole n)^(2*m+2):ℝ):ℂ) := by
    have hs : (-1:ℂ)^(2*m+1)= -1 := by
      rw [pow_add,pow_mul]
      simp
    have hs' : (-1:ℂ)^(2*m+2)=1 := by
      rw [pow_add,pow_mul]
      simp
    have heq : ((-(Complex.I*(pole n:ℂ)))⁻¹)^(2*m+2)=
        ((Complex.I*(pole n:ℂ))⁻¹)^(2*m+2) := by
      rw [←neg_inv,neg_pow,hs',one_mul]
    simp only [termD,zero_sub,zero_add,hs,show 2*m+1+1=2*m+2 by omega,heq]
    rw [show 2*m+2=2*(m+1) by omega,pow_mul,hI]
    push_cast
    rw [neg_pow,pow_add,pow_one]
    rw [←pow_mul]
    field_simp
    <;> ring
  simpa only [realD,Complex.ofReal_zero,Complex.ofReal_re] using congrArg Complex.re he

def atomTaylor (N : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  ∑ j∈Finset.range (N+1),realD j 0 n/(j.factorial:ℝ)*x^j
lemma atomTaylor_succ (N : ℕ) (x : ℝ) (n : ℕ) : atomTaylor (N+1) x n=
    atomTaylor N x n+realD (N+1) 0 n/((N+1).factorial:ℝ)*x^(N+1) := by
  simp only [atomTaylor,Finset.sum_range_succ]
lemma atomTaylor_hasSum (N : ℕ) (x : ℝ) : HasSum (atomTaylor N x)
    (taylorWithinEval Real.sigmoid N univ 0 x-1/2) := by
  induction N with
  | zero =>
    simp only [taylor_within_zero_eval,Real.sigmoid_zero,sub_self]
    convert (hasSum_zero : HasSum (fun _ : ℕ=>(0:ℝ)) 0) using 1
    ext n
    simp [atomTaylor,realD_zero,term]
    norm_num
  | succ N ih =>
    have hh := ((realD_summable (N+1) 0).hasSum.mul_right (((N+1).factorial:ℝ)⁻¹)).mul_right (x^(N+1))
    have ht := ih.add hh
    convert ht using 1
    · ext n
      exact atomTaylor_succ N x n
    · rw [taylorWithinEval_succ,iteratedDerivWithin_univ,iterated_sigmoid_succ]
      simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,sub_zero,smul_eq_mul]
      ring

def evenPoly (m : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  ∑ j∈Finset.range m,(-1:ℝ)^j*2*x^(2*j+1)/(pole n)^(2*j+2)
lemma atomTaylor_even (m : ℕ) (x : ℝ) (n : ℕ) : atomTaylor (2*m) x n=evenPoly m x n := by
  induction m with
  | zero => simp [atomTaylor,evenPoly,realD_even 0]
  | succ m ih =>
    rw [show 2*(m+1)=2*m+1+1 by omega,atomTaylor_succ,
      show 2*m+1+1=2*(m+1) by omega,realD_even]
    simp only [zero_div,zero_mul,add_zero]
    rw [atomTaylor_succ,ih,realD_odd]
    simp only [evenPoly,Finset.sum_range_succ]
    congr 1
    have hf : ((2*m+1).factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (2*m+1)
    field_simp
    <;> ring
lemma atomTaylor_odd (m : ℕ) (x : ℝ) (n : ℕ) : atomTaylor (2*m+1) x n=evenPoly (m+1) x n := by
  rw [atomTaylor_succ,atomTaylor_even,realD_odd]
  simp only [evenPoly,Finset.sum_range_succ]
  congr 1
  have hf : ((2*m+1).factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (2*m+1)
  field_simp
  <;> ring

lemma evenPoly_remainder (m : ℕ) (x : ℝ) (n : ℕ) :
    evenPoly m x n=term x n-(-1:ℝ)^m*2*x^(2*m+1)/
      ((pole n)^(2*m)*((pole n)^2+x^2)) := by
  have ha : pole n≠0 := (pole_pos n).ne'
  have hd : (pole n)^2+x^2≠0 := (denominator_pos x n).ne'
  induction m with
  | zero => simp [evenPoly,term,pole]
  | succ m ih =>
    simp only [evenPoly,Finset.sum_range_succ] at ⊢
    change evenPoly m x n+_= _
    rw [ih]
    simp only [show 2*(m+1)=2*m+2 by omega,show 2*(m+1)+1=(2*m+1)+2 by omega,
      pow_add,pow_succ]
    field_simp [ha,hd]
    <;> ring

def tailTerm (m : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  2*x^(2*m+1)/((pole n)^(2*m)*((pole n)^2+x^2))
lemma tail_nonnegative (m : ℕ) {x : ℝ} (hx : 0≤x) (n : ℕ) : 0≤tailTerm m x n := by
  have hp := pole_pos n
  dsimp [tailTerm]
  positivity
lemma tail_hasSum (N m : ℕ) (x : ℝ)
    (hN : ∀n,atomTaylor N x n=evenPoly m x n) :
    HasSum (tailTerm m x) ((-1:ℝ)^m*(Real.sigmoid x-taylorWithinEval Real.sigmoid N univ 0 x)) := by
  have hs := ((hasSum_partial_fractions x).sub (atomTaylor_hasSum N x)).mul_left ((-1:ℝ)^m)
  convert hs using 1
  · ext n
    rw [hN n,evenPoly_remainder]
    dsimp only [tailTerm]
    have hsign : (-1:ℝ)^m*(-1)^m=1 := by rw [←mul_pow];norm_num
    have hpow : (-1:ℝ)^(m*2)=1 := by rw [Nat.mul_comm m 2,pow_mul];norm_num
    ring_nf
    rw [hpow]
    ring
  · ring
lemma error_ge_first_pole (N m : ℕ) {x : ℝ} (hx : 0≤x)
    (hN : ∀n,atomTaylor N x n=evenPoly m x n) :
    tailTerm m x 0≤|taylorWithinEval Real.sigmoid N univ 0 x-Real.sigmoid x| := by
  have hs := tail_hasSum N m x hN
  have hnonneg : 0≤∑' n,tailTerm m x n := tsum_nonneg (tail_nonnegative m hx)
  have hfirst : tailTerm m x 0≤∑' n,tailTerm m x n :=
    hs.summable.le_tsum 0 (fun n _=>tail_nonnegative m hx n)
  rw [hs.tsum_eq] at hnonneg hfirst
  have he : |(-1:ℝ)^m*(Real.sigmoid x-taylorWithinEval Real.sigmoid N univ 0 x)|=
      |taylorWithinEval Real.sigmoid N univ 0 x-Real.sigmoid x| := by
    rw [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,abs_sub_comm]
  rw [←he,abs_of_nonneg hnonneg]
  exact hfirst

lemma evenPoly_neg (m : ℕ) (x : ℝ) (n : ℕ) : evenPoly m (-x) n= -evenPoly m x n := by
  unfold evenPoly
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hn : (-x)^(2*j+1)= -x^(2*j+1) := by
    rw [neg_pow,pow_add,pow_mul]
    simp
  rw [hn]
  ring

lemma atomTaylor_neg (N : ℕ) (x : ℝ) (n : ℕ) : atomTaylor N (-x) n= -atomTaylor N x n := by
  rcases Nat.even_or_odd N with hN|hN
  · obtain ⟨m,rfl⟩ := hN
    rw [show m+m=2*m by omega,atomTaylor_even,atomTaylor_even,evenPoly_neg]
  · obtain ⟨m,rfl⟩ := hN
    rw [atomTaylor_odd,atomTaylor_odd,evenPoly_neg]
lemma taylor_sigmoid_neg (N : ℕ) (x : ℝ) :
    taylorWithinEval Real.sigmoid N univ 0 (-x)=1-taylorWithinEval Real.sigmoid N univ 0 x := by
  have hs := (atomTaylor_hasSum N x).neg
  have he : taylorWithinEval Real.sigmoid N univ 0 (-x)-1/2=
      -(taylorWithinEval Real.sigmoid N univ 0 x-1/2) := by
    apply (atomTaylor_hasSum N (-x)).unique
    convert hs using 1
    exact funext (atomTaylor_neg N x)
  linarith

lemma tail_first_lower (m : ℕ) (hm : 1≤m) (x : ℝ) (hx : 9/2≤x) :
    (49:ℝ)/100≤tailTerm m x 0 := by
  have hp := Real.pi_pos
  have hxpos : 0<x := by linarith
  have hxπ : Real.pi≤x := by linarith [Real.pi_lt_four]
  have hratio : 1≤x/Real.pi := (one_le_div hp).mpr hxπ
  have hpow : (x/Real.pi)^2≤(x/Real.pi)^(2*m) := pow_le_pow_right₀ hratio (by omega)
  have hden : 0<Real.pi^2+x^2 := by positivity
  have hπ2 : Real.pi^2<10 := by nlinarith [Real.pi_lt_d2]
  have hπ4 : Real.pi^4<100 := by
    have hh := mul_pos (sub_pos.mpr hπ2) (by positivity : 0<10+Real.pi^2)
    nlinarith
  have hcross : Real.pi^2*x^2≤10*x^2 := mul_le_mul_of_nonneg_right hπ2.le (sq_nonneg x)
  have hx2 : 81/4≤x^2 := by nlinarith
  have hx3 : (9/2)*x^2≤x^3 := by
    have hh := mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg x)
    nlinarith
  have hbase : (49:ℝ)/100≤2*x^3/(Real.pi^2*(Real.pi^2+x^2)) := by
    apply (le_div_iff₀ (by positivity : 0<Real.pi^2*(Real.pi^2+x^2))).mpr
    nlinarith
  calc
    (49:ℝ)/100 ≤ 2*x^3/(Real.pi^2*(Real.pi^2+x^2)) := hbase
    _ = (2*x/(Real.pi^2+x^2))*(x/Real.pi)^2 := by field_simp <;> ring
    _ ≤ (2*x/(Real.pi^2+x^2))*(x/Real.pi)^(2*m) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = tailTerm m x 0 := by
      simp only [tailTerm,pole,Nat.cast_zero,mul_zero,zero_add,mul_one,div_pow,pow_succ]
      field_simp
      <;> ring

lemma all_degree_error {x : ℝ} (hx : 9/2≤x) (hfit : Real.sigmoid x=99/100) (N : ℕ) :
    (49:ℝ)/100≤|taylorWithinEval Real.sigmoid N univ 0 x-Real.sigmoid x| := by
  by_cases hzero : N=0
  · subst N
    rw [taylor_within_zero_eval,Real.sigmoid_zero,hfit]
    norm_num
  have hx0 : 0≤x := by linarith
  rcases Nat.even_or_odd N with hN|hN
  · obtain ⟨m,rfl⟩ := hN
    rw [show m+m=2*m by omega] at hzero ⊢
    exact (tail_first_lower m (by omega) x hx).trans
      (error_ge_first_pole (2*m) m hx0 (atomTaylor_even m x))
  · obtain ⟨m,rfl⟩ := hN
    exact (tail_first_lower (m+1) (by omega) x hx).trans
      (error_ge_first_pole (2*m+1) (m+1) hx0 (atomTaylor_odd m x))

lemma all_degree_negative_error {x : ℝ} (hx : 9/2≤x) (hfit : Real.sigmoid x=99/100) (N : ℕ) :
    (49:ℝ)/100≤|taylorWithinEval Real.sigmoid N univ 0 (-x)-Real.sigmoid (-x)| := by
  rw [taylor_sigmoid_neg,Real.sigmoid_neg]
  have he : 1-taylorWithinEval Real.sigmoid N univ 0 x-(1-Real.sigmoid x)=
      -(taylorWithinEval Real.sigmoid N univ 0 x-Real.sigmoid x) := by ring
  rw [he,abs_neg]
  exact all_degree_error hx hfit N

end
end AronowAudit.P015.LogisticTaylorCompletion
