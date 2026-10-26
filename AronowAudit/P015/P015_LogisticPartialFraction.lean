/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- The logistic partial fractions are derived from Mathlib's theorem
`cot_series_rep'` (Chris Birkbeck, Apache-2.0).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Tactic
namespace AronowAudit.P015.LogisticPartialFraction
open Complex Real Set Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

def term (x : ℝ) (n : ℕ) : ℝ := 2*x/((Real.pi*(2*n+1))^2+x^2)
def shift (x : ℝ) : ℂ := ((1/2:ℝ):ℂ)+Complex.I*((x/(2*Real.pi):ℝ):ℂ)
lemma denominator_pos (x : ℝ) (n : ℕ) : 0<(Real.pi*(2*n+1))^2+x^2 := by
  have : 0<Real.pi*(2*(n:ℝ)+1) := by positivity
  nlinarith [sq_pos_of_pos this,sq_nonneg x]
lemma shift_noninteger (x : ℝ) : shift x∈Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨k,hk⟩
  have he := congrArg Complex.re hk
  norm_num [shift,←Complex.ofReal_div,←Complex.ofReal_mul] at he
  have : (k:ℝ)<1 := by linarith
  have h0 : (0:ℝ)<k := by linarith
  norm_cast at this h0
  omega
lemma shift_exp (x : ℝ) : Complex.exp (2*Complex.I*(Real.pi*shift x))= -(Real.exp (-x):ℂ) := by
  have hp : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  have he : 2*Complex.I*(Real.pi*shift x)=(Real.pi*Complex.I)+(-x:ℂ) := by
    simp only [shift,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat]
    field_simp
    <;> ring_nf
    <;> simp [Complex.I_sq]
    <;> ring
  rw [he,Complex.exp_add,Complex.exp_pi_mul_I]
  norm_cast
  simp
lemma cot_value_im (x : ℝ) : (Real.pi*Complex.cot (Real.pi*shift x)).im=
    Real.pi*(1-2*Real.sigmoid x) := by
  have hx : 1+Real.exp (-x)≠0 := by positivity
  have he : (Complex.cot (Real.pi*shift x))=(Complex.I*(1-2*Real.sigmoid x):ℂ) := by
    rw [Complex.cot_eq_exp_ratio,shift_exp]
    have hxc : (1+(Real.exp (-x):ℂ))≠0 := by exact_mod_cast hx
    simp only [Real.sigmoid_def,Complex.ofReal_inv,Complex.ofReal_add,Complex.ofReal_one,sub_neg_eq_add]
    change (-(Real.exp (-x):ℂ)+1)/(Complex.I*(1+(Real.exp (-x):ℂ)))=
      Complex.I*(1-2*(1+(Real.exp (-x):ℂ))⁻¹)
    field_simp [hxc]
    <;> ring_nf
    <;> simp [Complex.I_sq]
    <;> ring

  rw [he]
  simp
lemma inverse_im (x : ℝ) (k : ℤ) : ((shift x+k)⁻¹).im=
    -Real.pi*(2*x/((Real.pi*(2*k+1))^2+x^2)) := by
  have hp : Real.pi≠0 := Real.pi_ne_zero
  have hk : 2*(k:ℝ)+1≠0 := by
    intro he
    have h : (2*k+1:ℤ)=0 := by exact_mod_cast he
    omega
  have hd : 0<(Real.pi*(2*k+1))^2+x^2 := by
    have hn : Real.pi*(2*(k:ℝ)+1)≠0 := mul_ne_zero hp hk
    nlinarith [sq_pos_of_ne_zero hn,sq_nonneg x]
  have hre : (shift x+(k:ℂ)).re=1/2+(k:ℝ) := by
    simp [shift,←Complex.ofReal_div,←Complex.ofReal_mul]
  have him : (shift x+(k:ℂ)).im=x/(2*Real.pi) := by
    simp [shift,←Complex.ofReal_div,←Complex.ofReal_mul]
  rw [Complex.inv_im,Complex.normSq_apply,hre,him]
  have hn : (1/2+(k:ℝ))^2+(x/(2*Real.pi))^2=
      ((Real.pi*(2*k+1))^2+x^2)/(4*Real.pi^2) := by
    field_simp [hp]
    <;> ring
  rw [←sq,←sq,hn]
  field_simp [hp,hd.ne']
  <;> ring


lemma inverse_zero (x : ℝ) : ((shift x)⁻¹).im= -Real.pi*term x 0 := by
  simpa [term] using inverse_im x 0
lemma inverse_plus (x : ℝ) (n : ℕ) : ((shift x+(n+1))⁻¹).im= -Real.pi*term x (n+1) := by
  simpa [term] using inverse_im x ((n:ℤ)+1)
lemma inverse_minus (x : ℝ) (n : ℕ) : ((shift x-(n+1))⁻¹).im= -Real.pi*term x n := by
  have he := inverse_im x (-((n:ℤ)+1))
  convert he using 1
  · congr 1
    push_cast
    ring
  · dsimp only [term]
    push_cast
    congr 3
    ring

lemma paired_sum (x : ℝ) : HasSum (fun n=> -Real.pi*(term x (n+1)+term x n))
    (Real.pi*(1-2*Real.sigmoid x)+Real.pi*term x 0) := by
  have hs := Complex.hasSum_im (summable_cotTerm (shift_noninteger x)).hasSum
  rw [← cot_series_rep' (shift_noninteger x)] at hs
  convert hs using 1
  · ext n
    simp only [cotTerm,one_div,Complex.add_im,inverse_plus,inverse_minus]
    ring
  · simp only [Complex.sub_im,cot_value_im,one_div,inverse_zero]
    ring

lemma term_nonnegative {x : ℝ} (hx : 0≤x) (n : ℕ) : 0≤term x n :=
  div_nonneg (by positivity) (denominator_pos x n).le

lemma term_summable_nonneg {x : ℝ} (hx : 0≤x) : Summable (term x) := by
  have hs := (paired_sum x).summable.mul_left (-Real.pi)⁻¹
  have hh : Summable (fun n=>term x (n+1)+term x n) := by
    simpa only [←mul_assoc,inv_mul_cancel₀ (neg_ne_zero.mpr Real.pi_ne_zero),one_mul] using hs
  exact Summable.of_nonneg_of_le (term_nonnegative hx)
    (fun n=>le_add_of_nonneg_left (term_nonnegative hx (n+1))) hh

lemma hasSum_nonnegative {x : ℝ} (hx : 0≤x) : HasSum (term x) (Real.sigmoid x-1/2) := by
  have ht := term_summable_nonneg hx
  have hs1 : HasSum (fun n=>term x (n+1)+term x n) (2*∑' n,term x n-term x 0) := by
    have hh : HasSum (fun n=>term x (n+1)) ((∑' n,term x n)-term x 0) := by
      simpa using (hasSum_nat_add_iff' 1).mpr ht.hasSum
    convert hh.add ht.hasSum using 1 <;> ring
  have hs2 := hs1.mul_left (-Real.pi)
  have he := (paired_sum x).unique hs2
  have hv : (∑' n,term x n)=Real.sigmoid x-1/2 := by
    nlinarith [Real.pi_pos]
  simpa only [hv] using ht.hasSum

lemma hasSum_partial_fractions (x : ℝ) : HasSum (term x) (Real.sigmoid x-1/2) := by
  rcases le_total 0 x with hx|hx
  · exact hasSum_nonnegative hx
  · have hh := (hasSum_nonnegative (neg_nonneg.mpr hx)).neg
    convert hh using 1
    · ext n
      simp only [term,neg_sq,mul_neg,neg_div,neg_neg]
    · rw [Real.sigmoid_neg]
      ring

end
end AronowAudit.P015.LogisticPartialFraction
