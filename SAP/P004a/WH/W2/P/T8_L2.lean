import SAP.P004a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W2.P.T8_L2

open ProbabilityTheory
open scoped NNReal
noncomputable section

private lemma student_prefactor_le_normal (ν : ℝ) (hν : 0 < ν) :
    Real.Gamma ((ν+1)/2)/(Real.sqrt (ν*Real.pi)*Real.Gamma (ν/2)) ≤
      1 / Real.sqrt (2*Real.pi) := by
  let a := ν / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hg0 : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hg1 : 0 < Real.Gamma (a+1) := Real.Gamma_pos_of_pos (by linarith)
  have hmid := AronowAudit.P004.Wave1.t7_gamma_midpoint_sq a (a+1) ha (by linarith)
  have harg : (a+(a+1))/2 = (ν+1)/2 := by dsimp [a]; ring
  rw [harg, Real.Gamma_add_one ha.ne'] at hmid
  have hsq :
      (Real.Gamma ((ν+1)/2))^2 ≤ (ν/2) * (Real.Gamma (ν/2))^2 := by
    calc
      _ ≤ Real.Gamma a * (a * Real.Gamma a) := hmid
      _ = _ := by dsimp [a]; ring
  have hden : 0 < ν*Real.pi := mul_pos hν Real.pi_pos
  have hsqrt : 0 < Real.sqrt (ν*Real.pi) := Real.sqrt_pos.mpr hden
  have hgamma : 0 < Real.Gamma (ν/2) := Real.Gamma_pos_of_pos (by linarith)
  have hp : 0 < Real.Gamma ((ν+1)/2)/(Real.sqrt (ν*Real.pi)*Real.Gamma (ν/2)) :=
    div_pos (Real.Gamma_pos_of_pos (by linarith)) (mul_pos hsqrt hgamma)
  have hn : 0 < 1/Real.sqrt (2*Real.pi) := by positivity
  apply (sq_le_sq₀ hp.le hn.le).mp
  have hleft :
      (Real.Gamma ((ν+1)/2))^2 / (Real.sqrt (ν*Real.pi)*Real.Gamma (ν/2))^2 ≤
        1/(2*Real.pi) := by
    rw [mul_pow, Real.sq_sqrt hden.le]
    apply (div_le_div_iff₀ (by positivity : 0 < (ν*Real.pi)*(Real.Gamma (ν/2))^2)
      (by positivity : 0 < 2*Real.pi)).2
    calc
      _ ≤ (ν/2 * (Real.Gamma (ν/2))^2) * (2*Real.pi) :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = (ν*Real.pi)*(Real.Gamma (ν/2))^2 := by ring
      _ = 1 * ((ν*Real.pi)*(Real.Gamma (ν/2))^2) := by ring
  have hrhs : (1/Real.sqrt (2*Real.pi))^2 = 1/(2*Real.pi) := by
    rw [one_div, inv_pow, Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi)]
    simp [one_div]
  rw [div_pow, hrhs]
  exact hleft

private lemma student_log_ratio_eq (ν : ℝ) (hν : 0 < ν) (t : ℝ) :
    Real.log (studentDensity ν t / gaussianPDFReal 0 1 t) =
      Real.log ((Real.Gamma ((ν+1)/2)/(Real.sqrt (ν*Real.pi)*Real.Gamma (ν/2))) *
        Real.sqrt (2*Real.pi)) +
        (-(ν+1)/2) * Real.log (1+t^2/ν) + t^2/2 := by
  let C := Real.Gamma ((ν+1)/2)/(Real.sqrt (ν*Real.pi)*Real.Gamma (ν/2))
  let B := 1+t^2/ν
  let e := -(ν+1)/2
  have hC : 0 < C := by
    dsimp [C]
    exact AronowAudit.P004.Wave1.t7_student_prefactor_pos ν hν
  have hB : 0 < B := by dsimp [B]; positivity
  have hS : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hE : 0 < Real.exp (t^2/2) := Real.exp_pos _
  have hratio : studentDensity ν t / gaussianPDFReal 0 1 t =
      (C * Real.sqrt (2*Real.pi)) * (B^e) * Real.exp (t^2/2) := by
    dsimp [C, B, e]
    unfold studentDensity ProbabilityTheory.gaussianPDFReal
    simp only [NNReal.coe_one, mul_one, sub_zero, one_div]
    field_simp
    rw [← Real.exp_add]
    simp
  rw [hratio, show C * Real.sqrt (2*Real.pi) * B^e * Real.exp (t^2/2) =
      (C * Real.sqrt (2*Real.pi)) * (B^e * Real.exp (t^2/2)) by ring,
    Real.log_mul (ne_of_gt (mul_pos hC hS))
      (ne_of_gt (mul_pos (Real.rpow_pos_of_pos hB e) hE)),
    Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hB e)) (ne_of_gt hE),
    Real.log_rpow hB, Real.log_exp]
  dsimp [C, B, e]
  ring

private lemma log_ratio_hasDerivAt (ν : ℝ) (hν : 0 < ν) (x : ℝ) :
    HasDerivAt (fun t => Real.log (studentDensity ν t / gaussianPDFReal 0 1 t))
      (x*(x^2-1)/(ν+x^2)) x := by
  let C := Real.Gamma ((ν+1)/2)/(Real.sqrt (ν*Real.pi)*Real.Gamma (ν/2))
  let e := -(ν+1)/2
  let B : ℝ → ℝ := fun t => 1+t^2/ν
  have hBpos : 0 < B x := by dsimp [B]; positivity
  have hsq : HasDerivAt (fun t : ℝ => t^2) (2*x) x := by
    simpa [pow_one] using (hasDerivAt_pow 2 x)
  have hB : HasDerivAt B (2*x/ν) x := by
    simpa [B, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((hsq.div_const ν).const_add 1)
  have hlogB : HasDerivAt (fun t => Real.log (B t)) ((2*x/ν)/B x) x :=
    hB.log (ne_of_gt hBpos)
  have hterm : HasDerivAt (fun t => e * Real.log (B t))
      (e*((2*x/ν)/B x)) x := hlogB.const_mul e
  have hquad : HasDerivAt (fun t : ℝ => t^2/2) (2*x/2) x := by
    simpa using hsq.div_const 2
  have hsum := (hterm.const_add (Real.log (C*Real.sqrt (2*Real.pi)))).add hquad
  have heq : (fun t => Real.log (studentDensity ν t / ProbabilityTheory.gaussianPDFReal 0 1 t)) =
      (fun t => Real.log (C*Real.sqrt (2*Real.pi)) + e*Real.log (B t) + t^2/2) := by
    funext t
    simpa [C, e, B] using student_log_ratio_eq ν hν t
  have hfinal := hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => by
    simpa using congrFun heq t))
  apply hfinal.congr_deriv
  dsimp [C, e, B]
  field_simp [ne_of_gt hν, ne_of_gt hBpos]
  <;> ring

end

end SAP.P004a.WH.W2.P.T8_L2

open SAP.P004a.WH.W2.P.T8_L2
open ProbabilityTheory

theorem SAP.P004a.WH.W2.T8_L2_proof : SAP.P004a.WH.W2.T8_L2 := by
  intro ν hν
  constructor
  · change studentDensity ν 0 ≤ ProbabilityTheory.gaussianPDFReal 0 1 0
    unfold studentDensity ProbabilityTheory.gaussianPDFReal
    simp only [NNReal.coe_one, mul_one, sub_zero, one_div, Real.rpow_zero, Real.exp_zero,
      mul_one]
    simpa [Real.sqrt_mul, Real.sqrt_sq_eq_abs, abs_of_pos Real.pi_pos] using
      student_prefactor_le_normal ν hν
  · intro x
    exact SAP.P004a.WH.W2.P.T8_L2.log_ratio_hasDerivAt ν hν x
