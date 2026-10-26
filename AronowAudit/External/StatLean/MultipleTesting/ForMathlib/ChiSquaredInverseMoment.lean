import AronowAudit.External.StatLean.MultipleTesting.ForMathlib.ChiSquared
import Mathlib.Tactic

/- The density reduction below is adapted from the private helper in
StatLean/Stat-Lean, StatLean/MultipleTesting/ForMathlib/GammaMoments.lean
(Apache-2.0; see NOTICE at the repository root).
The file also contains the inverse-moment calculation and sum-of-squares bridge. -/
namespace AronowAudit.GaussianCompletion
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators
noncomputable section
set_option maxHeartbeats 1000000

 theorem integral_gamma_eq_setIntegral {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (g : ℝ → ℝ) :
    ∫ x, g x ∂(gammaMeasure a r) = ∫ x in Ioi (0 : ℝ), gammaPDFReal a r x*g x := by
  have hpdf : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [gammaMeasure,integral_withDensity_eq_integral_toReal_smul
    hpdf
    (ae_of_all _ (fun _=>ENNReal.ofReal_lt_top))]
  have he : ∀ x : ℝ,(gammaPDF a r x).toReal • g x=gammaPDFReal a r x*g x := by
    intro x
    rw [show gammaPDF a r x=ENNReal.ofReal (gammaPDFReal a r x) from rfl,
      ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x),smul_eq_mul]
  simp_rw [he]
  refine (setIntegral_eq_integral_of_ae_compl_eq_zero ?_).symm
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (t:={(0:ℝ)}) ?_ Real.volume_singleton
  intro x hx
  simp only [mem_ofPred_eq,Classical.not_imp,mem_Ioi,not_lt] at hx
  obtain ⟨hx1,hx2⟩:=hx
  rcases lt_or_eq_of_le hx1 with h|h
  · exact absurd (by rw [gammaPDFReal,ite_eq_right (not_le.mpr h),zero_mul]) hx2
  · exact h

 theorem gamma_inverse_integrand {a r : ℝ} (x : ℝ) (hx : 0 < x) :
    gammaPDFReal a r x*x⁻¹ =
      r^a/Real.Gamma a*(x^(a-2)*Real.exp (-(r*x))) := by
  rw [gammaPDFReal,ite_eq_left hx.le]
  have hp : x^(a-1)*x⁻¹=x^(a-2) := by
    rw [←Real.rpow_neg_one,←Real.rpow_add hx]
    congr 1
    ring
  calc
    _ = r^a/Real.Gamma a*((x^(a-1)*x⁻¹)*Real.exp (-(r*x))) := by ring
    _ = _ := by rw [hp]

 theorem integral_inv_gammaMeasure {a r : ℝ} (ha : 1 < a) (hr : 0 < r) :
    (∫ x, x⁻¹ ∂gammaMeasure a r)=r/(a-1) := by
  have ha0 : 0<a := lt_trans zero_lt_one ha
  have ha1 : 0<a-1 := sub_pos.mpr ha
  rw [integral_gamma_eq_setIntegral ha0 hr]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx=>gamma_inverse_integrand x hx)]
  rw [integral_const_mul]
  rw [show a-2=(a-1)-1 by ring]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha1 hr]
  have hg : Real.Gamma a=(a-1)*Real.Gamma (a-1) := by
    convert Real.Gamma_add_one ha1.ne' using 1 <;> congr 1 <;> ring
  have hp : r^a=r^(a-1)*r := by
    calc
      _ = r^((a-1)+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hr,Real.rpow_one]
  rw [hg,hp,one_div,Real.inv_rpow hr.le]
  field_simp [(Real.Gamma_pos_of_pos ha1).ne',(Real.rpow_pos_of_pos hr (a-1)).ne',ha1.ne']
  <;> ring


 theorem gaussian_squares_eq_gamma {ν : ℕ} (hν : 0<ν) :
    (Measure.pi (fun _:Fin ν=>gaussianReal 0 1)).map (fun z=>∑ i,(z i)^2)=
      gammaMeasure ((ν:ℝ)/2) (1/2) := by
  exact StatLean.MultipleTesting.map_sum_sq_eq_chiSquared hν (Measure.pi (fun _:Fin ν=>gaussianReal 0 1))
    (fun i z=>z i) (fun i=>measurable_pi_apply i)
    (fun i=>by simpa using Measure.pi_map_eval (fun _:Fin ν=>gaussianReal 0 1) i)
    (iIndepFun_pi (fun _=>aemeasurable_id))

 theorem integral_inv_gaussian_squares {ν : ℕ} (hν : 2<ν) :
    (∫ z : Fin ν→ℝ,(∑ i,(z i)^2)⁻¹ ∂(Measure.pi (fun _:Fin ν=>gaussianReal 0 1)))=
      1/((ν:ℝ)-2) := by
  have hshape : 1<(ν:ℝ)/2 := by
    have hn : (2:ℝ)<ν := by exact_mod_cast hν
    linarith
  have hmeas : Measurable (fun z : Fin ν→ℝ=>∑ i,(z i)^2) := by fun_prop
  calc
    _ = ∫ x:ℝ,x⁻¹ ∂gammaMeasure ((ν:ℝ)/2) (1/2) := by
      rw [←gaussian_squares_eq_gamma (by omega : 0<ν)]
      rw [integral_map hmeas.aemeasurable measurable_inv.aestronglyMeasurable]
    _ = (1/2)/((ν:ℝ)/2-1) := integral_inv_gammaMeasure hshape (by norm_num)
    _ = _ := by
      have hn : (2:ℝ)<ν := by exact_mod_cast hν
      field_simp [ne_of_gt (sub_pos.mpr hn),ne_of_gt (sub_pos.mpr hshape)]
      <;> ring


end
end AronowAudit.GaussianCompletion
