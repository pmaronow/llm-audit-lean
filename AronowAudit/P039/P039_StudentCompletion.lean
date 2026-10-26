import AronowAudit.External.StatLean.MultipleTesting.ForMathlib.GaussianRatioMoments
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Exact moment-domain separation of different finite Student laws.
The law is the original explicit ratio of independent standard Gaussian coordinates.
No distribution identification or integrability statement is assumed. -/

namespace AronowAudit.P039.StudentCompletion
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators
noncomputable section
set_option maxHeartbeats 2000000

theorem gamma_rpow_integrand {a r q : ℝ} (x : ℝ) (hx : 0 < x) :
    gammaPDFReal a r x * x^q =
      r^a / Real.Gamma a * (x^(a+q-1) * Real.exp (-(r*x))) := by
  rw [gammaPDFReal, ite_eq_left hx.le]
  rw [show a+q-1=(a-1)+q by ring, Real.rpow_add hx]
  ring

theorem integrable_rpow_gamma {a r q : ℝ} (ha : 0<a) (hr : 0<r)
    (hq : -a<q) : Integrable (fun x : ℝ => x^q) (gammaMeasure a r) := by
  have hpdf : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [gammaMeasure, integrable_withDensity_iff hpdf
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have he : (fun x : ℝ => x^q * (gammaPDF a r x).toReal) =
      fun x => gammaPDFReal a r x * x^q := by
    funext x
    rw [show gammaPDF a r x=ENNReal.ofReal (gammaPDFReal a r x) from rfl,
      ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)]
    ring
  rw [he]
  have hm : IntegrableOn (fun x : ℝ => x^(a+q-1)*Real.exp (-(r*x))) (Ioi 0) := by
    have hh := integrableOn_rpow_mul_exp_neg_mul_rpow (p:=1) (s:=a+q-1) (b:=r)
      (by linarith) (by norm_num) hr
    exact hh.congr_fun (fun x hx => by simp only [Real.rpow_one,neg_mul]) measurableSet_Ioi
  have hmc : IntegrableOn (fun x : ℝ => r^a/Real.Gamma a *
      (x^(a+q-1)*Real.exp (-(r*x)))) (Ioi 0) := hm.const_mul _
  have hm' : IntegrableOn (fun x : ℝ => gammaPDFReal a r x*x^q) (Ioi 0) :=
    hmc.congr_fun (fun x hx => (gamma_rpow_integrand x hx).symm) measurableSet_Ioi
  rw [← integrableOn_univ, ← Iic_union_Ioi (a:=(0:ℝ)), integrableOn_union]
  refine ⟨?_, hm'⟩
  apply integrableOn_zero.congr
  filter_upwards [ae_restrict_mem measurableSet_Iic, ae_restrict_of_ae (Measure.ae_ne volume (0:ℝ))] with x hx hx0
  have hxn : x<0 := lt_of_le_of_ne hx hx0
  simp [gammaPDFReal,not_le.mpr hxn]

theorem not_integrable_rpow_gamma {a r q : ℝ} (ha : 0<a) (hr : 0<r)
    (hq : q≤-a) : ¬Integrable (fun x : ℝ => x^q) (gammaMeasure a r) := by
  intro h
  have hpdf : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [gammaMeasure, integrable_withDensity_iff hpdf
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))] at h
  have he : (fun x : ℝ => x^q * (gammaPDF a r x).toReal) =
      fun x => gammaPDFReal a r x * x^q := by
    funext x
    rw [show gammaPDF a r x=ENNReal.ofReal (gammaPDFReal a r x) from rfl,
      ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)]
    ring
  rw [he] at h
  have hi := h.integrableOn (s:=Ioo (0:ℝ) 1)
  have hc : ContinuousOn (fun x : ℝ => Real.exp (r*x)) (Icc 0 1) := by fun_prop
  have hi' := hi.mul_continuousOn_of_subset hc measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
  have hc0 : r^a / Real.Gamma a ≠ 0 := div_ne_zero
    (Real.rpow_pos_of_pos hr a).ne' (Real.Gamma_pos_of_pos ha).ne'
  have hi'' : IntegrableOn (fun x : ℝ => x^(a+q-1)) (Ioo 0 1) := by
    have hh : IntegrableOn (fun x : ℝ => (r^a / Real.Gamma a)⁻¹ *
        ((gammaPDFReal a r x*x^q)*Real.exp (r*x))) (Ioo 0 1) :=
      hi'.const_mul (r^a / Real.Gamma a)⁻¹
    apply hh.congr_fun _ measurableSet_Ioo
    intro x hx
    dsimp only
    rw [gamma_rpow_integrand x hx.1]
    have he0 : Real.exp (-(r*x))*Real.exp (r*x)=1 := by rw [←Real.exp_add]; simp
    change _ = x^(a+q-1)
    calc
      _ = ((r^a / Real.Gamma a)⁻¹ * (r^a / Real.Gamma a)) * x^(a+q-1) *
        (Real.exp (-(r*x))*Real.exp (r*x)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hc0,he0]; ring
  have ht := (intervalIntegral.integrableOn_Ioo_rpow_iff (show (0:ℝ)<1 by norm_num)).mp hi''
  linarith

theorem gaussian_squares_rpow_integrable_iff {ν : ℕ} (hν : 0<ν) (q : ℝ) :
    Integrable (fun z : Fin ν → ℝ => (∑ i, (z i)^2)^q)
      (Measure.pi (fun _ : Fin ν => gaussianReal 0 1)) ↔ -(ν:ℝ)/2<q := by
  have hs := AronowAudit.GaussianCompletion.gaussian_squares_eq_gamma hν
  have hmap : Integrable (fun x : ℝ => x^q)
      ((Measure.pi (fun _ : Fin ν => gaussianReal 0 1)).map (fun z => ∑ i, (z i)^2)) ↔
      Integrable (fun z : Fin ν → ℝ => (∑ i, (z i)^2)^q)
        (Measure.pi (fun _ : Fin ν => gaussianReal 0 1)) :=
    integrable_map_measure (by fun_prop)
      (show Measurable (fun z : Fin ν → ℝ => ∑ i, (z i)^2) from by fun_prop).aemeasurable
  rw [hs] at hmap
  rw [←hmap]
  constructor
  · intro h
    by_contra hq
    exact not_integrable_rpow_gamma (by positivity) (by norm_num)
      (by linarith [le_of_not_gt hq]) h
  · intro hq
    exact integrable_rpow_gamma (by positivity) (by norm_num) (by linarith)

theorem integrable_mul_prod_iff_right {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) (η : Measure β)
    [SFinite μ] [SFinite η] [NeZero μ]
    (f : α → ℝ) (g : β → ℝ) (hf : Integrable f μ)
    (hn : ∀ᵐ x ∂μ, f x≠0) :
    Integrable (fun z : α×β => f z.1*g z.2) (μ.prod η) ↔ Integrable g η := by
  constructor
  · intro h
    obtain ⟨x,hx,hxn⟩ := (h.prod_right_ae.and hn).exists
    exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hxn) g).mp hx
  · exact hf.mul_prod

def ratio {ν : ℕ} (z : Fin (ν+1) → ℝ) : ℝ :=
  z 0 / Real.sqrt ((∑ i ∈ Finset.univ.erase (0 : Fin (ν+1)), (z i)^2) / ν)

def tailSquares {ν : ℕ} (z : Fin ν → ℝ) : ℝ := ∑ i, (z i)^2

def split (ν : ℕ) : (Fin (ν+1) → ℝ) ≃ᵐ ℝ×(Fin ν → ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0

theorem split_tail {ν : ℕ} (z : Fin (ν+1) → ℝ) :
    (∑ i ∈ Finset.univ.erase (0 : Fin (ν+1)), (z i)^2) = tailSquares (split ν z).2 := by
  have ha := Fin.sum_univ_succAbove (fun i : Fin (ν+1) => (z i)^2) 0
  have hb := Finset.sum_erase_add Finset.univ (fun i : Fin (ν+1) => (z i)^2)
    (Finset.mem_univ (0 : Fin (ν+1)))
  change _=∑ j : Fin ν, (z ((0 : Fin (ν+1)).succAbove j))^2
  linarith

theorem abs_ratio_factor {ν : ℕ} (z : Fin (ν+1) → ℝ) :
    |ratio z| = |(split ν z).1| * (Real.sqrt (ν:ℝ) *
      (tailSquares (split ν z).2)^(-(1/2:ℝ))) := by
  have hs : 0≤tailSquares (split ν z).2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  simp only [ratio,abs_div,abs_of_nonneg (Real.sqrt_nonneg _),split_tail]
  rw [Real.sqrt_div hs, Real.rpow_neg hs, ←Real.sqrt_eq_rpow]
  change |z 0| / (Real.sqrt (tailSquares (split ν z).2) / Real.sqrt (ν:ℝ)) =
    |z 0| * (Real.sqrt (ν:ℝ) * (Real.sqrt (tailSquares (split ν z).2))⁻¹)
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]

theorem sq_ratio_factor {ν : ℕ} (z : Fin (ν+1) → ℝ) :
    (ratio z)^2 = ((split ν z).1)^2 * ((ν:ℝ) *
      (tailSquares (split ν z).2)^(-1:ℝ)) := by
  have hs : 0≤tailSquares (split ν z).2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  simp only [ratio,div_pow,Real.sq_sqrt (div_nonneg hs (Nat.cast_nonneg ν)),split_tail,
    Real.rpow_neg_one]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  rfl

theorem integrable_abs_ratio_iff {ν : ℕ} (hν : 0<ν) :
    Integrable (fun z : Fin (ν+1) → ℝ => |ratio z|)
      (Measure.pi (fun _ : Fin (ν+1) => gaussianReal 0 1)) ↔ 1<ν := by
  let μ := Measure.pi (fun _ : Fin (ν+1) => gaussianReal 0 1)
  let η := Measure.pi (fun _ : Fin ν => gaussianReal 0 1)
  let F : ℝ×(Fin ν → ℝ) → ℝ := fun z => |z.1| *
    (Real.sqrt (ν:ℝ) * (tailSquares z.2)^(-(1/2:ℝ)))
  have he : μ.map (split ν)=(gaussianReal 0 1).prod η :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (ν+1) => gaussianReal 0 1) 0).map_eq
  have hm : Integrable F (μ.map (split ν)) ↔ Integrable (F ∘ split ν) μ :=
    integrable_map_measure (show Measurable F from by dsimp [F,tailSquares]; fun_prop).aestronglyMeasurable
      (split ν).measurable.aemeasurable
  rw [he] at hm
  have hf : (fun z : Fin (ν+1) → ℝ => |ratio z|)=F ∘ split ν := funext abs_ratio_factor
  change Integrable (fun z : Fin (ν+1) → ℝ => |ratio z|) μ ↔ _
  rw [hf,←hm]
  have hg : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) := by
    simpa only [Real.norm_eq_abs,id_eq] using
      ((memLp_id_gaussianReal (μ:=0) (v:=1) 1).integrable (by norm_num)).norm
  have hn : ∀ᵐ x : ℝ ∂gaussianReal 0 1, |x|≠0 := by
    letI := nullSingletonClass_gaussianReal (μ:=0) (v:=1) (by norm_num)
    filter_upwards [Measure.ae_ne (gaussianReal 0 1) (0:ℝ)] with x hx
    exact abs_ne_zero.mpr hx
  rw [show F=(fun z : ℝ×(Fin ν → ℝ) => |z.1| *
    (Real.sqrt (ν:ℝ) * (tailSquares z.2)^(-(1/2:ℝ)))) from rfl,
    integrable_mul_prod_iff_right (gaussianReal 0 1) η (fun x : ℝ => |x|)
      (fun z : Fin ν → ℝ => Real.sqrt (ν:ℝ) * (tailSquares z)^(-(1/2:ℝ))) hg hn]
  have hs : Real.sqrt (ν:ℝ)≠0 := (Real.sqrt_pos.mpr (by exact_mod_cast hν)).ne'
  rw [integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hs)]
  have hi := gaussian_squares_rpow_integrable_iff hν (-(1/2:ℝ))
  change Integrable (fun z : Fin ν → ℝ => (∑ i, (z i)^2)^(-(1/2:ℝ))) η ↔ _
  rw [hi]
  constructor <;> intro h
  · exact_mod_cast (show (1:ℝ)<ν by linarith)
  · have hh : (1:ℝ)<ν := by exact_mod_cast h
    linarith

theorem integrable_sq_ratio_iff {ν : ℕ} (hν : 0<ν) :
    Integrable (fun z : Fin (ν+1) → ℝ => (ratio z)^2)
      (Measure.pi (fun _ : Fin (ν+1) => gaussianReal 0 1)) ↔ 2<ν := by
  let μ := Measure.pi (fun _ : Fin (ν+1) => gaussianReal 0 1)
  let η := Measure.pi (fun _ : Fin ν => gaussianReal 0 1)
  let F : ℝ×(Fin ν → ℝ) → ℝ := fun z => z.1^2 *
    ((ν:ℝ) * (tailSquares z.2)^(-1:ℝ))
  have he : μ.map (split ν)=(gaussianReal 0 1).prod η :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (ν+1) => gaussianReal 0 1) 0).map_eq
  have hm : Integrable F (μ.map (split ν)) ↔ Integrable (F ∘ split ν) μ :=
    integrable_map_measure (show Measurable F from by dsimp [F,tailSquares]; fun_prop).aestronglyMeasurable
      (split ν).measurable.aemeasurable
  rw [he] at hm
  have hf : (fun z : Fin (ν+1) → ℝ => (ratio z)^2)=F ∘ split ν := funext sq_ratio_factor
  change Integrable (fun z : Fin (ν+1) → ℝ => (ratio z)^2) μ ↔ _
  rw [hf,←hm]
  have hg : Integrable (fun x : ℝ => x^2) (gaussianReal 0 1) := by
    simpa only [id_eq] using (memLp_id_gaussianReal (μ:=0) (v:=1) 2).integrable_sq
  have hn : ∀ᵐ x : ℝ ∂gaussianReal 0 1, x^2≠0 := by
    letI := nullSingletonClass_gaussianReal (μ:=0) (v:=1) (by norm_num)
    filter_upwards [Measure.ae_ne (gaussianReal 0 1) (0:ℝ)] with x hx
    exact pow_ne_zero 2 hx
  rw [show F=(fun z : ℝ×(Fin ν → ℝ) => z.1^2 *
    ((ν:ℝ) * (tailSquares z.2)^(-1:ℝ))) from rfl,
    integrable_mul_prod_iff_right (gaussianReal 0 1) η (fun x : ℝ => x^2)
      (fun z : Fin ν → ℝ => (ν:ℝ) * (tailSquares z)^(-1:ℝ)) hg hn]
  have hs : (ν:ℝ)≠0 := by exact_mod_cast hν.ne'
  rw [integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hs)]
  have hi := gaussian_squares_rpow_integrable_iff hν (-1:ℝ)
  change Integrable (fun z : Fin ν → ℝ => (∑ i, (z i)^2)^(-1:ℝ)) η ↔ _
  rw [hi]
  constructor <;> intro h
  · exact_mod_cast (show (2:ℝ)<ν by linarith)
  · have hh : (2:ℝ)<ν := by exact_mod_cast h
    linarith

def ratioLaw (ν : ℕ) : Measure ℝ :=
  (Measure.pi (fun _ : Fin (ν+1) => gaussianReal 0 1)).map (ratio (ν:=ν))

theorem integrable_abs_ratioLaw_iff {ν : ℕ} (hν : 0<ν) :
    Integrable (fun t : ℝ => |t|) (ratioLaw ν) ↔ 1<ν := by
  rw [ratioLaw,integrable_map_measure (by fun_prop)
    (show Measurable (ratio (ν:=ν)) from by unfold ratio; fun_prop).aemeasurable]
  exact integrable_abs_ratio_iff hν

theorem integrable_sq_ratioLaw_iff {ν : ℕ} (hν : 0<ν) :
    Integrable (fun t : ℝ => t^2) (ratioLaw ν) ↔ 2<ν := by
  rw [ratioLaw,integrable_map_measure (by fun_prop)
    (show Measurable (ratio (ν:=ν)) from by unfold ratio; fun_prop).aemeasurable]
  exact integrable_sq_ratio_iff hν

theorem integrable_abs_scale_iff (μ : Measure ℝ) (c : ℝ) (hc : c≠0) :
    Integrable (fun t : ℝ => |t|) (μ.map (fun t => c*t)) ↔
      Integrable (fun t : ℝ => |t|) μ := by
  rw [integrable_map_measure (by fun_prop)
    (show Measurable (fun t : ℝ => c*t) from by fun_prop).aemeasurable]
  simp only [Function.comp_def,abs_mul]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (abs_ne_zero.mpr hc)) _

theorem integrable_sq_scale_iff (μ : Measure ℝ) (c : ℝ) (hc : c≠0) :
    Integrable (fun t : ℝ => t^2) (μ.map (fun t => c*t)) ↔
      Integrable (fun t : ℝ => t^2) μ := by
  rw [integrable_map_measure (by fun_prop)
    (show Measurable (fun t : ℝ => c*t) from by fun_prop).aemeasurable]
  simp only [Function.comp_def,mul_pow]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hc)) _

theorem ratioLaw_second_moment {ν : ℕ} (hν : 2<ν) :
    (∫ t : ℝ, t^2 ∂ratioLaw ν) = (ν:ℝ)/((ν:ℝ)-2) :=
  AronowAudit.GaussianCompletion.gaussian_ratio_law_second_moment hν

theorem scaled_ratioLaw_second_moment {ν : ℕ} (hν : 2<ν) (c : ℝ) :
    (∫ t : ℝ, t^2 ∂(ratioLaw ν).map (fun t => c*t)) =
      c^2 * ((ν:ℝ)/((ν:ℝ)-2)) := by
  rw [integral_map (by fun_prop : Measurable (fun t : ℝ => c*t)).aemeasurable (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul,ratioLaw_second_moment hν]

theorem scaled_ratioLaw_ne {ν ν' : ℕ} (hν : 0<ν) (hlt : ν<ν') :
    (ratioLaw ν).map (fun t => Real.sqrt ((ν':ℝ)/ν)*t) ≠ ratioLaw ν' := by
  have hν' : 0<ν' := lt_trans hν hlt
  have hνr : (0:ℝ)<ν := by exact_mod_cast hν
  have hν'r : (0:ℝ)<ν' := by exact_mod_cast hν'
  have hc : Real.sqrt ((ν':ℝ)/ν)≠0 := (Real.sqrt_pos.mpr (div_pos hν'r hνr)).ne'
  intro he
  by_cases h1 : ν=1
  · have ht : Integrable (fun t : ℝ => |t|) (ratioLaw ν') :=
      (integrable_abs_ratioLaw_iff hν').mpr (by omega)
    rw [←he] at ht
    have hs := (integrable_abs_scale_iff (ratioLaw ν) _ hc).mp ht
    have hh := (integrable_abs_ratioLaw_iff hν).mp hs
    omega
  by_cases h2 : ν=2
  · have ht : Integrable (fun t : ℝ => t^2) (ratioLaw ν') :=
      (integrable_sq_ratioLaw_iff hν').mpr (by omega)
    rw [←he] at ht
    have hs := (integrable_sq_scale_iff (ratioLaw ν) _ hc).mp ht
    have hh := (integrable_sq_ratioLaw_iff hν).mp hs
    omega
  have hn : 2<ν := by omega
  have hn' : 2<ν' := lt_trans hn hlt
  have hm := congrArg (fun μ : Measure ℝ => ∫ t : ℝ, t^2 ∂μ) he
  rw [scaled_ratioLaw_second_moment hn,ratioLaw_second_moment hn',
    Real.sq_sqrt (div_nonneg hν'r.le hνr.le)] at hm
  have hnr : (2:ℝ)<ν := by exact_mod_cast hn
  have hn'r : (2:ℝ)<ν' := by exact_mod_cast hn'
  have hlt' : (ν:ℝ)<ν' := by exact_mod_cast hlt
  have hn0 : (ν:ℝ)-2≠0 := (sub_pos.mpr hnr).ne'
  have hn'0 : (ν':ℝ)-2≠0 := (sub_pos.mpr hn'r).ne'
  field_simp [hνr.ne',hn0,hn'0] at hm
  nlinarith

end
end AronowAudit.P039.StudentCompletion
