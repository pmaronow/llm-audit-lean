import AronowAudit.P001.P001_Foundations
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Group.LIntegral

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidableGLP0013B2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

lemma bivariate_normal_q_pos (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) :
    0 < 1 - ρ ^ 2 := by
  rcases hρ with ⟨hl, hu⟩
  nlinarith [mul_pos (show 0 < 1 - ρ by linarith) (show 0 < 1 + ρ by linarith)]

/-- Completion of the square in the printed density, including its normalizer. -/
lemma bivariate_normal_factor (mx my sx sy ρ : ℝ) (hx : 0 < sx) (hy : 0 < sy)
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) (xy : ℝ × ℝ) :
    bivariateNormalPDF mx my sx sy ρ xy =
      normalDensity mx sx xy.1 *
        normalDensity (my + (ρ * sy / sx) * (xy.1 - mx))
          (sy * Real.sqrt (1 - ρ ^ 2)) xy.2 := by
  have hq := bivariate_normal_q_pos ρ hρ
  have hr : 0 < Real.sqrt (1 - ρ ^ 2) := Real.sqrt_pos.2 hq
  have hr2 := Real.sq_sqrt hq.le
  have hp2 := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have he :
      -(((xy.1-mx)/sx)^2+((xy.2-my)/sy)^2-
        2*ρ*(xy.1-mx)*(xy.2-my)/(sx*sy))/(2*(1-ρ^2)) =
      -(xy.1-mx)^2/(2*sx^2) +
        -(xy.2-(my+(ρ*sy/sx)*(xy.1-mx)))^2 /
          (2*(sy*Real.sqrt (1-ρ^2))^2) := by
    field_simp
    nlinarith [hr2]
  unfold bivariateNormalPDF normalDensity
  rw [he, Real.exp_add]
  have hd : (sx * Real.sqrt (2 * Real.pi)) *
        (sy * Real.sqrt (1 - ρ ^ 2) * Real.sqrt (2 * Real.pi)) =
      2 * Real.pi * sx * sy * Real.sqrt (1 - ρ ^ 2) := by
    calc
      _ = sx * sy * Real.sqrt (1 - ρ ^ 2) * (Real.sqrt (2 * Real.pi)) ^ 2 := by ring
      _ = _ := by rw [hp2]; ring
  rw [div_mul_div_comm, hd]

lemma bivariate_normal_density_measurable (mx my sx sy ρ : ℝ) :
    Measurable (bivariateNormalPDF mx my sx sy ρ) := by
  unfold bivariateNormalPDF
  fun_prop

lemma bivariate_normal_density_nonneg (mx my sx sy ρ : ℝ) (hx : 0 < sx) (hy : 0 < sy)
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) (xy : ℝ × ℝ) :
    0 ≤ bivariateNormalPDF mx my sx sy ρ xy := by
  have hq := bivariate_normal_q_pos ρ hρ
  unfold bivariateNormalPDF
  positivity

def bivariate_normal_sq (s : ℝ) : ℝ≥0 := ⟨s ^ 2, sq_nonneg _⟩

def bivariate_normal_source (mx sx d : ℝ) : Measure (ℝ × ℝ) :=
  (gaussianReal mx (bivariate_normal_sq sx)).prod
    (gaussianReal 0 (bivariate_normal_sq d))

def bivariate_normal_transport (mx my c : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1, my + c * (z.1 - mx) + z.2)

lemma bivariate_normal_source_density (mx sx d : ℝ) (hx : 0 < sx) (hd : 0 < d) :
    bivariate_normal_source mx sx d =
      volume.withDensity (fun z : ℝ × ℝ =>
        ENNReal.ofReal (normalDensity mx sx z.1 * normalDensity 0 d z.2)) := by
  let vx : ℝ≥0 := bivariate_normal_sq sx
  let vd : ℝ≥0 := bivariate_normal_sq d
  have hxv : vx ≠ 0 := by
    apply ne_of_gt
    change 0 < sx ^ 2
    positivity
  have hdv : vd ≠ 0 := by
    apply ne_of_gt
    change 0 < d ^ 2
    positivity
  change (gaussianReal mx vx).prod (gaussianReal 0 vd) = _
  rw [gaussianReal_of_var_ne_zero _ hxv, gaussianReal_of_var_ne_zero _ hdv,
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _)]
  congr 1
  funext z
  simp only [normalDensity_eq_gaussianPDFReal _ _ hx, normalDensity_eq_gaussianPDFReal _ _ hd]
  change ENNReal.ofReal (gaussianPDFReal mx vx z.1) *
      ENNReal.ofReal (gaussianPDFReal 0 vd z.2) =
    ENNReal.ofReal (gaussianPDFReal mx vx z.1 * gaussianPDFReal 0 vd z.2)
  exact (ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)).symm

/-- Tonelli identity for arbitrary nonnegative Borel tests. Both sides are lower integrals;
no Bochner-integrability assertion is made here. Translation in the second coordinate
realizes the conditional normal as an independent centered normal plus its conditional mean. -/
lemma bivariate_normal_conditional_lintegral (mx my sx d c : ℝ) (hx : 0 < sx) (hd : 0 < d)
    (H : ℝ × ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ z, H z ∂volume.withDensity (fun z : ℝ × ℝ =>
      ENNReal.ofReal (normalDensity mx sx z.1 *
        normalDensity (my + c * (z.1 - mx)) d z.2))) =
    ∫⁻ z, H (bivariate_normal_transport mx my c z) ∂bivariate_normal_source mx sx d := by
  have hnd : Measurable (fun z : ℝ × ℝ => normalDensity mx sx z.1 *
      normalDensity (my + c * (z.1 - mx)) d z.2) := by
    unfold normalDensity
    fun_prop
  have hnd0 : Measurable (fun z : ℝ × ℝ =>
      normalDensity mx sx z.1 * normalDensity 0 d z.2) := by
    unfold normalDensity
    fun_prop
  have hT : Measurable (bivariate_normal_transport mx my c) := by
    unfold bivariate_normal_transport
    fun_prop
  have hHT : Measurable (fun z => H (bivariate_normal_transport mx my c z)) := hH.comp hT
  rw [bivariate_normal_source_density mx sx d hx hd,
    lintegral_withDensity_eq_lintegral_mul _ hnd.ennreal_ofReal hH,
    lintegral_withDensity_eq_lintegral_mul _ hnd0.ennreal_ofReal hHT]
  change (∫⁻ z, ENNReal.ofReal (normalDensity mx sx z.1 *
      normalDensity (my + c * (z.1 - mx)) d z.2) * H z
      ∂(volume : Measure ℝ).prod volume) =
    ∫⁻ z, ENNReal.ofReal (normalDensity mx sx z.1 * normalDensity 0 d z.2) *
      H (bivariate_normal_transport mx my c z) ∂(volume : Measure ℝ).prod volume
  have hF : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal
      (normalDensity mx sx z.1 * normalDensity (my + c * (z.1 - mx)) d z.2) * H z) :=
    hnd.ennreal_ofReal.mul hH
  have hG : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal
      (normalDensity mx sx z.1 * normalDensity 0 d z.2) *
        H (bivariate_normal_transport mx my c z)) := hnd0.ennreal_ofReal.mul hHT
  rw [lintegral_prod _ hF.aemeasurable, lintegral_prod _ hG.aemeasurable]
  apply lintegral_congr
  intro x
  have he := lintegral_add_left_eq_self (μ := (volume : Measure ℝ))
    (fun y => ENNReal.ofReal (normalDensity mx sx x *
      normalDensity (my + c * (x - mx)) d y) * H (x,y))
    (my + c * (x - mx))
  simpa only [Pi.mul_apply, bivariate_normal_transport, normalDensity,
    add_sub_cancel_left, sub_zero] using he.symm

/-- The universal nonnegative-test identity for the bivariate density. -/
lemma bivariate_normal_lintegral (mx my sx sy ρ : ℝ) (hx : 0 < sx) (hy : 0 < sy)
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) (H : ℝ × ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ z, H z ∂volume.withDensity
      (fun z => ENNReal.ofReal (bivariateNormalPDF mx my sx sy ρ z))) =
    ∫⁻ z, H (bivariate_normal_transport mx my (ρ * sy / sx) z)
      ∂bivariate_normal_source mx sx (sy * Real.sqrt (1 - ρ ^ 2)) := by
  simp_rw [bivariate_normal_factor mx my sx sy ρ hx hy hρ]
  exact bivariate_normal_conditional_lintegral mx my sx _ _ hx
    (mul_pos hy (Real.sqrt_pos.2 (bivariate_normal_q_pos ρ hρ))) H hH

instance bivariate_normal_source_probability (mx sx d : ℝ) :
    IsProbabilityMeasure (bivariate_normal_source mx sx d) := by
  unfold bivariate_normal_source
  infer_instance

/-- The elementary moments on the independent Gaussian source space. These are genuine
finite moments, supplied by Mathlib's Gaussian `MemLp` theorem. -/
lemma bivariate_normal_source_moments (mx my sx d c : ℝ) :
    let η := bivariate_normal_source mx sx d
    let T := bivariate_normal_transport mx my c
    MemLp (Prod.fst : ℝ × ℝ → ℝ) 2 η ∧ MemLp (fun z => (T z).2) 2 η ∧
    (∫ z, z.1 ∂η) = mx ∧ (∫ z, (T z).2 ∂η) = my ∧
    (∫ z, (z.1 - mx) ^ 2 ∂η) = sx ^ 2 ∧
    (∫ z, ((T z).2 - my) ^ 2 ∂η) = c ^ 2 * sx ^ 2 + d ^ 2 ∧
    (∫ z, (z.1 - mx) * ((T z).2 - my) ∂η) = c * sx ^ 2 := by
  let η := bivariate_normal_source mx sx d
  let T := bivariate_normal_transport mx my c
  let U : ℝ × ℝ → ℝ := fun z => z.1 - mx
  let V : ℝ × ℝ → ℝ := Prod.snd
  have hX : MemLp (Prod.fst : ℝ × ℝ → ℝ) 2 η := by
    exact (memLp_id_gaussianReal 2).comp_fst _
  have hV : MemLp V 2 η := by
    exact (memLp_id_gaussianReal 2).comp_snd _
  have hU : MemLp U 2 η := hX.sub (memLp_const mx)
  have hW : MemLp (fun z => c * U z + V z) 2 η := (hU.const_mul c).add hV
  have hY : MemLp (fun z => (T z).2) 2 η := by
    convert (memLp_const my |>.add (hU.const_mul c)).add hV using 1
    rfl
  have mX : (∫ z, z.1 ∂η) = mx := by
    change (∫ z, id z.1 ∂(gaussianReal mx (bivariate_normal_sq sx)).prod
      (gaussianReal 0 (bivariate_normal_sq d))) = mx
    rw [integral_fun_fst]
    simp
  have mV : (∫ z, V z ∂η) = 0 := by
    change (∫ z, id z.2 ∂(gaussianReal mx (bivariate_normal_sq sx)).prod
      (gaussianReal 0 (bivariate_normal_sq d))) = 0
    rw [integral_fun_snd]
    simp
  have mU : (∫ z, U z ∂η) = 0 := by
    rw [show U = fun z => z.1 - mx from rfl,
      integral_sub (hX.integrable (by norm_num)) (integrable_const _), mX]
    simp
  have mW : (∫ z, c * U z + V z ∂η) = 0 := by
    rw [integral_add ((hU.const_mul c).integrable (by norm_num))
      (hV.integrable (by norm_num)), integral_const_mul, mU, mV]
    ring
  have mY : (∫ z, (T z).2 ∂η) = my := by
    change (∫ z, my + c * U z + V z ∂η) = my
    rw [integral_add (f := fun z => my + c * U z)
      ((memLp_const my |>.add (hU.const_mul c)).integrable (by norm_num))
      (hV.integrable (by norm_num)),
      integral_add (integrable_const _) ((hU.const_mul c).integrable (by norm_num)),
      integral_const_mul, mU, mV]
    simp
  have sU : (∫ z, U z ^ 2 ∂η) = sx ^ 2 := by
    change (∫ z, (z.1 - mx) ^ 2 ∂(gaussianReal mx (bivariate_normal_sq sx)).prod
      (gaussianReal 0 (bivariate_normal_sq d))) = sx ^ 2
    rw [integral_fun_fst (fun x : ℝ => (x - mx) ^ 2)]
    simp only [probReal_univ, one_smul]
    have hv := variance_fun_id_gaussianReal (μ := mx) (v := bivariate_normal_sq sx)
    rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at hv
    exact hv
  have sV : (∫ z, V z ^ 2 ∂η) = d ^ 2 := by
    change (∫ z, z.2 ^ 2 ∂(gaussianReal mx (bivariate_normal_sq sx)).prod
      (gaussianReal 0 (bivariate_normal_sq d))) = d ^ 2
    rw [integral_fun_snd (fun x : ℝ => x ^ 2)]
    simp only [probReal_univ, one_smul]
    have hv := variance_fun_id_gaussianReal (μ := 0) (v := bivariate_normal_sq d)
    rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at hv
    simp only [sub_zero] at hv
    exact hv
  have sUV : (∫ z, U z * V z ∂η) = 0 := by
    change (∫ z, (z.1 - mx) * z.2 ∂(gaussianReal mx (bivariate_normal_sq sx)).prod
      (gaussianReal 0 (bivariate_normal_sq d))) = 0
    rw [integral_prod_mul (fun x : ℝ => x - mx) (fun x : ℝ => x)]
    simp
  have sW : (∫ z, (c * U z + V z) ^ 2 ∂η) = c ^ 2 * sx ^ 2 + d ^ 2 := by
    have he : (fun z => (c * U z + V z) ^ 2) =
        (fun z => c ^ 2 * U z ^ 2 + (2*c) * (U z * V z) + V z ^ 2) := by
      funext z
      ring
    rw [he, integral_add (f := fun z => c ^ 2 * U z ^ 2 + (2*c) * (U z * V z))
      ((hU.integrable_sq.const_mul _).add
      ((hU.integrable_mul hV).const_mul _)) hV.integrable_sq,
      integral_add (f := fun z => c ^ 2 * U z ^ 2) (g := fun z => (2*c) * (U z * V z))
        (hU.integrable_sq.const_mul _) ((hU.integrable_mul hV).const_mul _),
      integral_const_mul, integral_const_mul, sU, sV, sUV]
    ring
  have cUW : (∫ z, U z * (c * U z + V z) ∂η) = c * sx ^ 2 := by
    have he : (fun z => U z * (c * U z + V z)) =
        (fun z => c * U z ^ 2 + U z * V z) := by
      funext z
      ring
    rw [he, integral_add (g := fun z => U z * V z)
      (hU.integrable_sq.const_mul _) (hU.integrable_mul hV),
      integral_const_mul, sU, sUV]
    ring
  refine ⟨hX, hY, mX, mY, sU, ?_, ?_⟩
  · convert sW using 1
    congr 1
    funext z
    dsimp [T, bivariate_normal_transport, U, V]
    ring
  · convert cUW using 1
    congr 1
    funext z
    dsimp [T, bivariate_normal_transport, U, V]
    ring

/-- Normalization is first obtained as a nonnegative mass identity. -/
lemma bivariate_normal_probability (mx my sx sy ρ : ℝ) (hx : 0 < sx) (hy : 0 < sy)
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) :
    let f := bivariateNormalPDF mx my sx sy ρ
    let ν := volume.withDensity (fun z => ENNReal.ofReal (f z))
    IsProbabilityMeasure ν ∧ HasJointPDF ν f := by
  let f := bivariateNormalPDF mx my sx sy ρ
  let ν := volume.withDensity (fun z => ENNReal.ofReal (f z))
  have hm : Measurable f := bivariate_normal_density_measurable mx my sx sy ρ
  have hn : ∀ z, 0 ≤ f z := bivariate_normal_density_nonneg mx my sx sy ρ hx hy hρ
  have hmass : ν Set.univ = 1 := by
    have hh := bivariate_normal_lintegral mx my sx sy ρ hx hy hρ (fun _ => 1) measurable_const
    simpa only [lintegral_one, measure_univ] using hh
  have hl : (∫⁻ z, ENNReal.ofReal (f z)) = 1 := by
    simpa only [ν, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using hmass
  have hi : Integrable f volume :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
      (ae_of_all _ hn)).1 (by rw [hl]; finiteness)
  exact ⟨⟨hmass⟩, hm.aemeasurable, hn, hi, rfl⟩

/-- Nonnegative moment identities: Tonelli is applied to the two centered squares,
and their finite extended values are computed before integrability on the target space. -/
lemma bivariate_normal_nonnegative_moments (mx my sx sy ρ : ℝ) (hx : 0 < sx) (hy : 0 < sy)
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) :
    let ν := volume.withDensity (fun z => ENNReal.ofReal (bivariateNormalPDF mx my sx sy ρ z))
    (∫⁻ z, ENNReal.ofReal ((z.1 - mx) ^ 2) ∂ν) = ENNReal.ofReal (sx ^ 2) ∧
    (∫⁻ z, ENNReal.ofReal ((z.2 - my) ^ 2) ∂ν) = ENNReal.ofReal (sy ^ 2) := by
  let d := sy * Real.sqrt (1 - ρ ^ 2)
  let c := ρ * sy / sx
  let η := bivariate_normal_source mx sx d
  let T := bivariate_normal_transport mx my c
  obtain ⟨hX, hY, _mX, _mY, sX, sY, _cXY⟩ := bivariate_normal_source_moments mx my sx d c
  have hU : MemLp (fun z : ℝ × ℝ => z.1 - mx) 2 η := hX.sub (memLp_const mx)
  have hW : MemLp (fun z => (T z).2 - my) 2 η := hY.sub (memLp_const my)
  have hscale : c ^ 2 * sx ^ 2 + d ^ 2 = sy ^ 2 := by
    dsimp [c, d]
    rw [mul_pow, Real.sq_sqrt (bivariate_normal_q_pos ρ hρ).le]
    field_simp
    ring
  constructor
  · calc
      _ = ∫⁻ z, ENNReal.ofReal ((z.1 - mx) ^ 2) ∂η := by
        simpa only [bivariate_normal_transport] using
          bivariate_normal_lintegral mx my sx sy ρ hx hy hρ
            (fun z => ENNReal.ofReal ((z.1 - mx) ^ 2)) (by fun_prop)
      _ = ENNReal.ofReal (∫ z, (z.1 - mx) ^ 2 ∂η) :=
        (ofReal_integral_eq_lintegral_ofReal hU.integrable_sq
          (ae_of_all _ (fun z => sq_nonneg (z.1 - mx)))).symm
      _ = _ := congrArg ENNReal.ofReal sX
  · calc
      _ = ∫⁻ z, ENNReal.ofReal (((T z).2 - my) ^ 2) ∂η :=
        bivariate_normal_lintegral mx my sx sy ρ hx hy hρ
          (fun z => ENNReal.ofReal ((z.2 - my) ^ 2)) (by fun_prop)
      _ = ENNReal.ofReal (∫ z, ((T z).2 - my) ^ 2 ∂η) :=
        (ofReal_integral_eq_lintegral_ofReal hW.integrable_sq
          (ae_of_all _ (fun z => sq_nonneg ((T z).2 - my)))).symm
      _ = _ := congrArg ENNReal.ofReal (sY.trans hscale)

/-- Conversion to genuine Bochner second moments and `MemLp` uses the finite lower
integrals above. In particular no real-integral convention is used to infer finiteness. -/
lemma bivariate_normal_second_moments (mx my sx sy ρ : ℝ) (hx : 0 < sx) (hy : 0 < sy)
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) :
    let ν := volume.withDensity (fun z => ENNReal.ofReal (bivariateNormalPDF mx my sx sy ρ z))
    MemLp (Prod.fst : ℝ × ℝ → ℝ) 2 ν ∧ MemLp (Prod.snd : ℝ × ℝ → ℝ) 2 ν ∧
    (∫ z, (z.1 - mx) ^ 2 ∂ν) = sx ^ 2 ∧ (∫ z, (z.2 - my) ^ 2 ∂ν) = sy ^ 2 := by
  let ν := volume.withDensity (fun z => ENNReal.ofReal (bivariateNormalPDF mx my sx sy ρ z))
  have hp := (bivariate_normal_probability mx my sx sy ρ hx hy hρ).1
  haveI instProbabilityGLP0013B2Second : IsProbabilityMeasure ν := hp
  obtain ⟨sX, sY⟩ := bivariate_normal_nonnegative_moments mx my sx sy ρ hx hy hρ
  have hiX : Integrable (fun z : ℝ × ℝ => (z.1 - mx) ^ 2) ν :=
    (lintegral_ofReal_ne_top_iff_integrable (μ := ν)
      (f := fun z : ℝ × ℝ => (z.1 - mx) ^ 2) (by fun_prop)
      (ae_of_all _ (fun z => sq_nonneg (z.1 - mx)))).1 (by rw [sX]; finiteness)
  have hiY : Integrable (fun z : ℝ × ℝ => (z.2 - my) ^ 2) ν :=
    (lintegral_ofReal_ne_top_iff_integrable (μ := ν)
      (f := fun z : ℝ × ℝ => (z.2 - my) ^ 2) (by fun_prop)
      (ae_of_all _ (fun z => sq_nonneg (z.2 - my)))).1 (by rw [sY]; finiteness)
  have hU : MemLp (fun z : ℝ × ℝ => z.1 - mx) 2 ν :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 hiX
  have hW : MemLp (fun z : ℝ × ℝ => z.2 - my) 2 ν :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 hiY
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hU.add (memLp_const mx) using 1
    funext z
    change z.1 = (z.1 - mx) + mx
    ring
  · convert hW.add (memLp_const my) using 1
    funext z
    change z.2 = (z.2 - my) + my
    ring
  · calc
      _ = (∫⁻ z, ENNReal.ofReal ((z.1 - mx) ^ 2) ∂ν).toReal :=
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun z => sq_nonneg (z.1 - mx)))
          hiX.aestronglyMeasurable
      _ = _ := by rw [sX, ENNReal.toReal_ofReal (sq_nonneg _)]
  · calc
      _ = (∫⁻ z, ENNReal.ofReal ((z.2 - my) ^ 2) ∂ν).toReal :=
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun z => sq_nonneg (z.2 - my)))
          hiY.aestronglyMeasurable
      _ = _ := by rw [sY, ENNReal.toReal_ofReal (sq_nonneg _)]

/-- Equality of laws follows from the universal lower-integral identity. -/
lemma bivariate_normal_eq_map (mx my sx sy ρ : ℝ) (hx : 0 < sx) (hy : 0 < sy)
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) :
    volume.withDensity (fun z => ENNReal.ofReal (bivariateNormalPDF mx my sx sy ρ z)) =
      (bivariate_normal_source mx sx (sy * Real.sqrt (1 - ρ ^ 2))).map
        (bivariate_normal_transport mx my (ρ * sy / sx)) := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map hH (by unfold bivariate_normal_transport; fun_prop)]
  exact bivariate_normal_lintegral mx my sx sy ρ hx hy hρ H hH

/-- The signed counterpart is deliberately restricted to integrable tests. Later uses
obtain this premise from the finite centered-square integrals and Cauchy--Schwarz. -/
lemma bivariate_normal_integral (mx my sx sy ρ : ℝ) (hx : 0 < sx) (hy : 0 < sy)
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) (H : ℝ × ℝ → ℝ)
    (hH : Integrable H (volume.withDensity
      (fun z => ENNReal.ofReal (bivariateNormalPDF mx my sx sy ρ z)))) :
    (∫ z, H z ∂volume.withDensity
      (fun z => ENNReal.ofReal (bivariateNormalPDF mx my sx sy ρ z))) =
    ∫ z, H (bivariate_normal_transport mx my (ρ * sy / sx) z)
      ∂bivariate_normal_source mx sx (sy * Real.sqrt (1 - ρ ^ 2)) := by
  rw [bivariate_normal_eq_map mx my sx sy ρ hx hy hρ] at hH ⊢
  exact integral_map (by unfold bivariate_normal_transport; fun_prop) hH.aestronglyMeasurable

/-- Signed first and cross moments. The integrability premises of the signed transport
identity come from `bivariate_normal_second_moments`, including its lower-integral proof. -/
lemma bivariate_normal_means_covariance (mx my sx sy ρ : ℝ) (hx : 0 < sx) (hy : 0 < sy)
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) :
    let ν := volume.withDensity (fun z => ENNReal.ofReal (bivariateNormalPDF mx my sx sy ρ z))
    mean ν Prod.fst = mx ∧ mean ν Prod.snd = my ∧
      covariance Prod.fst Prod.snd ν = ρ * sx * sy := by
  let ν := volume.withDensity (fun z => ENNReal.ofReal (bivariateNormalPDF mx my sx sy ρ z))
  let d := sy * Real.sqrt (1 - ρ ^ 2)
  let c := ρ * sy / sx
  let η := bivariate_normal_source mx sx d
  let T := bivariate_normal_transport mx my c
  haveI instProbabilityGLP0013B2Means : IsProbabilityMeasure ν :=
    (bivariate_normal_probability mx my sx sy ρ hx hy hρ).1
  obtain ⟨hX, hY, _sX, _sY⟩ := bivariate_normal_second_moments mx my sx sy ρ hx hy hρ
  obtain ⟨_hX, _hY, mX, mY, _sU, _sW, cXY⟩ := bivariate_normal_source_moments mx my sx d c
  have eX : mean ν Prod.fst = mx := by
    exact (bivariate_normal_integral mx my sx sy ρ hx hy hρ Prod.fst
      (hX.integrable (by norm_num))).trans mX
  have eY : mean ν Prod.snd = my := by
    exact (bivariate_normal_integral mx my sx sy ρ hx hy hρ Prod.snd
      (hY.integrable (by norm_num))).trans mY
  refine ⟨eX, eY, ?_⟩
  have hU : MemLp (fun z : ℝ × ℝ => z.1 - mx) 2 ν := hX.sub (memLp_const mx)
  have hW : MemLp (fun z : ℝ × ℝ => z.2 - my) 2 ν := hY.sub (memLp_const my)
  change (∫ z, (z.1 - mean ν Prod.fst) * (z.2 - mean ν Prod.snd) ∂ν) = _
  rw [eX, eY]
  calc
    _ = ∫ z, ((T z).1 - mx) * ((T z).2 - my) ∂η :=
      bivariate_normal_integral mx my sx sy ρ hx hy hρ
        (fun z => (z.1 - mx) * (z.2 - my)) (hU.integrable_mul hW)
    _ = c * sx ^ 2 := cXY
    _ = ρ * sx * sy := by
      dsimp [c]
      field_simp

lemma bivariate_normal_variance_scales (mx my sx sy ρ : ℝ) (hx : 0 < sx) (hy : 0 < sy)
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) :
    let ν := volume.withDensity (fun z => ENNReal.ofReal (bivariateNormalPDF mx my sx sy ρ z))
    Real.sqrt (var ν Prod.fst) = sx ∧ Real.sqrt (var ν Prod.snd) = sy ∧
      covariance Prod.fst Prod.snd ν / (sx * sy) = ρ := by
  let ν := volume.withDensity (fun z => ENNReal.ofReal (bivariateNormalPDF mx my sx sy ρ z))
  obtain ⟨_hX, _hY, sX, sY⟩ := bivariate_normal_second_moments mx my sx sy ρ hx hy hρ
  obtain ⟨mX, mY, hc⟩ := bivariate_normal_means_covariance mx my sx sy ρ hx hy hρ
  have vX : var ν Prod.fst = sx ^ 2 := by
    rw [var, variance_eq_integral measurable_fst.aemeasurable]
    change (∫ z, (z.1 - mean ν Prod.fst) ^ 2 ∂ν) = _
    rw [mX]
    exact sX
  have vY : var ν Prod.snd = sy ^ 2 := by
    rw [var, variance_eq_integral measurable_snd.aemeasurable]
    change (∫ z, (z.2 - mean ν Prod.snd) ^ 2 ∂ν) = _
    rw [mY]
    exact sY
  refine ⟨?_, ?_, ?_⟩
  · rw [vX, Real.sqrt_sq_eq_abs, abs_of_pos hx]
  · rw [vY, Real.sqrt_sq_eq_abs, abs_of_pos hy]
  · rw [hc]
    field_simp

/-- At zero correlation, the law is the product of its two positive-variance normal laws. -/
lemma bivariate_normal_zero_product (mx my sx sy : ℝ) (hx : 0 < sx) (hy : 0 < sy) :
    let f := bivariateNormalPDF mx my sx sy 0
    let ν := volume.withDensity (fun xy => ENNReal.ofReal (f xy))
    IndepFun Prod.fst Prod.snd ν ∧
      ∀ xy, f xy = normalDensity mx sx xy.1 * normalDensity my sy xy.2 := by
  have hz : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  have hT : bivariate_normal_transport mx my 0 = Prod.map id (fun z : ℝ => my + z) := by
    funext z
    ext <;> simp [bivariate_normal_transport]
  have he : volume.withDensity (fun z => ENNReal.ofReal (bivariateNormalPDF mx my sx sy 0 z)) =
      (bivariate_normal_source mx sx sy).map (bivariate_normal_transport mx my 0) := by
    simpa using bivariate_normal_eq_map mx my sx sy 0 hx hy hz
  have hp : volume.withDensity (fun z => ENNReal.ofReal (bivariateNormalPDF mx my sx sy 0 z)) =
      (gaussianReal mx (bivariate_normal_sq sx)).prod
        (gaussianReal my (bivariate_normal_sq sy)) := by
    rw [he, hT, bivariate_normal_source,
      ← Measure.map_prod_map _ _ measurable_id (show Measurable (fun z : ℝ => my + z) by fun_prop)]
    simp only [Measure.map_id, gaussianReal_map_const_add, zero_add]
  constructor
  · rw [hp]
    exact indepFun_prod measurable_id measurable_id
  · intro xy
    simpa using bivariate_normal_factor mx my sx sy 0 hx hy hz xy

theorem bivariate_normal_zero_correlation_independent_proof (mx my sx sy ρ : ℝ) (hx : 0 < sx) (hy : 0 < sy) (hρ : ρ∈Set.Ioo (-1 : ℝ) 1) :
   let f := bivariateNormalPDF mx my sx sy ρ
   let ν := volume.withDensity (fun xy => ENNReal.ofReal (f xy))
   IsProbabilityMeasure ν ∧ HasJointPDF ν f ∧
   mean ν Prod.fst=mx ∧ mean ν Prod.snd=my ∧
   Real.sqrt (var ν Prod.fst)=sx ∧ Real.sqrt (var ν Prod.snd)=sy ∧
   covariance Prod.fst Prod.snd ν/(sx*sy)=ρ ∧
   (ρ=0 → IndepFun Prod.fst Prod.snd ν ∧
      ∀ xy,f xy=normalDensity mx sx xy.1*normalDensity my sy xy.2) := by
  obtain ⟨hp, hpdf⟩ := bivariate_normal_probability mx my sx sy ρ hx hy hρ
  obtain ⟨mX, mY, _hc⟩ := bivariate_normal_means_covariance mx my sx sy ρ hx hy hρ
  obtain ⟨sX, sY, hc⟩ := bivariate_normal_variance_scales mx my sx sy ρ hx hy hρ
  refine ⟨hp, hpdf, mX, mY, sX, sY, hc, ?_⟩
  intro hz
  subst ρ
  exact bivariate_normal_zero_product mx my sx sy hx hy

end
end AronowAudit.P001.Wave1
