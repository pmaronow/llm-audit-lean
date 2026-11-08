import SAP.P004a.WH.W2.Leaves
import Mathlib.Probability.Distributions.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W2.P.T8_L1

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

lemma betaPDFReal_integrable {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Integrable (ProbabilityTheory.betaPDFReal α β) := by
  have hnonneg (x : ℝ) : 0 ≤ ProbabilityTheory.betaPDFReal α β x := by
    by_cases hx : 0 < x ∧ x < 1
    · exact (ProbabilityTheory.betaPDFReal_pos hx.1 hx.2 hα hβ).le
    · simp [ProbabilityTheory.betaPDFReal, hx]
  refine ⟨(ProbabilityTheory.measurable_betaPDFReal α β).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm,
    lintegral_enorm_of_ae_nonneg (ae_of_all _ hnonneg)]
  change (∫⁻ x, ProbabilityTheory.betaPDF α β x) < ∞
  rw [ProbabilityTheory.lintegral_betaPDF_eq_one hα hβ]
  norm_num

lemma betaPDFReal_integral {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (∫ x, ProbabilityTheory.betaPDFReal α β x) = 1 := by
  have hi := betaPDFReal_integrable hα hβ
  have hnonneg : 0 ≤ᵐ[(volume : Measure ℝ)] ProbabilityTheory.betaPDFReal α β :=
    ae_of_all _ fun x => by
      by_cases hx : 0 < x ∧ x < 1
      · exact (ProbabilityTheory.betaPDFReal_pos hx.1 hx.2 hα hβ).le
      · simp [ProbabilityTheory.betaPDFReal, hx]
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hi.aestronglyMeasurable]
  have hb : (∫⁻ x, ENNReal.ofReal (ProbabilityTheory.betaPDFReal α β x)) = 1 := by
    simpa [ProbabilityTheory.betaPDF] using
      ProbabilityTheory.lintegral_betaPDF_eq_one hα hβ
  rw [hb]
  norm_num

def studentBetaMap (ν x : ℝ) : ℝ := x^2 / (ν + x^2)

lemma studentBetaMap_image {ν : ℝ} (hν : 0 < ν) :
    studentBetaMap ν '' Ioi (0 : ℝ) = Ioo 0 1 := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · exact div_pos (sq_pos_of_pos hx) (by positivity)
    · have hden : 0 < ν + x^2 := by positivity
      change x^2 / (ν + x^2) < 1
      rw [div_lt_one hden]
      linarith [hν]
  · intro hu
    have harg : 0 < ν * u / (1-u) :=
      div_pos (mul_pos hν hu.1) (sub_pos.mpr hu.2)
    let x := Real.sqrt (ν * u / (1-u))
    have hx : 0 < x := Real.sqrt_pos.2 harg
    refine ⟨x, hx, ?_⟩
    dsimp [studentBetaMap, x]
    rw [Real.sq_sqrt harg.le]
    apply (div_eq_iff (ne_of_gt (by positivity))).2
    field_simp [ne_of_gt (sub_pos.mpr hu.2)]
    ring

lemma studentBetaMap_deriv {ν x : ℝ} (hν : 0 < ν) :
    HasDerivWithinAt (studentBetaMap ν)
      (2 * ν * x / (ν + x^2)^2) (Ioi 0) x := by
  have hnum : HasDerivAt (fun t : ℝ => t^2) (2*x) x := by
    convert (hasDerivAt_id x).pow 2 using 1
    · ext t
      rfl
    · norm_num [id_eq]
  have hden : HasDerivAt (fun t : ℝ => ν + t^2) (2*x) x := by
    simpa [mul_comm] using hnum.const_add ν
  have hden0 : ν + x^2 ≠ 0 := ne_of_gt (by positivity)
  convert (hnum.div hden hden0).hasDerivWithinAt using 1
  · rfl
  · field_simp
    <;> ring

lemma studentBetaKernel {ν x : ℝ} (hν : 0 < ν) (hx : 0 < x) :
    (2 * ν * x / (ν + x^2)^2) *
        (studentBetaMap ν x) ^ ((1 : ℝ) / 2 - 1) *
        (1 - studentBetaMap ν x) ^ (ν / 2 - 1) =
      (2 / Real.sqrt ν) *
        (1 + x^2 / ν) ^ (-((ν + 1) / 2)) := by
  let d := ν + x^2
  have hd : 0 < d := by dsimp [d]; positivity
  have hx2 : 0 < x^2 := sq_pos_of_pos hx
  have hu : studentBetaMap ν x = x^2 / d := by rfl
  have hv : 1 - x^2 / d = ν / d := by
    field_simp [ne_of_gt hd]
    ring
  have hbase : 1 + x^2 / ν = d / ν := by
    dsimp [d]
    field_simp [ne_of_gt hν]
  rw [hu, hv, hbase]
  norm_num only [show (1 : ℝ) / 2 - 1 = -(1 / 2 : ℝ) by norm_num]
  rw [Real.div_rpow hx2.le hd.le, Real.div_rpow hν.le hd.le,
    Real.div_rpow hd.le hν.le]
  have hpowx : (x^2) ^ (-(1 / 2 : ℝ)) = x⁻¹ := by
    rw [Real.rpow_neg (sq_nonneg x), ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs,
      abs_of_pos hx]
  have hpowd : d ^ (-(1 / 2 : ℝ)) = (d ^ ((1 : ℝ) / 2))⁻¹ := by
    exact Real.rpow_neg hd.le (1 / 2)
  have hpownu : ν ^ (ν / 2 - 1) = ν ^ (ν / 2) / ν := by
    rw [Real.rpow_sub hν (ν / 2) 1, Real.rpow_one]
  have hpowd' : d ^ (ν / 2 - 1) = d ^ (ν / 2) / d := by
    rw [Real.rpow_sub hd (ν / 2) 1, Real.rpow_one]
  have ha : -((ν + 1) / 2) = -((ν / 2) + (1 / 2)) := by ring
  rw [show ν + x^2 = d by rfl, hpowx, hpowd, hpownu, hpowd', ha,
    Real.rpow_neg hd.le (ν / 2 + 1 / 2), Real.rpow_neg hν.le (ν / 2 + 1 / 2),
    ]
  field_simp [ne_of_gt hx, ne_of_gt hν, ne_of_gt hd]
  rw [Real.sqrt_eq_rpow]
  rw [show (ν + 1) / 2 = ν / 2 + 1 / 2 by ring]
  calc
    _ = (d ^ ((1 : ℝ) / 2) * d ^ (ν / 2 + 1 / 2)) *
        (ν ^ (ν / 2) * ν ^ ((1 : ℝ) / 2)) := by ring
    _ = d ^ ((1 : ℝ) / 2 + (ν / 2 + 1 / 2)) * ν ^ (ν / 2 + 1 / 2) := by
      rw [← Real.rpow_add hd (1 / 2) (ν / 2 + 1 / 2),
        ← Real.rpow_add hν (ν / 2) (1 / 2)]
    _ = d ^ (1 + ν / 2) * ν ^ (ν / 2 + 1 / 2) := by
      congr 1 <;> congr 1 <;> ring
    _ = d * d ^ (ν / 2) * ν ^ (ν / 2 + 1 / 2) := by
      rw [Real.rpow_add hd 1 (ν / 2), Real.rpow_one]
    _ = _ := by ring

lemma studentBetaCoefficient {ν : ℝ} (hν : 0 < ν) :
    1 / ProbabilityTheory.beta (1 / 2) (ν / 2) =
      Real.Gamma ((ν + 1) / 2) /
        (Real.sqrt Real.pi * Real.Gamma (ν / 2)) := by
  rw [ProbabilityTheory.beta, Real.Gamma_one_half_eq]
  rw [show (1 : ℝ) / 2 + ν / 2 = (ν + 1) / 2 by ring]
  field_simp [ne_of_gt (Real.sqrt_pos.2 Real.pi_pos),
    ne_of_gt (Real.Gamma_pos_of_pos (by linarith : 0 < ν / 2))]

lemma studentCoefficient {ν : ℝ} (hν : 0 < ν) :
    Real.Gamma ((ν + 1) / 2) /
        (Real.sqrt (ν * Real.pi) * Real.Gamma (ν / 2)) =
      (1 / Real.sqrt ν) *
        (Real.Gamma ((ν + 1) / 2) /
          (Real.sqrt Real.pi * Real.Gamma (ν / 2))) := by
  rw [Real.sqrt_mul hν.le]
  field_simp [ne_of_gt (Real.sqrt_pos.2 hν),
    ne_of_gt (Real.sqrt_pos.2 Real.pi_pos),
    ne_of_gt (Real.Gamma_pos_of_pos (by linarith : 0 < ν / 2))]

lemma studentDensity_change {ν x : ℝ} (hν : 0 < ν) (hx : 0 < x) :
    AronowAudit.P004.studentDensity ν x =
      (2 * ν * x / (ν + x^2)^2) *
        ProbabilityTheory.betaPDFReal (1 / 2) (ν / 2) (studentBetaMap ν x) / 2 := by
  have hmap : studentBetaMap ν x ∈ Ioo (0 : ℝ) 1 := by
    rw [← studentBetaMap_image hν]
    exact ⟨x, hx, rfl⟩
  have hkernel := studentBetaKernel hν hx
  calc
    AronowAudit.P004.studentDensity ν x =
        (Real.Gamma ((ν + 1) / 2) /
          (Real.sqrt Real.pi * Real.Gamma (ν / 2))) / Real.sqrt ν *
          (1 + x^2 / ν) ^ (-((ν + 1) / 2)) := by
      rw [AronowAudit.P004.studentDensity, studentCoefficient hν]
      ring
    _ = (Real.Gamma ((ν + 1) / 2) /
          (Real.sqrt Real.pi * Real.Gamma (ν / 2))) / 2 *
          ((2 * ν * x / (ν + x^2)^2) *
            (studentBetaMap ν x) ^ ((1 : ℝ) / 2 - 1) *
            (1 - studentBetaMap ν x) ^ (ν / 2 - 1)) := by
      rw [hkernel]
      ring
    _ = (2 * ν * x / (ν + x^2)^2) *
          ((1 / ProbabilityTheory.beta (1 / 2) (ν / 2)) *
            (studentBetaMap ν x) ^ ((1 : ℝ) / 2 - 1) *
            (1 - studentBetaMap ν x) ^ (ν / 2 - 1)) / 2 := by
      rw [studentBetaCoefficient hν]
      ring
    _ = (2 * ν * x / (ν + x^2)^2) *
          ProbabilityTheory.betaPDFReal (1 / 2) (ν / 2) (studentBetaMap ν x) / 2 := by
      rw [ProbabilityTheory.betaPDFReal, if_pos ⟨hmap.1, hmap.2⟩]

lemma studentDensity_even (ν x : ℝ) :
    AronowAudit.P004.studentDensity ν (-x) = AronowAudit.P004.studentDensity ν x := by
  simp [AronowAudit.P004.studentDensity]

lemma studentDensity_integrableOn_Ioi {ν : ℝ} (hν : 0 < ν) :
    IntegrableOn (AronowAudit.P004.studentDensity ν) (Ioi (0 : ℝ)) := by
  let f := studentBetaMap ν
  let g := ProbabilityTheory.betaPDFReal (1 / 2) (ν / 2)
  have hα : 0 < (1 : ℝ) / 2 := by norm_num
  have hβ : 0 < ν / 2 := by linarith
  have hg : IntegrableOn g (f '' Ioi (0 : ℝ)) := by
    rw [show f = studentBetaMap ν by rfl, studentBetaMap_image hν]
    exact (betaPDFReal_integrable hα hβ).integrableOn
  have hinj : InjOn f (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := hx
    have hy0 : 0 < y := hy
    have hdx : ν + x^2 ≠ 0 := ne_of_gt (by positivity)
    have hdy : ν + y^2 ≠ 0 := ne_of_gt (by positivity)
    have hc : x^2 * (ν + y^2) = y^2 * (ν + x^2) := by
      apply (div_eq_div_iff hdx hdy).mp
      simpa [f, studentBetaMap] using hxy
    have hsq : x^2 = y^2 := by nlinarith [hc]
    nlinarith [hsq, hx0, hy0]
  have htrans :=
    (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      (fun x hx => studentBetaMap_deriv hν) hinj g).mp hg
  have htrans' : IntegrableOn
      (fun x => (2 * ν * x / (ν + x^2)^2) *
        ProbabilityTheory.betaPDFReal (1 / 2) (ν / 2) (studentBetaMap ν x))
      (Ioi (0 : ℝ)) := by
    apply htrans.congr_fun
    · intro x hx
      have hx0 : 0 < x := hx
      have hd : 0 < 2 * ν * x / (ν + x^2)^2 := by positivity
      simpa [f, g, abs_of_pos hd, smul_eq_mul]
    · exact measurableSet_Ioi
  have htwice : IntegrableOn (fun x => 2 * AronowAudit.P004.studentDensity ν x)
      (Ioi (0 : ℝ)) := by
    apply htrans'.congr_fun
    · intro x hx
      have hx0 : 0 < x := hx
      change (2 * ν * x / (ν + x^2)^2) *
          ProbabilityTheory.betaPDFReal (1 / 2) (ν / 2) (studentBetaMap ν x) =
        2 * AronowAudit.P004.studentDensity ν x
      rw [studentDensity_change hν hx]
      ring
    · exact measurableSet_Ioi
  have hhalf : IntegrableOn
      (fun x => (1 / 2 : ℝ) * (2 * AronowAudit.P004.studentDensity ν x))
      (Ioi (0 : ℝ)) := htwice.const_mul (1 / 2 : ℝ)
  exact hhalf.congr_fun (by intro x hx; ring) measurableSet_Ioi

lemma studentDensity_integral_Ioi {ν : ℝ} (hν : 0 < ν) :
    (∫ x in Ioi (0 : ℝ), AronowAudit.P004.studentDensity ν x) = 1 / 2 := by
  let f := studentBetaMap ν
  let g := ProbabilityTheory.betaPDFReal (1 / 2) (ν / 2)
  have hα : 0 < (1 : ℝ) / 2 := by norm_num
  have hβ : 0 < ν / 2 := by linarith
  have hinj : InjOn f (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := hx
    have hy0 : 0 < y := hy
    have hdx : ν + x^2 ≠ 0 := ne_of_gt (by positivity)
    have hdy : ν + y^2 ≠ 0 := ne_of_gt (by positivity)
    have hc : x^2 * (ν + y^2) = y^2 * (ν + x^2) := by
      apply (div_eq_div_iff hdx hdy).mp
      simpa [f, studentBetaMap] using hxy
    have hsq : x^2 = y^2 := by nlinarith [hc]
    nlinarith [hsq, hx0, hy0]
  have hβset : (∫ u in Ioo (0 : ℝ) 1, g u) = 1 := by
    have hglobal : (∫ u, g u) = 1 := by
      simpa [g] using betaPDFReal_integral hα hβ
    have hset : (∫ u, g u) = ∫ u in Ioo (0 : ℝ) 1, g u := by
      simpa only [setIntegral_univ] using
        (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
          (t := univ) (s := Ioo (0 : ℝ) 1) (f := g)
          MeasurableSet.univ (subset_univ _) (by
            intro u hu
            have hu' : ¬ (0 < u ∧ u < 1) := by simpa using hu.2
            simp [g, ProbabilityTheory.betaPDFReal, hu']))
    rw [← hset, hglobal]
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x hx => studentBetaMap_deriv hν) hinj g
  rw [studentBetaMap_image hν, hβset] at hchange
  have hpoint : ∀ x ∈ Ioi (0 : ℝ),
      |2 * ν * x / (ν + x^2)^2| • g (studentBetaMap ν x) =
        2 * AronowAudit.P004.studentDensity ν x := by
    intro x hx
    have hx0 : 0 < x := hx
    have hd : 0 < 2 * ν * x / (ν + x^2)^2 := by positivity
    rw [abs_of_pos hd, studentDensity_change hν hx]
    simp [g, smul_eq_mul]
    ring
  have hmass : (∫ x in Ioi (0 : ℝ), 2 * AronowAudit.P004.studentDensity ν x) = 1 := by
    calc
      _ = ∫ x in Ioi (0 : ℝ),
          |2 * ν * x / (ν + x^2)^2| • g (studentBetaMap ν x) := by
        apply integral_congr_ae
        exact ae_restrict_of_forall_mem measurableSet_Ioi
          (fun x hx => (hpoint x hx).symm)
      _ = 1 := hchange.symm
  rw [integral_const_mul] at hmass
  linarith

lemma studentDensity_integrable {ν : ℝ} (hν : 0 < ν) :
    Integrable (AronowAudit.P004.studentDensity ν) := by
  have hpos := studentDensity_integrableOn_Ioi hν
  have hneg : IntegrableOn (AronowAudit.P004.studentDensity ν) (Iio (0 : ℝ)) := by
    have hcomp : IntegrableOn
        (fun x : ℝ => AronowAudit.P004.studentDensity ν (-x)) (Ioi (0 : ℝ)) := by
      simpa [studentDensity_even] using hpos
    have himg := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      (fun x hx => (hasDerivAt_id x).neg.hasDerivWithinAt)
      neg_injective.injOn (AronowAudit.P004.studentDensity ν)).2 (by
        simpa [Function.id_def, smul_eq_mul] using hcomp)
    simpa using himg
  have hnonpos : IntegrableOn (AronowAudit.P004.studentDensity ν) (Iic (0 : ℝ)) :=
    (integrableOn_Iic_iff_integrableOn_Iio).2 hneg
  rw [← integrableOn_univ, ← Iic_union_Ioi, integrableOn_union]
  exact ⟨hnonpos, hpos⟩


end
end SAP.P004a.WH.W2.P.T8_L1

open MeasureTheory Set

theorem SAP.P004a.WH.W2.T8_L1_proof : SAP.P004a.WH.W2.T8_L1 := by
  intro ν hν
  have hf := SAP.P004a.WH.W2.P.T8_L1.studentDensity_integrable hν
  have hpos := SAP.P004a.WH.W2.P.T8_L1.studentDensity_integral_Ioi hν
  have hmirror :
      (∫ x in Ioi (0 : ℝ), AronowAudit.P004.studentDensity ν (-x)) =
        ∫ x in Ioi (0 : ℝ), AronowAudit.P004.studentDensity ν x := by
    apply integral_congr_ae
    exact ae_restrict_of_forall_mem measurableSet_Ioi
      (fun x hx => SAP.P004a.WH.W2.P.T8_L1.studentDensity_even ν x)
  have hneg :
      (∫ x in Iic (0 : ℝ), AronowAudit.P004.studentDensity ν x) =
        ∫ x in Ioi (0 : ℝ), AronowAudit.P004.studentDensity ν x := by
    calc
      _ = ∫ x in Ioi (0 : ℝ), AronowAudit.P004.studentDensity ν (-x) :=
        by simpa using (integral_comp_neg_Ioi 0 (AronowAudit.P004.studentDensity ν)).symm
      _ = ∫ x in Ioi (0 : ℝ), AronowAudit.P004.studentDensity ν x := hmirror
  have htotal : (∫ x, AronowAudit.P004.studentDensity ν x) = 1 := by
    calc
      _ = (∫ x in Ioi (0 : ℝ), AronowAudit.P004.studentDensity ν x) +
          (∫ x in Iic (0 : ℝ), AronowAudit.P004.studentDensity ν x) := by
        simpa [compl_Ioi] using (integral_add_compl measurableSet_Ioi hf).symm
      _ = 1 := by rw [hneg, hpos]; norm_num
  exact ⟨hf, htotal⟩
