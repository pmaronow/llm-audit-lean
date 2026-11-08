import SAP.P039.WH.W1.Leaves
import AronowAudit.P039.P039_GaussianCompletion
import AronowAudit.External.StatLean.MultipleTesting.ForMathlib.GammaMoments
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039.WH.W1.P.T7_L2

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option maxHeartbeats 1000000

theorem standard_gaussian_fourth_moment :
    Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) ∧
      (∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1)) = 3 := by
  let μ : Measure (Fin 1 → ℝ) := Measure.pi (fun _ : Fin 1 => gaussianReal 0 1)
  have hmem : MemLp (id : ℝ → ℝ) 4 (gaussianReal 0 1) := by
    exact memLp_id_gaussianReal (μ := 0) (v := 1) 4
  have hG4 : Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) := by
    have h := hmem.integrable_norm_pow'
    apply h.congr (ae_of_all _ fun x => ?_)
    change |x| ^ 4 = x ^ 4
    rw [← abs_pow]
    exact abs_of_nonneg (by positivity)
  have hsq : (gaussianReal 0 1).map (fun x : ℝ => x ^ 2) =
      gammaMeasure (1 / 2) (1 / 2) := by
    have heval : μ.map (fun z : Fin 1 → ℝ => z 0) = gaussianReal 0 1 := by
      simpa [μ] using Measure.pi_map_eval (fun _ : Fin 1 => gaussianReal 0 1) (0 : Fin 1)
    have hsum := AronowAudit.GaussianCompletion.gaussian_squares_eq_gamma
      (ν := 1) (by norm_num)
    calc
      (gaussianReal 0 1).map (fun x : ℝ => x ^ 2) =
          (μ.map (fun z : Fin 1 → ℝ => z 0)).map (fun x : ℝ => x ^ 2) := by rw [heval]
      _ = μ.map (fun z : Fin 1 → ℝ => (z 0) ^ 2) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        congr 1
      _ = μ.map (fun z : Fin 1 → ℝ => ∑ i : Fin 1, (z i) ^ 2) := by
        congr 1
        funext z
        simp
      _ = gammaMeasure (1 / 2) (1 / 2) := by
        simpa [μ] using hsum
  have : IsProbabilityMeasure (gammaMeasure (1 / 2) (1 / 2)) :=
    ProbabilityTheory.isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  have hX2 : Integrable (fun x : ℝ => x ^ 2) (gammaMeasure (1 / 2) (1 / 2)) := by
    rw [← hsq]
    have hmap : Integrable (fun y : ℝ => y ^ 2)
        ((gaussianReal 0 1).map (fun x : ℝ => x ^ 2)) ↔
        Integrable (fun x : ℝ => (x ^ 2) ^ 2) (gaussianReal 0 1) :=
      integrable_map_measure (by fun_prop)
        (show AEMeasurable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) from by fun_prop)
    have hG4' : Integrable (fun x : ℝ => (x ^ 2) ^ 2) (gaussianReal 0 1) := by
      apply hG4.congr (ae_of_all _ fun x => ?_)
      ring
    exact hmap.mpr hG4'
  have hXmem : MemLp (id : ℝ → ℝ) 2 (gammaMeasure (1 / 2) (1 / 2)) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 hX2
  have hX1 : Integrable (id : ℝ → ℝ) (gammaMeasure (1 / 2) (1 / 2)) :=
    hXmem.integrable (by norm_num)
  have hX1' : Integrable (fun x : ℝ => x) (gammaMeasure (1 / 2) (1 / 2)) := by
    convert hX1 using 1
    rfl
  have hmean : (∫ x : ℝ, x ∂gammaMeasure (1 / 2) (1 / 2)) = 1 := by
    rw [StatLean.MultipleTesting.integral_id_gammaMeasure (by norm_num) (by norm_num)]
    norm_num
  have hvar : (∫ x : ℝ, (x - 1) ^ 2 ∂gammaMeasure (1 / 2) (1 / 2)) = 2 := by
    have h := StatLean.MultipleTesting.variance_gammaMeasure
      (a := (1 / 2 : ℝ)) (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    norm_num [div_eq_mul_inv] at h ⊢
    exact h
  have hlin : Integrable (fun x : ℝ => x ^ 2 - 2 * x)
      (gammaMeasure (1 / 2) (1 / 2)) := hX2.sub (hX1'.const_mul 2)
  have hvar_expand : (∫ x : ℝ, (x - 1) ^ 2 ∂gammaMeasure (1 / 2) (1 / 2)) =
      (∫ x : ℝ, x ^ 2 ∂gammaMeasure (1 / 2) (1 / 2)) -
        2 * (∫ x : ℝ, x ∂gammaMeasure (1 / 2) (1 / 2)) + 1 := by
    calc
      _ = ∫ x : ℝ, (x ^ 2 - 2 * x) + 1 ∂gammaMeasure (1 / 2) (1 / 2) := by
        congr 1
        funext x
        ring
      _ = _ := by
        rw [integral_add hlin (integrable_const (1 : ℝ)),
          integral_sub hX2 (hX1'.const_mul 2), integral_const_mul, integral_const]
        rw [MeasureTheory.probReal_univ]
        ring
  have hsecond : (∫ x : ℝ, x ^ 2 ∂gammaMeasure (1 / 2) (1 / 2)) = 3 := by
    rw [hvar, hmean] at hvar_expand
    linarith
  constructor
  · exact hG4
  · calc
      (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) =
          ∫ x : ℝ, (x ^ 2) ^ 2 ∂gaussianReal 0 1 := by congr 1; funext x; ring
      _ = ∫ x : ℝ, x ^ 2 ∂((gaussianReal 0 1).map (fun x : ℝ => x ^ 2)) := by
          rw [← integral_map (by fun_prop : Measurable (fun x : ℝ => x ^ 2)).aemeasurable
            (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ 2)
              ((gaussianReal 0 1).map (fun x : ℝ => x ^ 2)))]
      _ = 3 := by rw [hsq, hsecond]

theorem ratio_fourth_factor (ν : ℕ) (hν : 4 < ν) (x w : ℝ) (hw : 0 ≤ w) :
    (x / Real.sqrt (w / (ν : ℝ))) ^ 4 =
      (ν : ℝ) ^ 2 * (x ^ 4 * (w⁻¹) ^ 2) := by
  by_cases hw0 : w = 0
  · subst w
    simp
  · have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    have hνpos : (0 : ℝ) < (ν : ℝ) := by exact_mod_cast (by omega : 0 < ν)
    have hden : (Real.sqrt (w / (ν : ℝ))) ^ 4 = (w / (ν : ℝ)) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul,
        Real.sq_sqrt (div_nonneg hw hνpos.le)]
    rw [div_pow, hden]
    field_simp [hw0, hνpos.ne']

end SAP.P039.WH.W1.P.T7_L2

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem SAP.P039.WH.W1.T7_L2_proof : SAP.P039.WH.W1.T7_L2 := by
  intro ν hν hInv hInvVal
  let μ : Measure (Fin (ν + 1) → ℝ) := Measure.pi (fun _ : Fin (ν + 1) => gaussianReal 0 1)
  let q : (Fin (ν + 1) → ℝ) → ℝ × ℝ :=
    fun z => (z 0, ∑ i : Fin ν, (z i.succ) ^ 2)
  let R : ℝ × ℝ → ℝ := fun p => p.1 / Real.sqrt (p.2 / (ν : ℝ))
  have hq : Measurable q := by
    change Measurable (fun z : Fin (ν + 1) → ℝ => (z 0, ∑ i : Fin ν, (z i.succ) ^ 2))
    fun_prop
  have hR : Measurable R := by
    change Measurable (fun p : ℝ × ℝ => p.1 / Real.sqrt (p.2 / (ν : ℝ)))
    fun_prop
  have hratio : (fun z : Fin (ν + 1) → ℝ =>
      z 0 / Real.sqrt ((∑ i ∈ Finset.univ.erase (0 : Fin (ν + 1)), (z i) ^ 2) / (ν : ℝ))) =
      R ∘ q := by
    funext z
    dsimp [R, q]
    rw [AronowAudit.P039.GaussianCompletion.erase_zero_sum]
  have hlaw : studentLaw ν =
      ((gaussianReal 0 1).prod (chiSquaredLaw ν)).map R := by
    have hchi : AronowAudit.P039.chiSquaredLaw ν = chiSquaredLaw ν := rfl
    calc
      studentLaw ν = μ.map (fun z : Fin (ν + 1) → ℝ =>
          z 0 / Real.sqrt ((∑ i ∈ Finset.univ.erase (0 : Fin (ν + 1)), (z i) ^ 2) / (ν : ℝ))) := rfl
      _ = μ.map (R ∘ q) := by rw [hratio]
      _ = (μ.map q).map R := by rw [Measure.map_map hR hq]
      _ = ((gaussianReal 0 1).prod (chiSquaredLaw ν)).map R := by
        rw [AronowAudit.P039.GaussianCompletion.standard_pair_squares, hchi]
  have : IsProbabilityMeasure (chiSquaredLaw ν) := by
    unfold chiSquaredLaw
    infer_instance
  have hWnonneg : ∀ᵐ w : ℝ ∂chiSquaredLaw ν, 0 ≤ w := by
    have hsmeas : Measurable (fun z : Fin ν → ℝ => ∑ i, (z i) ^ 2) := by fun_prop
    change ∀ᵐ w : ℝ ∂(Measure.pi (fun _ : Fin ν => gaussianReal 0 1)).map
      (fun z : Fin ν → ℝ => ∑ i, (z i) ^ 2), 0 ≤ id w
    have hall : ∀ᵐ z : Fin ν → ℝ ∂Measure.pi (fun _ : Fin ν => gaussianReal 0 1),
        0 ≤ id (∑ i, (z i) ^ 2) := by
      filter_upwards [] with z
      change 0 ≤ ∑ i, (z i) ^ 2
      exact Finset.sum_nonneg (fun i hi => sq_nonneg (z i))
    exact (ae_map_iff hsmeas.aemeasurable
      (measurableSet_le measurable_const measurable_id)).2 hall
  have hWprod : ∀ᵐ p : ℝ × ℝ ∂((gaussianReal 0 1).prod (chiSquaredLaw ν)), 0 ≤ p.2 := by
    exact (MeasureTheory.Measure.ae_prod_iff_ae_ae
      (p := fun p : ℝ × ℝ => 0 ≤ p.2)
      (measurableSet_le measurable_const measurable_snd)).2
      (ae_of_all _ fun _ => hWnonneg)
  have hG := SAP.P039.WH.W1.P.T7_L2.standard_gaussian_fourth_moment
  let f : ℝ → ℝ := fun x => x ^ 4
  let g : ℝ → ℝ := fun w => (w⁻¹) ^ 2
  have hprodBase : Integrable (fun p : ℝ × ℝ => f p.1 * g p.2)
      ((gaussianReal 0 1).prod (chiSquaredLaw ν)) := hG.1.mul_prod hInv
  have hprodEq : ∀ᵐ p : ℝ × ℝ ∂((gaussianReal 0 1).prod (chiSquaredLaw ν)),
      (R p) ^ 4 = (ν : ℝ) ^ 2 * (f p.1 * g p.2) := by
    filter_upwards [hWprod] with p hp
    exact SAP.P039.WH.W1.P.T7_L2.ratio_fourth_factor ν hν p.1 p.2 hp
  have hprodInt : Integrable (fun p : ℝ × ℝ => (R p) ^ 4)
      ((gaussianReal 0 1).prod (chiSquaredLaw ν)) := by
    apply (hprodBase.const_mul ((ν : ℝ) ^ 2)).congr
    filter_upwards [hprodEq] with p hp
    exact hp.symm
  have hstudentInt : Integrable (fun t : ℝ => t ^ 4) (studentLaw ν) := by
    rw [hlaw]
    exact (integrable_map_measure
      (by fun_prop : AEStronglyMeasurable (fun t : ℝ => t ^ 4)
        (((gaussianReal 0 1).prod (chiSquaredLaw ν)).map R)) hR.aemeasurable).mpr hprodInt
  have hstudentVal : (∫ t : ℝ, t ^ 4 ∂studentLaw ν) =
      (ν : ℝ) ^ 2 * ((∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) *
        (∫ w : ℝ, (w⁻¹) ^ 2 ∂chiSquaredLaw ν)) := by
    rw [hlaw, integral_map hR.aemeasurable (by fun_prop)]
    calc
      (∫ p : ℝ × ℝ, (R p) ^ 4 ∂((gaussianReal 0 1).prod (chiSquaredLaw ν))) =
          ∫ p : ℝ × ℝ, (ν : ℝ) ^ 2 * (f p.1 * g p.2)
            ∂((gaussianReal 0 1).prod (chiSquaredLaw ν)) := by
              exact integral_congr_ae hprodEq
      _ = (ν : ℝ) ^ 2 *
          (∫ p : ℝ × ℝ, f p.1 * g p.2 ∂((gaussianReal 0 1).prod (chiSquaredLaw ν))) := by
              rw [integral_const_mul]
      _ = (ν : ℝ) ^ 2 *
          ((∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) *
            (∫ w : ℝ, (w⁻¹) ^ 2 ∂chiSquaredLaw ν)) := by
              rw [integral_prod_mul]
  refine ⟨hstudentInt, ?_⟩
  rw [hstudentVal, hG.2, hInvVal]
  ring
