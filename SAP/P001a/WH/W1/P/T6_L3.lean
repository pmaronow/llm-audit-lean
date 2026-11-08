import SAP.P001a.WH.W1.Leaves
import AronowAudit.P001.Wave1.Gap.GP0013B1c

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology Classical
noncomputable section

namespace SAP.P001a.WH.W1.P.T6_L3

open AronowAudit.P001

private lemma uniformLaw_restrict (a b : ℝ) :
    uniformLaw a b = ENNReal.ofReal ((b-a)⁻¹) • volume.restrict (Set.Icc a b) := by
  unfold uniformLaw
  have he : (fun x : ℝ => ENNReal.ofReal (if x ∈ Set.Icc a b then (b-a)⁻¹ else 0)) =
      (Set.Icc a b).indicator (fun _ => ENNReal.ofReal ((b-a)⁻¹)) := by
    funext x
    by_cases hx : x ∈ Set.Icc a b <;> simp [hx]
  rw [he, withDensity_indicator measurableSet_Icc, withDensity_const]

private lemma mean_uniformLaw_interval (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) :
    mean (uniformLaw a b) f = (b-a)⁻¹ * ∫ x in a..b, f x := by
  rw [mean, uniformLaw_restrict, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (sub_nonneg.mpr hab)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  simp [smul_eq_mul]

private lemma mean_uniformLaw_affine (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) :
    mean (uniformLaw 0 1) (fun z => f (a+(b-a)*z)) = mean (uniformLaw a b) f := by
  calc
    mean (uniformLaw 0 1) (fun z => f (a+(b-a)*z)) =
        ∫ z in (0 : ℝ)..1, f (a+(b-a)*z) := by
      change (∫ z, f (a+(b-a)*z) ∂(AronowAudit.P001.uniformLaw 0 1)) = _
      rw [AronowAudit.P001.uniformLaw_zero_one_eq_restrict, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    _ = (b-a)⁻¹ * ∫ x in a..b, f x := by
      rw [intervalIntegral.integral_comp_add_mul f (sub_ne_zero.mpr hab.ne') a]
      simp [smul_eq_mul]
    _ = mean (uniformLaw a b) f := by
      rw [mean_uniformLaw_interval a b hab.le f]

private lemma uniformLaw_zero_one_probability : IsProbabilityMeasure (uniformLaw 0 1) := by
  rw [MeasureTheory.isProbabilityMeasure_iff]
  change (AronowAudit.P001.uniformLaw 0 1) Set.univ = 1
  rw [AronowAudit.P001.uniformLaw_zero_one_eq_restrict, Measure.restrict_apply_univ,
    Real.volume_Icc]
  norm_num

end SAP.P001a.WH.W1.P.T6_L3

open AronowAudit.P001
open SAP.P001a.WH.W1.P.T6_L3

theorem SAP.P001a.WH.W1.T6_L3_proof : SAP.P001a.WH.W1.T6_L3 := by
  intro a b hab K hK p hdeg horth x hx
  letI : IsProbabilityMeasure (uniformLaw 0 1) := uniformLaw_zero_one_probability
  let μ : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => uniformLaw 0 1)
  let X : ℕ → (ℕ → ℝ) → ℝ := fun i ω => ω i
  have hμ : IsProbabilityMeasure μ := by infer_instance
  have hmap (i : ℕ) : Measure.map (X i) μ = uniformLaw 0 1 := by
    simpa [μ, X] using measurePreserving_eval_infinitePi
      (fun _ : ℕ => uniformLaw 0 1) i |>.map_eq
  have hmeas (i : ℕ) : Measurable (X i) := by fun_prop
  have hiid : AronowAudit.P001.IID μ X := by
    refine ⟨hmeas, ?_, ?_⟩
    · simpa [μ, X] using
        (ProbabilityTheory.iIndepFun_infinitePi
          (P := fun _ : ℕ => uniformLaw 0 1) (X := fun (_i : ℕ) (ω : ℝ) => ω)
          (fun (_i : ℕ) => measurable_id))
    · intro i
      refine ⟨(hmeas i).aemeasurable, (hmeas 0).aemeasurable, ?_⟩
      rw [hmap i, hmap 0]

  let q : Fin K → Polynomial ℝ := fun k =>
    (p k).comp (Polynomial.C a + Polynomial.C (b-a)*Polynomial.X)
  have hqd (k : Fin K) : (q k).natDegree = k.val := by
    dsimp [q]
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_C_add,
      Polynomial.natDegree_C_mul_X _ (sub_ne_zero.mpr hab.ne'), mul_one, hdeg]
  have hqorth (j k : Fin K) :
      mean (uniformLaw 0 1) (fun z => (q j).eval z * (q k).eval z) =
        if j = k then 1 else 0 := by
    calc
      mean (uniformLaw 0 1) (fun z => (q j).eval z * (q k).eval z) =
          mean (uniformLaw 0 1)
            (fun z => (p j).eval (a+(b-a)*z) * (p k).eval (a+(b-a)*z)) := by
        apply congrArg (mean (uniformLaw 0 1))
        funext z
        simp [q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
          Polynomial.eval_mul, Polynomial.eval_X]
      _ = mean (uniformLaw a b) (fun y => (p j).eval y * (p k).eval y) :=
        mean_uniformLaw_affine a b hab (fun y => (p j).eval y * (p k).eval y)
      _ = if j = k then 1 else 0 := horth j k
  have hqorthμ (j k : Fin K) :
      mean μ (fun ω => (q j).eval (X 0 ω) * (q k).eval (X 0 ω)) =
        if j = k then 1 else 0 := by
    have hsm : StronglyMeasurable (fun z : ℝ => (q j).eval z * (q k).eval z) := by fun_prop
    calc
      mean μ (fun ω => (q j).eval (X 0 ω) * (q k).eval (X 0 ω)) =
          ∫ z, (q j).eval z * (q k).eval z ∂Measure.map (X 0) μ := by
        rw [mean, ← integral_map_of_stronglyMeasurable (hmeas 0) hsm]
      _ = mean (uniformLaw 0 1) (fun z => (q j).eval z * (q k).eval z) := by
        rw [hmap 0, mean]
      _ = if j = k then 1 else 0 := hqorth j k
  have hunit :=
    (AronowAudit.P001.Wave1.uniform_polynomial_gram_bound_proof
      μ X hiid (hmap 0) K 1 hK (by norm_num) q hqd hqorthμ).1
  have hz : (x-a)/(b-a) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hab.le)
    · exact (div_le_one (sub_pos.mpr hab)).mpr (by linarith [hx.2])
  have heval (k : Fin K) : (q k).eval ((x-a)/(b-a)) = (p k).eval x := by
    simp only [q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X]
    congr 1
    field_simp [sub_ne_zero.mpr hab.ne']
    <;> ring
  simpa only [heval] using hunit ((x-a)/(b-a)) hz

