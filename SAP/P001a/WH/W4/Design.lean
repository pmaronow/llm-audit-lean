import SAP.P001a.WH.W4.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Polynomial
open scoped BigOperators ENNReal NNReal Topology Matrix

noncomputable section

namespace SAP.P001a.WH.W4

open AronowAudit.P001.Wave1.SieveRate

private theorem source_uniform_restrict :
    AronowAudit.P001.uniformLaw (0 : ℝ) 1 = MeasureTheory.volume.restrict (Set.Icc 0 1) := by
  have hdensity :
      (fun x : ℝ => ENNReal.ofReal
        (if x ∈ Set.Icc (0 : ℝ) 1 then (1 - 0)⁻¹ else 0)) =
      (Set.Icc (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞) := by
    funext x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1 <;> simp [hx]
  rw [AronowAudit.P001.uniformLaw, hdensity, withDensity_indicator_one measurableSet_Icc]

private theorem source_uniform_probability :
    IsProbabilityMeasure (AronowAudit.P001.uniformLaw (0 : ℝ) 1) := by
  rw [source_uniform_restrict]
  constructor
  simp [Real.volume_Icc]

private theorem sum_integral_bound (n : ℕ) (hn : 0 < n) (q : Polynomial ℝ)
    (hint : (∫ x in Set.Icc (0 : ℝ) 1, (q.eval x) ^ 2) ≤ 1 / (n : ℝ)) :
    Integrable (fun x : Fin n → ℝ => ∑ i : Fin n, (q.eval (x i)) ^ 2) (unifVec n) ∧
      (∫ x : Fin n → ℝ, ∑ i : Fin n, (q.eval (x i)) ^ 2 ∂unifVec n) ≤ 1 := by
  let f : ℝ → ℝ := fun y => (q.eval y) ^ 2
  have hfcont : Continuous f := by
    dsimp [f]
    exact q.continuous.pow 2
  letI : IsProbabilityMeasure (AronowAudit.P001.uniformLaw (0 : ℝ) 1) :=
    source_uniform_probability
  have hfint : Integrable f (AronowAudit.P001.uniformLaw (0 : ℝ) 1) := by
    rw [source_uniform_restrict]
    exact hfcont.integrableOn_Icc
  have hcoord (i : Fin n) :
      Integrable (fun x : Fin n → ℝ => f (x i)) (unifVec n) ∧
        (∫ x : Fin n → ℝ, f (x i) ∂unifVec n) =
          ∫ y, f y ∂AronowAudit.P001.uniformLaw 0 1 := by
    constructor
    · exact (measurePreserving_eval
        (fun _ : Fin n => AronowAudit.P001.uniformLaw 0 1) i).integrable_comp_of_integrable hfint
    · simpa [unifVec] using
        (MeasureTheory.integral_comp_eval
          (μ := fun _ : Fin n => AronowAudit.P001.uniformLaw 0 1) (i := i)
          hfint.aestronglyMeasurable)
  have hsumint : Integrable (fun x : Fin n → ℝ => ∑ i : Fin n, f (x i)) (unifVec n) := by
    exact integrable_finsetSum (s := Finset.univ) (fun i hi => (hcoord i).1)
  have hsumval :
      (∫ x : Fin n → ℝ, ∑ i : Fin n, f (x i) ∂unifVec n) =
        (n : ℝ) * (∫ y, f y ∂AronowAudit.P001.uniformLaw 0 1) := by
    calc
      _ = ∑ i : Fin n, ∫ x : Fin n → ℝ, f (x i) ∂unifVec n := by
        rw [integral_finsetSum Finset.univ (fun i hi => (hcoord i).1)]
      _ = ∑ i : Fin n, ∫ y, f y ∂AronowAudit.P001.uniformLaw 0 1 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hcoord i).2
      _ = (n : ℝ) * (∫ y, f y ∂AronowAudit.P001.uniformLaw 0 1) := by
        simp [Finset.sum_const]
  have hset : (∫ y, f y ∂AronowAudit.P001.uniformLaw 0 1) =
      ∫ x in Set.Icc (0 : ℝ) 1, (q.eval x) ^ 2 := by
    rw [source_uniform_restrict]
  refine ⟨hsumint, ?_⟩
  rw [hsumval, hset]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  calc
    (n : ℝ) * (∫ x in Set.Icc (0 : ℝ) 1, (q.eval x) ^ 2) ≤
        (n : ℝ) * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_left hint hn0
    _ = 1 := by
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      field_simp

private theorem injective_ae (n : ℕ) :
    ∀ᵐ x : Fin n → ℝ ∂(unifVec n), Function.Injective x := by
  classical
  letI : IsProbabilityMeasure (unifVec n) := by unfold unifVec; infer_instance
  letI : IsProbabilityMeasure (AronowAudit.P001.uniformLaw (0 : ℝ) 1) :=
    source_uniform_probability
  letI : NullSingletonClass (AronowAudit.P001.uniformLaw (0 : ℝ) 1) := by
    rw [source_uniform_restrict]
    infer_instance
  letI : SFinite (AronowAudit.P001.uniformLaw (0 : ℝ) 1) := by
    rw [source_uniform_restrict]
    infer_instance
  have hdelta_meas : MeasurableSet {z : ℝ × ℝ | z.1 = z.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hdelta : (AronowAudit.P001.uniformLaw 0 1).prod
      (AronowAudit.P001.uniformLaw 0 1)
      {z : ℝ × ℝ | z.1 = z.2} = 0 := by
    rw [Measure.prod_apply hdelta_meas]
    have hsection (a : ℝ) :
        Prod.mk a ⁻¹' {z : ℝ × ℝ | z.1 = z.2} = {a} := by
      ext b
      simp [eq_comm]
    simp_rw [hsection]
    simp only [measure_singleton, lintegral_zero]
  have hind : iIndepFun (fun i : Fin n => fun x : Fin n → ℝ => x i) (unifVec n) := by
    exact iIndepFun_pi (μ := fun _ : Fin n => AronowAudit.P001.uniformLaw 0 1)
      (X := fun _ : Fin n => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)
  have hmarg (i : Fin n) :
      (unifVec n).map (fun x : Fin n → ℝ => x i) = AronowAudit.P001.uniformLaw 0 1 :=
    (measurePreserving_eval (fun _ : Fin n => AronowAudit.P001.uniformLaw 0 1) i).map_eq
  have hzero (i j : Fin n) (hij : i ≠ j) :
      (unifVec n) {x : Fin n → ℝ | x i = x j} = 0 := by
    have hpair : (unifVec n).map (fun x : Fin n → ℝ => (x i, x j)) =
        (AronowAudit.P001.uniformLaw 0 1).prod (AronowAudit.P001.uniformLaw 0 1) := by
      have heq := (indepFun_iff_map_prod_eq_prod_map_map
        (measurable_pi_apply i).aemeasurable
        (measurable_pi_apply j).aemeasurable).1 (hind.indepFun hij)
      simpa only [hmarg] using heq
    change (unifVec n) ((fun x : Fin n → ℝ => (x i, x j)) ⁻¹'
      {z : ℝ × ℝ | z.1 = z.2}) = 0
    rw [← Measure.map_apply
      ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) hdelta_meas,
      hpair, hdelta]
  have hpair_ae (i j : Fin n) :
      ∀ᵐ x : Fin n → ℝ ∂(unifVec n), x i = x j → i = j := by
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ _ => hij
    · have hne : ∀ᵐ x : Fin n → ℝ ∂(unifVec n), x i ≠ x j := by
        apply ae_iff.2
        simpa only [not_not] using hzero i j hij
      filter_upwards [hne] with x hx
      intro heq
      exact (hx heq).elim
  have hall : ∀ᵐ x : Fin n → ℝ ∂(unifVec n),
      ∀ i j : Fin n, x i = x j → i = j :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => hpair_ae i j
  filter_upwards [hall] with x hx
  intro i j hij
  exact hx i j hij


/-- A polynomial with uniform squared norm at most 1/n has empirical squared norm at
most two, with distinct covariates, on an event of probability at least one half.
Coordinate integration, Markov, and the null diagonal of two independent atomless
uniform variables prove this. This is the proved W3 design argument, reproduced in W4. -/
theorem good_design_mass :
  ∀ n : ℕ, 0 < n → ∀ q : Polynomial ℝ,
    (∫ x in Set.Icc (0 : ℝ) 1, (q.eval x) ^ 2) ≤ 1 / (n : ℝ) →
    1 / 2 ≤ prob (unifVec n) (goodDesign n q) := by
  classical
  intro n hn q hq
  letI : IsProbabilityMeasure (AronowAudit.P001.Wave1.SieveRate.unifVec n) := by
    unfold AronowAudit.P001.Wave1.SieveRate.unifVec
    infer_instance
  let f : (Fin n → ℝ) → ℝ := fun x => ∑ i : Fin n, (q.eval (x i)) ^ 2
  have hmom := sum_integral_bound n hn q hq
  have hfm : Measurable f := by
    exact Finset.measurable_sum Finset.univ fun i hi =>
      (q.continuous.measurable.comp (measurable_pi_apply i)).pow_const 2
  have hA : MeasurableSet {x : Fin n → ℝ | 2 ≤ f x} :=
    measurableSet_le measurable_const hfm
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun x => Finset.sum_nonneg fun i hi => sq_nonneg (q.eval (x i)))
    hmom.1 2
  have htail : AronowAudit.P001.prob (AronowAudit.P001.Wave1.SieveRate.unifVec n)
      {x : Fin n → ℝ | 2 ≤ f x} ≤ 1 / 2 := by
    have hnonneg : 0 ≤ AronowAudit.P001.prob (AronowAudit.P001.Wave1.SieveRate.unifVec n)
        {x : Fin n → ℝ | 2 ≤ f x} := by
      change 0 ≤ ((AronowAudit.P001.Wave1.SieveRate.unifVec n)
        {x : Fin n → ℝ | 2 ≤ f x}).toReal
      positivity
    change 2 * AronowAudit.P001.prob (AronowAudit.P001.Wave1.SieveRate.unifVec n)
      {x : Fin n → ℝ | 2 ≤ f x} ≤ _ at hmark
    change AronowAudit.P001.prob (AronowAudit.P001.Wave1.SieveRate.unifVec n)
      {x : Fin n → ℝ | 2 ≤ f x} ≤ 1 / 2
    nlinarith [hmark, hmom.2, hnonneg]
  have hbelow : AronowAudit.P001.prob (AronowAudit.P001.Wave1.SieveRate.unifVec n)
      {x : Fin n → ℝ | f x < 2} ≥ 1 / 2 := by
    have hcomp : {x : Fin n → ℝ | f x < 2} = {x | 2 ≤ f x}ᶜ := by
      ext x
      simp [not_le]
    change (AronowAudit.P001.Wave1.SieveRate.unifVec n).real
      {x : Fin n → ℝ | f x < 2} ≥ 1 / 2
    rw [hcomp, measureReal_compl hA]
    simp
    linarith [htail]
  have hgood : {x : Fin n → ℝ | f x < 2} ≤ᵐ[
      AronowAudit.P001.Wave1.SieveRate.unifVec n] goodDesign n q := by
    filter_upwards [injective_ae n] with x hinj hx
    exact ⟨hinj, le_of_lt hx⟩
  have hmono : AronowAudit.P001.prob (AronowAudit.P001.Wave1.SieveRate.unifVec n)
      {x : Fin n → ℝ | f x < 2} ≤
        AronowAudit.P001.prob (AronowAudit.P001.Wave1.SieveRate.unifVec n)
          (goodDesign n q) := by
    change ((AronowAudit.P001.Wave1.SieveRate.unifVec n)
      {x : Fin n → ℝ | f x < 2}).toReal ≤
      ((AronowAudit.P001.Wave1.SieveRate.unifVec n)
        (goodDesign n q)).toReal
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono_ae hgood)
  change (1 / 2 : ℝ) ≤ AronowAudit.P001.prob
    (AronowAudit.P001.Wave1.SieveRate.unifVec n) (goodDesign n q)
  exact hbelow.trans hmono


end SAP.P001a.WH.W4
