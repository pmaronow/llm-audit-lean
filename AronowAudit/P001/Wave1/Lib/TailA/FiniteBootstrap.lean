import AronowAudit.P001.P001_Foundations
import AronowAudit.External.StatLean.ComputationalStatistics.Resampling.BootstrapMoments
import AronowAudit.External.StatLean.ComputationalStatistics.Resampling.MultinomialMoments
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Logic.Equiv.Embedding
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Kernel.Composition.MapComap

/-! Exact finite resampling laws and occupancy moments. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

namespace AronowAudit.P001.TailA

local instance instDecidableFiniteBootstrap (p : Prop) : Decidable p := Classical.propDecidable p

abbrev MatchUnit := ℝ × Bool × Bool

instance instNonemptyResamplingMaps (n : ℕ) : Nonempty (Fin n → Fin n) := ⟨id⟩

/-- The uniform law on all resampling maps, including the unique empty map. -/
def UniformResampling (n : ℕ) : Measure (Fin n → Fin n) :=
  (PMF.uniformOfFintype (Fin n → Fin n)).toMeasure

instance instProbabilityUniformResampling (n : ℕ) :
    IsProbabilityMeasure (UniformResampling n) := by
  unfold UniformResampling
  infer_instance

theorem uniform_resampling_mean (n : ℕ) (g : (Fin n → Fin n) → ℝ) :
    mean (UniformResampling n) g = (∑ a, g a) / (n : ℝ)^n := by
  rw [mean, UniformResampling, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_fin,
    ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast, Nat.cast_pow, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

/-- Uniform independent labels give the same law as the uniform finite map. -/
theorem uniform_resampling_eq_pi {n : ℕ} (hn : 0 < n) :
    UniformResampling n =
      Measure.pi (fun _ : Fin n =>
        StatLean.ComputationalStatistics.categorical (fun _ : Fin n => (n : ℝ)⁻¹)) := by
  haveI instNonzero : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hcat : StatLean.ComputationalStatistics.categorical
      (fun _ : Fin n => (n : ℝ)⁻¹) = (PMF.uniformOfFintype (Fin n)).toMeasure := by
    apply Measure.ext_of_singleton
    intro i
    simp [StatLean.ComputationalStatistics.categorical, PMF.toMeasure_apply_singleton,
      PMF.uniformOfFintype_apply, ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr hn),
      Pi.single_apply, mul_ite]
  rw [hcat]
  apply Measure.ext_of_singleton
  intro a
  simp [UniformResampling, PMF.toMeasure_apply_singleton, PMF.uniformOfFintype_apply,
    Measure.pi_singleton, Fintype.card_fun, ENNReal.inv_pow]

/-- Empirical value sampling and index sampling coincide even for an empty sample. -/
theorem empirical_value_law_eq_index_map {E : Type*} [MeasurableSpace E]
    {n : ℕ} (x : Fin n → E) :
    (Measure.pi fun _ : Fin n => StatLean.ComputationalStatistics.empiricalMeasure x) =
      (UniformResampling n).map (resample x) := by
  by_cases hn : n = 0
  · subst n
    apply Measure.ext_of_singleton
    intro y
    have hy : resample x = fun _ : Fin 0 → Fin 0 => y :=
      funext fun _ => Subsingleton.elim _ _
    rw [hy, Measure.map_const]
    simp [Measure.pi_singleton]
  · have hp : 0 < n := Nat.pos_of_ne_zero hn
    haveI instNonzero : NeZero n := ⟨hn⟩
    rw [uniform_resampling_eq_pi hp]
    exact StatLean.ComputationalStatistics.resampleLaw_eq_map_indexResampling


/-- The conditional law of the centered and root-size scaled statistic. -/
def CenteredBootstrapLaw {n : ℕ} (T : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : Measure ℝ :=
  (UniformResampling n).map (fun a => Real.sqrt n * (T (resample x a) - T x))

instance instProbabilityCenteredBootstrapLaw {n : ℕ} (T : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : IsProbabilityMeasure (CenteredBootstrapLaw T x) := by
  unfold CenteredBootstrapLaw
  exact Measure.isProbabilityMeasure_map_iff Measurable.of_discrete.aemeasurable |>.mpr inferInstance


/-- Every measurable test has every Lp moment for a fixed data set, even at infinity. -/
theorem centered_bootstrap_memLp {n : ℕ} (T : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) {f : ℝ → ℝ} (hf : Measurable f) (p : ℝ≥0∞) :
    MemLp f p (CenteredBootstrapLaw T x) := by
  rw [CenteredBootstrapLaw]
  exact (memLp_map_measure_iff hf.aestronglyMeasurable
    Measurable.of_discrete.aemeasurable).mpr MemLp.of_discrete

theorem centered_bootstrap_test {n : ℕ} (T : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    mean (CenteredBootstrapLaw T x) f = bootstrapTestMean T x f := by
  rw [mean, CenteredBootstrapLaw, integral_map Measurable.of_discrete.aemeasurable
    hf.aestronglyMeasurable]
  exact uniform_resampling_mean n _

theorem centered_bootstrap_variance {n : ℕ} (T : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) :
    var (CenteredBootstrapLaw T x) id = (n : ℝ) * bootVar T x := by
  rw [var, CenteredBootstrapLaw, variance_id_map Measurable.of_discrete.aemeasurable,
    variance_const_mul, variance_sub_const Measurable.of_discrete.aestronglyMeasurable,
    Real.sq_sqrt (Nat.cast_nonneg n), variance_eq_integral Measurable.of_discrete.aemeasurable]
  have hm : (∫ a, T (resample x a) ∂UniformResampling n) = bootMean T x :=
    uniform_resampling_mean n _
  rw [hm]
  exact congrArg ((n : ℝ) * ·) (uniform_resampling_mean n _)


/-- Jointly measurable dependence on the observed data, for a measurable statistic. -/
theorem centered_bootstrap_measurable {n : ℕ} {T : (Fin n → ℝ) → ℝ}
    (hT : Measurable T) : Measurable (CenteredBootstrapLaw T) := by
  have hj : Measurable (fun p : (Fin n → ℝ) × (Fin n → Fin n) =>
      Real.sqrt n * (T (resample p.1 p.2) - T p.1)) := by
    apply measurable_from_prod_countable_left
    intro a
    exact ((hT.comp (measurable_pi_iff.mpr fun i => measurable_pi_apply (a i))).sub
      hT).const_mul _
  have hm := (Measure.measurable_map _ hj).comp
    (Measurable.map_prodMk_left (ν := UniformResampling n) (α := Fin n → ℝ))
  convert hm using 1
  funext x
  change _ = ((UniformResampling n).map (Prod.mk x)).map _
  rw [Measure.map_map hj measurable_prodMk_left]
  rfl

/-- The actual probability kernel on data samples. -/
def centeredBootstrapKernel {n : ℕ} {T : (Fin n → ℝ) → ℝ} (hT : Measurable T) :
    Kernel (Fin n → ℝ) ℝ where
  toFun := CenteredBootstrapLaw T
  measurable' := centered_bootstrap_measurable hT

instance instMarkovCenteredBootstrapKernel {n : ℕ} {T : (Fin n → ℝ) → ℝ}
    (hT : Measurable T) : IsMarkovKernel (centeredBootstrapKernel hT) :=
  ⟨fun _ => instProbabilityCenteredBootstrapLaw _ _⟩


/-- The product of uniform one-label laws is uniform on the entire map space. -/
theorem uniform_resampling_eq_uniform_pi {n : ℕ} [NeZero n] (hn : 0 < n) :
    UniformResampling n = Measure.pi (fun _ : Fin n =>
      (PMF.uniformOfFintype (Fin n)).toMeasure) := by
  haveI instNonzero : NeZero n := ⟨Nat.ne_of_gt hn⟩
  apply Measure.ext_of_singleton
  intro a
  simp [UniformResampling, PMF.toMeasure_apply_singleton, PMF.uniformOfFintype_apply,
    Measure.pi_singleton, Fintype.card_fun, ENNReal.inv_pow]

/-- A descending factorial counts ordered tuples of distinct occupied positions. -/
theorem finite_bootstrap_count_tuple {n k : ℕ} (a : Fin n → Fin n) (j : Fin n) :
    ((Finset.univ.filter (fun i => a i = j)).card.descFactorial k : ℝ) =
      ∑ e : Fin k ↪ Fin n, if ∀ i, a (e i) = j then 1 else 0 := by
  classical
  have h := Fintype.card_congr (Equiv.codRestrict (Fin k) {i : Fin n | a i = j})
  have hnat : (Finset.univ.filter (fun i => a i = j)).card.descFactorial k =
      ∑ e : Fin k ↪ Fin n, if ∀ i, a (e i) = j then 1 else 0 := by
    simpa only [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_subtype,
      Finset.card_filter, Set.mem_setOf_eq] using h.symm
  exact_mod_cast hnat

/-- The probability that specified distinct positions all select one label. -/
theorem finite_bootstrap_tuple_integral {n k : ℕ} (hn : 0 < n)
    (j : Fin n) (e : Fin k ↪ Fin n) :
    mean (UniformResampling n) (fun a => if ∀ i, a (e i) = j then 1 else 0) =
      (n : ℝ)⁻¹ ^ k := by
  classical
  haveI instNonzero : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [mean, uniform_resampling_eq_uniform_pi hn]
  let P := (PMF.uniformOfFintype (Fin n)).toMeasure
  have hind : iIndepFun (fun i : Fin n => fun a : Fin n → Fin n => a i)
      (Measure.pi fun _ : Fin n => P) :=
    iIndepFun_pi (X := fun _ : Fin n => (id : Fin n → Fin n)) fun _ => aemeasurable_id
  have hi := (iIndepFun.precomp e.injective hind).comp
    (fun _ : Fin k => fun z : Fin n => if z = j then (1 : ℝ) else 0)
    (fun _ => Measurable.of_discrete)
  have heq : (fun a : Fin n → Fin n => if ∀ i, a (e i) = j then (1 : ℝ) else 0) =
      fun a => ∏ i : Fin k, if a (e i) = j then (1 : ℝ) else 0 := by
    funext a
    simp [Fintype.prod_ite_zero]
  have hprod := hi.integral_fun_prod_eq_prod_integral (fun _ =>
    Measurable.of_discrete.aestronglyMeasurable)
  simp only [Function.comp_apply] at hprod
  rw [heq, hprod]
  have hcoord (i : Fin k) :
      (∫ a : Fin n → Fin n, (if a (e i) = j then (1 : ℝ) else 0)
        ∂(Measure.pi fun _ : Fin n => P)) = (n : ℝ)⁻¹ := by
    have hmp := measurePreserving_eval (fun _ : Fin n => P) (e i)
    have hh := integral_map (μ := Measure.pi fun _ : Fin n => P) hmp.measurable.aemeasurable
      (Measurable.of_discrete (f := fun z : Fin n => if z = j then (1 : ℝ) else 0)).aestronglyMeasurable
    rw [hmp.map_eq] at hh
    rw [← hh, uniform_index_integral]
    simp
  simp_rw [hcoord]
  simp

/-- Exact factorial moments of one occupancy under uniform size-`n` resampling. -/
theorem occupancy_factorial {n : ℕ} (hn : 0 < n) (j : Fin n) (k : ℕ) :
    mean (UniformResampling n) (fun a =>
      ((Finset.univ.filter (fun i => a i = j)).card.descFactorial k : ℝ)) =
        (n.descFactorial k : ℝ) / (n : ℝ)^k := by
  classical
  simp_rw [finite_bootstrap_count_tuple]
  rw [mean, integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [show ∀ e : Fin k ↪ Fin n,
    (∫ a, (if ∀ i, a (e i) = j then (1 : ℝ) else 0) ∂UniformResampling n) =
      (n : ℝ)⁻¹ ^ k from fun e => finite_bootstrap_tuple_integral hn j e]
  simp [Fintype.card_embedding_eq, div_eq_mul_inv, inv_pow]

/-- A uniform bound by a Bell-number sum, at every fixed natural order. -/
theorem occupancy_moment_le_stirling {n : ℕ} (hn : 0 < n) (j : Fin n) (k : ℕ) :
    mean (UniformResampling n) (fun a =>
      (((Finset.univ.filter (fun i => a i = j)).card : ℝ)^k)) ≤
        ∑ r ∈ Finset.range (k + 1), (Nat.stirlingSecond k r : ℝ) := by
  classical
  have hexp (a : Fin n → Fin n) :
      ((Finset.univ.filter (fun i => a i = j)).card : ℝ)^k =
        ∑ r ∈ Finset.range (k + 1), (Nat.stirlingSecond k r : ℝ) *
          ((Finset.univ.filter (fun i => a i = j)).card.descFactorial r : ℝ) := by
    exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial
      (Finset.univ.filter (fun i => a i = j)).card k
  simp_rw [hexp]
  rw [mean, integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [integral_const_mul]
  change (Nat.stirlingSecond k r : ℝ) * mean (UniformResampling n) _ ≤ _
  rw [occupancy_factorial hn j r]
  apply mul_le_of_le_one_right (Nat.cast_nonneg _)
  apply (div_le_one (pow_pos (Nat.cast_pos.mpr hn) r)).mpr
  exact_mod_cast Nat.descFactorial_le_pow n r


/-- A finite iid sample's event count has the binomial law, including zero draws. -/
theorem finite_bootstrap_iid_count_law {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (s : Set E) (hs : MeasurableSet s) (n : ℕ) :
    (Measure.pi fun _ : Fin n => μ).map
      (fun y => (Finset.univ.filter (fun i => y i ∈ s)).card) =
        binomial n ⟨μ.real s, by simp⟩ := by
  classical
  let p : unitInterval := ⟨μ.real s, by simp⟩
  have hpred : Measurable (fun z : E => z ∈ s) :=
    measurable_to_prop (by simpa using hs)
  have hprop : μ.map (fun z : E => z ∈ s) = bernoulliMeasure True False p := by
    have hb := (hasLaw_indicator_one_bernoulliMeasure (P := μ) (M := ℕ) (s := s) hs.nullMeasurableSet).map_eq
    have hh := map_bernoulliMeasure (1 : ℕ) 0 (fun k : ℕ => k = 1) p
    rw [← hb] at hh
    have hfun : (fun k : ℕ => k = 1) ∘ s.indicator (1 : E → ℕ) =
        (fun z : E => z ∈ s) := by
      funext z
      by_cases hz : z ∈ s <;> simp [Function.comp_apply, Set.indicator, hz]
    have hc := Measure.map_map (μ := μ) (g := fun k : ℕ => k = 1)
      (f := s.indicator (1 : E → ℕ)) Measurable.of_discrete (measurable_one.indicator hs)
    rw [hfun] at hc
    simpa using hc.symm.trans hh
  have hset : (Measure.pi fun _ : Fin n => μ).map
      (fun y => {i : Fin n | y i ∈ s}) = setBernoulli (Set.univ : Set (Fin n)) p := by
    rw [setBernoulli_eq_map, Measure.infinitePi_eq_pi]
    simp only [Set.mem_univ]
    have hp := Measure.pi_map_pi (μ := fun _ : Fin n => μ)
      (f := fun _ : Fin n => fun z : E => z ∈ s) (fun _ => hpred.aemeasurable)
    simp only [hprop] at hp
    rw [← hp]
    have hm : Measurable (fun y : Fin n → E => fun i : Fin n => y i ∈ s) :=
      measurable_pi_iff.mpr fun i => hpred.comp (measurable_pi_apply i)
    exact (Measure.map_map (μ := Measure.pi fun _ : Fin n => μ)
      measurable_setOfPred hm).symm
  have hc : (fun y : Fin n → E => (Finset.univ.filter (fun i => y i ∈ s)).card) =
      (fun y : Fin n → E => ({i : Fin n | y i ∈ s} : Set (Fin n)).ncard) := by
    funext y
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp
  rw [hc]
  have hm : Measurable (fun y : Fin n → E => {i : Fin n | y i ∈ s}) :=
    measurable_set_iff.mpr fun i => hpred.comp (measurable_pi_apply i)
  calc
    _ = ((Measure.pi fun _ : Fin n => μ).map
        (fun y => {i : Fin n | y i ∈ s})).map Set.ncard :=
      (Measure.map_map (μ := Measure.pi fun _ : Fin n => μ) measurable_ncard hm).symm
    _ = (setBernoulli (Set.univ : Set (Fin n)) p).map Set.ncard := by rw [hset]
    _ = binomial n ⟨μ.real s, by simp⟩ := by
      apply Measure.ext_of_singleton
      intro k
      rw [map_ncard_setBernoulli_singleton (Set.finite_univ) p k, binomial_singleton]
      simp [Set.ncard_univ, Nat.card_eq_fintype_card, p]

/-- Conditional probability of a weak threshold for a single empirical draw. -/
def empiricalThresholdProbability {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : unitInterval :=
  if hn : 0 < n then
    letI instNonzero : NeZero n := ⟨Nat.ne_of_gt hn⟩
    ⟨(StatLean.ComputationalStatistics.empiricalMeasure x).real (Set.Iic t), by simp⟩
  else 0

/-- Threshold counts of the actual resampled data have their empirical binomial law. -/
theorem bootstrap_threshold_count_law {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    (UniformResampling n).map (fun a =>
      (Finset.univ.filter (fun i => x (a i) ≤ t)).card) =
        binomial n (empiricalThresholdProbability x t) := by
  classical
  by_cases hn : 0 < n
  · haveI instNonzero : NeZero n := ⟨Nat.ne_of_gt hn⟩
    have h := finite_bootstrap_iid_count_law
      (StatLean.ComputationalStatistics.empiricalMeasure x) (Set.Iic t) measurableSet_Iic n
    have hm : Measurable (fun y : Fin n → ℝ =>
        (Finset.univ.filter (fun i => y i ∈ Set.Iic t)).card) := by
      simp only [Finset.card_filter]
      exact Finset.univ.measurable_sum fun i _ => Measurable.ite
        (measurableSet_le (measurable_pi_apply i) measurable_const)
        measurable_const measurable_const
    rw [empirical_value_law_eq_index_map x] at h
    have hmap := Measure.map_map (μ := UniformResampling n) hm
      (Measurable.of_discrete (f := resample x))
    have hfinal := hmap.symm.trans h
    simp only [Function.comp_def, resample, Set.mem_Iic,
      empiricalThresholdProbability, dif_pos hn] at hfinal ⊢
    convert hfinal using 1
    congr 1
  · have hz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [empiricalThresholdProbability, Measure.map_const, binomial_zero]

/-- The binomial parameter is exactly the observed threshold fraction. -/
theorem empirical_threshold_probability_eq {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    (empiricalThresholdProbability x t : ℝ) =
      ((Finset.univ.filter (fun i => x i ≤ t)).card : ℝ) / (n : ℝ) := by
  classical
  by_cases hn : 0 < n
  · haveI instNonzero : NeZero n := ⟨Nat.ne_of_gt hn⟩
    simp only [empiricalThresholdProbability, dif_pos hn]
    rw [Measure.real, StatLean.ComputationalStatistics.empiricalMeasure_apply _ measurableSet_Iic]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum]
    rw [Finset.card_filter]
    simp [Set.indicator, div_eq_mul_inv, Finset.mul_sum, mul_comm]
  · have hz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [empiricalThresholdProbability]

end AronowAudit.P001.TailA
