import AronowAudit.P022.P022_Variance
import AronowAudit.External.StatLean.HypothesisTesting.ForMathlib.CombinatorialCLT
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.HalfLineQuantile
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
Atom-sensitive endpoints for corrected P022 Lemma 2. Both strict and nonstrict
thresholds are retained at each quantile.
-/

namespace AronowAudit.P022.Wave1.TailA

open scoped BigOperators Topology ENNReal NNReal
open Filter MeasureTheory ProbabilityTheory Set
open AsymptoticStatistics.EmpiricalProcess
set_option autoImplicit false

noncomputable section

local instance instAtomEndpointsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem atom_block_moments (d : Design) {s : ℕ} (hs : 0 < s)
    (e : Fin s → Fin d.N) (he : Function.Injective e) (z : Fin d.N → ℝ) :
    designExpectation d (fun π => finiteMean (fun j => z (π (e j)))) = finiteMean z ∧
    designExpectation d (fun π =>
      (finiteMean (fun j => z (π (e j))) - finiteMean z) ^ 2) =
      ((d.N : ℝ) - s) / (((d.N : ℝ) - 1) * s) * finiteVariance z := by
  classical
  letI instAtomBlockNeZero : NeZero s := ⟨ne_of_gt hs⟩
  have hNnat : 0 < d.N := by have := d.population_min; omega
  have hN : (0 : ℝ) < d.N := by exact_mod_cast hNnat
  have hN₁ : (0 : ℝ) < (d.N : ℝ) - 1 := by
    have hh : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
    linarith
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  constructor
  · unfold designExpectation finiteMean
    rw [Finset.expect_comm]
    simp_rw [permutation_eval_mean hNnat]
    exact Fintype.expect_const _
  · let μ : ℝ := finiteMean z
    let w : Fin d.N → ℝ := fun i => z i - μ
    have hsumz : (∑ i, z i) = (d.N : ℝ) * μ := by
      simpa only [Fintype.card_fin, μ, finiteMean] using
        (Fintype.card_mul_expect z).symm
    have hw : ∑ i, w i = 0 := by
      dsimp [w]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hsumz]
      ring
    have hsumw : (∑ i, w i ^ 2) = (d.N : ℝ) * finiteVariance z := by
      simpa only [Fintype.card_fin, finiteVariance, finiteMean, w, μ] using
        (Fintype.card_mul_expect (fun i => w i ^ 2)).symm
    have hcenter : ∀ π : Assignment d,
        finiteMean (fun j => z (π (e j))) - finiteMean z =
          (∑ j, w (π (e j))) / (s : ℝ) := by
      intro π
      change (𝔼 j : Fin s, z (π (e j))) - μ =
        (∑ j : Fin s, (z (π (e j)) - μ)) / (s : ℝ)
      rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin,
        Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp [ne_of_gt hsR]
      <;> ring
    have hblock := StatLean.HypothesisTesting.avg_perm_blockSum_sq
      (show 2 ≤ d.N by have := d.population_min; omega) e he w hw
    have havg : designExpectation d (fun π => (∑ j, w (π (e j))) ^ 2) =
        (s : ℝ) * ((d.N : ℝ) - s) / ((d.N : ℝ) * ((d.N : ℝ) - 1)) *
          ∑ i, w i ^ 2 := by
      simpa only [designExpectation, Fintype.expect_eq_sum_div_card,
        div_eq_inv_mul] using hblock
    calc
      designExpectation d (fun π =>
          (finiteMean (fun j => z (π (e j))) - finiteMean z) ^ 2) =
          designExpectation d (fun π => (∑ j, w (π (e j))) ^ 2 / (s : ℝ) ^ 2) := by
        unfold designExpectation
        apply Finset.expect_congr rfl
        intro π _
        rw [hcenter π, div_pow]
      _ = designExpectation d (fun π => (∑ j, w (π (e j))) ^ 2) / (s : ℝ) ^ 2 := by
        unfold designExpectation
        exact (Finset.expect_div _ _ _).symm
      _ = ((d.N : ℝ) - s) / (((d.N : ℝ) - 1) * s) * finiteVariance z := by
        rw [havg, hsumw]
        field_simp [ne_of_gt hN, ne_of_gt hN₁, ne_of_gt hsR]
        <;> ring


/-- The same exact moments apply to either convention for an indicator endpoint. -/
theorem atom_indicator_block_moments (d : Design) {s : ℕ} (hs : 0 < s)
    (e : Fin s → Fin d.N) (he : Function.Injective e) (p : Fin d.N → Prop) :
    let z : Fin d.N → ℝ := fun i => if p i then 1 else 0
    designExpectation d (fun π => finiteMean (fun j => z (π (e j)))) = finiteMean z ∧
    designExpectation d (fun π =>
      (finiteMean (fun j => z (π (e j))) - finiteMean z) ^ 2) =
      ((d.N : ℝ) - s) / (((d.N : ℝ) - 1) * s) *
        (finiteMean z * (1 - finiteMean z)) := by
  classical
  dsimp only
  have hN : 0 < d.N := by have := d.population_min; omega
  have hv : finiteVariance (fun i => if p i then (1 : ℝ) else 0) =
      finiteMean (fun i => if p i then (1 : ℝ) else 0) *
        (1 - finiteMean (fun i => if p i then (1 : ℝ) else 0)) := by
    rw [finite_variance_second_moment hN]
    have hz : (fun i => (if p i then (1 : ℝ) else 0) ^ 2) =
        (fun i => if p i then (1 : ℝ) else 0) := by
      funext i
      split_ifs <;> norm_num
    rw [hz]
    ring
  simpa only [hv] using atom_block_moments d hs e he (fun i => if p i then 1 else 0)

/-- Empirical probability law, used to connect finite averages to Portmanteau. -/
def atom_empiricalLaw {α : Type*} [MeasurableSpace α] {N : ℕ} (hN : 0 < N)
    (y : Fin N → α) : ProbabilityMeasure α := by
  letI instAtomEmpiricalNeZero : NeZero N := ⟨ne_of_gt hN⟩
  exact ⟨empiricalMeasure N y, inferInstance⟩

theorem atom_empirical_integral {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {N : ℕ} (hN : 0 < N) (y : Fin N → α) (f : α → ℝ) :
    (∫ x, f x ∂(atom_empiricalLaw hN y : Measure α)) = finiteMean (fun i => f (y i)) := by
  change (∫ x, f x ∂empiricalMeasure N y) = _
  rw [empiricalMeasure, integral_smul_measure,
    integral_finsetSum_measure (fun i _ => integrable_dirac (by simp))]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul,
    finiteMean, Fintype.expect_eq_sum_div_card, Fintype.card_fin]
  ring

theorem atom_empirical_Iic {N : ℕ} (hN : 0 < N) (y : Fin N → ℝ) (x : ℝ) :
    (atom_empiricalLaw hN y : Measure ℝ).real (Iic x) = empiricalCDF y x := by
  rw [← integral_indicator_one measurableSet_Iic, atom_empirical_integral]
  rfl

theorem atom_empirical_Iio {N : ℕ} (hN : 0 < N) (y : Fin N → ℝ) (x : ℝ) :
    (atom_empiricalLaw hN y : Measure ℝ).real (Iio x) = empiricalLeftCDF y x := by
  rw [← integral_indicator_one measurableSet_Iio, atom_empirical_integral]
  rfl

/-- The coordinate marginal, rather than a joint CDF. -/
def atom_marginalLaw (H : JointLaw) (t : Bool) : ProbabilityMeasure ℝ :=
  H.map (fun p => if t then p.1 else p.2)

theorem atom_coordinate_continuous (t : Bool) :
    Continuous (fun p : ℝ × ℝ => if t then p.1 else p.2) := by
  cases t <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop

theorem atom_marginal_Iic (H : JointLaw) (t : Bool) (x : ℝ) :
    (atom_marginalLaw H t : Measure ℝ).real (Iic x) = lawCDF H t x := by
  rw [measureReal_def, atom_marginalLaw, ProbabilityMeasure.map_apply' H
    (atom_coordinate_continuous t).measurable.aemeasurable measurableSet_Iic]
  rfl

theorem atom_marginal_Iio (H : JointLaw) (t : Bool) (x : ℝ) :
    (atom_marginalLaw H t : Measure ℝ).real (Iio x) = lawLeftCDF H t x := by
  rw [measureReal_def, atom_marginalLaw, ProbabilityMeasure.map_apply' H
    (atom_coordinate_continuous t).measurable.aemeasurable measurableSet_Iio]
  rfl

theorem atom_marginal_cdf (H : JointLaw) (t : Bool) :
    (fun x => cdf (atom_marginalLaw H t : Measure ℝ) x) = lawCDF H t := by
  funext x
  rw [cdf_eq_real, atom_marginal_Iic]

theorem atom_marginal_weak (S : ExperimentSequence) (H : JointLaw)
    (hw : weakPopulationConvergence S H) (t : Bool) :
    Tendsto (fun q => atom_empiricalLaw
      (show 0 < (S.design q).N by have := (S.design q).population_min; omega)
      (rowOutcomes S t q)) atTop (𝓝 (atom_marginalLaw H t)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hf := hw (f.compContinuous
    ⟨(fun p : ℝ × ℝ => if t then p.1 else p.2), atom_coordinate_continuous t⟩)
  simpa only [atom_empirical_integral, atom_marginalLaw, ProbabilityMeasure.toMeasure_map,
    integral_map (atom_coordinate_continuous t).measurable.aemeasurable
      f.continuous.aestronglyMeasurable, BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.coe_mk, rowOutcomes, ite_apply] using hf

theorem atom_marginal_singleton_null (H : JointLaw) (t : Bool) (x : ℝ)
    (hx : ContinuousAt (lawCDF H t) x) :
    (atom_marginalLaw H t : Measure ℝ) {x} = 0 := by
  have hc : ContinuousAt (fun z => cdf (atom_marginalLaw H t : Measure ℝ) z) x := by
    rwa [atom_marginal_cdf]
  rw [← measure_cdf (atom_marginalLaw H t : Measure ℝ),
    StieltjesFunction.measure_singleton, hc.continuousWithinAt.leftLim_eq, sub_self,
    ENNReal.ofReal_zero]

/-- The closed endpoint converges at every threshold, including jumps. -/
theorem atom_cdf_endpoint_convergence (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (t : Bool) (x : ℝ) :
    Tendsto (fun q => empiricalCDF (rowOutcomes S t q) x) atTop (𝓝 (lawCDF H t x)) := by
  by_cases hx : ContinuousAt (lawCDF H t) x
  · have hp := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      (atom_marginal_weak S H h.2.2.2.2.2.2.1 t)
      (show (atom_marginalLaw H t : Measure ℝ) (frontier (Iic x)) = 0 by
        rw [frontier_Iic]; exact atom_marginal_singleton_null H t x hx)
    have hr := (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp hp
    simpa only [Function.comp_def, ← measureReal_def, atom_empirical_Iic,
      atom_marginal_Iic] using hr
  · exact h.2.2.2.2.2.2.2 t x hx

/-- The open endpoint converges at every threshold; jumps use the correction's input. -/
theorem atom_left_endpoint_convergence (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (hleft : AtomLeftConvergence S H) (t : Bool) (x : ℝ) :
    Tendsto (fun q => empiricalLeftCDF (rowOutcomes S t q) x) atTop
      (𝓝 (lawLeftCDF H t x)) := by
  by_cases hx : ContinuousAt (lawCDF H t) x
  · have hp := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      (atom_marginal_weak S H h.2.2.2.2.2.2.1 t)
      (show (atom_marginalLaw H t : Measure ℝ) (frontier (Iio x)) = 0 by
        rw [frontier_Iio]; exact atom_marginal_singleton_null H t x hx)
    have hr := (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp hp
    simpa only [Function.comp_def, ← measureReal_def, atom_empirical_Iio,
      atom_marginal_Iio] using hr
  · exact hleft t x hx

/-- Every real point lies at a grid endpoint, in a tail, or in an open adjacent gap.
Repeated grid points cause no difficulty. -/
theorem atom_grid_cover {n : ℕ} (q : Fin (n + 1) → ℝ) (x : ℝ) :
    x < q 0 ∨ q (Fin.last n) < x ∨ (∃ i, x = q i) ∨
      ∃ j : Fin n, q j.castSucc < x ∧ x < q j.succ := by
  classical
  by_cases hlo : x < q 0
  · exact Or.inl hlo
  by_cases hhi : q (Fin.last n) < x
  · exact Or.inr (Or.inl hhi)
  by_cases heq : ∃ i, x = q i
  · exact Or.inr (Or.inr (Or.inl heq))
  have hne : ∀ i, x ≠ q i := by simpa only [not_exists] using heq
  let I := Finset.univ.filter (fun i => q i < x)
  have hI : I.Nonempty := ⟨0, by
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_of_le_of_ne (le_of_not_gt hlo) (hne 0).symm⟩
  let i := I.max' hI
  have hi : q i < x := (Finset.mem_filter.mp (Finset.max'_mem I hI)).2
  have hin : i.val < n := by
    by_contra hh
    have he : i = Fin.last n := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
    rw [he] at hi
    exact hhi hi
  let j : Fin n := ⟨i.val, hin⟩
  have hji : j.castSucc = i := Fin.ext rfl
  have hnext : ¬q j.succ < x := by
    intro hn
    have hmem : j.succ ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
    have hh := Finset.le_max' I j.succ hmem
    change i.val + 1 ≤ i.val at hh
    omega
  refine Or.inr (Or.inr (Or.inr ⟨j, ?_, ?_⟩))
  · simpa only [hji] using hi
  · exact lt_of_le_of_ne (le_of_not_gt hnext) (hne _)

/-- Largest of the two endpoint errors at all grid points. -/
def atom_gridDeviation {n : ℕ} (P A : ProbabilityMeasure ℝ) (q : Fin (n + 1) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i =>
    max |(P : Measure ℝ).real (Iic (q i)) - (A : Measure ℝ).real (Iic (q i))|
      |(P : Measure ℝ).real (Iio (q i)) - (A : Measure ℝ).real (Iio (q i))|)

theorem atom_gridDeviation_bounds {n : ℕ} (P A : ProbabilityMeasure ℝ)
    (q : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    |(P : Measure ℝ).real (Iic (q i)) - (A : Measure ℝ).real (Iic (q i))| ≤
      atom_gridDeviation P A q ∧
    |(P : Measure ℝ).real (Iio (q i)) - (A : Measure ℝ).real (Iio (q i))| ≤
      atom_gridDeviation P A q := by
  have hm := Finset.le_sup'
    (fun j => max |(P : Measure ℝ).real (Iic (q j)) - (A : Measure ℝ).real (Iic (q j))|
      |(P : Measure ℝ).real (Iio (q j)) - (A : Measure ℝ).real (Iio (q j))|)
    (Finset.mem_univ i)
  exact ⟨(le_max_left _ _).trans hm, (le_max_right _ _).trans hm⟩

theorem atom_gridDeviation_lt {n : ℕ} (P A : ProbabilityMeasure ℝ)
    (q : Fin (n + 1) → ℝ) (ε : ℝ)
    (h : ∀ i, |(P : Measure ℝ).real (Iic (q i)) - (A : Measure ℝ).real (Iic (q i))| < ε ∧
      |(P : Measure ℝ).real (Iio (q i)) - (A : Measure ℝ).real (Iio (q i))| < ε) :
    atom_gridDeviation P A q < ε := by
  exact (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun i _ => max_lt (h i).1 (h i).2)

/-- An atom-safe grid controls the full CDF distance. The open gap bound is nonstrict. -/
theorem atom_grid_cdf_bound {n : ℕ} (P A : ProbabilityMeasure ℝ)
    (q : Fin (n + 1) → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hlo : (P : Measure ℝ).real (Iio (q 0)) ≤ δ)
    (hgap : ∀ j : Fin n,
      (P : Measure ℝ).real (Ioo (q j.castSucc) (q j.succ)) ≤ δ)
    (hhi : (P : Measure ℝ).real (Ioi (q (Fin.last n))) ≤ δ) :
    cdfDistance (fun x => (P : Measure ℝ).real (Iic x))
      (fun x => (A : Measure ℝ).real (Iic x)) ≤ atom_gridDeviation P A q + δ := by
  let M := atom_gridDeviation P A q
  have hM : 0 ≤ M := (abs_nonneg _).trans (atom_gridDeviation_bounds P A q 0).1
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  rcases atom_grid_cover q x with hx | hx | ⟨i, rfl⟩ | ⟨j, hjl, hju⟩
  · have hp := measureReal_mono (μ := (P : Measure ℝ)) (Iic_subset_Iio.mpr hx)
    have ha := measureReal_mono (μ := (A : Measure ℝ)) (Iic_subset_Iio.mpr hx)
    have he := (abs_le.mp (atom_gridDeviation_bounds P A q 0).2)
    have hp0 := measureReal_nonneg (μ := (P : Measure ℝ)) (s := Iic x)
    have ha0 := measureReal_nonneg (μ := (A : Measure ℝ)) (s := Iic x)
    apply abs_le.mpr
    constructor <;> dsimp [M] at * <;> linarith
  · have hp := measureReal_mono (μ := (P : Measure ℝ)) (Iic_subset_Iic.mpr hx.le)
    have ha := measureReal_mono (μ := (A : Measure ℝ)) (Iic_subset_Iic.mpr hx.le)
    have he := abs_le.mp (atom_gridDeviation_bounds P A q (Fin.last n)).1
    have htail := measureReal_add_measureReal_compl (μ := (P : Measure ℝ))
      (measurableSet_Iic : MeasurableSet (Iic (q (Fin.last n))))
    simp only [compl_Iic, probReal_univ] at htail
    have hp1 : (P : Measure ℝ).real (Iic x) ≤ 1 := by
      simpa only [probReal_univ] using
        (measureReal_mono (μ := (P : Measure ℝ)) (subset_univ (Iic x)))
    have ha1 : (A : Measure ℝ).real (Iic x) ≤ 1 := by
      simpa only [probReal_univ] using
        (measureReal_mono (μ := (A : Measure ℝ)) (subset_univ (Iic x)))
    apply abs_le.mpr
    constructor <;> dsimp [M] at * <;> linarith
  · exact (atom_gridDeviation_bounds P A q i).1.trans (le_add_of_nonneg_right hδ)
  · have hpL := measureReal_mono (μ := (P : Measure ℝ)) (Iic_subset_Iic.mpr hjl.le)
    have hpU := measureReal_mono (μ := (P : Measure ℝ)) (Iic_subset_Iio.mpr hju)
    have haL := measureReal_mono (μ := (A : Measure ℝ)) (Iic_subset_Iic.mpr hjl.le)
    have haU := measureReal_mono (μ := (A : Measure ℝ)) (Iic_subset_Iio.mpr hju)
    have heL := abs_le.mp (atom_gridDeviation_bounds P A q j.castSucc).1
    have heU := abs_le.mp (atom_gridDeviation_bounds P A q j.succ).2
    have hgap' : (P : Measure ℝ).real (Iio (q j.succ)) ≤
        (P : Measure ℝ).real (Iic (q j.castSucc)) + δ := by
      have hu := measureReal_union_le (μ := (P : Measure ℝ))
        (Iic (q j.castSucc)) (Ioo (q j.castSucc) (q j.succ))
      rw [Iic_union_Ioo_eq_Iio (hjl.trans hju)] at hu
      exact hu.trans (add_le_add le_rfl (hgap j))
    apply abs_le.mpr
    constructor <;> dsimp [M] at * <;> linarith

/-- A Boolean indexes the strict and the nonstrict threshold without dropping either. -/
def atom_endpoint {N : ℕ} (y : Fin N → ℝ) (b : Bool) (x : ℝ) : ℝ :=
  if b then empiricalLeftCDF y x else empiricalCDF y x

def atom_measureEndpoint (P : ProbabilityMeasure ℝ) (b : Bool) (x : ℝ) : ℝ :=
  (P : Measure ℝ).real (if b then Iio x else Iic x)

theorem atom_empirical_endpoint {N : ℕ} (hN : 0 < N) (y : Fin N → ℝ)
    (b : Bool) (x : ℝ) :
    atom_measureEndpoint (atom_empiricalLaw hN y) b x = atom_endpoint y b x := by
  cases b
  · simpa only [atom_measureEndpoint, atom_endpoint, Bool.false_eq_true, if_false] using
      atom_empirical_Iic hN y x
  · simpa only [atom_measureEndpoint, atom_endpoint, if_true] using atom_empirical_Iio hN y x

theorem atom_endpoint_convergence (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (hleft : AtomLeftConvergence S H)
    (t b : Bool) (x : ℝ) :
    Tendsto (fun q => atom_endpoint (rowOutcomes S t q) b x) atTop
      (𝓝 (atom_measureEndpoint (atom_marginalLaw H t) b x)) := by
  cases b
  · simpa only [atom_endpoint, atom_measureEndpoint, Bool.false_eq_true, if_false,
      atom_marginal_Iic] using
      atom_cdf_endpoint_convergence S H θ ρ h t x
  · simpa only [atom_endpoint, atom_measureEndpoint, if_true, atom_marginal_Iio] using
      atom_left_endpoint_convergence S H θ ρ h hleft t x

/-- Exact expectation and centered second moment for both injected-block endpoints. -/
theorem atom_endpoint_block_moments (d : Design) {s : ℕ} (hs : 0 < s)
    (e : Fin s → Fin d.N) (he : Function.Injective e) (y : Fin d.N → ℝ)
    (b : Bool) (x : ℝ) :
    designExpectation d (fun π => atom_endpoint (fun j => y (π (e j))) b x) =
      atom_endpoint y b x ∧
    designExpectation d (fun π =>
      (atom_endpoint (fun j => y (π (e j))) b x - atom_endpoint y b x) ^ 2) =
      ((d.N : ℝ) - s) / (((d.N : ℝ) - 1) * s) *
        (atom_endpoint y b x * (1 - atom_endpoint y b x)) := by
  cases b
  · simpa only [atom_endpoint, Bool.false_eq_true, if_false, empiricalCDF] using
      atom_indicator_block_moments d hs e he (fun i => y i ≤ x)
  · simpa only [atom_endpoint, if_true, empiricalLeftCDF] using
      atom_indicator_block_moments d hs e he (fun i => y i < x)

/-- A centered endpoint obeys Chebyshev with the exact finite-population correction. -/
theorem atom_endpoint_chebyshev (d : Design) {s : ℕ} (hs : 0 < s)
    (e : Fin s → Fin d.N) (he : Function.Injective e) (y : Fin d.N → ℝ)
    (b : Bool) (x η : ℝ) (hη : 0 < η) :
    designProbability d (fun π => η / 2 ≤
      |atom_endpoint (fun j => y (π (e j))) b x - atom_endpoint y b x|) ≤
      ((d.N : ℝ) - s) / (((d.N : ℝ) - 1) * s * η ^ 2) := by
  have hsN : s ≤ d.N := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e he
  have hcoef : 0 ≤ ((d.N : ℝ) - s) / (((d.N : ℝ) - 1) * s) := by
    have hh : (s : ℝ) ≤ d.N := by exact_mod_cast hsN
    have hN : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
    exact div_nonneg (sub_nonneg.mpr hh)
      (mul_nonneg (by linarith) (by exact_mod_cast Nat.le_of_lt hs))
  have hmarkov := finite_squared_markov d
    (fun π => atom_endpoint (fun j => y (π (e j))) b x - atom_endpoint y b x)
    (η / 2) (by positivity)
  rw [(atom_endpoint_block_moments d hs e he y b x).2] at hmarkov
  have hvar := mul_le_mul_of_nonneg_left (bernoulli_variance_bound (atom_endpoint y b x)).1 hcoef
  calc
    _ ≤ _ := hmarkov
    _ ≤ (((d.N : ℝ) - s) / (((d.N : ℝ) - 1) * s) * (1 / 4)) / (η / 2) ^ 2 :=
      div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ = _ := by field_simp; ring

theorem atom_probability_union {ι : Type*} [Fintype ι] (d : Design)
    (E : Assignment d → Prop) (F : ι → Assignment d → Prop)
    (h : ∀ π, E π → ∃ i, F i π) :
    designProbability d E ≤ ∑ i, designProbability d (F i) := by
  classical
  unfold designProbability designExpectation
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_le_expect
  intro π _
  by_cases hE : E π
  · rw [if_pos hE]
    obtain ⟨i, hi⟩ := h π hE
    calc
      (1 : ℝ) = if F i π then 1 else 0 := by rw [if_pos hi]
      _ ≤ ∑ j, if F j π then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun j => if F j π then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
  · rw [if_neg hE]
    apply Finset.sum_nonneg
    intro i _
    dsimp only
    split_ifs <;> norm_num

theorem atom_gridDeviation_endpoint_le {n : ℕ} (P A : ProbabilityMeasure ℝ)
    (q : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (b : Bool) :
    |atom_measureEndpoint P b (q i) - atom_measureEndpoint A b (q i)| ≤
      atom_gridDeviation P A q := by
  cases b
  · exact (atom_gridDeviation_bounds P A q i).1
  · exact (atom_gridDeviation_bounds P A q i).2

theorem atom_gridDeviation_le_endpoints {n : ℕ} (P A : ProbabilityMeasure ℝ)
    (q : Fin (n + 1) → ℝ) (ε : ℝ)
    (h : ∀ i b, |atom_measureEndpoint P b (q i) - atom_measureEndpoint A b (q i)| ≤ ε) :
    atom_gridDeviation P A q ≤ ε := by
  apply Finset.sup'_le
  intro i _
  exact max_le (h i false) (h i true)

theorem atom_gridDeviation_triangle {n : ℕ} (P A B : ProbabilityMeasure ℝ)
    (q : Fin (n + 1) → ℝ) :
    atom_gridDeviation P A q ≤ atom_gridDeviation P B q + atom_gridDeviation B A q := by
  apply atom_gridDeviation_le_endpoints
  intro i b
  exact (abs_sub_le _ _ _).trans (add_le_add
    (atom_gridDeviation_endpoint_le P B q i b) (atom_gridDeviation_endpoint_le B A q i b))

theorem atom_real_le_of_measure_le (μ : Measure ℝ) (E : Set ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : μ E ≤ ENNReal.ofReal δ) : μ.real E ≤ δ := by
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [measureReal_def, ENNReal.toReal_ofReal hδ] using hh

theorem atom_measureEndpoint_bounds (P : ProbabilityMeasure ℝ) (b : Bool) (x : ℝ) :
    0 ≤ atom_measureEndpoint P b x ∧ atom_measureEndpoint P b x ≤ 1 := by
  refine ⟨measureReal_nonneg, ?_⟩
  simpa only [probReal_univ, atom_measureEndpoint] using
    (measureReal_mono (μ := (P : Measure ℝ)) (subset_univ (if b then Iio x else Iic x)))

theorem atom_cdfDistance_bounds (P A : ProbabilityMeasure ℝ) :
    0 ≤ cdfDistance (fun x => (P : Measure ℝ).real (Iic x))
      (fun x => (A : Measure ℝ).real (Iic x)) ∧
    cdfDistance (fun x => (P : Measure ℝ).real (Iic x))
      (fun x => (A : Measure ℝ).real (Iic x)) ≤ 1 := by
  have hp : ∀ x, |(P : Measure ℝ).real (Iic x) - (A : Measure ℝ).real (Iic x)| ≤ 1 := by
    intro x
    have hP := atom_measureEndpoint_bounds P false x
    have hA := atom_measureEndpoint_bounds A false x
    apply abs_le.mpr
    constructor <;> change _ ≤ _ <;> dsimp [atom_measureEndpoint] at * <;> linarith
  have hb : BddAbove (range (fun x => |(P : Measure ℝ).real (Iic x) -
      (A : Measure ℝ).real (Iic x)|)) := ⟨1, by rintro _ ⟨x, rfl⟩; exact hp x⟩
  exact ⟨(abs_nonneg _).trans (le_csSup hb ⟨0, rfl⟩),
    csSup_le (range_nonempty _) (by rintro _ ⟨x, rfl⟩; exact hp x)⟩

/-- Endpoint convergence implies uniform CDF convergence, even when the limit has atoms. -/
theorem atom_endpoints_to_uniform (P : ProbabilityMeasure ℝ) (A : ℕ → ProbabilityMeasure ℝ)
    (h : ∀ b x, Tendsto (fun k => atom_measureEndpoint (A k) b x) atTop
      (𝓝 (atom_measureEndpoint P b x))) :
    Tendsto (fun k => cdfDistance (fun x => (P : Measure ℝ).real (Iic x))
      (fun x => (A k : Measure ℝ).real (Iic x))) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
  obtain ⟨q, -, hlo, hgap, hhi⟩ := exists_halfLine_atomSafeGrid (P : Measure ℝ) n
  let δ : ℝ := 1 / (n + 2 : ℝ)
  have hδ : 0 ≤ δ := by positivity
  have hδε : δ < ε / 2 := lt_of_le_of_lt
    (div_le_div_of_nonneg_left (by norm_num) (by positivity : (0 : ℝ) < n + 1)
      (by norm_num : (n + 1 : ℝ) ≤ n + 2)) hn
  have he : ∀ᶠ k in atTop, ∀ i : Fin (n + 1), ∀ b : Bool,
      |atom_measureEndpoint (A k) b (q i) - atom_measureEndpoint P b (q i)| < ε / 2 := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro b
    have ht := ((h b (q i)).sub
      (tendsto_const_nhds (x := atom_measureEndpoint P b (q i)))).abs
    have ht' : Tendsto (fun k => |atom_measureEndpoint (A k) b (q i) -
        atom_measureEndpoint P b (q i)|) atTop (𝓝 0) := by simpa only [sub_self, abs_zero] using ht
    exact ht'.eventually (eventually_lt_nhds (half_pos hε))
  filter_upwards [he] with k hk
  have hm : atom_gridDeviation P (A k) q < ε / 2 := by
    apply atom_gridDeviation_lt
    intro i
    constructor
    · simpa only [atom_measureEndpoint, Bool.false_eq_true, if_false, abs_sub_comm] using hk i false
    · simpa only [atom_measureEndpoint, if_true, abs_sub_comm] using hk i true
  have hb := atom_grid_cdf_bound P (A k) q δ hδ
    (atom_real_le_of_measure_le _ _ δ hδ hlo)
    (fun j => atom_real_le_of_measure_le _ _ δ hδ (hgap j))
    (atom_real_le_of_measure_le _ _ δ hδ hhi)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (atom_cdfDistance_bounds P (A k)).1]
  linarith

theorem atom_uniform_convergence (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (hleft : AtomLeftConvergence S H) (t : Bool) :
    Tendsto (fun q => cdfDistance (lawCDF H t) (empiricalCDF (rowOutcomes S t q)))
      atTop (𝓝 0) := by
  have hu := atom_endpoints_to_uniform (atom_marginalLaw H t)
    (fun q => atom_empiricalLaw
      (show 0 < (S.design q).N by have := (S.design q).population_min; omega)
      (rowOutcomes S t q))
    (by
      intro b x
      simpa only [atom_empirical_endpoint] using atom_endpoint_convergence S H θ ρ h hleft t b x)
  simpa only [atom_marginal_Iic, atom_empirical_Iic] using hu

/-- The finite grid/union/Chebyshev calculation for any injected sample block. -/
theorem atom_grid_sampling_bound (d : Design) {s n : ℕ} (hs : 0 < s)
    (e : Fin s → Fin d.N) (he : Function.Injective e) (y : Fin d.N → ℝ)
    (P : ProbabilityMeasure ℝ) (q : Fin (n + 1) → ℝ) (δ η : ℝ)
    (hδ : 0 ≤ δ) (hη : 0 < η) (hδη : δ ≤ η / 4)
    (hlo : (P : Measure ℝ).real (Iio (q 0)) ≤ δ)
    (hgap : ∀ j : Fin n,
      (P : Measure ℝ).real (Ioo (q j.castSucc) (q j.succ)) ≤ δ)
    (hhi : (P : Measure ℝ).real (Ioi (q (Fin.last n))) ≤ δ)
    (hpop : atom_gridDeviation P (atom_empiricalLaw
      (show 0 < d.N by have := d.population_min; omega) y) q < η / 4) :
    designProbability d (fun π => η ≤ cdfDistance
      (fun x => (P : Measure ℝ).real (Iic x))
      (empiricalCDF (fun j => y (π (e j))))) ≤
      (2 * (n + 1) : ℝ) * ((d.N : ℝ) - s) / (((d.N : ℝ) - 1) * s * η ^ 2) := by
  let hN : 0 < d.N := by have := d.population_min; omega
  let B := atom_empiricalLaw hN y
  let F : (Fin (n + 1) × Bool) → Assignment d → Prop := fun z π =>
    η / 2 ≤ |atom_endpoint (fun j => y (π (e j))) z.2 (q z.1) - atom_endpoint y z.2 (q z.1)|
  have hunion := atom_probability_union d
    (fun π => η ≤ cdfDistance (fun x => (P : Measure ℝ).real (Iic x))
      (empiricalCDF (fun j => y (π (e j))))) F (by
    intro π hπ
    by_contra hn
    have hall : ∀ i b,
        |atom_endpoint (fun j => y (π (e j))) b (q i) - atom_endpoint y b (q i)| < η / 2 := by
      intro i b
      exact lt_of_not_ge (fun hh => hn ⟨(i, b), hh⟩)
    let A := atom_empiricalLaw hs (fun j => y (π (e j)))
    have hsample : atom_gridDeviation B A q < η / 2 := by
      apply atom_gridDeviation_lt
      intro i
      constructor
      · simpa only [B, A, atom_empirical_Iic, atom_endpoint, Bool.false_eq_true, if_false,
          abs_sub_comm] using hall i false
      · simpa only [B, A, atom_empirical_Iio, atom_endpoint, if_true,
          abs_sub_comm] using hall i true
    have hbound := atom_grid_cdf_bound P A q δ hδ hlo hgap hhi
    have htri := atom_gridDeviation_triangle P A B q
    have hπ' : η ≤ cdfDistance (fun x => (P : Measure ℝ).real (Iic x))
        (fun x => (A : Measure ℝ).real (Iic x)) := by
      simpa only [A, atom_empirical_Iic] using hπ
    change atom_gridDeviation P B q < η / 4 at hpop
    linarith)
  calc
    _ ≤ ∑ z, designProbability d (F z) := hunion
    _ ≤ ∑ _z : Fin (n + 1) × Bool,
        ((d.N : ℝ) - s) / (((d.N : ℝ) - 1) * s * η ^ 2) := by
      apply Finset.sum_le_sum
      intro z _
      exact atom_endpoint_chebyshev d hs e he y z.2 (q z.1) η hη
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_add, Nat.cast_one]; ring

/-- Cardinality and mesh size for the explicit partition integer. -/
theorem atom_partition_mesh (η : ℝ) (hη : 0 < η) :
    let R := Nat.ceil (4 / min η 1)
    2 ≤ R ∧ (R - 2 + 2 = R) ∧
      (1 / ((R - 2 : ℕ) + 2 : ℝ) ≤ η / 4) ∧
      2 * (R - 2 + 1) ≤ correctedPartitionInteger η := by
  dsimp only
  let R := Nat.ceil (4 / min η 1)
  have hmin : 0 < min η 1 := lt_min hη (by norm_num)
  have hc : 4 / min η 1 ≤ (R : ℝ) := Nat.le_ceil _
  have h4 : (4 : ℝ) ≤ R := le_trans
    ((le_div_iff₀ hmin).mpr (by nlinarith [min_le_right η 1])) hc
  have h4n : 4 ≤ R := by exact_mod_cast h4
  have hsum : R - 2 + 2 = R := by omega
  refine ⟨by omega, hsum, ?_, ?_⟩
  · have hh : (4 : ℝ) ≤ R * min η 1 := (div_le_iff₀ hmin).mp hc
    have hhη : (4 : ℝ) ≤ R * η := hh.trans
      (mul_le_mul_of_nonneg_left (min_le_left η 1) (by positivity))
    have hdenEq : (((R - 2 : ℕ) : ℝ) + 2) = R := by exact_mod_cast hsum
    rw [hdenEq]
    have hden : (0 : ℝ) < R := by linarith
    apply (div_le_iff₀ hden).mpr
    nlinarith
  · unfold correctedPartitionInteger
    change 2 * (R - 2 + 1) ≤ 2 * R
    omega

theorem atom_population_size_atTop (S : ExperimentSequence) :
    Tendsto (fun q => ((S.design q).N : ℝ)) atTop atTop := by
  have hshift : Tendsto (fun q : ℕ => q + 4) atTop atTop :=
    (tendsto_add_atTop_iff_nat 4).2 tendsto_id
  simpa only [S.size, Function.comp_def] using
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp hshift

/-- The scaled finite-population correction has the exact allocation limit. -/
theorem atom_finite_correction_limit (S : ExperimentSequence) (s : ℕ → ℕ)
    (hs : ∀ q, 0 < s q) (p η K : ℝ) (hp : 0 < p) (hη : 0 < η)
    (hratio : Tendsto (fun q => (s q : ℝ) / (S.design q).N) atTop (𝓝 p)) :
    Tendsto (fun q => ((S.design q).N : ℝ) *
      (K * ((S.design q).N - s q) / (((S.design q).N - 1) * s q * η ^ 2))) atTop
      (𝓝 ((1 - p) * K / (p * η ^ 2))) := by
  have hinv : Tendsto (fun q => 1 / ((S.design q).N : ℝ)) atTop (𝓝 0) :=
    (atom_population_size_atTop S).const_div_atTop 1
  have hlim := (((tendsto_const_nhds (x := (1 : ℝ))).sub hratio).mul
    (tendsto_const_nhds (x := K))).div
    ((((tendsto_const_nhds (x := (1 : ℝ))).sub hinv).mul hratio).mul
      (tendsto_const_nhds (x := η ^ 2)))
    (show (1 - 0) * p * η ^ 2 ≠ 0 by positivity)
  have heq (q : ℕ) :
      ((S.design q).N : ℝ) *
        (K * ((S.design q).N - s q) / (((S.design q).N - 1) * s q * η ^ 2)) =
      (1 - (s q : ℝ) / (S.design q).N) * K /
        ((1 - 1 / ((S.design q).N : ℝ)) * ((s q : ℝ) / (S.design q).N) * η ^ 2) := by
    have hN : (0 : ℝ) < (S.design q).N := by
      exact_mod_cast (show 0 < (S.design q).N by have := (S.design q).population_min; omega)
    have hN1 : (0 : ℝ) < (S.design q).N - 1 := by
      have hh : (4 : ℝ) ≤ (S.design q).N := by exact_mod_cast (S.design q).population_min
      linarith
    have hsR : (0 : ℝ) < s q := by exact_mod_cast hs q
    field_simp [ne_of_gt hN, ne_of_gt hN1, ne_of_gt hsR, ne_of_gt hη]
    <;> ring
  apply (tendsto_congr heq).mpr
  simpa only [Pi.div_def, sub_zero, one_mul] using hlim

/-- Atom-safe tail bound for an arbitrary family of injected blocks. -/
theorem atom_injected_tail_bound (S : ExperimentSequence) (P : ProbabilityMeasure ℝ)
    (y : (q : ℕ) → Fin (S.design q).N → ℝ)
    (hconv : ∀ b x, Tendsto (fun q => atom_endpoint (y q) b x) atTop
      (𝓝 (atom_measureEndpoint P b x)))
    (s : ℕ → ℕ) (hs : ∀ q, 0 < s q)
    (e : (q : ℕ) → Fin (s q) → Fin (S.design q).N)
    (he : ∀ q, Function.Injective (e q)) (p : ℝ) (hp : 0 < p)
    (hratio : Tendsto (fun q => (s q : ℝ) / (S.design q).N) atTop (𝓝 p))
    (η : ℝ) (hη : 0 < η) :
    scaledProbabilityLimsup S (fun q π => η ≤
      cdfDistance (fun x => (P : Measure ℝ).real (Iic x))
        (empiricalCDF (fun j => y q (π (e q j))))) ≤
      ENNReal.ofReal ((1 - p) * correctedPartitionInteger η / (p * η ^ 2)) := by
  let R := Nat.ceil (4 / min η 1)
  let n := R - 2
  let δ : ℝ := 1 / (n + 2 : ℝ)
  have hmesh := atom_partition_mesh η hη
  have hδ : 0 ≤ δ := by positivity
  have hδη : δ ≤ η / 4 := hmesh.2.2.1
  obtain ⟨q, -, hlo, hgap, hhi⟩ := exists_halfLine_atomSafeGrid (P : Measure ℝ) n
  have hevent : ∀ᶠ k in atTop, ∀ i : Fin (n + 1), ∀ b : Bool,
      |atom_endpoint (y k) b (q i) - atom_measureEndpoint P b (q i)| < η / 4 := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro b
    have ht : Tendsto (fun k => |atom_endpoint (y k) b (q i) -
        atom_measureEndpoint P b (q i)|) atTop (𝓝 0) := by
      simpa only [sub_self, abs_zero] using ((hconv b (q i)).sub
        (tendsto_const_nhds (x := atom_measureEndpoint P b (q i)))).abs
    exact ht.eventually (eventually_lt_nhds (by positivity : 0 < η / 4))
  have hmajor : ∀ᶠ k in atTop,
      ENNReal.ofReal ((S.design k).N * designProbability (S.design k)
        (fun π => η ≤ cdfDistance (fun x => (P : Measure ℝ).real (Iic x))
          (empiricalCDF (fun j => y k (π (e k j)))))) ≤
      ENNReal.ofReal (((S.design k).N : ℝ) *
        ((correctedPartitionInteger η : ℝ) * ((S.design k).N - s k) /
          (((S.design k).N - 1) * s k * η ^ 2))) := by
    filter_upwards [hevent] with k hk
    have hpop : atom_gridDeviation P (atom_empiricalLaw
        (show 0 < (S.design k).N by have := (S.design k).population_min; omega) (y k)) q < η / 4 := by
      apply atom_gridDeviation_lt
      intro i
      constructor
      · simpa only [atom_empirical_Iic, atom_measureEndpoint, Bool.false_eq_true, if_false,
          atom_endpoint, abs_sub_comm] using hk i false
      · simpa only [atom_empirical_Iio, atom_measureEndpoint, if_true, atom_endpoint,
          abs_sub_comm] using hk i true
    have hfinite := atom_grid_sampling_bound (S.design k) (hs k) (e k) (he k) (y k) P q δ η
      hδ hη hδη (atom_real_le_of_measure_le _ _ δ hδ hlo)
      (fun j => atom_real_le_of_measure_le _ _ δ hδ (hgap j))
      (atom_real_le_of_measure_le _ _ δ hδ hhi) hpop
    have hcard : (2 * (n + 1) : ℝ) ≤ correctedPartitionInteger η := by
      exact_mod_cast hmesh.2.2.2
    have hsN : s k ≤ (S.design k).N := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (e k) (he k)
    have hdiff : (0 : ℝ) ≤ (S.design k).N - s k :=
      sub_nonneg.mpr (by exact_mod_cast hsN)
    have hNm1 : (0 : ℝ) ≤ (S.design k).N - 1 := by
      have hh : (4 : ℝ) ≤ (S.design k).N := by exact_mod_cast (S.design k).population_min
      linarith
    have hN : (0 : ℝ) ≤ (S.design k).N := by positivity
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left (hfinite.trans ?_) hN
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hdiff) (by positivity)
  unfold scaledProbabilityLimsup
  have hle := Filter.limsup_le_limsup hmajor
  have hlimit := ENNReal.tendsto_ofReal (atom_finite_correction_limit S s hs p η
    (correctedPartitionInteger η) hp hη hratio)
  exact hle.trans (le_of_eq hlimit.limsup_eq)

/-- Corrected Lemma 2 with an explicit partition and bounds for both sample CDFs. -/
theorem lemma2_corrected_explicit_final :
    (∀ (S : ExperimentSequence)
      (H : JointLaw)
      (θ ρ : ℝ)
      (h : Conditions123 S H θ ρ)
      (hleft : AtomLeftConvergence S H),
      (∀ η, 0 < η → 0 < correctedPartitionInteger η) ∧
    (∀ a b, 0 < a → a ≤ b → correctedPartitionInteger b ≤ correctedPartitionInteger a) ∧
    (∀ t, Tendsto (fun q => cdfDistance (lawCDF H t)
      (empiricalCDF (rowOutcomes S t q))) atTop (𝓝 0)) ∧
    (∀ η, 0 < η →
      scaledProbabilityLimsup S (fun q π => η ≤
        cdfDistance (lawCDF H true) (sampledCDF S true q π)) ≤
        ENNReal.ofReal ((1 - θ * ρ) * correctedPartitionInteger η / (θ * ρ * η ^ 2)) ∧
      scaledProbabilityLimsup S (fun q π => η ≤
        cdfDistance (lawCDF H false) (sampledCDF S false q π)) ≤
        ENNReal.ofReal ((1 - θ * (1 - ρ)) * correctedPartitionInteger η /
          (θ * (1 - ρ) * η ^ 2)))) := by
  intro S H θ ρ h hleft
  refine ⟨corrected_partition_integer_properties.1, corrected_partition_integer_properties.2,
    atom_uniform_convergence S H θ ρ h hleft, ?_⟩
  intro η hη
  let e1 : (q : ℕ) → Fin (S.design q).m → Fin (S.design q).N := fun q i =>
    ⟨i.val, by have := i.isLt; have := (S.design q).sample_le; omega⟩
  let e0 : (q : ℕ) → Fin (S.design q).k → Fin (S.design q).N := fun q i =>
    ⟨(S.design q).m + i.val, by have := i.isLt; have := (S.design q).sample_le; omega⟩
  have he1 : ∀ q, Function.Injective (e1 q) := by
    intro q i j hij
    have hv := congrArg Fin.val hij
    exact Fin.ext hv
  have he0 : ∀ q, Function.Injective (e0 q) := by
    intro q i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    dsimp only [e0] at hv
    omega
  have hm : ∀ q, 0 < (S.design q).m := by
    intro q; have := (S.design q).treatment_min; omega
  have hk : ∀ q, 0 < (S.design q).k := by
    intro q; have := (S.design q).control_min; omega
  have hkratio : Tendsto (fun q => ((S.design q).k : ℝ) / (S.design q).N)
      atTop (𝓝 (θ * (1 - ρ))) := by
    convert h.2.2.2.2.2.1.sub h.2.2.2.2.1 using 1
    · funext q; ring
    · ring
  constructor
  · have ht := atom_injected_tail_bound S (atom_marginalLaw H true)
      (fun q => rowOutcomes S true q)
      (atom_endpoint_convergence S H θ ρ h hleft true)
      (fun q => (S.design q).m) hm e1 he1 (θ * ρ) (mul_pos h.1 h.2.2.1)
      h.2.2.2.2.1 η hη
    convert ht using 1 <;>
      simp only [atom_marginal_Iic, sampledCDF, if_true, e1, observedTreatment] <;> rfl
  · have ht := atom_injected_tail_bound S (atom_marginalLaw H false)
      (fun q => rowOutcomes S false q)
      (atom_endpoint_convergence S H θ ρ h hleft false)
      (fun q => (S.design q).k) hk e0 he0 (θ * (1 - ρ))
      (mul_pos h.1 (sub_pos.mpr h.2.2.2.1)) hkratio η hη
    convert ht using 1 <;>
      simp only [atom_marginal_Iic, sampledCDF, Bool.false_eq_true, if_false, e0,
        observedControl] <;> rfl

end
end AronowAudit.P022.Wave1.TailA
