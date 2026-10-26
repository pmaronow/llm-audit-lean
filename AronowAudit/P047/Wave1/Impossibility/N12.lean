import AronowAudit.P047.Wave1.Impossibility.N14
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Group.Arithmetic

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

theorem measurable_observed_sample_for_transfer (n : ℕ) : Measurable (observedSample n) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_covariate.comp (measurable_pi_apply i.val)).prodMk
    (((measurable_pi_apply i.val).snd.fst).prodMk
      (measurable_observed.comp (measurable_pi_apply i.val)))

private theorem cellObservable_nonneg (family high : Bool) (k : Fin 3) :
    0 ≤ cellObservable family high k := by
  cases family <;> cases high <;> fin_cases k <;>
    norm_num [cellObservable, cellPropensity, cellMean]

private theorem sum_cellObservable (family high : Bool) :
    (∑ k : Fin 3, cellObservable family high k) = 1 := by
  cases family <;> cases high <;>
    norm_num [Fin.sum_univ_succ, cellObservable, cellPropensity, cellMean]

private theorem baseObs_nonneg (k : Fin 3) : 0 ≤ baseObs k := by
  fin_cases k <;> norm_num [baseObs]

private theorem sum_baseObs : (∑ k : Fin 3, baseObs k) = 1 := by
  norm_num [Fin.sum_univ_succ, baseObs]

/-- Conditional probability of an arbitrary observed event, retaining every real covariate. -/
private def recordKernel (n : ℕ) (q : ℝ → Fin 3 → ℝ)
    (E : Set (Fin n → ObservedUnit)) (w : Fin n → ℝ) : ℝ :=
  ∑ k : Fin n → Fin 3, (∏ i, q (w i) (k i)) *
    E.indicator (fun _ => (1 : ℝ)) (fun i => record (w i) (k i))

private theorem measurable_recordKernel (n : ℕ) (q : ℝ → Fin 3 → ℝ)
    (hq : ∀ k, Measurable fun w => q w k)
    (E : Set (Fin n → ObservedUnit)) (hE : MeasurableSet E) :
    Measurable (recordKernel n q E) := by
  classical
  apply Finset.measurable_fun_sum
  intro k _hk
  have hprod : Measurable fun w : Fin n → ℝ => ∏ i, q (w i) (k i) :=
    Finset.measurable_fun_prod Finset.univ
      (fun i _ => (hq (k i)).comp (measurable_pi_apply i))
  have hrec : Measurable fun w : Fin n → ℝ => fun i => record (w i) (k i) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_pi_apply i).prodMk (measurable_const.prodMk measurable_const)
  exact hprod.mul ((measurable_const.indicator hE).comp hrec)

private theorem recordKernel_bounds (n : ℕ) (q : ℝ → Fin 3 → ℝ)
    (hq : ∀ w k, 0 ≤ q w k) (hsum : ∀ w, (∑ k, q w k) = 1)
    (E : Set (Fin n → ObservedUnit)) (w : Fin n → ℝ) :
    0 ≤ recordKernel n q E w ∧ recordKernel n q E w ≤ 1 := by
  classical
  have hprod (k : Fin n → Fin 3) : 0 ≤ ∏ i, q (w i) (k i) :=
    Finset.prod_nonneg (fun i _ => hq (w i) (k i))
  have hI (k : Fin n → Fin 3) :
      0 ≤ E.indicator (fun _ => (1 : ℝ)) (fun i => record (w i) (k i)) ∧
      E.indicator (fun _ => (1 : ℝ)) (fun i => record (w i) (k i)) ≤ 1 := by
    by_cases hk : (fun i => record (w i) (k i)) ∈ E <;> simp [hk]
  have htotal : (∑ k : Fin n → Fin 3, ∏ i, q (w i) (k i)) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [hsum, Finset.prod_const_one]
  constructor
  · exact Finset.sum_nonneg (fun k _ => mul_nonneg (hprod k) (hI k).1)
  · calc
      recordKernel n q E w ≤ ∑ k : Fin n → Fin 3, ∏ i, q (w i) (k i) := by
        apply Finset.sum_le_sum
        intro k _
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hI k).2 (hprod k)
      _ = 1 := htotal

private theorem integrable_recordKernel (n : ℕ) (q : ℝ → Fin 3 → ℝ)
    (hqmeas : ∀ k, Measurable fun w => q w k)
    (hq : ∀ w k, 0 ≤ q w k) (hsum : ∀ w, (∑ k, q w k) = 1)
    (E : Set (Fin n → ObservedUnit)) (hE : MeasurableSet E) :
    Integrable (recordKernel n q E) (Measure.pi fun _ : Fin n => uniform01) := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_recordKernel n q hqmeas E hE).aestronglyMeasurable
  apply ae_of_all
  intro w
  simpa only [Real.norm_eq_abs, abs_of_nonneg (recordKernel_bounds n q hq hsum E w).1]
    using (recordKernel_bounds n q hq hsum E w).2

theorem n12_proof : N12 := by
  classical
  intro s6 s7 s8 s9 s10 s11 M family n E hE
  let μ : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => uniform01
  let p : ℝ := (1 / 2 : ℝ) ^ (M + 1)
  let q : (Fin (M + 1) → Bool) → ℝ → Fin 3 → ℝ :=
    fun σ w k => cellObservable family (σ (cellLabel M w)) k
  have hqmeas (σ : Fin (M + 1) → Bool) (k : Fin 3) :
      Measurable fun w => q σ w k :=
    (measurable_of_countable (fun j : Fin (M + 1) => cellObservable family (σ j) k)).comp
      (measurable_cellLabel M)
  have hqnonneg (σ : Fin (M + 1) → Bool) (w : ℝ) (k : Fin 3) : 0 ≤ q σ w k :=
    cellObservable_nonneg family (σ (cellLabel M w)) k
  have hqsum (σ : Fin (M + 1) → Bool) (w : ℝ) : (∑ k, q σ w k) = 1 :=
    sum_cellObservable family (σ (cellLabel M w))
  have hfamily (σ : Fin (M + 1) → Bool) :
      (sampleLaw (familyMeasure M family σ)).real {s | observedSample n s ∈ E} =
        ∫ w, recordKernel n (q σ) E w ∂μ := by
    change (sampleLaw (familyMeasure M family σ)).real (observedSample n ⁻¹' E) = _
    rw [← map_measureReal_apply (μ := sampleLaw (familyMeasure M family σ))
      (measurable_observed_sample_for_transfer n) hE, s6]
    apply s7 ((familyMeasure M family σ).map obsUnit) (q σ)
      (hqmeas σ) (hqnonneg σ) ?_ n E hE
    intro B hB
    have he (w : ℝ) : 0 ≤ cellProp M σ w ∧ cellProp M σ w ≤ 1 := by
      have hh := cell_overlap (σ (cellLabel M w))
      change 0 ≤ cellPropensity (σ (cellLabel M w)) ∧
        cellPropensity (σ (cellLabel M w)) ≤ 1
      constructor <;> linarith [hh.1, hh.2]
    have hm (w : ℝ) : 0 ≤ cellMeanFn M family σ w ∧ cellMeanFn M family σ w ≤ 1 :=
      cell_mean_bounds family (σ (cellLabel M w))
    exact s8 _ _ (measurable_cellProp M σ) (measurable_cellMeanFn M family σ) he hm B hB
  have hbase :
      (sampleLaw baselineLaw).real {s | observedSample n s ∈ E} =
        ∫ w, recordKernel n (fun _ k => baseObs k) E w ∂μ := by
    change (sampleLaw baselineLaw).real (observedSample n ⁻¹' E) = _
    rw [← map_measureReal_apply (μ := sampleLaw baselineLaw)
      (measurable_observed_sample_for_transfer n) hE, s6]
    exact s7 (baselineLaw.map obsUnit) (fun _ k => baseObs k)
      (fun _ => measurable_const) (fun _ k => baseObs_nonneg k) s9 n E hE
  let F : (Fin n → ℝ) → ℝ := fun w => ∑ σ : Fin (M + 1) → Bool,
    p * recordKernel n (q σ) E w
  let B : (Fin n → ℝ) → ℝ := recordKernel n (fun _ k => baseObs k) E
  have hKI (σ : Fin (M + 1) → Bool) : Integrable (recordKernel n (q σ) E) μ :=
    integrable_recordKernel n (q σ) (hqmeas σ) (hqnonneg σ) (hqsum σ) E hE
  have hFI : Integrable F μ :=
    integrable_finsetSum Finset.univ (fun σ _ => (hKI σ).const_mul p)
  have hBI : Integrable B μ :=
    integrable_recordKernel n (fun _ k => baseObs k) (fun _ => measurable_const)
      (fun _ k => baseObs_nonneg k) (fun _ => sum_baseObs) E hE
  have hFB (w : Fin n → ℝ) : 0 ≤ F w ∧ F w ≤ 1 := by
    have hp : 0 ≤ p := by positivity
    constructor
    · exact Finset.sum_nonneg (fun σ _ => mul_nonneg hp
        (recordKernel_bounds n (q σ) (hqnonneg σ) (hqsum σ) E w).1)
    · calc
        F w ≤ ∑ _σ : Fin (M + 1) → Bool, p * 1 := by
          apply Finset.sum_le_sum
          intro σ _
          exact mul_le_mul_of_nonneg_left
            (recordKernel_bounds n (q σ) (hqnonneg σ) (hqsum σ) E w).2 hp
        _ = 1 := prior_average_const (M + 1) 1
  have hBB (w : Fin n → ℝ) : 0 ≤ B w ∧ B w ≤ 1 :=
    recordKernel_bounds n (fun _ k => baseObs k) (fun _ k => baseObs_nonneg k)
      (fun _ => sum_baseObs) E w
  let G : Set (Fin n → ℝ) := {w | Function.Injective (fun i => cellLabel M (w i))}
  have hG : MeasurableSet G := by
    have hlabels : Measurable fun w : Fin n → ℝ => fun i => cellLabel M (w i) :=
      measurable_pi_iff.mpr (fun i => (measurable_cellLabel M).comp (measurable_pi_apply i))
    exact hlabels ((Set.toFinite {c : Fin n → Fin (M + 1) | Function.Injective c}).measurableSet)
  have hagree (w : Fin n → ℝ) (hw : w ∈ G) : F w = B w := by
    change (∑ σ : Fin (M + 1) → Bool, p *
      ∑ k : Fin n → Fin 3, (∏ i, cellObservable family (σ (cellLabel M (w i))) (k i)) *
        E.indicator (fun _ => (1 : ℝ)) (fun i => record (w i) (k i))) = _
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    have hfactor (k : Fin n → Fin 3) :
        (∑ σ : Fin (M + 1) → Bool, p *
          ∏ i, cellObservable family (σ (cellLabel M (w i))) (k i)) =
          ∏ i, baseObs (k i) := s10 M family n (fun i => cellLabel M (w i)) hw k
    change _ = ∑ k : Fin n → Fin 3, (∏ i, baseObs (k i)) *
      E.indicator (fun _ => (1 : ℝ)) (fun i => record (w i) (k i))
    apply Finset.sum_congr rfl
    intro k _
    rw [hfactor k]
  have hmix : (∑ σ : Fin (M + 1) → Bool, p *
      (sampleLaw (familyMeasure M family σ)).real {s | observedSample n s ∈ E}) =
      ∫ w, F w ∂μ := by
    simp_rw [hfamily]
    rw [show (∫ w, F w ∂μ) =
      ∑ σ : Fin (M + 1) → Bool, ∫ w, p * recordKernel n (q σ) E w ∂μ from
        integral_finsetSum Finset.univ (fun σ _ => (hKI σ).const_mul p)]
    simp_rw [integral_const_mul]
  have hnorm : |∫ w, F w - B w ∂μ| ≤ μ.real Gᶜ := by
    have hI : Integrable ((Gᶜ).indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const 1).indicator hG.compl
    have hbound : ∀ᵐ w ∂μ, ‖F w - B w‖ ≤ (Gᶜ).indicator (fun _ => (1 : ℝ)) w := by
      apply ae_of_all
      intro w
      by_cases hw : w ∈ G
      · rw [hagree w hw, sub_self, norm_zero, Set.indicator_of_notMem (by simpa using hw)]
      · rw [Set.indicator_of_mem (by simpa using hw), Real.norm_eq_abs, abs_le]
        constructor <;> linarith [(hFB w).1, (hFB w).2, (hBB w).1, (hBB w).2]
    have h := norm_integral_le_of_norm_le hI hbound
    rw [show (Gᶜ).indicator (fun _ => (1 : ℝ)) = (Gᶜ).indicator (1 : (Fin n → ℝ) → ℝ) from rfl,
      integral_indicator_one hG.compl] at h
    simpa only [Real.norm_eq_abs] using h
  calc
    |(∑ σ : Fin (M + 1) → Bool, (1 / 2 : ℝ) ^ (M + 1) *
        (sampleLaw (familyMeasure M family σ)).real {s | observedSample n s ∈ E}) -
      (sampleLaw baselineLaw).real {s | observedSample n s ∈ E}| =
        |∫ w, F w - B w ∂μ| := by
      rw [hmix, hbase, integral_sub hFI hBI]
    _ ≤ μ.real Gᶜ := hnorm
    _ ≤ (n : ℝ) * (n - 1) / (2 * (M + 1)) := s11 M n

end

end AronowAudit.P047.Wave1.Impossibility
