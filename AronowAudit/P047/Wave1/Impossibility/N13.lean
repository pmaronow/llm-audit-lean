import AronowAudit.P047.Wave1.Impossibility.N12
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

theorem measurable_sample_seed {R : Type u} [MeasurableSpace R] (n : ℕ) :
    Measurable (fun z : (ℕ → UnitData) × R => (observedSample n z.1, z.2)) :=
  ((measurable_observed_sample_for_transfer n).comp measurable_fst).prodMk measurable_snd

/-- Fubini for real event probabilities, together with the integrability needed for
finite averaging. No countability or standard-Borel assumption is imposed on the seed. -/
theorem real_prod_event_sections {X R : Type*} [MeasurableSpace X] [MeasurableSpace R]
    (P : Measure X) [IsProbabilityMeasure P] (Q : Measure R) [IsProbabilityMeasure Q]
    (E : Set (X × R)) (hE : MeasurableSet E) :
    (P.prod Q).real E = ∫ r, P.real {x | (x, r) ∈ E} ∂Q ∧
      Integrable (fun r => P.real {x | (x, r) ∈ E}) Q := by
  classical
  have hI : Integrable (E.indicator (1 : X × R → ℝ)) (P.prod Q) :=
    (integrable_const 1).indicator hE
  have hsection (r : R) : (∫ x, E.indicator (fun _ => (1 : ℝ)) (x, r) ∂P) =
      P.real {x | (x, r) ∈ E} := by
    have hs : MeasurableSet {x | (x, r) ∈ E} :=
      hE.preimage (measurable_id.prodMk measurable_const)
    change (∫ x, ({x | (x, r) ∈ E}).indicator (fun _ => (1 : ℝ)) x ∂P) = _
    exact integral_indicator_one hs
  constructor
  · rw [← integral_indicator_one hE, integral_prod_symm _ hI]
    exact integral_congr_ae (ae_of_all Q hsection)
  · exact hI.integral_prod_right.congr (ae_of_all Q hsection)

theorem n13_proof : N13.{u} := by
  classical
  intro s12 R _ Q _ M family n E hE
  let p : ℝ := (1 / 2 : ℝ) ^ (M + 1)
  let A : (Fin (M + 1) → Bool) → R → ℝ := fun σ r =>
    (sampleLaw (familyMeasure M family σ)).real {s | (observedSample n s, r) ∈ E}
  let B : R → ℝ := fun r =>
    (sampleLaw baselineLaw).real {s | (observedSample n s, r) ∈ E}
  have hpre : MeasurableSet {z : (ℕ → UnitData) × R |
      (observedSample n z.1, z.2) ∈ E} := hE.preimage (measurable_sample_seed n)
  have hprod (σ : Fin (M + 1) → Bool) :
      ((sampleLaw (familyMeasure M family σ)).prod Q).real
        {z | (observedSample n z.1, z.2) ∈ E} = ∫ r, A σ r ∂Q ∧
      Integrable (A σ) Q :=
    real_prod_event_sections (sampleLaw (familyMeasure M family σ)) Q _ hpre
  have hbase : ((sampleLaw baselineLaw).prod Q).real
        {z | (observedSample n z.1, z.2) ∈ E} = ∫ r, B r ∂Q ∧ Integrable B Q :=
    real_prod_event_sections (sampleLaw baselineLaw) Q _ hpre
  have hprod_eq (σ : Fin (M + 1) → Bool) :
      ((sampleLaw (familyMeasure M family σ)).prod Q).real
        {z | (observedSample n z.1, z.2) ∈ E} = ∫ r, A σ r ∂Q := (hprod σ).1
  let F : R → ℝ := fun r => ∑ σ : Fin (M + 1) → Bool, p * A σ r
  have hFI : Integrable F Q :=
    integrable_finsetSum Finset.univ (fun σ _ => (hprod σ).2.const_mul p)
  have hmix : (∑ σ : Fin (M + 1) → Bool, p *
      ((sampleLaw (familyMeasure M family σ)).prod Q).real
        {z | (observedSample n z.1, z.2) ∈ E}) = ∫ r, F r ∂Q := by
    simp_rw [hprod_eq]
    rw [show (∫ r, F r ∂Q) =
      ∑ σ : Fin (M + 1) → Bool, ∫ r, p * A σ r ∂Q from
        integral_finsetSum Finset.univ (fun σ _ => (hprod σ).2.const_mul p)]
    simp_rw [integral_const_mul]
  have hbound (r : R) : |F r - B r| ≤ (n : ℝ) * (n - 1) / (2 * (M + 1)) := by
    have hs : MeasurableSet {o : Fin n → ObservedUnit | (o, r) ∈ E} :=
      hE.preimage (measurable_id.prodMk measurable_const)
    exact s12 M family n {o | (o, r) ∈ E} hs
  have hnorm : |∫ r, F r - B r ∂Q| ≤ (n : ℝ) * (n - 1) / (2 * (M + 1)) := by
    have hn := norm_integral_le_of_norm_le
      (μ := Q) (f := fun r => F r - B r)
      (integrable_const ((n : ℝ) * (n - 1) / (2 * (M + 1))))
      (ae_of_all Q (fun r => by simpa only [Real.norm_eq_abs] using hbound r))
    simpa only [Real.norm_eq_abs, integral_const, measureReal_def, measure_univ,
      ENNReal.toReal_one, one_smul] using hn
  calc
    |(∑ σ : Fin (M + 1) → Bool, (1 / 2 : ℝ) ^ (M + 1) *
        ((sampleLaw (familyMeasure M family σ)).prod Q).real
          {z | (observedSample n z.1, z.2) ∈ E}) -
      ((sampleLaw baselineLaw).prod Q).real {z | (observedSample n z.1, z.2) ∈ E}| =
        |∫ r, F r - B r ∂Q| := by
      rw [hmix, hbase.1, integral_sub hFI hbase.2]
    _ ≤ (n : ℝ) * (n - 1) / (2 * (M + 1)) := hnorm

end

end AronowAudit.P047.Wave1.Impossibility
