import SAP.P022.WH.W1.Leaves
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T17_L5

open MeasureTheory Filter Topology
open scoped BigOperators

private lemma empiricalMean_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : Integrable f P) :
    ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ℕ => P) : Measure (ℕ → Ω)),
      Tendsto (fun n => SAP.P022.finiteMean
        (fun i : Fin (n + 4) => f (ω i.val))) atTop (𝓝 (∫ x, f x ∂P)) := by
  classical
  let μinf : Measure (ℕ → Ω) := Measure.infinitePi (fun _ : ℕ => P)
  have hf_aesm : AEStronglyMeasurable f P := hf.aestronglyMeasurable
  let f' : Ω → ℝ := hf_aesm.mk f
  have hf'_meas : Measurable f' := hf_aesm.measurable_mk
  have hff' : f =ᵐ[P] f' := hf_aesm.ae_eq_mk
  have hf'_int : Integrable f' P := hf.congr hff'
  have hf_integral : ∫ x, f' x ∂P = ∫ x, f x ∂P :=
    integral_congr_ae hff'.symm
  let Y : ℕ → (ℕ → Ω) → ℝ := fun i ω => f' (ω i)
  have hY_meas : ∀ i, Measurable (Y i) := fun i =>
    hf'_meas.comp (measurable_pi_apply i)
  have hMP : ∀ i : ℕ,
      MeasurePreserving (Function.eval i : (ℕ → Ω) → Ω) μinf P := fun i =>
    measurePreserving_eval_infinitePi (μ := fun _ : ℕ => P) i
  have hY0_int : Integrable (Y 0) μinf := by
    have hcomp := (hMP 0).integrable_comp hf'_meas.aestronglyMeasurable
    simpa [Y, Function.eval, Function.comp_def] using hcomp.mpr hf'_int
  have h_iIndep : ProbabilityTheory.iIndepFun Y μinf := by
    simpa [Y, Function.eval] using
      (ProbabilityTheory.iIndepFun_infinitePi (Ω := fun _ : ℕ => Ω)
        (P := fun _ : ℕ => P) (X := fun _ : ℕ => f') (fun _ => hf'_meas))
  have h_pair : Pairwise
      (fun i j => ProbabilityTheory.IndepFun (Y i) (Y j) μinf) := by
    intro i j hij
    exact h_iIndep.indepFun hij
  have hY_map : ∀ i, Measure.map (Y i) μinf = Measure.map f' P := by
    intro i
    have hcomp : Y i = f' ∘ (Function.eval i : (ℕ → Ω) → Ω) := by
      funext ω
      rfl
    rw [hcomp, ← Measure.map_map hf'_meas (measurable_pi_apply i), (hMP i).map_eq]
  have h_ident : ∀ i,
      ProbabilityTheory.IdentDistrib (Y i) (Y 0) μinf μinf := fun i =>
    { aemeasurable_fst := (hY_meas i).aemeasurable
      aemeasurable_snd := (hY_meas 0).aemeasurable
      map_eq := by rw [hY_map i, hY_map 0] }
  have h_mean : ∫ ω, Y 0 ω ∂μinf = ∫ x, f x ∂P := by
    have h_int : ∫ x, f' x ∂P = ∫ ω, Y 0 ω ∂μinf := by
      have hP_eq : P = Measure.map (Function.eval 0 : (ℕ → Ω) → Ω) μinf :=
        (hMP 0).map_eq.symm
      calc
        ∫ x, f' x ∂P = ∫ x, f' x ∂Measure.map
            (Function.eval 0 : (ℕ → Ω) → Ω) μinf := by rw [← hP_eq]
        _ = ∫ ω, f' ((Function.eval 0 : (ℕ → Ω) → Ω) ω) ∂μinf := by
          exact integral_map (measurable_pi_apply 0).aemeasurable
            hf'_meas.aestronglyMeasurable
        _ = ∫ ω, Y 0 ω ∂μinf := by rfl
    rw [← h_int, hf_integral]
  have h_sll : ∀ᵐ ω ∂μinf,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, Y i ω) / (n : ℝ))
        atTop (𝓝 (∫ ω, Y 0 ω ∂μinf)) :=
    ProbabilityTheory.strong_law_ae_real Y hY0_int h_pair h_ident
  have h_eq_all : ∀ᵐ ω ∂μinf, ∀ i : ℕ, f (ω i) = f' (ω i) := by
    rw [ae_all_iff]
    intro i
    have hqmp : Measure.QuasiMeasurePreserving
        (fun ω : ℕ → Ω => ω i) μinf P := (hMP i).quasiMeasurePreserving
    exact hqmp.ae_eq_comp hff'
  have hshift : Tendsto (fun n : ℕ => n + 4) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n 4) tendsto_id
  filter_upwards [h_sll, h_eq_all] with ω hω heq
  have hseq : ∀ n : ℕ,
      SAP.P022.finiteMean (fun i : Fin (n + 4) => f (ω i.val)) =
        (∑ i ∈ Finset.range (n + 4), Y i ω) / ((n + 4 : ℕ) : ℝ) := by
    intro n
    calc
      SAP.P022.finiteMean (fun i : Fin (n + 4) => f (ω i.val)) =
          (∑ i : Fin (n + 4), f (ω i.val)) / ((n + 4 : ℕ) : ℝ) := by
            simp [SAP.P022.finiteMean, Finset.expect_eq_sum_div_card]
      _ = (∑ i ∈ Finset.range (n + 4), f (ω i)) / ((n + 4 : ℕ) : ℝ) := by
            congr 1
            rw [← Fin.sum_univ_eq_sum_range (fun i => f (ω i))]
      _ = (∑ i ∈ Finset.range (n + 4), Y i ω) / ((n + 4 : ℕ) : ℝ) := by
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            simpa [Y] using heq i
  have hωshift := hω.comp hshift
  rw [h_mean] at hωshift
  have hωshift' : Tendsto
      (fun n : ℕ => (∑ i ∈ Finset.range (n + 4), Y i ω) / ((n + 4 : ℕ) : ℝ))
      atTop (𝓝 (∫ x, f x ∂P)) := by
    simpa [Function.comp_def] using hωshift
  simpa only [hseq] using hωshift'

end SAP.P022.WH.W1.P.T17_L5

open MeasureTheory Filter Topology
open scoped BigOperators

theorem SAP.P022.WH.W1.T17_L5_proof : SAP.P022.WH.W1.T17_L5 := by
  classical
  intro J C hC hCmeas F hFint
  let P : Measure (ℝ × ℝ) := (J : Measure (ℝ × ℝ))
  let μinf : Measure (ℕ → ℝ × ℝ) := Measure.infinitePi (fun _ : ℕ => P)
  have hsets : ∀ᵐ ω ∂μinf, ∀ s : {s : Set (ℝ × ℝ) // s ∈ C},
      Tendsto (fun n => SAP.P022.finiteMean (fun i : Fin (n + 4) =>
        if ω i.val ∈ s.1 then (1 : ℝ) else 0)) atTop
        (𝓝 ((P s.1).toReal)) := by
    letI : Countable {s : Set (ℝ × ℝ) // s ∈ C} := hC.to_subtype
    rw [ae_all_iff]
    intro s
    let f : ℝ × ℝ → ℝ := s.1.indicator (fun _ => (1 : ℝ))
    have hf_sm : StronglyMeasurable f := by
      exact stronglyMeasurable_const.indicator (hCmeas s.1 s.2)
    have hf_meas : Measurable f := by
      exact hf_sm.measurable
    have hf_int : Integrable f P := by
      refine Integrable.of_bound hf_meas.aestronglyMeasurable 1 ?_
      filter_upwards [] with p
      by_cases hp : p ∈ s.1 <;> simp [f, Set.indicator, hp]
    have hf_integral : ∫ p, f p ∂P = (P s.1).toReal := by
      calc
        ∫ p, f p ∂P = (P.real s.1) := by
          change ∫ p, s.1.indicator (fun _ : ℝ × ℝ => (1 : ℝ)) p ∂P = P.real s.1
          exact integral_indicator_one (hCmeas s.1 s.2)
        _ = (P s.1).toReal := by simp [Measure.real_def]
    have h := SAP.P022.WH.W1.P.T17_L5.empiricalMean_tendsto P f hf_int
    filter_upwards [h] with ω hω
    rw [← hf_integral]
    simpa [f, Set.indicator] using hω
  have hobs : ∀ᵐ ω ∂μinf, ∀ t : Fin 2,
      Tendsto (fun n => SAP.P022.finiteMean
        (fun i : Fin (n + 4) => F t (ω i.val))) atTop
        (𝓝 (∫ p, F t p ∂P)) := by
    rw [ae_all_iff]
    intro t
    exact SAP.P022.WH.W1.P.T17_L5.empiricalMean_tendsto P (F t) (hFint t)
  have hall : ∀ᵐ ω ∂μinf,
      (∀ s ∈ C, Tendsto (fun n => SAP.P022.finiteMean (fun i : Fin (n + 4) =>
        if ω i.val ∈ s then (1 : ℝ) else 0)) atTop
          (𝓝 ((P s).toReal))) ∧
      (∀ t : Fin 2, Tendsto (fun n => SAP.P022.finiteMean
        (fun i : Fin (n + 4) => F t (ω i.val))) atTop
          (𝓝 (∫ p, F t p ∂P))) := by
    filter_upwards [hsets, hobs] with ω hsetω hobsω
    exact ⟨fun s hmem => hsetω ⟨s, hmem⟩, hobsω⟩
  obtain ⟨ω, hω⟩ := hall.exists
  exact ⟨ω, hω.1, hω.2⟩

