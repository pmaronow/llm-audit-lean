import SAP.P037a.WH.W2.Leaves
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Probability.Distributions.Exponential

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal Classical Topology

namespace SAP.P037a.WH.W2.P.T5_L4

noncomputable def expOnePDF (x : ℝ) : ℝ≥0∞ := ProbabilityTheory.exponentialPDF 1 x

noncomputable def productExpPDF (n : ℕ) (x : Fin n → ℝ) : ℝ≥0∞ :=
  ∏ i, expOnePDF (x i)

lemma measurable_expOnePDF : Measurable expOnePDF := by
  exact ENNReal.measurable_ofReal.comp (ProbabilityTheory.measurable_exponentialPDFReal 1)

lemma measurable_productExpPDF (n : ℕ) : Measurable (productExpPDF n) := by
  unfold productExpPDF
  exact Finset.measurable_prod _ (fun i _ => measurable_expOnePDF.comp (measurable_pi_apply i))

lemma expMeasure_one_withDensity : ProbabilityTheory.expMeasure 1 =
    volume.withDensity expOnePDF := by
  rfl

lemma map_withDensity_measurableEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : α ≃ᵐ β)
    (hmp : MeasurePreserving e μ ν) {f : α → ℝ≥0∞} (hf : Measurable f) :
    Measure.map e (μ.withDensity f) = ν.withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply f (hs.preimage e.measurable),
    withDensity_apply _ hs]
  calc
    ∫⁻ x in e ⁻¹' s, f x ∂μ =
        ∫⁻ x in e ⁻¹' s, (fun y => f (e.symm y)) (e x) ∂μ := by
          apply setLIntegral_congr_fun (hs.preimage e.measurable)
          intro x hx
          simp
    _ = ∫⁻ y in s, f (e.symm y) ∂ν :=
      hmp.setLIntegral_comp_preimage hs (hf.comp e.symm.measurable)

lemma pi_exp_density (n : ℕ) :
    Measure.pi (fun _ : Fin n => ProbabilityTheory.expMeasure 1) =
      (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).withDensity (productExpPDF n) := by
  induction n with
  | zero =>
      have hprod : productExpPDF 0 = fun _ => (1 : ℝ≥0∞) := by
        funext x
        simp [productExpPDF]
      rw [hprod]
      change Measure.pi (fun _ : Fin 0 => ProbabilityTheory.expMeasure 1) =
        (Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ))).withDensity
          (1 : (Fin 0 → ℝ) → ℝ≥0∞)
      rw [withDensity_one]
      let x0 : Fin 0 → ℝ := fun i => Fin.elim0 i
      exact (Measure.pi_of_empty _ x0).trans (Measure.pi_of_empty _ x0).symm
  | succ n ih =>
      letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
        ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
      let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      let ν : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => (volume : Measure ℝ))
      have hsrc : Measure.map e (Measure.pi (fun _ : Fin (n + 1) => ProbabilityTheory.expMeasure 1)) =
          (ProbabilityTheory.expMeasure 1).prod
            (Measure.pi (fun _ : Fin n => ProbabilityTheory.expMeasure 1)) := by
        simpa [e] using
          (measurePreserving_piFinSuccAbove
            (fun _ : Fin (n + 1) => ProbabilityTheory.expMeasure 1) 0).map_eq
      have hbase : MeasurePreserving e
          (Measure.pi (fun _ : Fin (n + 1) => (volume : Measure ℝ)))
          ((volume : Measure ℝ).prod ν) := by
        simpa [e, ν] using
          (measurePreserving_piFinSuccAbove
            (fun _ : Fin (n + 1) => (volume : Measure ℝ)) 0)
      have hmap := map_withDensity_measurableEquiv e hbase (measurable_productExpPDF (n + 1))
      have hfactor : (fun z : ℝ × (Fin n → ℝ) => productExpPDF (n + 1) (e.symm z)) =
          (fun z => expOnePDF z.1 * productExpPDF n z.2) := by
        funext z
        simp [productExpPDF, expOnePDF, e, Fin.prod_univ_succ]
      have hprod :
          (volume.withDensity expOnePDF).prod (ν.withDensity (productExpPDF n)) =
            ((volume : Measure ℝ).prod ν).withDensity
              (fun z => expOnePDF z.1 * productExpPDF n z.2) :=
        MeasureTheory.prod_withDensity (μ := (volume : Measure ℝ)) (ν := ν)
          measurable_expOnePDF (measurable_productExpPDF n)
      apply e.measurableEmbedding.map_injective
      calc
        Measure.map e (Measure.pi (fun _ : Fin (n + 1) => ProbabilityTheory.expMeasure 1)) =
            (ProbabilityTheory.expMeasure 1).prod
              (Measure.pi (fun _ : Fin n => ProbabilityTheory.expMeasure 1)) := hsrc
        _ = (volume.withDensity expOnePDF).prod (ν.withDensity (productExpPDF n)) := by
          calc
            (ProbabilityTheory.expMeasure 1).prod
                (Measure.pi (fun _ : Fin n => ProbabilityTheory.expMeasure 1)) =
                (volume.withDensity expOnePDF).prod
                  (Measure.pi (fun _ : Fin n => ProbabilityTheory.expMeasure 1)) :=
              congrArg (fun μ : Measure ℝ =>
                μ.prod (Measure.pi (fun _ : Fin n => ProbabilityTheory.expMeasure 1)))
                expMeasure_one_withDensity
            _ = (volume.withDensity expOnePDF).prod (ν.withDensity (productExpPDF n)) := by
              simpa [ν] using congrArg
                (fun μ : Measure (Fin n → ℝ) => (volume.withDensity expOnePDF).prod μ) ih
        _ = ((volume : Measure ℝ).prod ν).withDensity
              (fun z => expOnePDF z.1 * productExpPDF n z.2) := hprod
        _ = Measure.map e
              ((Measure.pi (fun _ : Fin (n + 1) => (volume : Measure ℝ))).withDensity
                (productExpPDF (n + 1))) := by
          rw [hmap]
          rw [hfactor]

lemma productExpPDF_eq_target_of_ne_zero {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, x i ≠ 0) : productExpPDF n x = exponentialDensityW2 n x := by
  classical
  by_cases hp : ∀ i, 0 < x i
  · have hexp : (∏ i : Fin n, ENNReal.ofReal (Real.exp (-x i))) =
        ENNReal.ofReal (Real.exp (-∑ i, x i)) := by
      rw [← ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
        (f := fun i : Fin n => Real.exp (-x i)) (by
          intro i hi
          positivity)]
      rw [← Real.exp_sum]
      congr 1
      simp
    have hpdf : productExpPDF n x =
        ∏ i : Fin n, ENNReal.ofReal (Real.exp (-x i)) := by
      unfold productExpPDF expOnePDF
      apply Finset.prod_congr rfl
      intro i hi
      rw [ProbabilityTheory.exponentialPDF_eq]
      simp [le_of_lt (hp i)]
    have htarget : exponentialDensityW2 n x =
        ENNReal.ofReal (Real.exp (-∑ i, x i)) := by
      simp [exponentialDensityW2, positiveOrthantW2, hp]
    rw [hpdf, hexp, htarget]
  · obtain ⟨i, hi⟩ := not_forall.mp hp
    have hneg : x i < 0 := by
      have hle : x i ≤ 0 := le_of_not_gt hi
      exact lt_of_le_of_ne hle (hx i)
    have hpdf : expOnePDF (x i) = 0 := by
      simp [expOnePDF, ProbabilityTheory.exponentialPDF_of_neg hneg]
    have hprod : productExpPDF n x = 0 := by
      unfold productExpPDF
      exact Finset.prod_eq_zero (Finset.mem_univ i) hpdf
    have hnot : x ∉ positiveOrthantW2 n := by
      intro h
      exact hp h
    rw [hprod, exponentialDensityW2]
    simp [hnot]

lemma productExpPDF_ae_eq_target (n : ℕ) :
    productExpPDF n =ᵐ[volume] exponentialDensityW2 n := by
  have hcoords : ∀ᵐ x : Fin n → ℝ ∂
      (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))), ∀ i, x i ≠ 0 := by
    apply ae_all_iff.mpr
    intro i
    rw [ae_iff]
    have hnull : Measure.pi (fun _ : Fin n => (volume : Measure ℝ))
        ((fun x : Fin n → ℝ => x i) ⁻¹' ({0} : Set ℝ)) = 0 :=
      Measure.pi_eval_preimage_null (μ := fun _ : Fin n => (volume : Measure ℝ))
        (i := i) (s := {0}) (by simp)
    have hset : {x : Fin n → ℝ | ¬ x i ≠ 0} =
        (fun x : Fin n → ℝ => x i) ⁻¹' ({0} : Set ℝ) := by
      ext x
      simp
    rw [hset]
    exact hnull
  filter_upwards [hcoords] with x hx
  exact productExpPDF_eq_target_of_ne_zero x hx

lemma expMeasure_one_ae_pos : ∀ᵐ x : ℝ ∂ProbabilityTheory.expMeasure 1, 0 < x := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  rw [ae_iff]
  simp only [not_lt]
  change ProbabilityTheory.expMeasure 1 (Set.Iic 0) = 0
  rw [← ProbabilityTheory.ofReal_cdf,
    ProbabilityTheory.cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 1)]
  norm_num

end SAP.P037a.WH.W2.P.T5_L4

theorem SAP.P037a.WH.W2.T5_L4_proof : SAP.P037a.WH.W2.T5_L4 := by
  intro m
  constructor
  · have hd := SAP.P037a.WH.W2.P.T5_L4.pi_exp_density (m + 1)
    change Measure.pi (fun _ : Fin (m + 1) => ProbabilityTheory.expMeasure 1) =
      volume.withDensity (exponentialDensityW2 (m + 1))
    rw [volume_pi]
    rw [hd]
    exact withDensity_congr_ae
      (SAP.P037a.WH.W2.P.T5_L4.productExpPDF_ae_eq_target (m + 1))
  · have hpos : ∀ᵐ x : ℝ ∂ProbabilityTheory.expMeasure 1, 0 < x :=
      SAP.P037a.WH.W2.P.T5_L4.expMeasure_one_ae_pos
    letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
      ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
    have hm (i : Fin (m + 1)) :
        Measure.map (fun x : Fin (m + 1) → ℝ => x i)
          (Measure.pi (fun _ : Fin (m + 1) => ProbabilityTheory.expMeasure 1)) =
            ProbabilityTheory.expMeasure 1 :=
      (measurePreserving_eval (fun _ : Fin (m + 1) => ProbabilityTheory.expMeasure 1) i).map_eq
    have hall : ∀ᵐ x : Fin (m + 1) → ℝ ∂
        Measure.pi (fun _ : Fin (m + 1) => ProbabilityTheory.expMeasure 1), ∀ i, 0 < x i := by
      apply ae_all_iff.mpr
      intro i
      apply ae_of_ae_map (measurable_pi_apply i).aemeasurable
      rw [hm i]
      exact hpos
    simpa [exponentialInputW2, positiveOrthantW2] using hall
