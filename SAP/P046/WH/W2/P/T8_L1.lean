import SAP.P046.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046.WH.W2.P.T8_L1

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators

abbrev Label := Bool × (Bool × Bool)

def relabel {n : ℕ} (a : Sample n) (labels : Fin n → Label) : Sample n :=
  fun i => (W (a i), labels i)

def labelsOf {n : ℕ} (a : Sample n) : Fin n → Label := fun i => (a i).2

def envelope {n : ℕ} (F : CrossFit n) (a : Sample n) : ℝ :=
  ∑ labels : Fin n → Label, ∑ i : Fin n, |wholePrediction F i (relabel a labels)|

def cutoff {n : ℕ} (F : CrossFit n) (k : ℕ) (a : Sample n) : ℝ :=
  if envelope F a ≤ (k : ℝ) then 1 else 0

theorem measurable_relabel {n : ℕ} (labels : Fin n → Label) :
    Measurable (fun a : Sample n => relabel a labels) := by
  classical
  apply measurable_pi_lambda
  intro i
  change Measurable (fun a : Sample n => ((a i).1, labels i))
  fun_prop

theorem measurable_prediction_relabel {n : ℕ} (F : CrossFit n) (i : Fin n)
    (labels : Fin n → Label) :
    Measurable (fun a : Sample n => wholePrediction F i (relabel a labels)) := by
  change Measurable (fun a : Sample n =>
    F.g (F.fold i) (relabel a labels) (W (a i)))
  exact (F.measurable_g (F.fold i)).comp
    ((measurable_relabel labels).prodMk
      (measurable_fst.comp (measurable_pi_apply i)))

theorem measurable_envelope {n : ℕ} (F : CrossFit n) :
    Measurable (envelope F) := by
  classical
  unfold envelope
  apply Finset.measurable_sum
  intro labels hlabels
  apply Finset.measurable_sum
  intro i hi
  exact (measurable_prediction_relabel F i labels).abs

theorem relabel_actual {n : ℕ} (a : Sample n) : relabel a (labelsOf a) = a := by
  funext i
  rfl

theorem abs_prediction_le_envelope {n : ℕ} (F : CrossFit n) (a : Sample n) (i : Fin n) :
    |wholePrediction F i a| ≤ envelope F a := by
  classical
  have hinner :
      |wholePrediction F i (relabel a (labelsOf a))| ≤
        ∑ j : Fin n, |wholePrediction F j (relabel a (labelsOf a))| :=
    Finset.single_le_sum (f := fun j : Fin n =>
      |wholePrediction F j (relabel a (labelsOf a))|)
      (fun j hj => abs_nonneg _) (Finset.mem_univ i)
  rw [relabel_actual a] at hinner
  have houter :
      (∑ j : Fin n, |wholePrediction F j (relabel a (labelsOf a))|) ≤
        ∑ labels : Fin n → Label,
          ∑ j : Fin n, |wholePrediction F j (relabel a labels)| :=
    Finset.single_le_sum (f := fun labels : Fin n → Label =>
      ∑ j : Fin n, |wholePrediction F j (relabel a labels)|)
      (fun labels hlabels => Finset.sum_nonneg fun j hj => abs_nonneg _)
      (Finset.mem_univ (labelsOf a))
  change |wholePrediction F i a| ≤ _
  simpa [envelope] using le_trans hinner houter

theorem envelope_nonneg {n : ℕ} (F : CrossFit n) (a : Sample n) : 0 ≤ envelope F a := by
  classical
  unfold envelope
  exact Finset.sum_nonneg fun labels hlabels =>
    Finset.sum_nonneg fun i hi => abs_nonneg _

theorem envelope_eq_of_covariates_eq {n : ℕ} (F : CrossFit n) (a b : Sample n)
    (h : covariates a = covariates b) : envelope F a = envelope F b := by
  classical
  have hab : ∀ i, W (a i) = W (b i) := fun i => congrFun h i
  have hrel (labels : Fin n → Label) : relabel a labels = relabel b labels := by
    funext i
    exact congrArg (fun w : ℝ => (w, labels i)) (hab i)
  unfold envelope
  apply Finset.sum_congr rfl
  intro labels hlabels
  apply Finset.sum_congr rfl
  intro i hi
  rw [hrel]

theorem measurable_cutoff {n : ℕ} (F : CrossFit n) (k : ℕ) :
    Measurable (cutoff F k) := by
  unfold cutoff
  exact Measurable.ite
    (measurableSet_le (measurable_envelope F) measurable_const)
    measurable_const measurable_const

theorem cutoff_range {n : ℕ} (F : CrossFit n) (k : ℕ) (a : Sample n) :
    0 ≤ cutoff F k a ∧ cutoff F k a ≤ 1 := by
  by_cases h : envelope F a ≤ (k : ℝ) <;> simp [cutoff, h]

theorem cutoff_covariates_eq {n : ℕ} (F : CrossFit n) (k : ℕ) (a b : Sample n)
    (h : covariates a = covariates b) : cutoff F k a = cutoff F k b := by
  rw [cutoff, cutoff, envelope_eq_of_covariates_eq F a b h]

theorem cutoff_tendsto {n : ℕ} (F : CrossFit n) (a : Sample n) :
    Tendsto (fun k => cutoff F k a) atTop (nhds 1) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (envelope F a)
  apply Filter.Tendsto.congr' ?_
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
  filter_upwards [Filter.eventually_atTop.2 ⟨N, fun k hk => hk⟩] with k hk
  have hcast : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hle : envelope F a ≤ (k : ℝ) := hN.le.trans hcast
  simp [cutoff, hle]

theorem measurable_prediction {n : ℕ} (F : CrossFit n) (i : Fin n) :
    Measurable (wholePrediction F i) := by
  change Measurable (fun a : Sample n => F.g (F.fold i) a (W (a i)))
  exact (F.measurable_g (F.fold i)).comp
    (measurable_id.prodMk (measurable_fst.comp (measurable_pi_apply i)))

theorem localized_bound {n : ℕ} (F : CrossFit n) (k : ℕ) (i : Fin n)
    (a : Sample n) :
    ‖cutoff F k a * wholePrediction F i a‖ ≤ (k : ℝ) := by
  rw [Real.norm_eq_abs]
  by_cases h : envelope F a ≤ (k : ℝ)
  · simp [cutoff, h]
    exact le_trans (abs_prediction_le_envelope F a i) h
  · simp [cutoff, h]

theorem integrable_localized {M : Study} (hM : ValidStudy M) {n : ℕ}
    (F : CrossFit n) (k : ℕ) (i : Fin n) :
    Integrable (fun a : Sample n => cutoff F k a * wholePrediction F i a)
      (sampleLaw M n) := by
  letI := hM.probability
  have hm : Measurable (fun a : Sample n => cutoff F k a * wholePrediction F i a) :=
    (measurable_cutoff F k).mul (measurable_prediction F i)
  exact Integrable.of_bound hm.aestronglyMeasurable (k : ℝ)
    (Filter.Eventually.of_forall (localized_bound F k i))

end

end SAP.P046.WH.W2.P.T8_L1

open SAP.P046.WH.W2.P.T8_L1

theorem SAP.P046.WH.W2.T8_L1_proof : SAP.P046.WH.W2.T8_L1 := by
  intro M hM n F
  classical
  refine ⟨cutoff F, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact measurable_cutoff F k
  · intro k a
    exact cutoff_range F k a
  · intro k a b h
    exact cutoff_covariates_eq F k a b h
  · intro a
    exact cutoff_tendsto F a
  · intro k i
    exact integrable_localized hM F k i
