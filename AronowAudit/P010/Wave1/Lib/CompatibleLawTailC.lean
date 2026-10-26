import AronowAudit.P010.P010_Population
import AronowAudit.P010.Wave1.Lib.StatusCouplingTailC
import Mathlib.MeasureTheory.Measure.Sub

namespace AronowAudit.P010.Wave1

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

set_option maxHeartbeats 800000

/-- Complete observable equality preserves every outcome submeasure selected
by a measurable event in the observed status and assignment. -/
theorem tcLift_observed_slice {K d : ℕ} (μ ν : Measure (State K d))
    (he : ν.map (fun ω => (observedY ω, observedS ω, assignment ω)) =
      μ.map (fun ω => (observedY ω, observedS ω, assignment ω)))
    (E : Set (Bool × Fin K)) (hE : MeasurableSet E) :
    (ν.restrict {ω | (observedS ω, assignment ω) ∈ E}).map observedY =
      (μ.restrict {ω | (observedS ω, assignment ω) ∈ E}).map observedY := by
  ext B hB
  have hh := congrArg (fun η : Measure (ℝ × Bool × Fin K) => η (B ×ˢ E)) he
  rw [Measure.map_apply (by fun_prop) (hB.prod hE),
    Measure.map_apply (by fun_prop) (hB.prod hE)] at hh
  have hs : (fun ω : State K d => (observedY ω, observedS ω, assignment ω)) ⁻¹'
      (B ×ˢ E) = observedY ⁻¹' B ∩ {ω | (observedS ω, assignment ω) ∈ E} := by
    ext ω
    rfl
  rw [hs] at hh
  simpa only [Measure.map_apply measurable_observedY hB,
    Measure.restrict_apply (measurable_observedY hB)] using hh

/-- Both passer and failer outcome submeasures are fixed by compatibility. -/
theorem compatible_status_submeasures {K d : ℕ} (μ ν : Measure (State K d))
    (hc : Compatible μ ν) (a : Fin K) (b : Bool) :
    (ν.restrict ({ω | observedS ω = b} ∩ armEvent a)).map observedY =
      (μ.restrict ({ω | observedS ω = b} ∩ armEvent a)).map observedY := by
  have he := tcLift_observed_slice μ ν hc.2.2 ({b} ×ˢ {a})
    ((measurableSet_singleton b).prod (measurableSet_singleton a))
  change (ν.restrict ({ω | observedS ω = b} ∩ armEvent a)).map observedY =
    (μ.restrict ({ω | observedS ω = b} ∩ armEvent a)).map observedY at he
  exact he

/-- Assignment probabilities are fixed by complete observable equality. -/
theorem compatible_arm_mass {K d : ℕ} (μ ν : Measure (State K d))
    (hc : Compatible μ ν) (a : Fin K) : ν (armEvent a) = μ (armEvent a) := by
  have hh := congrArg (fun η : Measure (ℝ × Bool × Fin K) =>
    η (univ ×ˢ (univ ×ˢ {a}))) hc.2.2
  rw [Measure.map_apply (by fun_prop)
      (MeasurableSet.univ.prod (MeasurableSet.univ.prod (measurableSet_singleton a))),
    Measure.map_apply (by fun_prop)
      (MeasurableSet.univ.prod (MeasurableSet.univ.prod (measurableSet_singleton a)))] at hh
  simpa only [preimage, mem_prod, mem_univ, mem_singleton_iff, true_and, armEvent] using hh

/-- In particular the masses of both status slices are fixed, even when a
slice has mass zero. -/
theorem compatible_status_mass {K d : ℕ} (μ ν : Measure (State K d))
    (hc : Compatible μ ν) (a : Fin K) (b : Bool) :
    ν ({ω | observedS ω = b} ∩ armEvent a) =
      μ ({ω | observedS ω = b} ∩ armEvent a) := by
  have he := congrArg (fun η : Measure ℝ => η univ)
    (compatible_status_submeasures μ ν hc a b)
  simpa only [Measure.map_apply measurable_observedY MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ] using he

/-- The exact observable passing rate and normalized passer law are invariant. -/
theorem compatible_passer_invariants {K d : ℕ} (μ ν : Measure (State K d))
    (h : Assumptions μ) (hc : Compatible μ ν) (a : Fin K) :
    passingRate ν a = passingRate μ a ∧ passerLaw ν a = passerLaw μ a := by
  have hm : ν (passEvent ∩ armEvent a) = μ (passEvent ∩ armEvent a) :=
    compatible_status_mass μ ν hc a true
  constructor
  · simp only [passingRate, hm, compatible_arm_mass μ ν hc a]
  · unfold passerLaw eventLaw
    have he := compatible_status_submeasures μ ν hc a true
    change (ν.restrict (passEvent ∩ armEvent a)).map observedY =
      (μ.restrict (passEvent ∩ armEvent a)).map observedY at he
    rw [hm, he]

/-- Integrability of the observed focal passer outcomes is preserved. -/
theorem compatible_observed_integrable {K d : ℕ} (μ ν : Measure (State K d))
    (hc : Compatible μ ν) (a : Fin K)
    (hi : Integrable observedY (μ.restrict (passEvent ∩ armEvent a))) :
    Integrable observedY (ν.restrict (passEvent ∩ armEvent a)) := by
  have he := compatible_status_submeasures μ ν hc a true
  change (ν.restrict (passEvent ∩ armEvent a)).map observedY =
    (μ.restrict (passEvent ∩ armEvent a)).map observedY at he
  have hy : Measurable (observedY (K := K) (d := d)) := measurable_observedY
  have hm : Integrable (id : ℝ → ℝ)
      ((μ.restrict (passEvent ∩ armEvent a)).map observedY) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hy.aemeasurable).mpr hi
  rw [← he] at hm
  exact (integrable_map_measure measurable_id.aestronglyMeasurable hy.aemeasurable).mp hm

/-- Focal passer integrability transfers from the observed law to each
compatible potential law, and hence to its always-passer restriction. -/
theorem compatible_focal_integrable {K d : ℕ} (μ ν : Measure (State K d))
    (h : Assumptions μ) (hc : Compatible μ ν) (a : Fin K)
    (hi : Integrable observedY (μ.restrict (passEvent ∩ armEvent a))) :
    Integrable (potentialY a) (ν.restrict (potentialPass a)) ∧
      Integrable (potentialY a) (ν.restrict alwaysPass) := by
  letI tcLift_integrable_original_probability := h.1
  letI tcLift_integrable_compatible_probability := hc.1.1
  have hm := passing_event_positive μ h a
  have hp := (nonzero_passing_corrected ν hc.1.1 hc.1.2.1).2.mp hc.1.2.2 a
  have hiF : Integrable (id : ℝ → ℝ) (passerLaw μ a) := by
    unfold passerLaw eventLaw
    apply (integrable_smul_measure (by simp [measure_ne_top])
      (by simpa using ne_of_gt hm)).mpr
    exact (integrable_map_measure measurable_id.aestronglyMeasurable
      measurable_observedY.aemeasurable).mpr hi
  rw [← (compatible_passer_invariants μ ν h hc a).2,
    ← conditional_law_consistency ν hc.1 a] at hiF
  unfold eventLaw at hiF
  have hiP : Integrable (potentialY a) (ν.restrict (potentialPass a)) := by
    have hiM := (integrable_smul_measure
      (by simp [measure_ne_top]) (by simpa using ne_of_gt hp)).mp hiF
    exact (integrable_map_measure measurable_id.aestronglyMeasurable
      (measurable_potentialY a).aemeasurable).mp hiM
  have hsub : (alwaysPass : Set (State K d)) ⊆ potentialPass a := fun ω hω => hω a
  exact ⟨hiP, hiP.mono_measure (Measure.restrict_mono hsub le_rfl)⟩

/-- A single status stratum, with independent coordinate outcomes and an
independent assignment drawn from the specified original assignment law. -/
noncomputable def tcLift_stratum {K d : ℕ} (s : Fin K → Bool)
    (M : Fin K → Measure ℝ) (Z : Measure (Fin K)) : Measure (State K d) :=
  ((Measure.pi M).prod Z).map (fun yz => (yz.1, s, yz.2, fun _ => 0))

local instance tcLift_stratum_probability {K d : ℕ} (s : Fin K → Bool)
    (M : Fin K → Measure ℝ) (Z : Measure (Fin K))
    [∀ a, IsProbabilityMeasure (M a)] [IsProbabilityMeasure Z] :
    IsProbabilityMeasure (tcLift_stratum (d := d) s M Z) := by
  unfold tcLift_stratum
  infer_instance

/-- Each stratum has the required per-arm pair/assignment product law. -/
theorem tcLift_stratum_joint {K d : ℕ} (s : Fin K → Bool)
    (M : Fin K → Measure ℝ) (Z : Measure (Fin K))
    [∀ a, IsProbabilityMeasure (M a)] [IsProbabilityMeasure Z] (a : Fin K) :
    (tcLift_stratum (d := d) s M Z).map
      (fun ω => ((potentialY a ω, potentialS a ω), assignment ω)) =
      ((M a).map (fun y => (y, s a))).prod Z := by
  unfold tcLift_stratum
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  change (((Measure.pi M).prod Z).map
    (Prod.map (fun y => (y a, s a)) id)) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id, Measure.map_id]
  have he : (Measure.pi M).map (fun y => (y a, s a)) =
      (M a).map (fun y => (y, s a)) := by
    change (Measure.pi M).map ((fun y : ℝ => (y, s a)) ∘ Function.eval a) = _
    rw [← Measure.map_map (show Measurable (fun y : ℝ => (y, s a)) by fun_prop)
      (measurable_pi_apply a),
      (measurePreserving_eval M a).map_eq]
  rw [he]

/-- The coordinate outcome marginal in a stratum. -/
theorem tcLift_stratum_outcome {K d : ℕ} (s : Fin K → Bool)
    (M : Fin K → Measure ℝ) (Z : Measure (Fin K))
    [∀ a, IsProbabilityMeasure (M a)] [IsProbabilityMeasure Z] (a : Fin K) :
    (tcLift_stratum (d := d) s M Z).map (potentialY a) = M a := by
  unfold tcLift_stratum
  rw [Measure.map_map (measurable_potentialY a) (by fun_prop)]
  change ((Measure.pi M).prod Z).map (Function.eval a ∘ Prod.fst) = _
  rw [← Measure.map_map (measurable_pi_apply a) measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul, (measurePreserving_eval M a).map_eq]

/-- Restriction to always-passers selects exactly the all-true stratum. -/
theorem tcLift_stratum_always {K d : ℕ} (s : Fin K → Bool)
    (M : Fin K → Measure ℝ) (Z : Measure (Fin K)) :
    (tcLift_stratum (d := d) s M Z).restrict alwaysPass =
      if s = (fun _ => true) then tcLift_stratum s M Z else 0 := by
  classical
  unfold tcLift_stratum
  rw [Measure.restrict_map (by fun_prop) measurableSet_always]
  have he : (fun yz : (Fin K → ℝ) × Fin K =>
      (yz.1, s, yz.2, fun _ : Fin d => (0 : ℝ))) ⁻¹' alwaysPass =
      if s = (fun _ => true) then univ else ∅ := by
    by_cases hs : s = (fun _ => true)
    · simp [hs, alwaysPass, potentialS]
    · ext yz
      simp [hs, alwaysPass, potentialS, ← funext_iff]
  rw [he]
  split_ifs <;> simp

/-- The finite mixture keeps the whole Boolean status index type. -/
noncomputable def tcLift_mixture {K d : ℕ} (w : (Fin K → Bool) → ℝ)
    (M : (Fin K → Bool) → Fin K → Measure ℝ) (Z : Measure (Fin K)) :
    Measure (State K d) :=
  Measure.sum fun s => ENNReal.ofReal (w s) • tcLift_stratum s (M s) Z

theorem tcLift_mixture_probability {K d : ℕ} (w : (Fin K → Bool) → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hs : ∑ s, w s = 1)
    (M : (Fin K → Bool) → Fin K → Measure ℝ) (Z : Measure (Fin K))
    [∀ s a, IsProbabilityMeasure (M s a)] [IsProbabilityMeasure Z] :
    IsProbabilityMeasure (tcLift_mixture (d := d) w M Z) := by
  classical
  constructor
  simp only [tcLift_mixture, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, smul_eq_mul, measure_univ, mul_one, tsum_fintype]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => hw s), hs, ENNReal.ofReal_one]

theorem tcLift_mixture_joint {K d : ℕ} (w : (Fin K → Bool) → ℝ)
    (M : (Fin K → Bool) → Fin K → Measure ℝ) (Z : Measure (Fin K))
    [∀ s a, IsProbabilityMeasure (M s a)] [IsProbabilityMeasure Z] (a : Fin K) :
    (tcLift_mixture (d := d) w M Z).map
      (fun ω => ((potentialY a ω, potentialS a ω), assignment ω)) =
      (Measure.sum fun s => ENNReal.ofReal (w s) •
        (M s a).map (fun y => (y, s a))).prod Z := by
  have hm : Measurable (fun ω : State K d =>
      ((potentialY a ω, potentialS a ω), assignment ω)) := by fun_prop
  unfold tcLift_mixture
  rw [Measure.map_sum hm.aemeasurable]
  simp_rw [Measure.map_smul _ hm.aemeasurable, tcLift_stratum_joint,
    ← Measure.prod_smul_left]
  rw [Measure.prod_sum_left]

theorem tcLift_mixture_always {K d : ℕ} (w : (Fin K → Bool) → ℝ)
    (M : (Fin K → Bool) → Fin K → Measure ℝ) (Z : Measure (Fin K))
    [∀ s a, IsProbabilityMeasure (M s a)] [IsProbabilityMeasure Z] (a : Fin K) :
    ((tcLift_mixture (d := d) w M Z).restrict alwaysPass).map (potentialY a) =
      ENNReal.ofReal (w (fun _ => true)) • M (fun _ => true) a := by
  classical
  unfold tcLift_mixture
  rw [Measure.restrict_sum_of_countable, Measure.map_sum (by fun_prop)]
  simp_rw [Measure.restrict_smul, tcLift_stratum_always]
  have he (s : Fin K → Bool) :
      (ENNReal.ofReal (w s) •
        (if s = (fun _ => true) then tcLift_stratum (d := d) s (M s) Z else 0)).map
          (potentialY a) =
      if s = (fun _ => true) then ENNReal.ofReal (w s) • M s a else 0 := by
    split_ifs <;> simp [Measure.map_smul _ (measurable_potentialY a).aemeasurable,
      tcLift_stratum_outcome]
  simp_rw [he]
  rw [Measure.sum_fintype]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Normalize a finite outcome submeasure. A null branch receives a harmless
Dirac law; multiplying back by its zero mass recovers the null submeasure. -/
noncomputable def tcLift_normalize (D : Measure ℝ) : Measure ℝ :=
  if D univ = 0 then Measure.dirac 0 else (D univ)⁻¹ • D

local instance tcLift_normalize_probability (D : Measure ℝ) [IsFiniteMeasure D] :
    IsProbabilityMeasure (tcLift_normalize D) := by
  classical
  unfold tcLift_normalize
  split_ifs with hz
  · infer_instance
  · constructor
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hz (measure_ne_top D univ)

theorem tcLift_normalize_cancel (D : Measure ℝ) [IsFiniteMeasure D] :
    D univ • tcLift_normalize D = D := by
  classical
  unfold tcLift_normalize
  by_cases hz : D univ = 0
  · have he : D = 0 := Measure.measure_univ_eq_zero.mp hz
    simp [he]
  · simp only [hz, ite_false, smul_smul,
      ENNReal.mul_inv_cancel hz (measure_ne_top D univ), one_smul]

/-- Potential outcome submeasure on one Boolean status slice. -/
noncomputable def tcLift_statusOutcome {K d : ℕ} (μ : Measure (State K d))
    (a : Fin K) (b : Bool) : Measure ℝ :=
  (μ.restrict {ω | potentialS a ω = b}).map (potentialY a)

local instance tcLift_statusOutcome_finite {K d : ℕ} (μ : Measure (State K d))
    [IsFiniteMeasure μ] (a : Fin K) (b : Bool) :
    IsFiniteMeasure (tcLift_statusOutcome μ a b) := by
  unfold tcLift_statusOutcome
  infer_instance

theorem tcLift_statusOutcome_mass {K d : ℕ} (μ : Measure (State K d))
    (a : Fin K) (b : Bool) :
    tcLift_statusOutcome μ a b univ = μ {ω | potentialS a ω = b} := by
  simp only [tcLift_statusOutcome, Measure.map_apply (measurable_potentialY a)
    MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ]

theorem tcLift_passing_submeasure {K d : ℕ} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K) :
    tcLift_statusOutcome μ a true =
      ENNReal.ofReal (passingRate μ a) • passerLaw μ a := by
  letI tcLift_passing_original_probability := h.1
  have hp := (nonzero_passing_corrected μ h.1 h.2.1).2.mp h.2.2 a
  have hr := (nonzero_passing_corrected μ h.1 h.2.1).1 a
  rw [hr, ENNReal.ofReal_toReal (measure_ne_top μ _),
    ← conditional_law_consistency μ h a]
  unfold eventLaw tcLift_statusOutcome
  rw [smul_smul, ENNReal.mul_inv_cancel (ne_of_gt hp) (measure_ne_top μ _), one_smul]
  rfl

/-- The original full pair marginal splits into its passing and failing
outcome submeasures, with neither branch discarded. -/
theorem tcLift_pair_split {K d : ℕ} (μ : Measure (State K d)) (a : Fin K) :
    μ.map (fun ω => (potentialY a ω, potentialS a ω)) =
      (tcLift_statusOutcome μ a true).map (fun y => (y, true)) +
      (tcLift_statusOutcome μ a false).map (fun y => (y, false)) := by
  have hcomp : ({ω : State K d | potentialS a ω = true})ᶜ =
      {ω | potentialS a ω = false} := by
    ext ω
    cases hs : potentialS a ω <;> simp [hs]
  have he : μ = μ.restrict {ω | potentialS a ω = true} +
      μ.restrict {ω | potentialS a ω = false} := by
    rw [← hcomp]
    exact (Measure.restrict_add_restrict_compl (measurableSet_potentialPass a)).symm
  conv_lhs => rw [he]
  rw [Measure.map_add _ _ (by fun_prop)]
  congr 1 <;> unfold tcLift_statusOutcome <;>
    rw [Measure.map_map (by fun_prop) (measurable_potentialY a)] <;>
    apply Measure.map_congr
  · filter_upwards [self_mem_ae_restrict (measurableSet_potentialPass a)] with ω hω
    simp only [Function.comp_apply]
    exact congrArg (fun b => (potentialY a ω, b)) hω
  · filter_upwards [self_mem_ae_restrict ((measurable_potentialS a)
      (measurableSet_singleton false))] with ω hω
    simp only [Function.comp_apply]
    exact congrArg (fun b => (potentialY a ω, b)) hω

/-- Boolean mixtures reduce to three tagged outcome laws: all-passers,
other passers and failers. -/
theorem tcLift_tagged_partition {K : ℕ} (w : (Fin K → Bool) → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hs : ∑ s, w s = 1)
    (p : Fin K → ℝ) (α : ℝ)
    (hm : ∀ a, (∑ s, if s a = true then w s else 0) = p a)
    (hu : w (fun _ => true) = α) (a : Fin K) (A B C : Measure ℝ) :
    (Measure.sum fun s => ENNReal.ofReal (w s) •
      (if s = (fun _ => true) then A else if s a = true then B else C).map
        (fun y => (y, s a))) =
      ENNReal.ofReal α • A.map (fun y => (y, true)) +
      ENNReal.ofReal (p a - α) • B.map (fun y => (y, true)) +
      ENNReal.ofReal (1 - p a) • C.map (fun y => (y, false)) := by
  classical
  let u : Fin K → Bool := fun _ => true
  change w u = α at hu
  have h2 : (∑ s, if s = u then 0 else if s a = true then w s else 0) = p a - α := by
    have he : (∑ s, if s a = true then w s else 0) =
        (∑ s, if s = u then w s else 0) +
          ∑ s, if s = u then 0 else if s a = true then w s else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      by_cases hsu : s = u
      · simp [hsu, u]
      · simp [hsu]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at he
    rw [hm a, hu] at he
    linarith
  have h3 : (∑ s, if s a = true then 0 else w s) = 1 - p a := by
    have he : (∑ s, w s) = (∑ s, if s a = true then w s else 0) +
        ∑ s, if s a = true then 0 else w s := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      split_ifs <;> simp
    rw [hs, hm a] at he
    linarith
  have he (s : Fin K → Bool) : ENNReal.ofReal (w s) •
      (if s = u then A else if s a = true then B else C).map (fun y => (y, s a)) =
      (if s = u then ENNReal.ofReal (w s) else 0) • A.map (fun y => (y, true)) +
      (if s = u then 0 else if s a = true then ENNReal.ofReal (w s) else 0) •
        B.map (fun y => (y, true)) +
      (if s a = true then 0 else ENNReal.ofReal (w s)) • C.map (fun y => (y, false)) := by
    by_cases hsu : s = u
    · simp [hsu, u]
    · cases ha : s a <;> simp [hsu, ha]
  change (Measure.sum fun s => ENNReal.ofReal (w s) •
    (if s = u then A else if s a = true then B else C).map (fun y => (y, s a))) = _
  simp_rw [he]
  rw [Measure.sum_fintype, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_smul, ← Finset.sum_smul, ← Finset.sum_smul]
  have he2 : (∑ s, if s = u then 0 else if s a = true then ENNReal.ofReal (w s) else 0) =
      ENNReal.ofReal (p a - α) := by
    rw [← h2, ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro s _
      split_ifs <;> simp
    · intro s _
      split_ifs <;> simp [hw s]
  have he3 : (∑ s, if s a = true then 0 else ENNReal.ofReal (w s)) =
      ENNReal.ofReal (1 - p a) := by
    rw [← h3, ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro s _
      split_ifs <;> simp
    · intro s _
      split_ifs <;> simp [hw s]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, he2, he3, hu]


theorem tcLift_statusOutcome_false_mass {K d : ℕ} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K) :
    tcLift_statusOutcome μ a false univ = ENNReal.ofReal (1 - passingRate μ a) := by
  letI tcLift_failure_original_probability := h.1
  rw [tcLift_statusOutcome_mass]
  have he : {ω : State K d | potentialS a ω = false} = (potentialPass a)ᶜ := by
    ext ω
    cases hs : potentialS a ω <;> simp [hs, potentialPass]
  rw [he, measure_compl (measurableSet_potentialPass a) (measure_ne_top μ _),
    measure_univ, (nonzero_passing_corrected μ h.1 h.2.1).1 a,
    ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one,
    ENNReal.ofReal_toReal (measure_ne_top μ _)]

/-- Partition a population law by every assignment, with no positivity
assumption on the individual arms. -/
theorem tcLift_arm_partition {K d : ℕ} (μ : Measure (State K d)) :
    μ = Measure.sum (fun a : Fin K => μ.restrict (armEvent a)) := by
  have hu : (⋃ a : Fin K, armEvent (d := d) a) = univ := by
    ext ω
    simp [armEvent]
  have hd : Pairwise (fun a b : Fin K => Disjoint (armEvent (d := d) a) (armEvent b)) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro ω ha hb
    exact hab (ha.symm.trans hb)
  simpa only [hu, Measure.restrict_univ] using
    (Measure.restrict_iUnion hd (fun a => measurableSet_arm (d := d) a) (μ := μ))

theorem tcLift_observable_arm {K d : ℕ} (μ : Measure (State K d)) (a : Fin K) :
    (μ.restrict (armEvent a)).map
      (fun ω => (observedY ω, observedS ω, assignment ω)) =
    ((μ.map (fun ω => ((potentialY a ω, potentialS a ω), assignment ω))).restrict
      (Prod.snd ⁻¹' {a})).map (fun p => (p.1.1, p.1.2, p.2)) := by
  have hm : Measurable (fun ω : State K d =>
    ((potentialY a ω, potentialS a ω), assignment ω)) := by fun_prop
  rw [Measure.restrict_map hm (measurable_snd (measurableSet_singleton a)),
    Measure.map_map (by fun_prop) hm]
  change (μ.restrict (armEvent a)).map _ = (μ.restrict (armEvent a)).map _
  apply Measure.map_congr
  filter_upwards [self_mem_ae_restrict (measurableSet_arm a)] with ω hω
  change assignment ω = a at hω
  simp [Function.comp_def, observedY, observedS, hω]

/-- Equality of all per-arm pair/assignment laws determines the complete
observed triple law, by consistency on each assignment event. -/
theorem tcLift_observed_of_joints {K d : ℕ} (μ ν : Measure (State K d))
    (hj : ∀ a : Fin K,
      ν.map (fun ω => ((potentialY a ω, potentialS a ω), assignment ω)) =
      μ.map (fun ω => ((potentialY a ω, potentialS a ω), assignment ω))) :
    ν.map (fun ω => (observedY ω, observedS ω, assignment ω)) =
      μ.map (fun ω => (observedY ω, observedS ω, assignment ω)) := by
  have hm : Measurable (fun ω : State K d =>
    (observedY ω, observedS ω, assignment ω)) := by fun_prop
  calc
    _ = Measure.sum (fun a : Fin K => (ν.restrict (armEvent a)).map
        (fun ω => (observedY ω, observedS ω, assignment ω))) := by
      conv_lhs => rw [tcLift_arm_partition ν]
      rw [Measure.map_sum hm.aemeasurable]
    _ = Measure.sum (fun a : Fin K => (μ.restrict (armEvent a)).map
        (fun ω => (observedY ω, observedS ω, assignment ω))) := by
      congr 1
      funext a
      rw [tcLift_observable_arm, tcLift_observable_arm, hj a]
    _ = _ := by
      conv_rhs => rw [tcLift_arm_partition μ]
      rw [Measure.map_sum hm.aemeasurable]

/-- A finite product-outcome lift is compatible whenever its complete
per-arm pair marginals agree with the original ones. -/
theorem tcLift_mixture_compatible {K d : ℕ} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K) (w : (Fin K → Bool) → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hs : ∑ s, w s = 1) (hu : 0 < w (fun _ => true))
    (M : (Fin K → Bool) → Fin K → Measure ℝ)
    [∀ s b, IsProbabilityMeasure (M s b)]
    (hmarg : ∀ b : Fin K, (Measure.sum fun s => ENNReal.ofReal (w s) •
      (M s b).map (fun y => (y, s b))) =
        μ.map (fun ω => (potentialY b ω, potentialS b ω))) :
    Compatible μ (tcLift_mixture w M (μ.map assignment)) := by
  letI tcLift_original_probability := h.1
  let ν := tcLift_mixture (d := d) w M (μ.map assignment)
  letI tcLift_new_probability : IsProbabilityMeasure ν := tcLift_mixture_probability w hw hs M _
  have hj (b : Fin K) :
      ν.map (fun ω => ((potentialY b ω, potentialS b ω), assignment ω)) =
      (μ.map (fun ω => (potentialY b ω, potentialS b ω))).prod (μ.map assignment) := by
    rw [tcLift_mixture_joint, hmarg]
  have hp (b : Fin K) : ν.map (fun ω => (potentialY b ω, potentialS b ω)) =
      μ.map (fun ω => (potentialY b ω, potentialS b ω)) := by
    have he := congrArg (Measure.map Prod.fst) (hj b)
    rw [Measure.map_map measurable_fst (by fun_prop), Measure.map_fst_prod,
      measure_univ, one_smul] at he
    exact he
  have hz : ν.map assignment = μ.map assignment := by
    have he := congrArg (Measure.map Prod.snd) (hj a)
    rw [Measure.map_map measurable_snd (by fun_prop), Measure.map_snd_prod,
      measure_univ, one_smul] at he
    exact he
  have hI : Ignorability ν := by
    constructor
    · intro b
      apply (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).mpr
      rw [hj, hp, hz]
    · intro b
      have he := congrArg (fun η : Measure (Fin K) => η {b}) hz
      rw [Measure.map_apply measurable_assignment (measurableSet_singleton b),
        Measure.map_apply measurable_assignment (measurableSet_singleton b)] at he
      change ν (armEvent b) = μ (armEvent b) at he
      rw [he]
      exact h.2.1.2 b
  have hP : NonzeroPassing ν := by
    apply (nonzero_passing_corrected ν inferInstance hI).2.mpr
    intro b
    have he := congrArg (fun η : Measure (ℝ × Bool) => η (univ ×ˢ {true})) (hp b)
    rw [Measure.map_apply (by fun_prop)
      (MeasurableSet.univ.prod (measurableSet_singleton true)),
      Measure.map_apply (by fun_prop)
      (MeasurableSet.univ.prod (measurableSet_singleton true))] at he
    have he' : ν (potentialPass b) = μ (potentialPass b) := by
      simpa only [preimage, mem_prod, mem_univ, mem_singleton_iff, true_and, potentialPass] using he
    rw [he']
    exact (nonzero_passing_corrected μ h.1 h.2.1).2.mp h.2.2 b
  have hA : ν alwaysPass = ENNReal.ofReal (w (fun _ => true)) := by
    have he := congrArg (fun η : Measure ℝ => η univ)
      (tcLift_mixture_always (d := d) w M (μ.map assignment) a)
    simpa only [Measure.map_apply (measurable_potentialY a) MeasurableSet.univ,
      preimage_univ, Measure.restrict_apply_univ, Measure.smul_apply,
      smul_eq_mul, measure_univ, mul_one] using he
  refine ⟨⟨inferInstance, hI, hP⟩, ?_, ?_⟩
  · rw [hA]
    exact ENNReal.ofReal_pos.mpr hu
  · apply tcLift_observed_of_joints
    intro b
    rw [hj]
    exact ((indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).mp
      (h.2.1.1 b)).symm

/-- Realize any dominated focal always-passer law at any feasible positive
all-pass mass, while preserving the entire observed `(Y,S,Z)` law. -/
theorem compatible_localized_law {K d : ℕ} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hαp : ∀ b, α ≤ passingRate μ b)
    (hL : 1 - ∑ b, (1 - passingRate μ b) ≤ α)
    (G : Measure ℝ) [IsProbabilityMeasure G]
    (hdom : ENNReal.ofReal α • G ≤ ENNReal.ofReal (passingRate μ a) • passerLaw μ a) :
    ∃ ν : Measure (State K d), Compatible μ ν ∧
      ν alwaysPass = ENNReal.ofReal α ∧ eventLaw ν (potentialY a) alwaysPass = G := by
  classical
  letI tcLift_main_probability := h.1
  let p := passingRate μ
  have hp (b : Fin K) : 0 ≤ p b ∧ p b ≤ 1 := by
    change 0 ≤ passingRate μ b ∧ passingRate μ b ≤ 1
    rw [(nonzero_passing_corrected μ h.1 h.2.1).1 b]
    exact ⟨ENNReal.toReal_nonneg, measureReal_le_one⟩
  obtain ⟨w, hw, hs, hm, hu⟩ := bernoulli_status_coupling K p α hp hα0.le hα1 hαp hL
  let A := fun b : Fin K => tcLift_statusOutcome μ b true
  let C := fun b : Fin K => tcLift_statusOutcome μ b false
  have hAmass (b : Fin K) : A b univ = ENNReal.ofReal (p b) := by
    rw [tcLift_statusOutcome_mass]
    change μ (potentialPass b) = ENNReal.ofReal (passingRate μ b)
    rw [(nonzero_passing_corrected μ h.1 h.2.1).1 b,
      ENNReal.ofReal_toReal (measure_ne_top μ _)]
  have hCmass (b : Fin K) : C b univ = ENNReal.ofReal (1 - p b) :=
    tcLift_statusOutcome_false_mass μ h b
  let F := fun b : Fin K => tcLift_normalize (A b)
  let J := fun b : Fin K => tcLift_normalize (C b)
  have hFc (b : Fin K) : ENNReal.ofReal (p b) • F b = A b := by
    rw [← hAmass]
    exact tcLift_normalize_cancel (A b)
  have hJc (b : Fin K) : ENNReal.ofReal (1 - p b) • J b = C b := by
    rw [← hCmass]
    exact tcLift_normalize_cancel (C b)
  have hd : ENNReal.ofReal α • G ≤ A a := by
    change ENNReal.ofReal α • G ≤ tcLift_statusOutcome μ a true
    rw [tcLift_passing_submeasure μ h a]
    exact hdom
  letI tcLift_selected_finite : IsFiniteMeasure (ENNReal.ofReal α • G) :=
    isFiniteMeasure_of_le (A a) hd
  let D := A a - ENNReal.ofReal α • G
  letI tcLift_residual_finite : IsFiniteMeasure D :=
    isFiniteMeasure_of_le (A a) Measure.sub_le
  let H := tcLift_normalize D
  have hDmass : D univ = ENNReal.ofReal (p a - α) := by
    rw [Measure.sub_apply MeasurableSet.univ hd, hAmass,
      Measure.smul_apply, smul_eq_mul, measure_univ, mul_one,
      ENNReal.ofReal_sub _ hα0.le]
  have hHc : ENNReal.ofReal (p a - α) • H = D := by
    rw [← hDmass]
    exact tcLift_normalize_cancel D
  have hres : ENNReal.ofReal α • G + ENNReal.ofReal (p a - α) • H = A a := by
    rw [hHc, add_comm]
    exact Measure.sub_add_cancel_of_le hd
  let T := fun b : Fin K => if b = a then G else F b
  let R := fun b : Fin K => if b = a then H else F b
  let M := fun (s : Fin K → Bool) (b : Fin K) =>
    if s = (fun _ => true) then T b else if s b = true then R b else J b
  letI tcLift_kernel_probability : ∀ s b, IsProbabilityMeasure (M s b) := by
    intro s b
    dsimp [M, T, R]
    split_ifs <;> infer_instance
  have htrue (b : Fin K) : ENNReal.ofReal α • T b +
      ENNReal.ofReal (p b - α) • R b = A b := by
    by_cases hb : b = a
    · simpa [T, R, hb] using hres
    · simp only [T, R, hb, ite_false, ← add_smul]
      have he : ENNReal.ofReal α + ENNReal.ofReal (p b - α) = ENNReal.ofReal (p b) := by
        rw [← ENNReal.ofReal_add hα0.le (sub_nonneg.mpr (hαp b))]
        congr 1
        ring
      rw [he, hFc]
  have hpair (b : Fin K) : (Measure.sum fun s => ENNReal.ofReal (w s) •
      (M s b).map (fun y => (y, s b))) =
        μ.map (fun ω => (potentialY b ω, potentialS b ω)) := by
    change (Measure.sum fun s => ENNReal.ofReal (w s) •
      (if s = (fun _ => true) then T b else if s b = true then R b else J b).map
        (fun y => (y, s b))) = _
    rw [tcLift_tagged_partition w hw hs p α hm hu b]
    have ht := congrArg (Measure.map (fun y : ℝ => (y, true))) (htrue b)
    rw [Measure.map_add _ _ (by fun_prop),
      Measure.map_smul _ (by fun_prop), Measure.map_smul _ (by fun_prop)] at ht
    rw [ht, ← Measure.map_smul _ (show Measurable (fun y : ℝ => (y, false)) by fun_prop).aemeasurable,
      hJc]
    exact (tcLift_pair_split μ b).symm
  let ν : Measure (State K d) := tcLift_mixture w M (μ.map assignment)
  have hc : Compatible μ ν := tcLift_mixture_compatible μ h a w hw hs (by rw [hu]; exact hα0) M hpair
  have hsub : (ν.restrict alwaysPass).map (potentialY a) = ENNReal.ofReal α • G := by
    rw [tcLift_mixture_always]
    simp only [hu, M, T, ite_true]
  have hA : ν alwaysPass = ENNReal.ofReal α := by
    have he := congrArg (fun η : Measure ℝ => η univ) hsub
    simpa only [Measure.map_apply (measurable_potentialY a) MeasurableSet.univ,
      preimage_univ, Measure.restrict_apply_univ, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one] using he
  refine ⟨ν, hc, hA, ?_⟩
  unfold eventLaw
  rw [hA, hsub, smul_smul, ENNReal.inv_mul_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr hα0)) ENNReal.ofReal_ne_top, one_smul]

end AronowAudit.P010.Wave1
