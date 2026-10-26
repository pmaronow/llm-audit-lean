import AronowAudit.P010.P010_Population
import AronowAudit.P053.P053_NormalQuantiles
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
P010-T10 and P010-T13: simulation width comparison and normal counterexample.

The simulation certificate includes zero Gaussian variance and zero stratum weights.
Its width comparison uses concavity of trimmed spread under mixing, with strictness
proved for the particular Gaussian mixtures being compared. The normal counterexample
uses the actual EReal quantile and exact Gaussian truncated first moments.
-/

namespace AronowAudit.P010.Wave1

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Classical Topology

noncomputable section

lemma t10_fair_probability : IsProbabilityMeasure fairAssignment := by
  constructor
  norm_num [fairAssignment, Measure.add_apply, Measure.smul_apply, ENNReal.inv_two_add_inv_two]

local instance instT10FairProbability : IsProbabilityMeasure fairAssignment :=
  t10_fair_probability

lemma t10_fair_singleton (a : Fin 2) : fairAssignment {a} = 1/2 := by
  fin_cases a <;> norm_num [fairAssignment, Measure.add_apply, Measure.smul_apply]

noncomputable def t10_block (s r : Bool) (F : Measure ℝ) : Measure (State 2 0) :=
  (F.prod fairAssignment).map (fun ω => (![ω.1,ω.1], ![s,r], ω.2, fun _ => 0))

lemma t10_block_measurable (s r : Bool) :
    Measurable (fun ω : ℝ × Fin 2 =>
      ((![ω.1,ω.1], ![s,r], ω.2, fun _ => 0) : State 2 0)) := by fun_prop

local instance instT10BlockProbability (s r : Bool) (F : Measure ℝ) [IsProbabilityMeasure F] :
    IsProbabilityMeasure (t10_block s r F) := by unfold t10_block; infer_instance

lemma t10_block_rect (s r : Bool) (F : Measure ℝ) [IsProbabilityMeasure F]
    (a : Fin 2) (U : Set (ℝ × Bool)) (V : Set (Fin 2))
    (hU : MeasurableSet U) (hV : MeasurableSet V) :
    t10_block s r F ((fun ω => (potentialY a ω, potentialS a ω)) ⁻¹' U ∩ assignment ⁻¹' V) =
      F ((fun x => (x, ![s,r] a)) ⁻¹' U) * fairAssignment V := by
  rw [t10_block, Measure.map_apply (t10_block_measurable s r)
    (((measurable_potentialY a).prodMk (measurable_potentialS a) hU).inter
      (measurable_assignment hV))]
  have he : (fun ω : ℝ × Fin 2 =>
      ((![ω.1,ω.1], ![s,r], ω.2, fun _ => 0) : State 2 0)) ⁻¹'
        ((fun ω => (potentialY a ω, potentialS a ω)) ⁻¹' U ∩ assignment ⁻¹' V) =
      ((fun x => (x, ![s,r] a)) ⁻¹' U) ×ˢ V := by
    ext ω
    fin_cases a <;> simp [potentialY, potentialS, assignment]
  rw [he, Measure.prod_prod]

lemma t10_block_pair (s r : Bool) (F : Measure ℝ) [IsProbabilityMeasure F]
    (a : Fin 2) (U : Set (ℝ × Bool)) (hU : MeasurableSet U) :
    t10_block s r F ((fun ω => (potentialY a ω, potentialS a ω)) ⁻¹' U) =
      F ((fun x => (x, ![s,r] a)) ⁻¹' U) := by
  simpa using t10_block_rect s r F a U univ hU MeasurableSet.univ

noncomputable def t10_law (p q a lam : ℝ) (v : NNReal) : Measure (State 2 0) :=
  ENNReal.ofReal (1-p-q+a) • t10_block false false (gaussianReal 0 v) +
  ENNReal.ofReal (p-a) • t10_block true false (gaussianReal (-lam) v) +
  ENNReal.ofReal (q-a) • t10_block false true (gaussianReal lam v) +
  ENNReal.ofReal a • t10_block true true (gaussianReal 0 v)

lemma t10_law_weights (p q a : ℝ) (h0 : 0 ≤ 1-p-q+a)
    (h1 : a ≤ p) (h2 : a ≤ q) (ha : 0 ≤ a) :
    ENNReal.ofReal (1-p-q+a) + ENNReal.ofReal (p-a) + ENNReal.ofReal (q-a) + ENNReal.ofReal a = 1 := by
  rw [← ENNReal.ofReal_add h0 (sub_nonneg.mpr h1),
    ← ENNReal.ofReal_add (by linarith) (sub_nonneg.mpr h2),
    ← ENNReal.ofReal_add (by linarith) ha]
  convert ENNReal.ofReal_one using 1
  congr 1
  ring

lemma t10_law_probability (p q a lam : ℝ) (v : NNReal) (h0 : 0 ≤ 1-p-q+a)
    (h1 : a ≤ p) (h2 : a ≤ q) (ha : 0 ≤ a) : IsProbabilityMeasure (t10_law p q a lam v) := by
  constructor
  simpa only [t10_law, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one] using t10_law_weights p q a h0 h1 h2 ha

lemma t10_law_joint (p q a lam : ℝ) (v : NNReal) (j : Fin 2)
    (U : Set (ℝ × Bool)) (V : Set (Fin 2)) (hU : MeasurableSet U) (hV : MeasurableSet V) :
    t10_law p q a lam v
      ((fun ω => (potentialY j ω, potentialS j ω)) ⁻¹' U ∩ assignment ⁻¹' V) =
      t10_law p q a lam v ((fun ω => (potentialY j ω, potentialS j ω)) ⁻¹' U) * fairAssignment V := by
  simp only [t10_law, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    t10_block_rect _ _ _ j U V hU hV, t10_block_pair _ _ _ j U hU]
  ring

lemma t10_law_assignment (p q a lam : ℝ) (v : NNReal)
    (h0 : 0 ≤ 1-p-q+a) (h1 : a ≤ p) (h2 : a ≤ q) (ha : 0 ≤ a)
    (V : Set (Fin 2)) (hV : MeasurableSet V) :
    t10_law p q a lam v (assignment ⁻¹' V) = fairAssignment V := by
  letI := t10_law_probability p q a lam v h0 h1 h2 ha
  simpa using t10_law_joint p q a lam v 0 univ V MeasurableSet.univ hV

lemma t10_law_ignorability (p q a lam : ℝ) (v : NNReal)
    (h0 : 0 ≤ 1-p-q+a) (h1 : a ≤ p) (h2 : a ≤ q) (ha : 0 ≤ a) :
    Ignorability (t10_law p q a lam v) := by
  constructor
  · intro j
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro U V hU hV
    rw [t10_law_joint _ _ _ _ _ j U V hU hV, t10_law_assignment _ _ _ _ _ h0 h1 h2 ha V hV]
  · intro j
    change 0 < t10_law p q a lam v (assignment ⁻¹' {j})
    rw [t10_law_assignment _ _ _ _ _ h0 h1 h2 ha _ (measurableSet_singleton j), t10_fair_singleton]
    norm_num

lemma t10_block_potential (s r : Bool) (F : Measure ℝ) [IsProbabilityMeasure F] (j : Fin 2) :
    t10_block s r F (potentialPass j) = if ![s,r] j then 1 else 0 := by
  have h := t10_block_pair s r F j (univ ×ˢ {true})
    (MeasurableSet.univ.prod (measurableSet_singleton true))
  have he : (fun ω : State 2 0 => (potentialY j ω, potentialS j ω)) ⁻¹'
      (univ ×ˢ {true}) = potentialPass j := by ext ω; simp [potentialPass]
  rw [he] at h
  cases hs : ![s,r] j <;> simpa [hs] using h

lemma t10_law_marginals (p q a lam : ℝ) (v : NNReal)
    (h1 : a ≤ p) (h2 : a ≤ q) (ha : 0 ≤ a) :
    t10_law p q a lam v (potentialPass 0) = ENNReal.ofReal p ∧
      t10_law p q a lam v (potentialPass 1) = ENNReal.ofReal q := by
  constructor <;>
    simp only [t10_law, Measure.add_apply, Measure.smul_apply, smul_eq_mul, t10_block_potential]
  · simp only [Matrix.cons_val_zero, Bool.false_eq_true, Bool.true_eq, if_false, if_true,
      mul_zero, mul_one, zero_add, add_zero]
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr h1) ha]
    congr 1
    ring
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Bool.false_eq_true, Bool.true_eq,
      if_false, if_true, mul_zero, mul_one, zero_add, add_zero]
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr h2) ha]
    congr 1
    ring

lemma t10_block_all_mass (s r : Bool) (F : Measure ℝ) [IsProbabilityMeasure F] :
    t10_block s r F alwaysPass = if s && r then 1 else 0 := by
  rw [t10_block, Measure.map_apply (t10_block_measurable s r) measurableSet_always]
  have he : (fun ω : ℝ × Fin 2 =>
      ((![ω.1,ω.1], ![s,r], ω.2, fun _ => 0) : State 2 0)) ⁻¹' alwaysPass =
        if s && r then univ else ∅ := by
    cases s <;> cases r <;> ext ω <;> simp [alwaysPass, potentialS, Fin.forall_fin_two]
  rw [he]
  cases s <;> cases r <;> simp

lemma t10_law_all_mass (p q a lam : ℝ) (v : NNReal) :
    t10_law p q a lam v alwaysPass = ENNReal.ofReal a := by
  simp [t10_law, Measure.add_apply, Measure.smul_apply, t10_block_all_mass]

lemma t10_block_passer_map (s r : Bool) (F : Measure ℝ) [IsProbabilityMeasure F] (j : Fin 2) :
    ((t10_block s r F).restrict (potentialPass j)).map (potentialY j) =
      if ![s,r] j then F else 0 := by
  ext U hU
  rw [Measure.map_apply (measurable_potentialY j) hU,
    Measure.restrict_apply ((measurable_potentialY j) hU)]
  have he : (potentialY (d := 0) j) ⁻¹' U ∩ potentialPass j =
      (fun ω => (potentialY j ω, potentialS j ω)) ⁻¹' (U ×ˢ {true}) := by
    ext ω
    simp [potentialPass]
  rw [he, t10_block_pair s r F j _ (hU.prod (measurableSet_singleton true))]
  cases hs : ![s,r] j <;> simp [hs]

lemma t10_law_passer_maps (p q a lam : ℝ) (v : NNReal) :
    ((t10_law p q a lam v).restrict (potentialPass 0)).map (potentialY 0) =
      ENNReal.ofReal a • gaussianReal 0 v + ENNReal.ofReal (p-a) • gaussianReal (-lam) v ∧
    ((t10_law p q a lam v).restrict (potentialPass 1)).map (potentialY 1) =
      ENNReal.ofReal a • gaussianReal 0 v + ENNReal.ofReal (q-a) • gaussianReal lam v := by
  constructor <;>
    simp only [t10_law, Measure.restrict_add, Measure.restrict_smul] <;>
    simp only [Measure.map_add _ _ (measurable_potentialY _),
      Measure.map_smul _ (measurable_potentialY _).aemeasurable, t10_block_passer_map] <;>
    simp [add_comm]

lemma t10_law_rates (p q a lam : ℝ) (v : NNReal)
    (hp : 0 < p) (hq : 0 < q) (h0 : 0 ≤ 1-p-q+a)
    (h1 : a ≤ p) (h2 : a ≤ q) (ha : 0 ≤ a) :
    passingRate (t10_law p q a lam v) 0 = p ∧ passingRate (t10_law p q a lam v) 1 = q := by
  have hr := (nonzero_passing_corrected _ (t10_law_probability p q a lam v h0 h1 h2 ha)
    (t10_law_ignorability p q a lam v h0 h1 h2 ha)).1
  rw [hr 0, hr 1, (t10_law_marginals p q a lam v h1 h2 ha).1,
    (t10_law_marginals p q a lam v h1 h2 ha).2,
    ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hq.le]
  exact ⟨rfl,rfl⟩

lemma t10_law_assumptions (p q a lam : ℝ) (v : NNReal)
    (hp : 0 < p) (hq : 0 < q) (h0 : 0 ≤ 1-p-q+a)
    (h1 : a ≤ p) (h2 : a ≤ q) (ha : 0 ≤ a) :
    Assumptions (t10_law p q a lam v) := by
  refine ⟨t10_law_probability p q a lam v h0 h1 h2 ha,
    t10_law_ignorability p q a lam v h0 h1 h2 ha, ?_⟩
  intro j
  have hr := t10_law_rates p q a lam v hp hq h0 h1 h2 ha
  fin_cases j
  · change 0 < passingRate (t10_law p q a lam v) 0
    rw [hr.1]; exact hp
  · change 0 < passingRate (t10_law p q a lam v) 1
    rw [hr.2]; exact hq

lemma t10_normalize_coeff (p b : ℝ) (hp : 0 < p) :
    (ENNReal.ofReal p)⁻¹ * ENNReal.ofReal b = ENNReal.ofReal (b/p) := by
  rw [mul_comm, ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos hp]

lemma t10_law_passers (p q a lam : ℝ) (v : NNReal)
    (hp : 0 < p) (hq : 0 < q) (h0 : 0 ≤ 1-p-q+a)
    (h1 : a ≤ p) (h2 : a ≤ q) (ha : 0 ≤ a) :
    passerLaw (t10_law p q a lam v) 0 =
      ENNReal.ofReal (1-(1-a/p)) • gaussianReal 0 v +
        ENNReal.ofReal (1-a/p) • gaussianReal (-lam) v ∧
    passerLaw (t10_law p q a lam v) 1 =
      ENNReal.ofReal (1-(1-a/q)) • gaussianReal 0 v +
        ENNReal.ofReal (1-a/q) • gaussianReal lam v := by
  have hA := t10_law_assumptions p q a lam v hp hq h0 h1 h2 ha
  have hpm := t10_law_marginals p q a lam v h1 h2 ha
  have hmaps := t10_law_passer_maps p q a lam v
  constructor
  · rw [← conditional_law_consistency _ hA, eventLaw, hpm.1, hmaps.1,
      smul_add, smul_smul, smul_smul, t10_normalize_coeff p a hp,
      t10_normalize_coeff p (p-a) hp]
    congr 2
    · ring
    · rw [sub_div, div_self hp.ne']
  · rw [← conditional_law_consistency _ hA, eventLaw, hpm.2, hmaps.2,
      smul_add, smul_smul, smul_smul, t10_normalize_coeff q a hq,
      t10_normalize_coeff q (q-a) hq]
    congr 2
    · ring
    · rw [sub_div, div_self hq.ne']

lemma t10_simulation_block (s r : Bool) (lam : ℝ) (v : NNReal) :
    ((gaussianReal 0 v).prod fairAssignment).map (simulationState s r lam) =
      t10_block s r (gaussianReal (lam*((if r then (1:ℝ) else 0)-(if s then (1:ℝ) else 0))) v) := by
  let m := lam*((if r then (1:ℝ) else 0)-(if s then (1:ℝ) else 0))
  have hm : (gaussianReal 0 v).map (fun x : ℝ => m+x) = gaussianReal m v := by
    simpa using (gaussianReal_map_const_add (μ := (0:ℝ)) (v := v) m)
  change _ = t10_block s r (gaussianReal m v)
  have hh := Measure.map_prod_map (gaussianReal 0 v) fairAssignment
    (show Measurable (fun x : ℝ => m+x) by fun_prop) measurable_id
  rw [hm, Measure.map_id] at hh
  rw [t10_block, hh, Measure.map_map (t10_block_measurable s r) (by fun_prop)]
  rfl

lemma t10_simulation_law (p q ρ lam σ : ℝ) : simulationLaw p q ρ lam σ =
    t10_law p q (p*q+ρ*Real.sqrt (p*(1-p)*q*(1-q))) lam ⟨σ^2,sq_nonneg σ⟩ := by
  let v : NNReal := ⟨σ^2,sq_nonneg σ⟩
  change ENNReal.ofReal (1-p-q+(p*q+ρ*Real.sqrt (p*(1-p)*q*(1-q)))) •
      ((gaussianReal 0 v).prod fairAssignment).map (simulationState false false lam) +
    ENNReal.ofReal (p-(p*q+ρ*Real.sqrt (p*(1-p)*q*(1-q)))) •
      ((gaussianReal 0 v).prod fairAssignment).map (simulationState true false lam) +
    ENNReal.ofReal (q-(p*q+ρ*Real.sqrt (p*(1-p)*q*(1-q)))) •
      ((gaussianReal 0 v).prod fairAssignment).map (simulationState false true lam) +
    ENNReal.ofReal (p*q+ρ*Real.sqrt (p*(1-p)*q*(1-q))) •
      ((gaussianReal 0 v).prod fairAssignment).map (simulationState true true lam) =
    t10_law p q (p*q+ρ*Real.sqrt (p*(1-p)*q*(1-q))) lam v
  rw [t10_simulation_block, t10_simulation_block, t10_simulation_block, t10_simulation_block]
  norm_num [t10_law]

lemma t10_eventMean_passer {K d : ℕ} (μ : Measure (State K d)) (j : Fin K) :
    eventMean μ observedY (passEvent ∩ armEvent j) = ∫ x, x ∂passerLaw μ j := by
  unfold passerLaw eventLaw eventMean
  rw [integral_smul_measure, integral_map (f := fun x : ℝ => x) measurable_observedY.aemeasurable
    (by fun_prop)]
  simp only [id_eq, ENNReal.toReal_inv, smul_eq_mul, div_eq_mul_inv]
  ring

lemma t10_mixture_mean (u m : ℝ) (v : NNReal) :
    (∫ x, x ∂(ENNReal.ofReal (1-u) • gaussianReal 0 v + ENNReal.ofReal u • gaussianReal m v)) =
      (ENNReal.ofReal u).toReal * m := by
  rw [integral_add_measure (f := fun x : ℝ => x)
    (((memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable (by norm_num)).smul_measure (by finiteness))
    (((memLp_id_gaussianReal (μ := m) (v := v) 2).integrable (by norm_num)).smul_measure (by finiteness)),
    integral_smul_measure, integral_smul_measure]
  simp [integral_id_gaussianReal]

/-- Correlation of the simulated passing indicators under the feasibility hypotheses. -/
lemma t10_simulation_correlation (p₁ p₂ ρ lam σ : ℝ)
    (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hp₂ : 0 < p₂) (hp₂' : p₂ < 1)
    (hσ : 0 ≤ σ)
    (ha₀ : 0 ≤ 1-p₁-p₂+(p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂))))
    (ha₁ : p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)) ≤ p₁)
    (ha₂ : p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)) ≤ p₂)
    (ha : 0 ≤ p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂))) :
    checkCorrelation (simulationLaw p₁ p₂ ρ lam σ) 0 1 = ρ := by
  let v : NNReal := ⟨σ^2,sq_nonneg σ⟩
  have hlaw : simulationLaw p₁ p₂ ρ lam σ = t10_law p₁ p₂ _ lam v :=
    t10_simulation_law p₁ p₂ ρ lam σ
  rw [hlaw]
  have hpm := t10_law_marginals p₁ p₂ _ lam v ha₁ ha₂ ha
  have he : (potentialPass (d := 0) (0:Fin 2) ∩ potentialPass 1) = alwaysPass := by
    ext ω
    simp [potentialPass, alwaysPass, Fin.forall_fin_two]
  simp only [checkCorrelation, hpm.1, hpm.2, he]
  rw [t10_law_all_mass,
    ENNReal.toReal_ofReal hp₁.le, ENNReal.toReal_ofReal hp₂.le, ENNReal.toReal_ofReal ha]
  have hD : 0 < Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)) := by
    apply Real.sqrt_pos.mpr
    exact mul_pos (mul_pos (mul_pos hp₁ (sub_pos.mpr hp₁')) hp₂) (sub_pos.mpr hp₂')
  apply (div_eq_iff hD.ne').mpr
  ring

lemma t10_simulation_certificate (p₁ p₂ ρ lam σ : ℝ)
    (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hp₂ : 0 < p₂) (hp₂' : p₂ < 1)
    (hσ : 0 ≤ σ)
    (ha₀ : 0 ≤ 1-p₁-p₂+(p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂))))
    (ha₁ : p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)) ≤ p₁)
    (ha₂ : p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)) ≤ p₂)
    (ha : 0 ≤ p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂))) :
    let a := p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂))
    let w₁ := 1-a/p₁
    let w₂ := 1-a/p₂
    let μ := simulationLaw p₁ p₂ ρ lam σ
    Assumptions μ ∧ (μ alwaysPass).toReal = a ∧ checkCorrelation μ 0 1 = ρ ∧
    passingRate μ 0 = p₁ ∧ passingRate μ 1 = p₂ ∧
    passerLaw μ 0 = ENNReal.ofReal (1-w₁) • gaussianReal 0 ⟨σ^2,sq_nonneg σ⟩ +
      ENNReal.ofReal w₁ • gaussianReal (-lam) ⟨σ^2,sq_nonneg σ⟩ ∧
    passerLaw μ 1 = ENNReal.ofReal (1-w₂) • gaussianReal 0 ⟨σ^2,sq_nonneg σ⟩ +
      ENNReal.ofReal w₂ • gaussianReal lam ⟨σ^2,sq_nonneg σ⟩ ∧
    eventMean μ observedY (passEvent ∩ armEvent 0) = -lam*w₁ ∧
    eventMean μ observedY (passEvent ∩ armEvent 1) = lam*w₂ := by
  dsimp only
  let v : NNReal := ⟨σ^2,sq_nonneg σ⟩
  have hlaw : simulationLaw p₁ p₂ ρ lam σ = t10_law p₁ p₂ _ lam v :=
    t10_simulation_law p₁ p₂ ρ lam σ
  have hA := t10_law_assumptions p₁ p₂ _ lam v hp₁ hp₂ ha₀ ha₁ ha₂ ha
  have hr := t10_law_rates p₁ p₂ _ lam v hp₁ hp₂ ha₀ ha₁ ha₂ ha
  have hf := t10_law_passers p₁ p₂ _ lam v hp₁ hp₂ ha₀ ha₁ ha₂ ha
  have hw₁ : 0 ≤ 1-(p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)))/p₁ :=
    sub_nonneg.mpr ((div_le_one hp₁).mpr ha₁)
  have hw₂ : 0 ≤ 1-(p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)))/p₂ :=
    sub_nonneg.mpr ((div_le_one hp₂).mpr ha₂)
  refine ⟨?_, ?_, t10_simulation_correlation p₁ p₂ ρ lam σ hp₁ hp₁' hp₂ hp₂' hσ ha₀ ha₁ ha₂ ha,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlaw]
    exact hA
  · rw [hlaw, t10_law_all_mass, ENNReal.toReal_ofReal ha]
  · rw [hlaw]
    exact hr.1
  · rw [hlaw]
    exact hr.2
  · rw [hlaw]
    exact hf.1
  · rw [hlaw]
    exact hf.2
  · rw [t10_eventMean_passer, hlaw, hf.1, t10_mixture_mean,
      ENNReal.toReal_ofReal hw₁]
    ring
  · rw [t10_eventMean_passer, hlaw, hf.2, t10_mixture_mean,
      ENNReal.toReal_ofReal hw₂]
    ring

/-- Upper-tail variational cost at a proposed cutoff. -/
noncomputable def t10_call (F : Measure ℝ) (a q : ℝ) : ℝ :=
  (∫ x, max (x-q) 0 ∂F) + a*q

lemma t10_call_integrable (F : Measure ℝ) [IsProbabilityMeasure F]
    (hi : Integrable id F) (q : ℝ) : Integrable (fun x => max (x-q) 0) F := by
  exact (hi.sub (integrable_const q)).pos_part

lemma t10_call_gap (x q t : ℝ) :
    0 ≤ max (x-t) 0 - max (x-q) 0 +
      (t-q) * (Ioi q).indicator (fun _ => (1:ℝ)) x := by
  by_cases hx : q < x
  · simp only [indicator_of_mem (show x ∈ Ioi q from hx), mul_one, max_eq_left (sub_nonneg.mpr hx.le)]
    have hh := le_max_left (x-t) 0
    linarith
  · simp only [indicator_of_notMem (show x ∉ Ioi q from hx), mul_zero, add_zero,
      max_eq_right (sub_nonpos.mpr (le_of_not_gt hx)), sub_zero]
    exact le_max_right _ _

lemma t10_call_min (F : Measure ℝ) [IsProbabilityMeasure F]
    (hi : Integrable id F) (a q : ℝ) (hm : F.real (Ioi q) = a) (t : ℝ) :
    t10_call F a q ≤ t10_call F a t := by
  let g := fun x => max (x-t) 0 - max (x-q) 0 +
    (t-q) * (Ioi q).indicator (fun _ => (1:ℝ)) x
  have hc := (integrable_const (μ := F) (1:ℝ)).indicator (s := Ioi q) measurableSet_Ioi
  have hg : Integrable g F :=
    ((t10_call_integrable F hi t).sub (t10_call_integrable F hi q)).add (hc.const_mul (t-q))
  have hn : 0 ≤ ∫ x, g x ∂F := integral_nonneg (fun x => t10_call_gap x q t)
  dsimp only [g] at hn
  rw [integral_add (f := fun x : ℝ => max (x-t) 0 - max (x-q) 0)
    ((t10_call_integrable F hi t).sub (t10_call_integrable F hi q))
    (hc.const_mul (t-q)), integral_sub (f := fun x : ℝ => max (x-t) 0) (g := fun x : ℝ => max (x-q) 0) (t10_call_integrable F hi t)
      (t10_call_integrable F hi q), integral_const_mul,
      integral_indicator_const (1:ℝ) measurableSet_Ioi] at hn
  simp only [smul_eq_mul, mul_one, ← measureReal_def, hm] at hn
  unfold t10_call
  linarith

/-- Full support makes the quantile cutoff the unique minimizer. -/
lemma t10_call_strict (F : Measure ℝ) [IsProbabilityMeasure F]
    (hi : Integrable id F) (hs : FullRealSupport F id)
    (a q : ℝ) (hm : F.real (Ioi q) = a) (t : ℝ) (ht : t ≠ q) :
    t10_call F a q < t10_call F a t := by
  let g := fun x => max (x-t) 0 - max (x-q) 0 +
    (t-q) * (Ioi q).indicator (fun _ => (1:ℝ)) x
  have hc := (integrable_const (μ := F) (1:ℝ)).indicator (s := Ioi q) measurableSet_Ioi
  have hg : Integrable g F :=
    ((t10_call_integrable F hi t).sub (t10_call_integrable F hi q)).add (hc.const_mul (t-q))
  have hsup : 0 < F (Function.support g) := by
    rcases lt_or_gt_of_ne ht with ht | ht
    · apply lt_of_lt_of_le (hs t q ht)
      apply measure_mono
      intro x hx
      change g x ≠ 0
      have hxt : t < x := hx.1
      have hxq : x < q := hx.2
      have he : g x = x-t := by
        simp only [g, Pi.zero_apply, indicator_of_notMem (show x ∉ Ioi q by exact not_lt.mpr hxq.le),
          mul_zero, add_zero, max_eq_left (sub_nonneg.mpr hxt.le),
          max_eq_right (sub_nonpos.mpr hxq.le), sub_zero]
      rw [he]
      exact (sub_pos.mpr hxt).ne'
    · apply lt_of_lt_of_le (hs q t ht)
      apply measure_mono
      intro x hx
      change g x ≠ 0
      have hqx : q < x := hx.1
      have hxt : x < t := hx.2
      have he : g x = t-x := by
        simp only [g, Pi.zero_apply, indicator_of_mem (show x ∈ Ioi q from hqx), mul_one,
          max_eq_right (sub_nonpos.mpr hxt.le), max_eq_left (sub_nonneg.mpr hqx.le)]
        ring
      rw [he]
      exact (sub_pos.mpr hxt).ne'
  have hn : 0 < ∫ x, g x ∂F :=
    (integral_pos_iff_support_of_nonneg (fun x => t10_call_gap x q t) hg).mpr hsup
  dsimp only [g] at hn
  rw [integral_add (f := fun x : ℝ => max (x-t) 0 - max (x-q) 0)
    ((t10_call_integrable F hi t).sub (t10_call_integrable F hi q))
    (hc.const_mul (t-q)), integral_sub (f := fun x : ℝ => max (x-t) 0) (g := fun x : ℝ => max (x-q) 0) (t10_call_integrable F hi t)
      (t10_call_integrable F hi q), integral_const_mul,
      integral_indicator_const (1:ℝ) measurableSet_Ioi] at hn
  simp only [smul_eq_mul, mul_one, ← measureReal_def, hm] at hn
  unfold t10_call
  linarith

noncomputable def t10_put (F : Measure ℝ) (a q : ℝ) : ℝ :=
  (∫ x, max (q-x) 0 ∂F) - a*q

lemma t10_put_integrable (F : Measure ℝ) [IsProbabilityMeasure F]
    (hi : Integrable id F) (q : ℝ) : Integrable (fun x => max (q-x) 0) F := by
  exact ((integrable_const q).sub hi).pos_part

lemma t10_put_min (F : Measure ℝ) [IsProbabilityMeasure F]
    (hi : Integrable id F) (a q : ℝ) (hm : F.real (Iio q) = a) (t : ℝ) :
    t10_put F a q ≤ t10_put F a t := by
  let g := fun x => max (t-x) 0 - max (q-x) 0 -
    (t-q) * (Iio q).indicator (fun _ => (1:ℝ)) x
  have hc := (integrable_const (μ := F) (1:ℝ)).indicator (s := Iio q) measurableSet_Iio
  have hg : Integrable g F :=
    ((t10_put_integrable F hi t).sub (t10_put_integrable F hi q)).sub (hc.const_mul (t-q))
  have hn : 0 ≤ ∫ x, g x ∂F := by
    apply integral_nonneg
    intro x
    change (0:ℝ) ≤ max (t-x) 0 - max (q-x) 0 -
      (t-q) * (Iio q).indicator (fun _ => (1:ℝ)) x
    by_cases hx : x < q
    · simp only [g, Pi.zero_apply, indicator_of_mem (show x ∈ Iio q from hx), mul_one,
        max_eq_left (sub_nonneg.mpr hx.le)]
      have hh := le_max_left (t-x) 0
      linarith
    · simp only [g, Pi.zero_apply, indicator_of_notMem (show x ∉ Iio q from hx), mul_zero, sub_zero,
        max_eq_right (sub_nonpos.mpr (le_of_not_gt hx))]
      exact le_max_right _ _
  dsimp only [g] at hn
  rw [integral_sub (f := fun x : ℝ => max (t-x) 0 - max (q-x) 0)
    ((t10_put_integrable F hi t).sub (t10_put_integrable F hi q))
    (hc.const_mul (t-q)), integral_sub (f := fun x : ℝ => max (t-x) 0) (g := fun x : ℝ => max (q-x) 0) (t10_put_integrable F hi t)
      (t10_put_integrable F hi q), integral_const_mul,
      integral_indicator_const (1:ℝ) measurableSet_Iio] at hn
  simp only [smul_eq_mul, mul_one, ← measureReal_def, hm] at hn
  unfold t10_put
  linarith

noncomputable def t10_cost (F : Measure ℝ) (a s t : ℝ) : ℝ :=
  t10_put F a s + t10_call F a t

lemma t10_cost_min (F : Measure ℝ) [IsProbabilityMeasure F]
    (hi : Integrable id F) (a s t : ℝ)
    (hs : F.real (Iio s) = a) (ht : F.real (Ioi t) = a) (s' t' : ℝ) :
    t10_cost F a s t ≤ t10_cost F a s' t' := by
  exact add_le_add (t10_put_min F hi a s hs s') (t10_call_min F hi a t ht t')

lemma t10_cost_strict (F : Measure ℝ) [IsProbabilityMeasure F]
    (hi : Integrable id F) (hfull : FullRealSupport F id) (a s t : ℝ)
    (hs : F.real (Iio s) = a) (ht : F.real (Ioi t) = a) (s' t' : ℝ) (hne : t' ≠ t) :
    t10_cost F a s t < t10_cost F a s' t' := by
  exact add_lt_add_of_le_of_lt (t10_put_min F hi a s hs s')
    (t10_call_strict F hi hfull a t ht t' hne)

lemma t10_cdf_strict (F : Measure ℝ) [IsProbabilityMeasure F]
    (hs : FullRealSupport F id) : StrictMono (cdf F) := by
  intro y z hyz
  have hpos : 0 < F (Ioc y z) :=
    lt_of_lt_of_le (hs y z hyz) (measure_mono Ioo_subset_Ioc_self)
  have he : F (Iic z) = F (Iic y) + F (Ioc y z) := by
    rw [← measure_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Iic_union_Ioc_eq_Iic hyz.le]
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def, he,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  exact lt_add_of_pos_right _ (ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _))

lemma t10_quantile (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (hs : FullRealSupport F id) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ q : ℝ, quantile F p = q ∧ cdf F q = p := by
  obtain ⟨q,hq⟩ := AronowAudit.P053.NormalCompletion.exists_cdf_eq F hp0 hp1
  refine ⟨q, ?_, hq⟩
  have he : {x : EReal | p ≤ (F {y : ℝ | (y : EReal) ≤ x}).toReal} =
      Ici (q : EReal) := by
    ext x
    cases x using EReal.rec with
    | bot => simp [not_le.mpr hp0]
    | top => simp [hp1.le]
    | coe x =>
      simp only [EReal.coe_le_coe_iff, mem_setOf_eq, mem_Ici]
      change (p ≤ F.real (Iic x)) ↔ q ≤ x
      rw [← cdf_eq_real, ← hq]
      exact (t10_cdf_strict F hs).le_iff_le
  rw [quantile, he, csInf_Ici]

lemma t10_cut_mass (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (hs : FullRealSupport F id) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    let q := (quantile F p).toReal
    quantile F p = (q : EReal) ∧ F.real (Iio q) = p ∧ F.real (Ioi q) = 1-p ∧
      F.real (Iic q) = p ∧ F.real (Ici q) = 1-p := by
  obtain ⟨q,hq,hcdf⟩ := t10_quantile F hs p hp0 hp1
  rw [hq, EReal.toReal_coe]
  have hl : F.real (Iic q) = p := by simpa only [cdf_eq_real] using hcdf
  have he : F (Ioi q) = F (Ici q) := measure_congr (Ioi_ae_eq_Ici' (measure_singleton q))
  have he' : F (Iio q) = F (Iic q) := measure_congr (Iio_ae_eq_Iic' (measure_singleton q))
  have hh := measureReal_add_measureReal_compl (μ := F) (s := Iic q) measurableSet_Iic
  simp only [probReal_univ, compl_Iic, hl] at hh
  refine ⟨rfl, ?_, ?_, hl, ?_⟩
  · simpa only [measureReal_def, he'] using hl
  · linarith
  · simpa only [measureReal_def, ← he] using (show F.real (Ioi q) = 1-p by linarith)

lemma t10_cost_mix (F G : Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    (hF : Integrable id F) (hG : Integrable id G)
    (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c+d=1) (a s t : ℝ) :
    t10_cost (ENNReal.ofReal c • F + ENNReal.ofReal d • G) a s t =
      c*t10_cost F a s t + d*t10_cost G a s t := by
  unfold t10_cost t10_put t10_call
  rw [integral_add_measure ((t10_put_integrable F hF s).smul_measure (by finiteness))
    ((t10_put_integrable G hG s).smul_measure (by finiteness)),
    integral_add_measure ((t10_call_integrable F hF t).smul_measure (by finiteness))
    ((t10_call_integrable G hG t).smul_measure (by finiteness))]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal hd, smul_eq_mul]
  have hd' : d = 1-c := by linarith
  rw [hd']
  ring

lemma t10_cost_reflect (F : Measure ℝ) [IsProbabilityMeasure F] (a b s t : ℝ) :
    t10_cost (F.map (fun x => b-x)) a s t = t10_cost F a (b-t) (b-s) := by
  unfold t10_cost t10_put t10_call
  rw [integral_map (by fun_prop : AEMeasurable (fun x : ℝ => b-x) F)
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => max (s-x) 0) _),
    integral_map (by fun_prop : AEMeasurable (fun x : ℝ => b-x) F)
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => max (x-t) 0) _)]
  have h1 : (fun x : ℝ => max (s-(b-x)) 0) = fun x => max (x-(b-s)) 0 := by
    funext x
    congr 1
    ring
  have h2 : (fun x : ℝ => max ((b-x)-t) 0) = fun x => max ((b-t)-x) 0 := by
    funext x
    congr 1
    ring
  rw [h1,h2]
  ring

local instance instT10GaussianNull (m : ℝ) : NullSingletonClass (gaussianReal m 1) :=
  nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)

lemma t10_mix_probability (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    IsProbabilityMeasure (normalMixture w) := by
  constructor
  simp only [normalMixture, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hw1) hw]
  norm_num

lemma t10_mix_integrable (w : ℝ) : Integrable id (normalMixture w) := by
  unfold normalMixture
  exact (((memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable (by norm_num)).smul_measure
    (by finiteness)).add_measure
    (((memLp_id_gaussianReal (μ := -1) (v := 1) 2).integrable (by norm_num)).smul_measure
      (by finiteness))

local instance instT10MixNull (w : ℝ) : NullSingletonClass (normalMixture w) := by
  constructor
  intro x
  simp [normalMixture, Measure.add_apply, Measure.smul_apply]

lemma t10_normal_support (l u : ℝ) (hlu : l < u) : 0 < gaussianReal 0 1 (Ioo l u) := by
  rw [pos_iff_ne_zero]
  intro hzero
  have hv := (gaussianReal_absolutelyContinuous' 0
    (by norm_num : (1 : NNReal) ≠ 0)) hzero
  rw [Real.volume_Ioo] at hv
  exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hlu)).ne' hv

lemma t10_mix_support (w : ℝ) (hw : w < 1) : FullRealSupport (normalMixture w) id := by
  intro l u hlu
  change 0 < normalMixture w (Ioo l u)
  apply lt_of_lt_of_le _ (le_add_right (le_refl _) :
    ENNReal.ofReal (1-w) * gaussianReal 0 1 (Ioo l u) ≤
      ENNReal.ofReal (1-w) * gaussianReal 0 1 (Ioo l u) +
        ENNReal.ofReal w * gaussianReal (-1) 1 (Ioo l u))
  exact pos_iff_ne_zero.mpr (mul_ne_zero
    (ENNReal.ofReal_pos.mpr (sub_pos.mpr hw)).ne' (t10_normal_support l u hlu).ne')

lemma t10_shift_cdf (x : ℝ) :
    (gaussianReal (-1) 1).real (Iic x) = (gaussianReal 0 1).real (Iic (x+1)) := by
  have hm : (gaussianReal 0 1).map (fun t : ℝ => t-1) = gaussianReal (-1) 1 := by
    simpa only [zero_add, sub_eq_add_neg] using
      (gaussianReal_map_add_const (μ := (0:ℝ)) (v := (1:NNReal)) (-1))
  rw [← hm, map_measureReal_apply (by fun_prop : Measurable (fun t : ℝ => t-1)) measurableSet_Iic]
  congr 1
  ext t
  simp only [mem_preimage, mem_Iic]
  constructor <;> intro h <;> linarith

lemma t10_mix_cdf (w x : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    (normalMixture w).real (Iic x) =
      (1-w)*(gaussianReal 0 1).real (Iic x) + w*(gaussianReal 0 1).real (Iic (x+1)) := by
  simp only [normalMixture, measureReal_def, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hw,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hw1)]
  rw [← measureReal_def, ← measureReal_def, t10_shift_cdf]
  rfl

lemma t10_mix_cdf_weight_strict (v w x : ℝ) (hv : 0 ≤ v) (hw1 : w ≤ 1) (hvw : v < w) :
    (normalMixture v).real (Iic x) < (normalMixture w).real (Iic x) := by
  rw [t10_mix_cdf v x hv (by linarith), t10_mix_cdf w x (by linarith) hw1]
  have hh := AronowAudit.P053.NormalCompletion.strictMono_normal_cdf (show x < x+1 by linarith)
  simp only [cdf_eq_real] at hh
  nlinarith

lemma t10_mix_reflect (w : ℝ) :
    (normalMixture w).map (fun x : ℝ => -1-x) = normalMixture (1-w) := by
  have hg (m : ℝ) : (gaussianReal m 1).map (fun x : ℝ => -1-x) = gaussianReal (-1-m) 1 := by
    have he : (fun x : ℝ => -1-x) = (fun x : ℝ => -1+x) ∘ (fun x : ℝ => -x) := by
      funext x
      simp only [Function.comp_apply]
      ring
    rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_neg,
      gaussianReal_map_const_add]
    congr 1
    ring
  rw [normalMixture, Measure.map_add _ _ (by fun_prop), Measure.map_smul _ (by fun_prop),
    Measure.map_smul _ (by fun_prop), hg, hg]
  norm_num [normalMixture, sub_sub_cancel, add_comm]

lemma t10_call_integral (F : Measure ℝ) [IsProbabilityMeasure F]
    (hi : Integrable id F) (a t : ℝ) (hm : F.real (Ioi t) = a) :
    t10_call F a t = ∫ x in Ioi t, x ∂F := by
  have he : (fun x : ℝ => max (x-t) 0) = (Ioi t).indicator (fun x => x-t) := by
    funext x
    by_cases hx : t < x
    · simp [indicator_of_mem (show x ∈ Ioi t from hx), max_eq_left (sub_nonneg.mpr hx.le)]
    · simp [indicator_of_notMem (show x ∉ Ioi t from hx),
        max_eq_right (sub_nonpos.mpr (le_of_not_gt hx))]
  rw [t10_call, he, integral_indicator measurableSet_Ioi,
    integral_sub (f := fun x : ℝ => x) hi.integrableOn (integrable_const t), integral_const]
  simp only [smul_eq_mul, measureReal_restrict_apply MeasurableSet.univ, univ_inter, hm]
  ring

lemma t10_put_integral (F : Measure ℝ) [IsProbabilityMeasure F]
    (hi : Integrable id F) (a t : ℝ) (hm : F.real (Iio t) = a) :
    t10_put F a t = -(∫ x in Iio t, x ∂F) := by
  have he : (fun x : ℝ => max (t-x) 0) = (Iio t).indicator (fun x => t-x) := by
    funext x
    by_cases hx : x < t
    · simp [indicator_of_mem (show x ∈ Iio t from hx), max_eq_left (sub_nonneg.mpr hx.le)]
    · simp [indicator_of_notMem (show x ∉ Iio t from hx),
        max_eq_right (sub_nonpos.mpr (le_of_not_gt hx))]
  rw [t10_put, he, integral_indicator measurableSet_Iio,
    integral_sub (g := fun x : ℝ => x) (integrable_const t) hi.integrableOn, integral_const]
  simp only [smul_eq_mul, measureReal_restrict_apply MeasurableSet.univ, univ_inter, hm]
  ring

/-- Difference of the upper- and lower-quarter unnormalized first moments. -/
noncomputable def t10_spread (F : Measure ℝ) : ℝ :=
  t10_cost F (1/4) ((quantile F (1/4)).toReal) ((quantile F (3/4)).toReal)

lemma t10_spread_min (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (hi : Integrable id F) (hfull : FullRealSupport F id) (s t : ℝ) :
    t10_spread F ≤ t10_cost F (1/4) s t := by
  have hs := (t10_cut_mass F hfull (1/4) (by norm_num) (by norm_num)).2.1
  have ht := (t10_cut_mass F hfull (3/4) (by norm_num) (by norm_num)).2.2.1
  norm_num at ht
  exact t10_cost_min F hi _ _ _ hs ht s t

lemma t10_spread_tail (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (hi : Integrable id F) (hfull : FullRealSupport F id) :
    tailUpper F (1/4) - eventMean F id {x | (x:EReal) ≤ quantile F (3/4)} =
      t10_spread F / (3/4) := by
  have hs := t10_cut_mass F hfull (1/4) (by norm_num) (by norm_num)
  have ht := t10_cut_mass F hfull (3/4) (by norm_num) (by norm_num)
  let s := (quantile F (1/4)).toReal
  let t := (quantile F (3/4)).toReal
  have heS : {x : ℝ | quantile F (1/4) ≤ (x:EReal)} = Ici s := by
    rw [hs.1]
    ext x
    simp [s]
  have heT : {x : ℝ | (x:EReal) ≤ quantile F (3/4)} = Iic t := by
    rw [ht.1]
    ext x
    simp [t]
  have hsi : (∫ x in Iio s, x ∂F) = ∫ x in Iic s, x ∂F :=
    setIntegral_congr_set (Iio_ae_eq_Iic' (measure_singleton s))
  have hso : (∫ x in Ioi s, x ∂F) = ∫ x in Ici s, x ∂F :=
    setIntegral_congr_set (Ioi_ae_eq_Ici' (measure_singleton s))
  have hsall := integral_add_compl (s := Iic s) measurableSet_Iic hi
  have htall := integral_add_compl (s := Iic t) measurableSet_Iic hi
  simp only [compl_Iic, id_eq] at hsall htall
  have htop : F.real (Ioi t) = 1/4 := by
    convert ht.2.2.1 using 1 <;> norm_num
  have hbot : F.real (Iio s) = 1/4 := hs.2.1
  rw [tailUpper, heS, heT, eventMean, eventMean]
  simp only [id_eq]
  rw [show (F (Ici s)).toReal = 3/4 by
      convert hs.2.2.2.2 using 1 <;> norm_num [s, measureReal_def],
    show (F (Iic t)).toReal = 3/4 from ht.2.2.2.1]
  rw [t10_spread, t10_cost, t10_put_integral F hi _ _ hbot,
    t10_call_integral F hi _ _ htop]
  rw [← hsi] at hsall
  rw [← hso]
  linarith

lemma t10_spread_reflect (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (hi : Integrable id F) (hfull : FullRealSupport F id)
    (b : ℝ) [NullSingletonClass (F.map (fun x => b-x))]
    (hfull' : FullRealSupport (F.map (fun x => b-x)) id) :
    t10_spread (F.map (fun x => b-x)) = t10_spread F := by
  let G := F.map (fun x => b-x)
  have hG : Integrable id G := by
    apply (integrable_map_measure measurable_id.aestronglyMeasurable (by fun_prop)).mpr
    exact (integrable_const b).sub hi
  apply le_antisymm
  · have h := t10_spread_min G hG hfull'
      (b-(quantile F (3/4)).toReal) (b-(quantile F (1/4)).toReal)
    rw [show G = F.map (fun x => b-x) from rfl, t10_cost_reflect] at h
    simpa [t10_spread] using h
  · have h := t10_spread_min F hi hfull
      (b-(quantile G (3/4)).toReal) (b-(quantile G (1/4)).toReal)
    change t10_spread F ≤ t10_cost (F.map (fun x => b-x)) (1/4) _ _
    rw [t10_cost_reflect]
    exact h

/-- This convex combination permits a strict comparison without decimal quantiles. -/
lemma t10_mix_decomposition : normalMixture (3/20) =
    ENNReal.ofReal (15/16) • normalMixture (1/10) +
      ENNReal.ofReal (1/16) • normalMixture (9/10) := by
  have h0 : ENNReal.ofReal (15/16) * ENNReal.ofReal (1-(1/10:ℝ)) +
      ENNReal.ofReal (1/16) * ENNReal.ofReal (1-(9/10:ℝ)) = ENNReal.ofReal (1-(3/20:ℝ)) := by
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  have h1 : ENNReal.ofReal (15/16) * ENNReal.ofReal (1/10:ℝ) +
      ENNReal.ofReal (1/16) * ENNReal.ofReal (9/10:ℝ) = ENNReal.ofReal (3/20:ℝ) := by
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  unfold normalMixture
  rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
  rw [show ENNReal.ofReal (1-(3/20:ℝ)) = _ from h0.symm,
    show ENNReal.ofReal (3/20:ℝ) = _ from h1.symm, add_smul, add_smul]
  abel

/-- For these Gaussian mixtures, distinct quantile cutoffs and reflection symmetry
give a strict comparison of the two spreads. -/
lemma t10_spread_mixtures : t10_spread (normalMixture (1/10)) <
    t10_spread (normalMixture (3/20)) := by
  letI : IsProbabilityMeasure (normalMixture (1/10)) := t10_mix_probability _ (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure (normalMixture (3/20)) := t10_mix_probability _ (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure (normalMixture (9/10)) := t10_mix_probability _ (by norm_num) (by norm_num)
  let s := (quantile (normalMixture (3/20)) (1/4)).toReal
  let t := (quantile (normalMixture (3/20)) (3/4)).toReal
  have hfull := t10_mix_support (1/10) (by norm_num)
  have hs := (t10_cut_mass (normalMixture (1/10)) hfull (1/4) (by norm_num) (by norm_num)).2.1
  have ht := (t10_cut_mass (normalMixture (1/10)) hfull (3/4) (by norm_num) (by norm_num)).2.2.1
  norm_num at ht
  have hne : t ≠ (quantile (normalMixture (1/10)) (3/4)).toReal := by
    intro he
    have hfirst := (t10_cut_mass (normalMixture (1/10)) hfull (3/4)
      (by norm_num) (by norm_num)).2.2.2.1
    have hsecond := (t10_cut_mass (normalMixture (3/20))
      (t10_mix_support _ (by norm_num)) (3/4) (by norm_num) (by norm_num)).2.2.2.1
    change (normalMixture (3/20)).real (Iic t) = 3/4 at hsecond
    have hstrict := t10_mix_cdf_weight_strict (1/10) (3/20) t
      (by norm_num) (by norm_num) (by norm_num)
    rw [he] at hsecond hstrict
    rw [hfirst] at hstrict
    linarith
  have hlt := t10_cost_strict (normalMixture (1/10)) (t10_mix_integrable _) hfull
    (1/4) _ _ hs ht s t hne
  change t10_spread (normalMixture (1/10)) < t10_cost (normalMixture (1/10)) (1/4) s t at hlt
  have hle : t10_spread (normalMixture (1/10)) ≤ t10_cost (normalMixture (9/10)) (1/4) s t := by
    rw [← show (normalMixture (1/10)).map (fun x : ℝ => -1-x) = normalMixture (9/10) by
      convert t10_mix_reflect (1/10) using 1 <;> norm_num, t10_cost_reflect]
    exact t10_spread_min _ (t10_mix_integrable _) hfull _ _
  have he := t10_cost_mix (normalMixture (1/10)) (normalMixture (9/10))
    (t10_mix_integrable _) (t10_mix_integrable _) (15/16) (1/16)
    (by norm_num) (by norm_num) (by norm_num) (1/4) s t
  rw [← t10_mix_decomposition] at he
  change t10_spread (normalMixture (3/20)) = _ at he
  rw [he]
  linarith

local instance instT10ReflectNull (F : Measure ℝ) [NullSingletonClass F] (b : ℝ) :
    NullSingletonClass (F.map (fun x => b-x)) := by
  constructor
  intro x
  rw [Measure.map_apply (by fun_prop : Measurable (fun y : ℝ => b-y)) (measurableSet_singleton x)]
  have he : (fun y : ℝ => b-y) ⁻¹' {x} = {b-x} := by
    ext y
    simp only [mem_preimage, mem_singleton_iff]
    constructor <;> intro h <;> linarith
  rw [he, measure_singleton]

lemma t10_support_reflect (F : Measure ℝ) (hfull : FullRealSupport F id) (b : ℝ) :
    FullRealSupport (F.map (fun x => b-x)) id := by
  intro l u hlu
  change 0 < F.map (fun x => b-x) (Ioo l u)
  rw [Measure.map_apply (by fun_prop : Measurable (fun x : ℝ => b-x)) measurableSet_Ioo]
  have he : (fun x : ℝ => b-x) ⁻¹' Ioo l u = Ioo (b-u) (b-l) := by
    ext x
    simp only [mem_preimage, mem_Ioo]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  rw [he]
  exact hfull _ _ (by linarith)

lemma t10_effect_width (μ : Measure (State 2 0)) (hA : Assumptions μ)
    (w : ℝ) (hw : 0 ≤ w) (hw1 : w < 1)
    (hr : passingRate μ 0 = 4/5 ∧ passingRate μ 1 = 4/5)
    (hF : passerLaw μ 0 = normalMixture w ∧
      passerLaw μ 1 = (normalMixture w).map (fun x : ℝ => -x)) :
    effectBoundWidth μ = 2*t10_spread (normalMixture w)/(3/4) := by
  letI : IsProbabilityMeasure (normalMixture w) := t10_mix_probability w hw hw1.le
  let F := normalMixture w
  let G := F.map (fun x : ℝ => (0:ℝ)-x)
  have hi := t10_mix_integrable w
  have hfull := t10_mix_support w hw1
  have hG : Integrable id G := by
    apply (integrable_map_measure measurable_id.aestronglyMeasurable (by fun_prop)).mpr
    exact (integrable_const (0:ℝ)).sub hi
  have hfullG : FullRealSupport G id := t10_support_reflect F hfull 0
  have hs := t10_spread_tail F hi hfull
  have hsG := t10_spread_tail G hG hfullG
  have hreflect : t10_spread G = t10_spread F := t10_spread_reflect F hi hfull 0 hfullG
  rw [hreflect] at hsG
  have htrim (j : Fin 2) : trimRatio μ j = 1/4 := by
    fin_cases j <;> norm_num [trimRatio, Fin.sum_univ_two, hr.1, hr.2]
  unfold effectBoundWidth
  rw [(passer_tail_mean_formula μ hA 0).1, (passer_tail_mean_formula μ hA 1).1,
    (passer_tail_mean_formula μ hA 0).2, (passer_tail_mean_formula μ hA 1).2,
    htrim 0, htrim 1, hF.1, hF.2]
  have hn : (normalMixture w).map (fun x : ℝ => -x) = G := by simp [G, F]
  rw [hn]
  norm_num only [show (1-(1/4:ℝ)) = 3/4 from by norm_num]
  change (tailUpper G (1/4) - eventMean F id {x | (x:EReal) ≤ quantile F (3/4)}) -
    (eventMean G id {x | (x:EReal) ≤ quantile G (3/4)} - tailUpper F (1/4)) = _
  linarith


lemma t10_design_sqrt : Real.sqrt ((4/5:ℝ)*(1-4/5)*(4/5)*(1-4/5)) = 4/25 := by
  rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]
  norm_num

lemma t10_design_law (ρ : ℝ) : simulationLaw (4/5) (4/5) ρ 1 1 =
    t10_law (4/5) (4/5) (16/25+ρ*(4/25)) 1 1 := by
  rw [t10_simulation_law, t10_design_sqrt]
  congr 1 <;> norm_num <;> rfl

lemma t10_design_passers (a : ℝ) (ha : 3/5 ≤ a) (ha' : a ≤ 4/5) :
    Assumptions (t10_law (4/5) (4/5) a 1 1) ∧
    passingRate (t10_law (4/5) (4/5) a 1 1) 0 = 4/5 ∧
    passingRate (t10_law (4/5) (4/5) a 1 1) 1 = 4/5 ∧
    passerLaw (t10_law (4/5) (4/5) a 1 1) 0 = normalMixture (1-a/(4/5)) ∧
    passerLaw (t10_law (4/5) (4/5) a 1 1) 1 =
      (normalMixture (1-a/(4/5))).map (fun x : ℝ => -x) := by
  have h0 : 0 ≤ 1-(4/5:ℝ)-4/5+a := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hA := t10_law_assumptions (4/5) (4/5) a 1 1
    (by norm_num) (by norm_num) h0 ha' ha' ha0
  have hr := t10_law_rates (4/5) (4/5) a 1 1
    (by norm_num) (by norm_num) h0 ha' ha' ha0
  have hf := t10_law_passers (4/5) (4/5) a 1 1
    (by norm_num) (by norm_num) h0 ha' ha' ha0
  refine ⟨hA, hr.1, hr.2, hf.1, ?_⟩
  rw [hf.2, normalMixture, Measure.map_add _ _ measurable_neg,
    Measure.map_smul _ measurable_neg.aemeasurable, Measure.map_smul _ measurable_neg.aemeasurable,
    gaussianReal_map_neg, gaussianReal_map_neg]
  norm_num

lemma t10_width_inequality :
    effectBoundWidth (simulationLaw (4/5) (4/5) (1/4) 1 1) ≠
      effectBoundWidth (simulationLaw (4/5) (4/5) (1/2) 1 1) := by
  have hfirst := t10_design_passers (17/25) (by norm_num) (by norm_num)
  have hsecond := t10_design_passers (18/25) (by norm_num) (by norm_num)
  have hF1 : passerLaw (t10_law (4/5) (4/5) (17/25) 1 1) 0 = normalMixture (3/20) ∧
      passerLaw (t10_law (4/5) (4/5) (17/25) 1 1) 1 =
        (normalMixture (3/20)).map (fun x : ℝ => -x) := by
    convert And.intro hfirst.2.2.2.1 hfirst.2.2.2.2 using 1 <;> norm_num
  have hF2 : passerLaw (t10_law (4/5) (4/5) (18/25) 1 1) 0 = normalMixture (1/10) ∧
      passerLaw (t10_law (4/5) (4/5) (18/25) 1 1) 1 =
        (normalMixture (1/10)).map (fun x : ℝ => -x) := by
    convert And.intro hsecond.2.2.2.1 hsecond.2.2.2.2 using 1 <;> norm_num
  have hw1 := t10_effect_width _ hfirst.1 (3/20) (by norm_num) (by norm_num)
    ⟨hfirst.2.1,hfirst.2.2.1⟩ hF1
  have hw2 := t10_effect_width _ hsecond.1 (1/10) (by norm_num) (by norm_num)
    ⟨hsecond.2.1,hsecond.2.2.1⟩ hF2
  rw [t10_design_law, t10_design_law]
  norm_num only [show (16/25+(1/4:ℝ)*(4/25)) = 17/25 from by norm_num,
    show (16/25+(1/2:ℝ)*(4/25)) = 18/25 from by norm_num]
  rw [hw1,hw2]
  have h := t10_spread_mixtures
  linarith

theorem simulation_invariance_corrected_proof (p₁ p₂ ρ lam σ : ℝ)
    (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hp₂ : 0 < p₂) (hp₂' : p₂ < 1)
    (hσ : 0 ≤ σ)
    (ha₀ : 0 ≤ 1-p₁-p₂+(p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂))))
    (ha₁ : p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)) ≤ p₁)
    (ha₂ : p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)) ≤ p₂)
    (ha : 0 ≤ p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂))) :
    (∀ (K d : ℕ) (μ ν : Measure (State K d)), Assumptions μ → Assumptions ν →
      ∀ a : Fin K, passingRate μ = passingRate ν → passerLaw μ a = passerLaw ν a →
        correctedBoundPair μ a = correctedBoundPair ν a) ∧
    (let a := p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂))
     let w₁ := 1-a/p₁
     let w₂ := 1-a/p₂
     let μ := simulationLaw p₁ p₂ ρ lam σ
     Assumptions μ ∧ (μ alwaysPass).toReal = a ∧ checkCorrelation μ 0 1 = ρ ∧
     passingRate μ 0 = p₁ ∧ passingRate μ 1 = p₂ ∧
     passerLaw μ 0 = ENNReal.ofReal (1-w₁) • gaussianReal 0 ⟨σ^2,sq_nonneg σ⟩ +
       ENNReal.ofReal w₁ • gaussianReal (-lam) ⟨σ^2,sq_nonneg σ⟩ ∧
     passerLaw μ 1 = ENNReal.ofReal (1-w₂) • gaussianReal 0 ⟨σ^2,sq_nonneg σ⟩ +
       ENNReal.ofReal w₂ • gaussianReal lam ⟨σ^2,sq_nonneg σ⟩ ∧
     eventMean μ observedY (passEvent ∩ armEvent 0) = -lam*w₁ ∧
     eventMean μ observedY (passEvent ∩ armEvent 1) = lam*w₂) ∧
    (lam ≠ 0 → ∀ ρ' : ℝ, ρ' ≠ ρ →
      -lam*(1-(p₁*p₂+ρ'*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)))/p₁) ≠
      -lam*(1-(p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)))/p₁) ∧
      lam*(1-(p₁*p₂+ρ'*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)))/p₂) ≠
      lam*(1-(p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)))/p₂)) ∧
    effectBoundWidth (simulationLaw (4/5) (4/5) (1/4) 1 1) ≠
      effectBoundWidth (simulationLaw (4/5) (4/5) (1/2) 1 1) := by
  refine ⟨?_, t10_simulation_certificate p₁ p₂ ρ lam σ hp₁ hp₁' hp₂ hp₂' hσ ha₀ ha₁ ha₂ ha,
    ?_, t10_width_inequality⟩
  · intro K d μ ν hμ hν a hp hF
    exact bounds_fixed_observables_actual μ ν hμ hν a hp hF
  · intro hlam ρ' hρ
    exact simulation_mean_formula_injective p₁ p₂ ρ ρ' lam hp₁ hp₁' hp₂ hp₂' hlam hρ

lemma t13_diagonal_measurable (s : Bool) :
    Measurable (fun ω : ℝ × Fin 2 =>
      ((![ω.1,ω.1], ![s,s], ω.2, fun _ => 0) : State 2 0)) := by
  fun_prop

lemma t13_diagonal_probability (s : Bool) :
    IsProbabilityMeasure (diagonalLaw s (gaussianReal 0 1)) := by
  unfold diagonalLaw
  infer_instance

local instance instT13DiagonalProbability (s : Bool) :
    IsProbabilityMeasure (diagonalLaw s (gaussianReal 0 1)) :=
  t13_diagonal_probability s

lemma t13_weights : (4/5 : ℝ≥0∞) + 1/5 = 1 := by
  rw [← ENNReal.add_div]
  norm_num only [show (4 + 1 : ℝ≥0∞) = 5 from by norm_num]
  exact ENNReal.div_self (by norm_num) (by norm_num)

lemma t13_probability : IsProbabilityMeasure normalCommonLaw := by
  constructor
  simpa only [normalCommonLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one] using t13_weights

local instance instT13Probability : IsProbabilityMeasure normalCommonLaw := t13_probability

lemma t13_diagonal_rect (s : Bool) (a : Fin 2)
    (U : Set (ℝ × Bool)) (V : Set (Fin 2))
    (hU : MeasurableSet U) (hV : MeasurableSet V) :
    diagonalLaw s (gaussianReal 0 1)
      ((fun ω => (potentialY a ω, potentialS a ω)) ⁻¹' U ∩ assignment ⁻¹' V) =
      gaussianReal 0 1 ((fun x => (x,s)) ⁻¹' U) * fairAssignment V := by
  rw [diagonalLaw, Measure.map_apply (t13_diagonal_measurable s)
    (((measurable_potentialY a).prodMk (measurable_potentialS a) hU).inter
      (measurable_assignment hV))]
  have he : (fun ω : ℝ × Fin 2 =>
      ((![ω.1,ω.1], ![s,s], ω.2, fun _ => 0) : State 2 0)) ⁻¹'
        ((fun ω => (potentialY a ω, potentialS a ω)) ⁻¹' U ∩ assignment ⁻¹' V) =
      ((fun x => (x,s)) ⁻¹' U) ×ˢ V := by
    ext ω
    fin_cases a <;> simp [potentialY, potentialS, assignment]
  rw [he, Measure.prod_prod]

lemma t13_rect (a : Fin 2) (U : Set (ℝ × Bool)) (V : Set (Fin 2))
    (hU : MeasurableSet U) (hV : MeasurableSet V) :
    normalCommonLaw
      ((fun ω => (potentialY a ω, potentialS a ω)) ⁻¹' U ∩ assignment ⁻¹' V) =
      ((4/5 : ℝ≥0∞) * gaussianReal 0 1 ((fun x => (x,true)) ⁻¹' U) +
        (1/5 : ℝ≥0∞) * gaussianReal 0 1 ((fun x => (x,false)) ⁻¹' U)) *
          fairAssignment V := by
  simp only [normalCommonLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    t13_diagonal_rect _ a U V hU hV]
  ring

lemma t13_pair_mass (a : Fin 2) (U : Set (ℝ × Bool)) (hU : MeasurableSet U) :
    normalCommonLaw ((fun ω => (potentialY a ω, potentialS a ω)) ⁻¹' U) =
      (4/5 : ℝ≥0∞) * gaussianReal 0 1 ((fun x => (x,true)) ⁻¹' U) +
        (1/5 : ℝ≥0∞) * gaussianReal 0 1 ((fun x => (x,false)) ⁻¹' U) := by
  simpa using t13_rect a U univ hU MeasurableSet.univ

lemma t13_assignment_mass (V : Set (Fin 2)) (hV : MeasurableSet V) :
    normalCommonLaw (assignment ⁻¹' V) = fairAssignment V := by
  have h := t13_rect 0 univ V MeasurableSet.univ hV
  simpa only [preimage_univ, univ_inter, measure_univ, mul_one, t13_weights, one_mul] using h

lemma t13_ignorability : Ignorability normalCommonLaw := by
  constructor
  · intro a
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro U V hU hV
    rw [t13_rect a U V hU hV, t13_pair_mass a U hU, t13_assignment_mass V hV]
  · intro a
    change 0 < normalCommonLaw (assignment ⁻¹' {a})
    rw [t13_assignment_mass _ (measurableSet_singleton a), t10_fair_singleton]
    norm_num

lemma t13_potential_mass (a : Fin 2) : normalCommonLaw (potentialPass a) = 4/5 := by
  have h := t13_pair_mass a (univ ×ˢ {true})
    (MeasurableSet.univ.prod (measurableSet_singleton true))
  have he : (fun ω : State 2 0 => (potentialY a ω, potentialS a ω)) ⁻¹'
      (univ ×ˢ {true}) = potentialPass a := by ext ω; simp [potentialPass]
  rw [he] at h
  simpa using h

lemma t13_rates (a : Fin 2) : passingRate normalCommonLaw a = 4/5 := by
  have h := (nonzero_passing_corrected normalCommonLaw t13_probability t13_ignorability).1 a
  rw [h, t13_potential_mass]
  norm_num

lemma t13_assumptions : Assumptions normalCommonLaw := by
  refine ⟨t13_probability, t13_ignorability, ?_⟩
  intro a
  rw [t13_rates]
  norm_num

lemma t13_diagonal_outcome (s : Bool) (a : Fin 2) :
    (diagonalLaw s (gaussianReal 0 1)).map (potentialY a) = gaussianReal 0 1 := by
  rw [diagonalLaw, Measure.map_map (measurable_potentialY a) (t13_diagonal_measurable s)]
  have he : (potentialY a) ∘ (fun ω : ℝ × Fin 2 =>
      ((![ω.1,ω.1], ![s,s], ω.2, fun _ => 0) : State 2 0)) = Prod.fst := by
    funext ω
    fin_cases a <;> rfl
  rw [he, Measure.map_fst_prod]
  simp

lemma t13_diagonal_observed (s : Bool) :
    (diagonalLaw s (gaussianReal 0 1)).map observedY = gaussianReal 0 1 := by
  rw [diagonalLaw, Measure.map_map measurable_observedY (t13_diagonal_measurable s)]
  have he : observedY ∘ (fun ω : ℝ × Fin 2 =>
      ((![ω.1,ω.1], ![s,s], ω.2, fun _ => 0) : State 2 0)) = Prod.fst := by
    funext ⟨x,z⟩
    fin_cases z <;> rfl
  rw [he, Measure.map_fst_prod]
  simp

lemma t13_outcome (a : Fin 2) :
    normalCommonLaw.map (potentialY a) = gaussianReal 0 1 := by
  rw [normalCommonLaw, Measure.map_add, Measure.map_smul, Measure.map_smul,
    t13_diagonal_outcome, t13_diagonal_outcome, ← add_smul, t13_weights, one_smul]
  all_goals fun_prop

lemma t13_observed : normalCommonLaw.map observedY = gaussianReal 0 1 := by
  rw [normalCommonLaw, Measure.map_add, Measure.map_smul, Measure.map_smul,
    t13_diagonal_observed, t13_diagonal_observed, ← add_smul, t13_weights, one_smul]
  all_goals fun_prop

lemma t13_diagonal_all_mass (s : Bool) :
    diagonalLaw s (gaussianReal 0 1) alwaysPass = if s then 1 else 0 := by
  rw [diagonalLaw, Measure.map_apply (t13_diagonal_measurable s) measurableSet_always]
  have he : (fun ω : ℝ × Fin 2 =>
      ((![ω.1,ω.1], ![s,s], ω.2, fun _ => 0) : State 2 0)) ⁻¹' alwaysPass =
        if s then univ else ∅ := by
    cases s <;> ext ω <;> simp [alwaysPass, potentialS, Fin.forall_fin_two]
  rw [he]
  cases s <;> simp

lemma t13_all_mass : normalCommonLaw alwaysPass = 4/5 := by
  simp [normalCommonLaw, Measure.add_apply, Measure.smul_apply, t13_diagonal_all_mass]

lemma t13_passer_map (a : Fin 2) :
    (normalCommonLaw.restrict (potentialPass a)).map (potentialY a) =
      (4/5 : ℝ≥0∞) • gaussianReal 0 1 := by
  ext U hU
  rw [Measure.map_apply (measurable_potentialY a) hU,
    Measure.restrict_apply ((measurable_potentialY a) hU), Measure.smul_apply]
  have he : (potentialY (d := 0) a) ⁻¹' U ∩ potentialPass a =
      (fun ω => (potentialY a ω, potentialS a ω)) ⁻¹' (U ×ˢ {true}) := by
    ext ω
    simp [potentialPass]
  rw [he, t13_pair_mass a _ (hU.prod (measurableSet_singleton true))]
  simp

lemma t13_passer (a : Fin 2) : passerLaw normalCommonLaw a = gaussianReal 0 1 := by
  rw [← conditional_law_consistency normalCommonLaw t13_assumptions a,
    eventLaw, t13_potential_mass, t13_passer_map, smul_smul,
    ENNReal.inv_mul_cancel (ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩) (by finiteness), one_smul]

lemma t13_trim : trimRatio normalCommonLaw 0 = 1/4 := by
  norm_num [trimRatio, Fin.sum_univ_two, t13_rates]

lemma t13_all_mean : eventMean normalCommonLaw (potentialY 0) alwaysPass = 0 := by
  have he : (normalCommonLaw.restrict alwaysPass).map (potentialY 0) =
      (4/5 : ℝ≥0∞) • gaussianReal 0 1 := by
    ext U hU
    rw [Measure.map_apply (measurable_potentialY 0) hU,
      Measure.restrict_apply ((measurable_potentialY 0) hU),
      normalCommonLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    have hd (s : Bool) : diagonalLaw s (gaussianReal 0 1)
        ((potentialY 0) ⁻¹' U ∩ alwaysPass) = if s then gaussianReal 0 1 U else 0 := by
      rw [diagonalLaw, Measure.map_apply (t13_diagonal_measurable s)
        (((measurable_potentialY 0) hU).inter measurableSet_always)]
      have he' : (fun ω : ℝ × Fin 2 =>
          ((![ω.1,ω.1], ![s,s], ω.2, fun _ => 0) : State 2 0)) ⁻¹'
          ((potentialY 0) ⁻¹' U ∩ alwaysPass) = if s then U ×ˢ univ else ∅ := by
        cases s <;> ext ω <;> simp [alwaysPass, potentialS, potentialY, Fin.forall_fin_two]
      rw [he']
      cases s <;> simp [Measure.prod_prod]
    simp [hd]
  unfold eventMean
  have hi := integral_map (μ := normalCommonLaw.restrict alwaysPass)
    (measurable_potentialY 0).aemeasurable measurable_id.aestronglyMeasurable
  rw [he, integral_smul_measure] at hi
  simp only [id_eq, integral_id_gaussianReal, smul_zero] at hi
  rw [← hi]
  simp

local instance instT13NormalNullSingleton : NullSingletonClass (gaussianReal 0 1) :=
  nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)

lemma t13_atomless : Atomless (normalCommonLaw.map observedY) := by
  rw [t13_observed]
  intro x
  exact measure_singleton x

lemma t13_support : FullRealSupport normalCommonLaw observedY := by
  intro l u hlu
  change 0 < normalCommonLaw (observedY ⁻¹' Ioo l u)
  rw [← Measure.map_apply measurable_observedY measurableSet_Ioo, t13_observed]
  rw [pos_iff_ne_zero]
  intro hzero
  have hv := (gaussianReal_absolutelyContinuous' 0
    (by norm_num : (1 : NNReal) ≠ 0)) hzero
  rw [Real.volume_Ioo] at hv
  exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hlu)).ne' hv

/-- The source EReal quantile is the unique finite Gaussian CDF inverse. -/
lemma t13_quantile (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ q : ℝ, quantile (gaussianReal 0 1) p = q ∧ cdf (gaussianReal 0 1) q = p := by
  obtain ⟨q,hq⟩ := AronowAudit.P053.NormalCompletion.exists_cdf_eq
    (gaussianReal 0 1) hp0 hp1
  refine ⟨q, ?_, hq⟩
  have he : {x : EReal | p ≤ (gaussianReal 0 1 {y : ℝ | (y : EReal) ≤ x}).toReal} =
      Ici (q : EReal) := by
    ext x
    cases x using EReal.rec with
    | bot => simp [not_le.mpr hp0]
    | top => simp [hp1.le]
    | coe x =>
      simp only [EReal.coe_le_coe_iff, mem_setOf_eq, mem_Ici]
      change (p ≤ (gaussianReal 0 1).real (Iic x)) ↔ q ≤ x
      rw [← cdf_eq_real, ← hq]
      exact AronowAudit.P053.NormalCompletion.strictMono_normal_cdf.le_iff_le
  rw [quantile, he, csInf_Ici]

lemma t13_quantile_mass (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (gaussianReal 0 1 (Iic ((quantile (gaussianReal 0 1) p).toReal))).toReal = p ∧
      (gaussianReal 0 1 (Ici ((quantile (gaussianReal 0 1) p).toReal))).toReal = 1-p := by
  obtain ⟨q,hq,hcdf⟩ := t13_quantile p hp0 hp1
  rw [hq, EReal.toReal_coe]
  have hl : (gaussianReal 0 1 (Iic q)).toReal = p := by
    simpa only [cdf_eq_real, measureReal_def] using hcdf
  refine ⟨hl, ?_⟩
  have h := measureReal_add_measureReal_compl (μ := gaussianReal 0 1)
    (s := Iic q) measurableSet_Iic
  simp only [compl_Iic, measureReal_def, measure_univ, ENNReal.toReal_one] at h
  have he : gaussianReal 0 1 (Ioi q) = gaussianReal 0 1 (Ici q) :=
    measure_congr (Ioi_ae_eq_Ici' (measure_singleton q))
  rw [hl, he] at h
  linarith

lemma t13_pdf_deriv (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h := (((((hasDerivAt_id' x).pow 2).neg).div_const 2).exp).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  change HasDerivAt (fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y^2/2))
    (-x * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x^2/2))) x
  convert h using 1 <;> norm_num <;> ring

lemma t13_pdf_limit : Tendsto (gaussianPDFReal 0 1) atTop (𝓝 0) := by
  have h := (Real.tendsto_exp_atBot.comp
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop_of_neg
      (by norm_num : (- (1/2 : ℝ)) < 0))).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  change Tendsto (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x^2/2))
    atTop (𝓝 0)
  convert h using 1
  · funext x
    congr 1
    congr 1
    ring
  · simp

lemma t13_pdf_weight_integrable :
    Integrable (fun x : ℝ => x * gaussianPDFReal 0 1 x) volume := by
  have h := (integrable_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert h using 1
  funext x
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [show -(x^2)/2 = -(1/2 : ℝ)*x^2 by ring]
  ring

lemma t13_upper_moment (q : ℝ) :
    (∫ x in Ici q, x ∂gaussianReal 0 1) = gaussianPDFReal 0 1 q := by
  have hd : ∀ x ∈ Ici q, HasDerivAt (fun y => -gaussianPDFReal 0 1 y)
      (x * gaussianPDFReal 0 1 x) x := by
    intro x _
    convert (t13_pdf_deriv x).neg using 1 <;> ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd
    t13_pdf_weight_integrable.integrableOn t13_pdf_limit.neg
  simp only [neg_zero, zero_sub, neg_neg] at h
  have he : (∫ x in Ioi q, x ∂gaussianReal 0 1) =
      ∫ x in Ioi q, x * gaussianPDFReal 0 1 x := by
    rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : NNReal) ≠ 0),
      setIntegral_withDensity_eq_setIntegral_toReal_smul
        (measurable_gaussianPDF 0 1) (ae_of_all _ (fun _ => gaussianPDF_lt_top))
        (fun x : ℝ => x) measurableSet_Ioi]
    simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), smul_eq_mul]
    congr 1
    funext x
    ring
  calc
    _ = ∫ x in Ioi q, x ∂gaussianReal 0 1 :=
      (setIntegral_congr_set (Ioi_ae_eq_Ici' (measure_singleton q))).symm
    _ = _ := he.trans h

lemma t13_lower_moment (q : ℝ) :
    (∫ x in Iic q, x ∂gaussianReal 0 1) = -gaussianPDFReal 0 1 q := by
  have hi : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable (by norm_num)
  have h := integral_add_compl (s := Iic q) measurableSet_Iic hi
  have hu : (∫ x in Ioi q, x ∂gaussianReal 0 1) = gaussianPDFReal 0 1 q := by
    calc
      _ = ∫ x in Ici q, x ∂gaussianReal 0 1 :=
        setIntegral_congr_set (Ioi_ae_eq_Ici' (measure_singleton q))
      _ = _ := t13_upper_moment q
  simp only [compl_Iic, hu, integral_id_gaussianReal] at h
  linarith

lemma t13_outcome_eventMean (a : Fin 2) (E : Set ℝ) (hE : MeasurableSet E) :
    eventMean normalCommonLaw (potentialY a) ((potentialY a) ⁻¹' E) =
      eventMean (gaussianReal 0 1) id E := by
  have hi := setIntegral_map (μ := normalCommonLaw) (g := potentialY a)
    hE measurable_id.aestronglyMeasurable (measurable_potentialY a).aemeasurable
  have hm := Measure.map_apply (μ := normalCommonLaw) (measurable_potentialY a) hE
  rw [t13_outcome] at hi hm
  simp only [id_eq] at hi
  unfold eventMean
  rw [← hi, ← hm]
  rfl

lemma t13_lower_tail_mean (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    let q := (quantile (gaussianReal 0 1) p).toReal
    eventMean normalCommonLaw (potentialY 0) {ω | potentialY 0 ω ≤ q} =
      -gaussianPDFReal 0 1 q / p := by
  dsimp only
  change eventMean normalCommonLaw (potentialY 0)
    ((potentialY 0) ⁻¹' Iic ((quantile (gaussianReal 0 1) p).toReal)) = _
  rw [t13_outcome_eventMean 0 _ measurableSet_Iic, eventMean]
  simp only [id_eq]
  rw [t13_lower_moment, (t13_quantile_mass p hp0 hp1).1]

lemma t13_upper_tail_mean (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    tailUpper (gaussianReal 0 1) p =
      gaussianPDFReal 0 1 ((quantile (gaussianReal 0 1) p).toReal) / (1-p) := by
  have hm := (t13_quantile_mass p hp0 hp1).2
  obtain ⟨q,hq,_⟩ := t13_quantile p hp0 hp1
  rw [hq, EReal.toReal_coe] at hm ⊢
  have he : {y : ℝ | quantile (gaussianReal 0 1) p ≤ (y : EReal)} = Ici q := by
    rw [hq]
    ext y
    simp
  rw [tailUpper, he, eventMean]
  simp only [id_eq]
  rw [t13_upper_moment, hm]

lemma t13_upper_bound : upperBound normalCommonLaw 0 =
    gaussianPDFReal 0 1 ((quantile (gaussianReal 0 1) (1/4)).toReal) / (3/4) := by
  rw [(passer_tail_mean_formula normalCommonLaw t13_assumptions 0).2,
    t13_passer, t13_trim, t13_upper_tail_mean (1/4) (by norm_num) (by norm_num)]
  norm_num

theorem lower_tail_upper_bound_counterexample_proof :
    Assumptions normalCommonLaw ∧ normalCommonLaw alwaysPass = 4/5 ∧
    Atomless (normalCommonLaw.map observedY) ∧ FullRealSupport normalCommonLaw observedY ∧
    (∀ a : Fin 2, passingRate normalCommonLaw a = 4/5 ∧
      passerLaw normalCommonLaw a = gaussianReal 0 1) ∧
    potentialTrim normalCommonLaw 0 = 1/4 ∧ trimRatio normalCommonLaw 0 = 1/4 ∧
    eventMean normalCommonLaw (potentialY 0) alwaysPass = 0 ∧
    eventMean normalCommonLaw (potentialY 0) (otherPass 0 ∩ potentialPass 0) = 0 ∧
    (let q := (quantile (gaussianReal 0 1) (3/4)).toReal
     eventMean normalCommonLaw (potentialY 0) {ω | potentialY 0 ω ≤ q} =
       -gaussianPDFReal 0 1 q / (3/4) ∧
     eventMean normalCommonLaw (potentialY 0) {ω | potentialY 0 ω ≤ q} < 0 ∧
     ¬ (eventMean normalCommonLaw (potentialY 0) alwaysPass ≤
       eventMean normalCommonLaw (potentialY 0) {ω | potentialY 0 ω ≤ q})) ∧
    upperBound normalCommonLaw 0 =
      gaussianPDFReal 0 1 ((quantile (gaussianReal 0 1) (1/4)).toReal) / (3/4) ∧
    0 < upperBound normalCommonLaw 0 := by
  have hl := t13_lower_tail_mean (3/4) (by norm_num) (by norm_num)
  have hd : 0 < gaussianPDFReal 0 1 ((quantile (gaussianReal 0 1) (3/4)).toReal) :=
    gaussianPDFReal_pos 0 1 _ (by norm_num)
  have hneg : eventMean normalCommonLaw (potentialY 0)
      {ω | potentialY 0 ω ≤ (quantile (gaussianReal 0 1) (3/4)).toReal} < 0 := by
    rw [hl]
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hd) (by norm_num)
  refine ⟨t13_assumptions, t13_all_mass, t13_atomless, t13_support,
    fun a => ⟨t13_rates a, t13_passer a⟩, ?_, t13_trim, t13_all_mean, ?_,
    ⟨hl, hneg, ?_⟩, t13_upper_bound, ?_⟩
  · rw [potential_trim_consistency normalCommonLaw t13_assumptions, t13_trim]
  · rw [← always_pass_focal, t13_all_mean]
  · rw [t13_all_mean]
    exact not_le.mpr hneg
  · rw [t13_upper_bound]
    exact div_pos (gaussianPDFReal_pos 0 1 _ (by norm_num)) (by norm_num)

end
end AronowAudit.P010.Wave1
