import SAP.P011b.WH.W1.P.T15_L1.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b.WH.W1.P.T15_L1

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

def leafWitness (upper : Bool) (s : Fin 3 → Bool) : Fin 3 → Fin 4 :=
  fun j => ⟨if s j then 0 else leafThreshold upper j,
    by have h := leafThreshold_lt_four upper j; split_ifs <;> omega⟩

lemma leafWitness_matches (upper : Bool) (s : Fin 3 → Bool) :
    leafMatches upper s (leafWitness upper s) := by
  intro j
  have hstar : AronowAudit.P011.starLeaves upper (leafWitness upper s) j =
      (if (leafWitness upper s j).val < leafThreshold upper j then (1 : ℝ) else 0) := by
    rfl
  rw [hstar]
  by_cases hs : s j
  · have hp := leafThreshold_pos upper j
    simp [leafWitness, hs, hp]
  · simp [leafWitness, hs]
  all_goals rfl

lemma leafPattern_count_pos (upper : Bool) (s : Fin 3 → Bool) :
    0 < ∑ u : Fin 3 → Fin 4,
      if leafMatches upper s u then (1 : ℝ) else 0 := by
  have hw := leafWitness_matches upper s
  have hnonneg (u : Fin 3 → Fin 4) :
      0 ≤ (if leafMatches upper s u then (1 : ℝ) else 0) := by
    split_ifs <;> positivity
  have hle : (1 : ℝ) ≤ ∑ u : Fin 3 → Fin 4,
      if leafMatches upper s u then (1 : ℝ) else 0 := by
    calc
      1 = (if leafMatches upper s (leafWitness upper s) then 1 else 0) := by simp [hw]
      _ ≤ ∑ u : Fin 3 → Fin 4, if leafMatches upper s u then (1 : ℝ) else 0 :=
        Finset.single_le_sum (fun u _ => hnonneg u) (Finset.mem_univ _)
  linarith

lemma leafPattern_probability_pos (upper : Bool) (s : Fin 3 → Bool) :
    0 < SAP.P011b.probability (SAP.P011b.starModel upper 1)
      (SAP.P011b.w1LeafEvent s) := by
  have hE : MeasurableSet (SAP.P011b.w1LeafEvent s) := by
    simp only [SAP.P011b.w1LeafEvent, Set.setOf_forall]
    exact MeasurableSet.iInter fun j => measurableSet_eq_fun (measurable_pi_apply j.succ)
      measurable_const
  rw [probability_count upper _ hE, leafPattern_count]
  have hc : 0 < (Fintype.card StarSource : ℝ) := by
    norm_num [StarSource, Fintype.card_prod, Fintype.card_fun]
  have hsum := leafPattern_count_pos upper s
  positivity

def leafSourceCount (upper : Bool) (s : Fin 3 → Bool) : ℝ :=
  ∑ a : StarSource,
    if sourceObs upper a ∈ SAP.P011b.w1LeafEvent s then (1 : ℝ) else 0

def jointSourceCount (upper : Bool) (s : Fin 3 → Bool) : ℝ :=
  ∑ a : StarSource,
    if sourceObs upper a ∈ ({y | y 0 = 1} ∩ SAP.P011b.w1LeafEvent s) then
      (1 : ℝ) else 0

lemma center_pattern_count (upper : Bool) (s : Fin 3 → Bool) :
    jointSourceCount upper s =
      SAP.P011b.w1CenterProb upper (fun j => if s j then 1 else 0) *
        leafSourceCount upper s := by
  classical
  let bits : Fin 3 → ℝ := fun j => if s j then (1 : ℝ) else 0
  let q := SAP.P011b.w1CenterProb upper bits
  have h48 : (if upper then (18 : ℝ) else 33) +
      4 * ∑ j : Fin 3, bits j = 48 * q := by
    cases upper <;> simp [q, bits, SAP.P011b.w1CenterProb, Fin.sum_univ_succ] <;> ring
  have hcenter (u : Fin 3 → Fin 4) (hu : leafMatches upper s u) :
      (∑ v : Fin 48, AronowAudit.P011.starBlock upper u v 0) = 48 * q := by
    rw [AronowAudit.P011.BlockOLSCompletion.star_center_sum]
    have hsum : (∑ j : Fin 3, AronowAudit.P011.starLeaves upper u j) =
        ∑ j : Fin 3, bits j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hu j
    rw [hsum]
    exact h48
  have hterm (u : Fin 3 → Fin 4) (v : Fin 48) :
      (if sourceObs upper (u, v) ∈
          ({y | y 0 = 1} ∩ SAP.P011b.w1LeafEvent s) then (1 : ℝ) else 0) =
        (if leafMatches upper s u then AronowAudit.P011.starBlock upper u v 0 else 0) := by
    have hleaf : sourceObs upper (u, v) ∈ SAP.P011b.w1LeafEvent s ↔
        leafMatches upper s u := source_leaf_event_iff upper s (u, v)
    change (if (sourceObs upper (u, v) 0 = 1 ∧
        sourceObs upper (u, v) ∈ SAP.P011b.w1LeafEvent s) then (1 : ℝ) else 0) = _
    rw [hleaf]
    by_cases hu : leafMatches upper s u
    · simp [sourceObs, hu, AronowAudit.P011.starBlock]
    · simp [hu]
  have hinner (u : Fin 3 → Fin 4) :
      (∑ v : Fin 48,
        if leafMatches upper s u then AronowAudit.P011.starBlock upper u v 0 else 0) =
      if leafMatches upper s u then 48 * q else 0 := by
    by_cases hu : leafMatches upper s u
    · simp [hu, hcenter u hu]
    · simp [hu]
  unfold jointSourceCount leafSourceCount
  rw [Fintype.sum_prod_type]
  simp_rw [hterm, hinner]
  calc
    (∑ u : Fin 3 → Fin 4, if leafMatches upper s u then 48 * q else 0) =
        (48 * q) * ∑ u : Fin 3 → Fin 4,
          if leafMatches upper s u then (1 : ℝ) else 0 := by
      calc
        (∑ u : Fin 3 → Fin 4, if leafMatches upper s u then 48 * q else 0) =
            ∑ u : Fin 3 → Fin 4,
              (48 * q) * (if leafMatches upper s u then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro u hu
          by_cases hp : leafMatches upper s u <;> simp [hp]
        _ = (48 * q) * ∑ u : Fin 3 → Fin 4,
            if leafMatches upper s u then (1 : ℝ) else 0 := by rw [Finset.mul_sum]
    _ = q * (48 * ∑ u : Fin 3 → Fin 4,
            if leafMatches upper s u then (1 : ℝ) else 0) := by ring
    _ = q * leafSourceCount upper s := by
      rw [← leafPattern_count]
      rfl

lemma leaf_probability_formula (upper : Bool) (s : Fin 3 → Bool) :
    SAP.P011b.probability (SAP.P011b.starModel upper 1)
      (SAP.P011b.w1LeafEvent s) =
      (Fintype.card StarSource : ℝ)⁻¹ * leafSourceCount upper s := by
  have hE : MeasurableSet (SAP.P011b.w1LeafEvent s) := by
    simp only [SAP.P011b.w1LeafEvent, Set.setOf_forall]
    exact MeasurableSet.iInter fun j => measurableSet_eq_fun (measurable_pi_apply j.succ)
      measurable_const
  simpa [leafSourceCount] using probability_count upper _ hE

lemma joint_probability_formula (upper : Bool) (s : Fin 3 → Bool) :
    SAP.P011b.probability (SAP.P011b.starModel upper 1)
      ({y | y 0 = 1} ∩ SAP.P011b.w1LeafEvent s) =
      (Fintype.card StarSource : ℝ)⁻¹ * jointSourceCount upper s := by
  have hE : MeasurableSet ({y : Fin 4 → ℝ | y 0 = 1} ∩ SAP.P011b.w1LeafEvent s) := by
    have hc : MeasurableSet {y : Fin 4 → ℝ | y 0 = 1} := by measurability
    have hl : MeasurableSet (SAP.P011b.w1LeafEvent s) := by
      simp only [SAP.P011b.w1LeafEvent, Set.setOf_forall]
      exact MeasurableSet.iInter fun j => measurableSet_eq_fun (measurable_pi_apply j.succ)
        measurable_const
    exact hc.inter hl
  simpa [jointSourceCount] using probability_count upper _ hE

lemma conditional_center_formula (upper : Bool) (s : Fin 3 → Bool) :
    SAP.P011b.probability (SAP.P011b.starModel upper 1)
      ({y | y 0 = 1} ∩ SAP.P011b.w1LeafEvent s) /
      SAP.P011b.probability (SAP.P011b.starModel upper 1)
        (SAP.P011b.w1LeafEvent s) =
      SAP.P011b.w1CenterProb upper (fun j => if s j then 1 else 0) := by
  rw [joint_probability_formula, leaf_probability_formula, center_pattern_count]
  have hpos := leafPattern_probability_pos upper s
  have hcard : 0 < (Fintype.card StarSource : ℝ)⁻¹ := by
    positivity
  have hden : 0 < (Fintype.card StarSource : ℝ)⁻¹ * leafSourceCount upper s := by
    rw [← leaf_probability_formula]
    exact hpos
  apply (div_eq_iff (ne_of_gt hden)).2
  ring

lemma center_probability_bounds (upper : Bool) (s : Fin 3 → Bool) :
    (if upper then (3/8 : ℝ) else 11/16) ≤
        SAP.P011b.w1CenterProb upper (fun j => if s j then 1 else 0) ∧
      SAP.P011b.w1CenterProb upper (fun j => if s j then 1 else 0) ≤
        (if upper then (5/8 : ℝ) else 15/16) := by
  let b : Fin 3 → ℝ := fun j => if s j then 1 else 0
  have hb (j : Fin 3) : 0 ≤ b j ∧ b j ≤ 1 := by
    dsimp [b]
    split_ifs <;> norm_num
  cases upper with
  | false =>
      have hlo : (-3/4 : ℝ) ≤ ∑ j : Fin 3, (b j - (1/4 : ℝ)) := by
        calc
          (-3/4 : ℝ) = ∑ j : Fin 3, (-(1/4 : ℝ)) := by norm_num [Fin.sum_univ_succ]
          _ ≤ ∑ j : Fin 3, (b j - (1/4 : ℝ)) :=
            Finset.sum_le_sum fun j _ => by linarith [(hb j).1]
      have hhi : ∑ j : Fin 3, (b j - (1/4 : ℝ)) ≤ 9/4 := by
        calc
          ∑ j : Fin 3, (b j - (1/4 : ℝ)) ≤
              ∑ j : Fin 3, (1 - (1/4 : ℝ)) :=
            Finset.sum_le_sum fun j _ => by linarith [(hb j).2]
          _ = (9/4 : ℝ) := by norm_num [Fin.sum_univ_succ]
      change 11/16 ≤ 3/4 + (∑ j : Fin 3, (b j - (1/4 : ℝ)))/12 ∧
        3/4 + (∑ j : Fin 3, (b j - (1/4 : ℝ)))/12 ≤ 15/16
      constructor <;> nlinarith
  | true =>
      have hlo : (-3/2 : ℝ) ≤
          ∑ j : Fin 3, (b j - (![3/4, 1/4, 1/2] : Fin 3 → ℝ) j) := by
        calc
          (-3/2 : ℝ) = ∑ j : Fin 3, -((![3/4, 1/4, 1/2] : Fin 3 → ℝ) j) := by
            norm_num [Fin.sum_univ_succ]
          _ ≤ ∑ j : Fin 3, (b j - (![3/4, 1/4, 1/2] : Fin 3 → ℝ) j) :=
            Finset.sum_le_sum fun j _ => by linarith [(hb j).1]
      have hhi :
          ∑ j : Fin 3, (b j - (![3/4, 1/4, 1/2] : Fin 3 → ℝ) j) ≤ 3/2 := by
        calc
          ∑ j : Fin 3, (b j - (![3/4, 1/4, 1/2] : Fin 3 → ℝ) j) ≤
              ∑ j : Fin 3, (1 - (![3/4, 1/4, 1/2] : Fin 3 → ℝ) j) :=
            Finset.sum_le_sum fun j _ => by linarith [(hb j).2]
          _ = (3/2 : ℝ) := by norm_num [Fin.sum_univ_succ]
      change 3/8 ≤ 1/2 +
          (∑ j : Fin 3, (b j - (![3/4, 1/4, 1/2] : Fin 3 → ℝ) j))/12 ∧
        1/2 + (∑ j : Fin 3, (b j - (![3/4, 1/4, 1/2] : Fin 3 → ℝ) j))/12 ≤ 5/8
      constructor <;> nlinarith

end
end SAP.P011b.WH.W1.P.T15_L1

theorem SAP.P011b.WH.W1.T15_L1_proof : SAP.P011b.WH.W1.T15_L1 := by
  change SAP.P011b.W1StarBlockLaw
  intro upper
  refine ⟨SAP.P011b.WH.W1.P.T15_L1.observed_leaf_indep upper,
    ?_, ?_⟩
  · exact SAP.P011b.WH.W1.P.T15_L1.marginal_probability upper
  · intro s
    have hp := SAP.P011b.WH.W1.P.T15_L1.leafPattern_probability_pos upper s
    have hq := SAP.P011b.WH.W1.P.T15_L1.conditional_center_formula upper s
    have hb := SAP.P011b.WH.W1.P.T15_L1.center_probability_bounds upper s
    exact ⟨hp, hq, hb.1, hb.2⟩
