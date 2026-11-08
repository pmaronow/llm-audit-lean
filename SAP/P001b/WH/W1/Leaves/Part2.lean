import SAP.P001b.WH.W1.Leaves.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001b.WH.W1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Classical Topology

noncomputable section

universe u v

local instance instDyadicLeavesPart2 : MeasurableSpace DyadicIndex := ⊤
local instance instGeometricLeavesPart2 : MeasurableSpace (ℕ × Bool) := ⊤

theorem uniform_probability : IsProbabilityMeasure W1Uniform := by
  constructor
  norm_num [W1Uniform]

theorem uniform_closed : Density W1Uniform closedUniformDensity := by
  have hf : closedUniformDensity = (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) := by
    ext x
    simp [closedUniformDensity, Set.indicator]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hf]
    exact (measurable_const.indicator measurableSet_Icc).aemeasurable
  · intro x
    simp only [closedUniformDensity]
    split_ifs <;> norm_num
  · rw [hf]
    apply IntegrableOn.integrable_indicator _ measurableSet_Icc
    exact integrableOn_const (by simp) (by simp)
  · have he : (fun x => ENNReal.ofReal (closedUniformDensity x)) =
        (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) := by
      ext x
      by_cases hx : x ∈ Set.Icc (0 : ℝ) 1 <;> simp [closedUniformDensity, hx]
    rw [he]
    exact (withDensity_indicator_one (μ := volume) measurableSet_Icc).symm

theorem uniform_open : Density W1Uniform openUniformDensity := by
  have hf : openUniformDensity = (Set.Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) := by
    ext x
    simp [openUniformDensity, Set.indicator]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hf]
    exact (measurable_const.indicator measurableSet_Ioo).aemeasurable
  · intro x
    simp only [openUniformDensity]
    split_ifs <;> norm_num
  · rw [hf]
    apply IntegrableOn.integrable_indicator _ measurableSet_Ioo
    exact integrableOn_const (by simp) (by simp)
  · have he : (fun x => ENNReal.ofReal (openUniformDensity x)) =
        (Set.Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) := by
      ext x
      by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1 <;> simp [openUniformDensity, hx]
    rw [he]
    exact (Measure.restrict_congr_set Ioo_ae_eq_Icc).symm.trans
      (withDensity_indicator_one (μ := volume) measurableSet_Ioo).symm


theorem binary_cell_split {Ω : Type u} {E : Type v} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (D : Ω → ℝ)
    (hX : Measurable X) (hD : Measurable D) (hb : ∀ ω, D ω = 0 ∨ D ω = 1) (x : E) :
    probability μ {ω | X ω = x} = W1JointMass μ X D 1 x + W1JointMass μ X D 0 x := by
  have hA : MeasurableSet {ω | X ω = x ∧ D ω = 1} :=
    (hX (measurableSet_singleton x)).inter (hD (measurableSet_singleton 1))
  have hB : MeasurableSet {ω | X ω = x ∧ D ω = 0} :=
    (hX (measurableSet_singleton x)).inter (hD (measurableSet_singleton 0))
  have hd : Disjoint {ω | X ω = x ∧ D ω = 1} {ω | X ω = x ∧ D ω = 0} := by
    apply Set.disjoint_left.mpr
    intro ω ha hb
    have : (1 : ℝ) = 0 := ha.2.symm.trans hb.2
    norm_num at this
  have he : {ω | X ω = x} =
      {ω | X ω = x ∧ D ω = 1} ∪ {ω | X ω = x ∧ D ω = 0} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    rcases hb ω with h | h <;> simp [h]
  unfold probability W1JointMass
  rw [he, measure_union hd hB, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  rfl

theorem discrete_overlap : W1DiscreteOverlap.{u, v} := by
  intro Ω E _ _ _ _ μ _ X D hX hD hb hD0 hD1
  let t := W1JointMass μ X D 1
  let c := W1JointMass μ X D 0
  have ht : ∀ x, 0 ≤ t x := fun _ => ENNReal.toReal_nonneg
  have hc : ∀ x, 0 ≤ c x := fun _ => ENNReal.toReal_nonneg
  have hq (x : E) : probability μ {ω | X ω = x} = t x + c x :=
    binary_cell_split μ X D hX hD hb x
  have hst : {x | 0 < W1ArmPMF μ X D 1 x} = {x | 0 < t x} := by
    ext x
    exact div_pos_iff_of_pos_right hD1
  have hsc : {x | 0 < W1ArmPMF μ X D 0 x} = {x | 0 < c x} := by
    ext x
    exact div_pos_iff_of_pos_right hD0
  have hp (x : E) (hx : 0 < probability μ {ω | X ω = x}) :
      W1CellPropensity μ X D x = t x / (t x + c x) := by
    rw [W1CellPropensity, ite_eq_left hx, hq]
  have hi : {x | 0 < W1ArmPMF μ X D 1 x} = {x | 0 < W1ArmPMF μ X D 0 x} ↔
      ∀ x, 0 < probability μ {ω | X ω = x} →
        0 < W1CellPropensity μ X D x ∧ W1CellPropensity μ X D x < 1 := by
    rw [hst, hsc, AronowAudit.P001.discrete_overlap_pointwise t c ht hc]
    constructor
    · intro h x hx
      rw [hp x hx]
      exact h x (by rwa [← hq])
    · intro h x hx
      have hxq : 0 < probability μ {ω | X ω = x} := by rwa [hq]
      simpa only [hp x hxq] using h x hxq
  refine ⟨?_, ?_, hi, ?_, ?_⟩
  · rw [hst]
    ext x
    constructor
    · intro hx
      change 0 < t x at hx
      have hxq : 0 < probability μ {ω | X ω = x} := by rw [hq]; linarith [hc x]
      exact ⟨hxq, by rw [hp x hxq]; exact div_pos hx (by rwa [← hq])⟩
    · rintro ⟨hxq, hx⟩
      rw [hp x hxq] at hx
      exact (div_pos_iff_of_pos_right (by rwa [← hq])).mp hx
  · rw [hsc]
    ext x
    constructor
    · intro hx
      change 0 < c x at hx
      have hxq : 0 < probability μ {ω | X ω = x} := by rw [hq]; linarith [ht x]
      refine ⟨hxq, ?_⟩
      rw [hp x hxq]
      exact (div_lt_one (by rwa [← hq])).mpr (by linarith)
    · rintro ⟨hxq, hx⟩
      rw [hp x hxq] at hx
      have hh := (div_lt_one (by rwa [← hq])).mp hx
      dsimp
      linarith
  · rintro ⟨ε, hε, hbound⟩
    apply hi.mpr
    intro x hx
    exact ⟨lt_trans hε (hbound x hx).1, by linarith [(hbound x hx).2]⟩
  · intro hfinite hover
    letI : Fintype {x // 0 < probability μ {ω | X ω = x}} := hfinite.fintype
    have hpoint := hi.mp hover
    obtain ⟨ε, hε, hbound⟩ := AronowAudit.P001.finite_overlap_uniform_bound
      (fun x : {x // 0 < probability μ {ω | X ω = x}} => W1CellPropensity μ X D x.val)
      (fun x => hpoint x.val x.property)
    exact ⟨ε, hε, fun x hx => hbound ⟨x, hx⟩⟩

theorem coherent_overlap : W1CoherentOverlap.{v} := by
  intro E t c a b ht hc ha hb
  have hst : {x | 0 < t x / a} = {x | 0 < t x} := by
    ext x
    exact div_pos_iff_of_pos_right ha
  have hsc : {x | 0 < c x / b} = {x | 0 < c x} := by
    ext x
    exact div_pos_iff_of_pos_right hb
  rw [hst, hsc]
  have hi := AronowAudit.P001.discrete_overlap_pointwise t c ht hc
  refine ⟨hi, ?_⟩
  rintro ⟨ε, hε, hbound⟩
  apply hi.mpr
  intro x hx
  exact ⟨lt_trans hε (hbound x hx).1, by linarith [(hbound x hx).2]⟩


theorem T20_assembly (h1 : T20_L1V2.{u, v}) (h2 : T20_L2V2.{u, v})
    (h3 : T20_L3V2) : T20WholeStatement.{u, v} := by
  refine ⟨?_, discrete_overlap, ?_, coherent_overlap⟩
  · intro Ω E _ _ μ _ X D hX hD hb hD0 hD1 p hp
    exact ⟨h1 μ X D hX hD hb hD0 hD1 p hp, h2 μ X D hX hD hb p hp⟩
  · obtain ⟨hsT, hsC, ht, hc, hpos, hno⟩ :=
      AronowAudit.P001.complete_overlap_without_uniform_positivity
    change Summable W1OverlapT at hsT
    change Summable W1OverlapC at hsC
    change (∑' k, W1OverlapT k) = 1 / 2 at ht
    change (∑' k, W1OverlapC k) = 1 / 2 at hc
    have hT (k : ℕ) : 0 < W1OverlapT k := (hpos k).1
    have hC (k : ℕ) : 0 < W1OverlapC k := (hpos k).2.1
    obtain ⟨hprob, hcells, hD0, hD1⟩ := h3
    letI : IsProbabilityMeasure W1GeometricLaw := hprob
    have hb (z : ℕ × Bool) : W1BinaryValue z.2 = 0 ∨ W1BinaryValue z.2 = 1 := by
      cases z.2 <;> simp [W1BinaryValue]
    have hq (k : ℕ) : probability W1GeometricLaw {z | z.1 = k} =
        W1OverlapT k + W1OverlapC k := by
      rw [binary_cell_split W1GeometricLaw Prod.fst (fun z => W1BinaryValue z.2)
        (measurable_of_countable _) (measurable_of_countable _) hb k,
        (hcells k).1, (hcells k).2]
    have hqpos (k : ℕ) : 0 < probability W1GeometricLaw {z | z.1 = k} := by
      rw [hq]
      exact add_pos (hT k) (hC k)
    have hp (k : ℕ) :
        W1CellPropensity W1GeometricLaw Prod.fst (fun z => W1BinaryValue z.2) k =
          AronowAudit.P001.overlapPropensity k := by
      rw [W1CellPropensity, ite_eq_left (hqpos k), hq k, (hcells k).1]
      rfl
    refine ⟨hsT, hsC, ht, hc, hprob, (fun _ => trivial), hcells, hD0, hD1, ?_, ?_, ?_, ?_⟩
    · exact Set.eq_univ_of_forall hqpos
    · apply Set.eq_univ_of_forall
      intro k
      change 0 < W1JointMass W1GeometricLaw Prod.fst (fun z => W1BinaryValue z.2) 1 k /
        probability W1GeometricLaw {z | W1BinaryValue z.2 = 1}
      rw [(hcells k).1, hD1]
      exact div_pos (hT k) (by norm_num)
    · apply Set.eq_univ_of_forall
      intro k
      change 0 < W1JointMass W1GeometricLaw Prod.fst (fun z => W1BinaryValue z.2) 0 k /
        probability W1GeometricLaw {z | W1BinaryValue z.2 = 0}
      rw [(hcells k).2, hD0]
      exact div_pos (hC k) (by norm_num)
    · rintro ⟨ε, hε, hbound⟩
      apply hno
      refine ⟨ε, hε, ?_⟩
      intro k
      simpa only [hp k] using hbound k


theorem electorate_counterexample : T21Statement := by
  obtain ⟨_, _, hcount, hmodel, hbounds, heffect, hD1, hm1, hm0, hci⟩ :=
    AronowAudit.P001.complete_coding_not_ignorability
  have hm1' : finiteConditionalMean voterMass observedVoteShare displayedGender 1 = 55 := hm1
  have hm0' : finiteConditionalMean voterMass observedVoteShare displayedGender 0 = 30 := hm0
  have hci' : ¬ FiniteConditionalIndependence voterMass
      (fun i => (potentialVoteShare 0 i, potentialVoteShare 1 i)) displayedGender
      (fun _ => (0 : ℝ)) := by
    simpa only [Bridge.voterMass_eq, Bridge.potentialVoteShare_eq, Bridge.displayedGender_eq,
      Bridge.finiteConditionalIndependence_eq] using hci
  refine ⟨AronowAudit.P001.binaryJoint.nonneg, AronowAudit.P001.binaryJoint.total,
    (fun _ => ⟨rfl, rfl, rfl⟩), hcount, hmodel, hbounds, ?_, heffect, hD1,
    ?_, ?_, ?_, ?_, ?_, hci', hm1', hm0', ?_, ?_, by norm_num⟩
  · intro i; fin_cases i <;>
      norm_num [observedVoteShare, potentialVoteShare, electorateType, displayedGender]
  · norm_num [finiteProbability, voterMass, displayedGender, Fin.sum_univ_succ]
  · norm_num [finiteConditionalMean, finiteProbability, voterMass, displayedGender, Fin.sum_univ_succ]
  · norm_num [finiteProbability, voterMass, potentialVoteShare, electorateType,
      displayedGender, Fin.sum_univ_succ]
  · norm_num [finiteProbability, voterMass, potentialVoteShare, electorateType, Fin.sum_univ_succ]
  · norm_num [finiteProbability, voterMass, potentialVoteShare, electorateType,
      displayedGender, Fin.sum_univ_succ]
  · rw [hm1', hm0']; norm_num
  · have heffect' : ∀ i, potentialVoteShare 1 i - potentialVoteShare 0 i = 5 := heffect
    simp only [finiteMean, heffect']
    norm_num [voterMass, Fin.sum_univ_succ]


theorem T22_assembly (h1 : T22_L1V2.{u, v}) (h2 : T22_L2V2.{u, v}) :
    T22WholeStatement.{u, v} := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨electorate_counterexample, ⟨fun _ d z => 20 + 40 * z + 5 * d, ?_⟩, ?_, ?_⟩
    · intro i d
      rfl
    · norm_num [finiteConditionalMean, finiteProbability, voterMass, displayedGender,
        Fin.sum_univ_succ]
    · norm_num [finiteConditionalMean, finiteProbability, voterMass, displayedGender,
        Fin.sum_univ_succ]
  · intro Ω E _ _ μ _ X hX D hD response hm0 hm1
    exact AronowAudit.P001.description_only_outcomes_conditional_independence
      μ X hX D hD response hm0 hm1
  · intro Ω E _ _ _ _ μ _ X hX Y0 Y1 D hY0 hY1 hD hi0 hi1 hb hpos hCI
    obtain ⟨hp, hm0, hm1⟩ := h1 μ X hX Y0 Y1 D hY0 hY1 hD hi0 hi1 hb
    obtain ⟨hmi0, hmi1⟩ := h2 μ X hX Y0 Y1 D hY0 hY1 hD hi0 hi1 hb hpos
    obtain ⟨ε, hε, hbound⟩ := hpos
    let δ : ℝ := min ε (1 / 4)
    have hδ : 0 < δ := lt_min hε (by norm_num)
    have hδε : δ ≤ ε := min_le_left _ _
    have hδquarter : δ ≤ 1 / 4 := min_le_right _ _
    have hpall (ω : Ω) :
        δ < W1CellPropensity μ X D (X ω) ∧ W1CellPropensity μ X D (X ω) < 1 - δ := by
      by_cases hx : 0 < probability μ {z | X z = X ω}
      · constructor <;> linarith [(hbound (X ω) hx).1, (hbound (X ω) hx).2]
      · simp only [W1CellPropensity, ite_eq_right hx]
        constructor <;> linarith
    have heq := AronowAudit.P001.Wave1.explicit_ignorability_discrete_ate_proof
      μ X hX Y0 Y1 D hY0 hY1 hD hi0 hi1 hb (W1CellPropensity μ X D) hp δ hδ hpall hCI
      (W1ArmMean μ X Y0 Y1 D 0) (W1ArmMean μ X Y0 Y1 D 1) hm0 hm1 hmi0 hmi1
    have hs0 := (AronowAudit.P001.Wave1.MarDiscrete.n1_proof
      μ X hX (W1ArmMean μ X Y0 Y1 D 0) hmi0).1
    have hs1 := (AronowAudit.P001.Wave1.MarDiscrete.n1_proof
      μ X hX (W1ArmMean μ X Y0 Y1 D 1) hmi1).1
    exact ⟨hs0, hs1, heq⟩


end
end SAP.P001b.WH.W1
