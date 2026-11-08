import SAP.P006b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P006b.WH.W1.P.T17_L3

open SAP.P006b MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

noncomputable section

lemma badAtom_nonneg (p : ℝ) (π : BinaryPolicy)
    (hp : 0 ≤ p ∧ p ≤ 1) (hπ : binaryFeasible π) (z : Bool × Bool) :
    0 ≤ coinMass p z.1 * coinMass (binaryRule π z.1) z.2 := by
  have hrule : 0 ≤ binaryRule π z.1 ∧ binaryRule π z.1 ≤ 1 := by
    cases z.1 with
    | false => exact ⟨hπ.1, hπ.2.1⟩
    | true => exact ⟨hπ.2.2.1, hπ.2.2.2⟩
  exact mul_nonneg ((AronowAudit.P006.coin_is_probability p hp).1 z.1)
    ((AronowAudit.P006.coin_is_probability (binaryRule π z.1) hrule).1 z.2)

lemma badLaw_atom (p : ℝ) (π : BinaryPolicy)
    (hp : 0 ≤ p ∧ p ≤ 1) (hπ : binaryFeasible π) (z : Bool × Bool) :
    binaryPopulationLaw p π {z} =
      ENNReal.ofReal (coinMass p z.1 * coinMass (binaryRule π z.1) z.2) := by
  classical
  simp [binaryPopulationLaw, Pi.single_apply, Finset.sum_ite_eq',
    Finset.mem_univ, badAtom_nonneg p π hp hπ]

lemma badLaw_probability_b (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    IsProbabilityMeasure (binaryPopulationLaw p (1,0)) := by
  rw [isProbabilityMeasure_iff]
  simp [binaryPopulationLaw, Fintype.sum_prod_type, Measure.add_apply,
    Measure.smul_apply, Measure.dirac_apply, Set.indicator_univ,
    binaryRule, coinMass]
  rw [← ENNReal.ofReal_add hp.1 (by linarith [hp.2])]
  norm_num

lemma badLaw_probability_s (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    IsProbabilityMeasure (binaryPopulationLaw p (0,1)) := by
  rw [isProbabilityMeasure_iff]
  simp [binaryPopulationLaw, Fintype.sum_prod_type, Measure.add_apply,
    Measure.smul_apply, Measure.dirac_apply, Set.indicator_univ,
    binaryRule, coinMass]
  rw [← ENNReal.ofReal_add hp.1 (by linarith [hp.2])]
  norm_num

lemma badLaw_integral (p : ℝ) (π : BinaryPolicy)
    (hp : 0 ≤ p ∧ p ≤ 1) (hπ : binaryFeasible π)
    (hprob : IsProbabilityMeasure (binaryPopulationLaw p π)) (f : Bool × Bool → ℝ) :
    (∫ z, f z ∂binaryPopulationLaw p π) =
      ∑ z : Bool × Bool,
        coinMass p z.1 * coinMass (binaryRule π z.1) z.2 * f z := by
  letI : IsProbabilityMeasure (binaryPopulationLaw p π) := hprob
  rw [integral_fintype (Integrable.of_finite : Integrable f (binaryPopulationLaw p π))]
  simp_rw [Measure.real_def, badLaw_atom p π hp hπ,
    ENNReal.toReal_ofReal (badAtom_nonneg p π hp hπ _), smul_eq_mul]

lemma badLaw_event_false_b (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (binaryPopulationLaw p (1,0) {z | z.2 = false}).toReal = p := by
  simp [binaryPopulationLaw, Fintype.sum_prod_type, Measure.add_apply,
    Measure.smul_apply, Measure.dirac_apply, binaryRule, coinMass,
    ENNReal.toReal_ofReal, hp.1, sub_nonneg.mpr hp.2]

lemma badLaw_event_false_s (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (binaryPopulationLaw p (0,1) {z | z.2 = false}).toReal = 1-p := by
  simp [binaryPopulationLaw, Fintype.sum_prod_type, Measure.add_apply,
    Measure.smul_apply, Measure.dirac_apply, binaryRule, coinMass,
    ENNReal.toReal_ofReal, hp.1, sub_nonneg.mpr hp.2]

lemma badLaw_restrict_integral (p : ℝ) (π : BinaryPolicy)
    (hp : 0 ≤ p ∧ p ≤ 1) (hπ : binaryFeasible π)
    (hprob : IsProbabilityMeasure (binaryPopulationLaw p π)) (f : Bool × Bool → ℝ) :
    (∫ z in {z | z.2 = false}, f z ∂binaryPopulationLaw p π) =
      ∑ z : Bool × Bool,
        coinMass p z.1 * coinMass (binaryRule π z.1) z.2 *
          (if z.2 = false then f z else 0) := by
  have hs : MeasurableSet {z : Bool × Bool | z.2 = false} := (Set.toFinite _).measurableSet
  rw [← integral_indicator hs]
  rw [badLaw_integral p π hp hπ hprob]
  simp [Set.indicator]

end
end SAP.P006b.WH.W1.P.T17_L3

open SAP.P006b
open SAP.P006b.WH.W1.P.T17_L3
open MeasureTheory
open scoped BigOperators ENNReal Topology

theorem SAP.P006b.WH.W1.T17_L3_proof : SAP.P006b.WH.W1.T17_L3 := by
  classical
  intro L hL
  let p := T17BadProbability L
  let y0 := T17BadY0 L
  let y1 := T17BadY1 L
  let F := binaryEndogenousTT p y0 y1
  let V := binaryActualWelfare p y0 y1
  have hLpos : 0 < L := by linarith
  have hp : 0 < p := by dsimp [p, T17BadProbability]; positivity
  have hp1 : p < 1 := by
    dsimp [p, T17BadProbability]
    have hd : 0 < 2*L-1 := by linarith
    rw [div_lt_one (by positivity)]
    nlinarith
  have hpc : 0 ≤ p ∧ p ≤ 1 := ⟨le_of_lt hp, le_of_lt hp1⟩
  have honeSub : 0 < 1-p := by linarith
  have hdenL : 0 < 2*L-1 := by linarith
  have hpL : p*L = 1/2 := by
    dsimp [p, T17BadProbability]
    field_simp [ne_of_gt hLpos]
    <;> ring
  have hfalse : y0 false = 1/(2*(1-p)) := by rfl
  have htrue : y0 true = -L := by rfl
  have hfalseMass : (1-p)*y0 false = 1/2 := by
    rw [hfalse]
    field_simp [ne_of_gt honeSub]
  have htrueMass : p*y0 true = -1/2 := by
    calc
      p*y0 true = p*(-L) := by rw [htrue]
      _ = -(p*L) := by ring
      _ = -1/2 := by rw [hpL]; norm_num
  have hmean : (1-p)*y0 false+p*y0 true=0 := by linarith
  have hy0pos : 0 < y0 false := by rw [hfalse]; positivity
  have hy1neg : y0 true < 0 := by rw [htrue]; linarith
  have hhet : binaryMarginalHeterogeneity p y0 = 1 := by
    simp [binaryMarginalHeterogeneity, hmean,
      abs_of_pos hy0pos, abs_of_neg hy1neg]
    nlinarith [hfalseMass, htrueMass]
  have hprobB : IsProbabilityMeasure (binaryPopulationLaw p (1,0)) :=
    badLaw_probability_b p hpc
  have hprobS : IsProbabilityMeasure (binaryPopulationLaw p (0,1)) :=
    badLaw_probability_s p hpc
  have hbfeas : binaryFeasible (1,0) := by norm_num [binaryFeasible]
  have hsfeas : binaryFeasible (0,1) := by norm_num [binaryFeasible]
  have hbbase : binarySelectedBaseline p y0 (1,0) = -L := by
    dsimp [binarySelectedBaseline, binaryUntreatedMass, binaryRule]
    rw [htrue]
    field_simp [ne_of_gt hp]
    <;> ring
  have hsbase : binarySelectedBaseline p y0 (0,1) = 1/(2*(1-p)) := by
    dsimp [binarySelectedBaseline, binaryUntreatedMass, binaryRule]
    rw [hfalse]
    field_simp [ne_of_gt honeSub]
    <;> ring
  have hFb : F (1,0) = (1-p)*L/2 := by
    change (∫ z, (binaryObserved y0 y1 z-binarySelectedBaseline p y0 (1,0)) * bit z.2
      ∂binaryPopulationLaw p (1,0)) = _
    rw [badLaw_integral p (1,0) hpc hbfeas hprobB]
    rw [hbbase]
    simp [Fintype.sum_prod_type, binaryObserved, binaryRule, coinMass,
      bit, y1, T17BadY1]
    field_simp [ne_of_gt honeSub]
    <;> ring
  have hFs : F (0,1) = -p/(2*(1-p)) := by
    change (∫ z, (binaryObserved y0 y1 z-binarySelectedBaseline p y0 (0,1)) * bit z.2
      ∂binaryPopulationLaw p (0,1)) = _
    rw [badLaw_integral p (0,1) hpc hsfeas hprobS]
    rw [hsbase]
    simp [Fintype.sum_prod_type, binaryObserved, binaryRule, coinMass,
      bit, y1, T17BadY1]
    field_simp [ne_of_gt honeSub]
    <;> ring
  have hVb : V (1,0) = -(1-p)*L/2-1/2 := by
    change (∫ z, binaryObserved y0 y1 z-y0 z.1 ∂binaryPopulationLaw p (1,0)) = _
    rw [badLaw_integral p (1,0) hpc hbfeas hprobB]
    simp [Fintype.sum_prod_type, binaryObserved, binaryRule, coinMass,
      bit, y1, T17BadY1]
    rw [hfalse]
    field_simp [ne_of_gt honeSub]
    <;> ring_nf
    <;> norm_num
  have hVs : V (0,1) = 1/2 := by
    change (∫ z, binaryObserved y0 y1 z-y0 z.1 ∂binaryPopulationLaw p (0,1)) = _
    rw [badLaw_integral p (0,1) hpc hsfeas hprobS]
    simp [Fintype.sum_prod_type, binaryObserved, binaryRule, coinMass,
      bit, y1, T17BadY1, htrue]
    rw [hpL]
    norm_num
  have hbScorePos : 0 < F (1,0) := by rw [hFb]; positivity
  have hsScoreNeg : F (0,1) < 0 := by
    rw [hFs]
    have hpos : 0 < p/(2*(1-p)) := by positivity
    calc
      -p/(2*(1-p)) = -(p/(2*(1-p))) := by ring
      _ < 0 := neg_neg_of_pos hpos
  have hWcompare : V (1,0) ≤ V (0,1) := by
    rw [hVb, hVs]
    have hn : 0 ≤ (1-p)*L := mul_nonneg (by linarith [hp1]) (le_of_lt hLpos)
    nlinarith
  have hbest : IsBest T17BadPolicies F (1,0) := by
    refine ⟨by simp [T17BadPolicies], ?_⟩
    intro π hπ
    simp only [T17BadPolicies, Set.mem_insert_iff, Set.mem_singleton_iff] at hπ
    rcases hπ with rfl | rfl
    · rfl
    · linarith
  have hwbest : IsBest T17BadPolicies V (0,1) := by
    refine ⟨by simp [T17BadPolicies], ?_⟩
    intro π hπ
    simp only [T17BadPolicies, Set.mem_insert_iff, Set.mem_singleton_iff] at hπ
    rcases hπ with rfl | rfl
    · exact hWcompare
    · rfl
  have hbestiff : ∀ π, IsBest T17BadPolicies F π ↔ π = (1,0) := by
    intro π
    constructor
    · intro hh
      have hin : π ∈ T17BadPolicies := hh.1
      simp only [T17BadPolicies, Set.mem_insert_iff, Set.mem_singleton_iff] at hin
      rcases hin with h | h
      · exact h
      · subst π
        have hle := hh.2 (1,0) (by simp [T17BadPolicies])
        linarith
    · rintro rfl
      exact hbest
  have hreg : regret T17BadPolicies V (1,0) = L/2+3/4 := by
    rw [regret, bestValue_at hwbest, hVs, hVb]
    have hmul : (1-p)*L = L-1/2 := by
      calc
        (1-p)*L = L-p*L := by ring
        _ = L-1/2 := by rw [hpL]
    calc
      1/2 - (-(1-p)*L/2-1/2) = 1+((1-p)*L)/2 := by ring
      _ = 1+(L-1/2)/2 := by rw [hmul]
      _ = L/2+3/4 := by ring
  have heventB : (binaryPopulationLaw p (1,0) {z | z.2 = false}).toReal = p :=
    badLaw_event_false_b p hpc
  have heventS : (binaryPopulationLaw p (0,1) {z | z.2 = false}).toReal = 1-p :=
    badLaw_event_false_s p hpc
  have hnumB : (∫ z in {z | z.2 = false}, binaryObserved y0 y1 z
      ∂binaryPopulationLaw p (1,0)) = p*y0 true := by
    rw [badLaw_restrict_integral p (1,0) hpc hbfeas hprobB]
    simp [Fintype.sum_prod_type, Fintype.sum_bool, binaryObserved,
      binaryRule, coinMass]
  have hnumS : (∫ z in {z | z.2 = false}, binaryObserved y0 y1 z
      ∂binaryPopulationLaw p (0,1)) = (1-p)*y0 false := by
    rw [badLaw_restrict_integral p (0,1) hpc hsfeas hprobS]
    simp [Fintype.sum_prod_type, Fintype.sum_bool, binaryObserved,
      binaryRule, coinMass]
  have hmeanB : eventMean (binaryPopulationLaw p (1,0))
      {z | z.2 = false} (binaryObserved y0 y1) = binarySelectedBaseline p y0 (1,0) := by
    rw [eventMean, hnumB, heventB, hbbase]
    rw [htrue]
    field_simp [ne_of_gt hp]
  have hmeanS : eventMean (binaryPopulationLaw p (0,1))
      {z | z.2 = false} (binaryObserved y0 y1) = binarySelectedBaseline p y0 (0,1) := by
    rw [eventMean, hnumS, heventS, hsbase]
    rw [hfalse]
    field_simp [ne_of_gt honeSub]
  have hregime : ∀ π ∈ T17BadPolicies,
      binaryFeasible π ∧ IsProbabilityMeasure (binaryPopulationLaw p π) ∧
      0 < binaryUntreatedMass p π ∧
      (binaryPopulationLaw p π {z | z.2 = false}).toReal = binaryUntreatedMass p π ∧
      eventMean (binaryPopulationLaw p π) {z | z.2 = false} (binaryObserved y0 y1) =
        binarySelectedBaseline p y0 π := by
    intro π hπ
    simp only [T17BadPolicies, Set.mem_insert_iff, Set.mem_singleton_iff] at hπ
    rcases hπ with rfl | rfl
    · refine ⟨hbfeas, hprobB, ?_, ?_, hmeanB⟩
      · simpa [binaryUntreatedMass, binaryRule] using hp
      · rw [heventB]; simp [binaryUntreatedMass, binaryRule]
    · refine ⟨hsfeas, hprobS, ?_, ?_, hmeanS⟩
      · simpa [binaryUntreatedMass, binaryRule] using honeSub
      · rw [heventS]; simp [binaryUntreatedMass, binaryRule]
  change T17BadFamily L
  dsimp [T17BadFamily]
  exact ⟨hp, hp1, hmean, hhet, hregime, hbbase, hsbase, hFb, hFs,
    hbestiff, hwbest, hVs, hVb, hreg⟩
