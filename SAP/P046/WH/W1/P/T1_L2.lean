import SAP.P046.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace SAP.P046.WH.W1.P.T1_L2

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

theorem failure_iff (hRed : WholeT1Reductions) {a : Sample 100}
    (ha : ∀ i, (a i).2.2 = (false, decide ((a i).1 ≤ (3 / 5 : ℝ)))) :
    (printedRadius IntervalExample.study (1 / 10000000) a <
      |ht IntervalExample.study a - mu IntervalExample.study|) ↔
      Real.log 20000000 < wholeCountThreshold (wholeK a) (wholeS a) := by
  have hfeas := counts_feasible a
  have hred := hRed a ha
  have hex := count_exclusion (wholeK a) (wholeS a) hfeas.1 hfeas.2
  have hrad : printedRadius IntervalExample.study (1 / 10000000) a =
      Real.sqrt (IntervalExample.xiK (wholeK a) * Real.log 20000000 / 200) := by
    simp only [printedRadius]
    rw [hred.2.2]
    have harg : (2 : ℝ) / (1 / 10000000) = 20000000 := by norm_num
    rw [harg]
    congr 1
    norm_num
  have habs : |((wholeS a : ℝ) - 39) / 65| =
      |(wholeS a : ℝ) / 65 - 3 / 5| := by
    congr 1
    ring
  rw [hrad, hred.2.1, habs]
  exact hex.2.1.trans hex.2.2

end

end SAP.P046.WH.W1.P.T1_L2

open SAP.P046 SAP.P046.WH.W1 SAP.P046.WH.W1.P.T1_L2
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

theorem SAP.P046.WH.W1.T1_L2_proof : SAP.P046.WH.W1.T1_L2 := by
  classical
  intro hRed hLaw
  have hM := Bridge.target1.1
  letI := hM.probability
  let P : Measure (Sample 100) := sampleLaw IntervalExample.study 100
  have hsupp : ∀ᵐ a ∂P,
      ∀ i, (a i).2.2 = (false, decide ((a i).1 ≤ (3 / 5 : ℝ))) := by
    change ∀ᵐ a ∂sampleLaw IntervalExample.study 100, _
    exact AronowAudit.P046.Wave1.PropositionThree.n6_proof
  let D : Finset (Sigma (fun _ : ℕ => ℕ)) :=
    (range 101).sigma (fun k =>
      (range (k + 1)).filter (fun s =>
        Real.log 20000000 < wholeCountThreshold k s))
  have hDdef : D = (range 101).sigma (fun k =>
      (range (k + 1)).filter (fun s =>
        Real.log 20000000 < wholeCountThreshold k s)) := rfl
  let E : Sigma (fun _ : ℕ => ℕ) → Set (Sample 100) :=
    fun q => {a | wholeK a = q.1 ∧ wholeS a = q.2}
  have hD (q : Sigma (fun _ : ℕ => ℕ)) (hq : q ∈ D) :
      q.1 ≤ 100 ∧ q.2 ≤ q.1 ∧
        Real.log 20000000 < wholeCountThreshold q.1 q.2 := by
    rw [hDdef] at hq
    simp only [mem_sigma, mem_range, mem_filter] at hq
    exact ⟨by omega, by omega, hq.2.2⟩
  have mf : Measurable (fun a : Sample 100 => fun i => wholeCat (a i)) :=
    measurable_pi_lambda (fun i => hLaw.1.comp (measurable_pi_apply i))
  have mK : Measurable (wholeK (n := 100)) :=
    (measurable_of_countable (fun b : Fin 100 → Fin 3 =>
      (univ.filter (fun i => b i ≠ 2)).card)).comp mf
  have mS : Measurable (wholeS (n := 100)) :=
    (measurable_of_countable (fun b : Fin 100 → Fin 3 =>
      (univ.filter (fun i => b i = 0)).card)).comp mf
  have mE (q : Sigma (fun _ : ℕ => ℕ)) : MeasurableSet (E q) :=
    (measurableSet_eq_fun mK measurable_const).inter
      (measurableSet_eq_fun mS measurable_const)
  have hdis : Set.PairwiseDisjoint (D : Set (Sigma (fun _ : ℕ => ℕ))) E := by
    intro q hq r hr hqr
    apply Set.disjoint_left.2
    intro a haq har
    have hfirst : q.1 = r.1 := haq.1.symm.trans har.1
    have hsecond : q.2 = r.2 := haq.2.symm.trans har.2
    apply hqr
    rcases q with ⟨k, s⟩
    rcases r with ⟨k', s'⟩
    dsimp only at hfirst hsecond
    cases hfirst
    cases hsecond
    rfl
  have hmass (q : Sigma (fun _ : ℕ => ℕ)) (hq : q ∈ D) :
      P (E q) = ENNReal.ofReal (wholeCountMass q.1 q.2) := by
    have hd := hD q hq
    change sampleLaw IntervalExample.study 100
      {a | wholeK a = q.1 ∧ wholeS a = q.2} = _
    exact hLaw.2.2 q.1 q.2 hd.2.1 hd.1
  have hAE : {a : Sample 100 |
      printedRadius IntervalExample.study (1 / 10000000) a <
        |ht IntervalExample.study a - mu IntervalExample.study|} =ᵐ[P]
      ⋃ q ∈ D, E q := by
    filter_upwards [hsupp] with a ha
    have hv := SAP.P046.WH.W1.P.T1_L2.failure_iff hRed ha
    simp only [Set.mem_iUnion]
    apply propext
    constructor
    · intro hf
      let q : Sigma (fun _ : ℕ => ℕ) := ⟨wholeK a, wholeS a⟩
      have hq : q ∈ D := by
        rw [hDdef]
        simp only [mem_sigma, mem_range, mem_filter]
        dsimp [q]
        have hfcut := hv.mp hf
        have hfeas := counts_feasible a
        exact ⟨by omega, by omega, hfcut⟩
      exact ⟨q, hq, by simp [E, q]
        ⟩
    · rintro ⟨q, hq, he⟩
      rcases q with ⟨k, s⟩
      change wholeK a = k ∧ wholeS a = s at he
      have hd := hD ⟨k, s⟩ hq
      have hcut : Real.log 20000000 <
          wholeCountThreshold (wholeK a) (wholeS a) := by
        rw [he.1, he.2]
        exact hd.2.2
      exact hv.mpr hcut
  have hunion : (P (⋃ q ∈ D, E q)).toReal =
      ∑ q ∈ D, wholeCountMass q.1 q.2 := by
    rw [measure_biUnion_finset hdis (fun q hq => mE q),
      ENNReal.toReal_sum (fun q hq => measure_ne_top P (E q))]
    apply sum_congr rfl
    intro q hq
    have hmnonneg : 0 ≤ wholeCountMass q.1 q.2 := by
      unfold wholeCountMass
      apply div_nonneg
      · positivity
      · positivity
    rw [hmass q hq, ENNReal.toReal_ofReal hmnonneg]
  have hsum : (∑ q ∈ D, wholeCountMass q.1 q.2) =
      ∑ k ∈ range 101, ∑ s ∈ range (k + 1),
        if Real.log 20000000 < wholeCountThreshold k s then wholeCountMass k s else 0 := by
    rw [hDdef]
    simp only [sum_sigma, sum_filter]
  change (P {a : Sample 100 |
      printedRadius IntervalExample.study (1 / 10000000) a <
        |ht IntervalExample.study a - mu IntervalExample.study|}).toReal = _
  rw [measure_congr hAE, hunion, hsum]
