import AronowAudit.P046.Wave1.PropositionThreeBlueprint

set_option autoImplicit false

namespace AronowAudit.P046.Wave1.PropositionThree

open AronowAudit.P046 AronowAudit.P046.IntervalExample MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

noncomputable section

theorem n7_proof : N7 := by
  classical
  intro h3 h4 h5 h6
  letI := IntervalExample.probability_continuity_mean.1
  let P := sampleLaw IntervalExample.study 100
  obtain ⟨D, hDdef⟩ : ∃ D : Finset (Sigma (fun _ : ℕ => ℕ)),
      D = (range 101).sigma (fun k => (range (k + 1)).filter (fun s => cut17 k s = true)) :=
    ⟨_, rfl⟩
  let E : (Sigma (fun _ : ℕ => ℕ)) → Set (Sample 100) :=
    fun q => {a | countK a = q.1 ∧ countS a = q.2}
  let F : Set (Sample 100) := {a |
    printedRadius IntervalExample.study (1 / 10000000) a <
      |ht IntervalExample.study a - mu IntervalExample.study|}
  have hD (q : Sigma (fun _ : ℕ => ℕ)) (hq : q ∈ D) :
      q.1 ≤ 100 ∧ q.2 ≤ q.1 ∧ cut17 q.1 q.2 = true := by
    rw [hDdef] at hq
    simp only [mem_sigma, mem_range, mem_filter] at hq
    exact ⟨by omega, by omega, hq.2.2⟩
  have mf : Measurable (fun a : Sample 100 => fun i => cat (a i)) :=
    measurable_pi_lambda (fun i => h3.1.comp (measurable_pi_apply i))
  have mK : Measurable (countK (N := 100)) :=
    (measurable_of_countable (fun b : Fin 100 → Fin 3 =>
      (univ.filter (fun i => b i ≠ 2)).card)).comp mf
  have mS : Measurable (countS (N := 100)) :=
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
  have hp (j : Fin 3) : 0 ≤ catProb j := by
    fin_cases j <;> norm_num [catProb]
  have hmass (q : Sigma (fun _ : ℕ => ℕ)) (hq : q ∈ D) :
      P (E q) = ENNReal.ofReal ((massNumerator q.1 q.2 : ℝ) / (100 : ℝ) ^ 100) := by
    have hd := hD q hq
    have hh := h4 IntervalExample.study.law cat h3.1 catProb hp h3.2
      100 q.1 q.2 hd.2.1 hd.1
    have harith : (Nat.choose 100 q.1 : ℝ) * (Nat.choose q.1 q.2 : ℝ) *
        catProb 0 ^ q.2 * catProb 1 ^ (q.1 - q.2) * catProb 2 ^ (100 - q.1) =
        (massNumerator q.1 q.2 : ℝ) / (100 : ℝ) ^ 100 := by
      have hexp : q.2 + (q.1 - q.2) + (100 - q.1) = 100 := by omega
      have hden : (100 : ℝ) ^ q.2 * 100 ^ (q.1 - q.2) * 100 ^ (100 - q.1) =
          (100 : ℝ) ^ 100 := by
        rw [← pow_add, ← pow_add, hexp]
      change (Nat.choose 100 q.1 : ℝ) * (Nat.choose q.1 q.2 : ℝ) *
        (39 / 100 : ℝ) ^ q.2 * (21 / 100 : ℝ) ^ (q.1 - q.2) *
          (40 / 100 : ℝ) ^ (100 - q.1) = _
      simp only [massNumerator, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, div_pow]
      rw [← hden]
      field_simp
      <;> ring
    rw [harith] at hh
    exact hh
  have hunion : (P (⋃ q ∈ D, E q)).toReal =
      ∑ q ∈ D, (massNumerator q.1 q.2 : ℝ) / (100 : ℝ) ^ 100 := by
    rw [measure_biUnion_finset hdis (fun q _ => mE q),
      ENNReal.toReal_sum (fun q _ => measure_ne_top P (E q))]
    apply sum_congr rfl
    intro q hq
    rw [hmass q hq, ENNReal.toReal_ofReal (by positivity)]
  have hsum : (∑ q ∈ D, (massNumerator q.1 q.2 : ℝ)) = (lowerNumerator : ℝ) := by
    rw [hDdef]
    simp only [sum_sigma, sum_filter, lowerNumerator, Nat.cast_sum,
      Nat.cast_ite, Nat.cast_zero]
  have hlower : (P (⋃ q ∈ D, E q)).toReal = (lowerNumerator : ℝ) / (100 : ℝ) ^ 100 := by
    rw [hunion, ← sum_div, hsum]
  have hmono : P (⋃ q ∈ D, E q) ≤ P F := by
    apply measure_mono_ae
    filter_upwards [h6] with a ha
    intro hamem
    simp only [Set.mem_iUnion] at hamem
    obtain ⟨q, hq, he⟩ := hamem
    apply h5 a ha
    change countK a = q.1 ∧ countS a = q.2 at he
    rw [he.1, he.2]
    exact (hD q hq).2.2
  change (lowerNumerator : ℝ) / (100 : ℝ) ^ 100 ≤ (P F).toReal
  rw [← hlower]
  exact ENNReal.toReal_mono (measure_ne_top P F) hmono

end

end AronowAudit.P046.Wave1.PropositionThree
