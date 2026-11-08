import SAP.P018a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018a.WH.W2.P.T2_L1

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

private def witnessCountTerm (i j : Fin 4) : ℝ :=
  if i.val = 0 ∧ j.val = 1 then 2 else
  if i.val = 2 ∧ j.val = 3 then 3 else 1

private lemma witness_count_sum :
    (∑ d : Dyad 4, (wholeRepairWitness.T 4 d : ℝ)) = 9 := by
  calc
    _ = ∑ d : Dyad 4, witnessCountTerm (firstUnit d) (secondUnit d) := by
      apply Finset.sum_congr rfl
      intro d hd
      norm_num [wholeRepairWitness, witnessCountTerm]
    _ = ∑ i : Fin 4, ∑ j : Fin 4,
        if i < j then witnessCountTerm i j else 0 :=
      AronowAudit.P018.Wave1.printed_upper_sum witnessCountTerm
    _ = 9 := by norm_num [witnessCountTerm, Fin.sum_univ_succ]

private lemma sum_fin_one (n : ℕ) : (∑ _ : Fin n, (1 : ℝ)) = n := by
  simp

private lemma witness_X (N : ℕ) (d : Dyad N)
    (t : Fin (wholeRepairWitness.T N d)) (u v : Unit) :
    wholeRepairWitness.X N d t u v = ![1] := rfl

private lemma witness_gram_entry (ω : Fin 4 → Unit) :
    (repeatedGram wholeRepairWitness ω) 0 0 =
      ∑ d : Dyad 4, (wholeRepairWitness.T 4 d : ℝ) := by
  simp only [repeatedGram, Matrix.sum_apply, repeatedX, outer, witness_X]
  simp only [Matrix.cons_val_zero, one_mul]
  change (∑ d : Dyad 4, ∑ t : Fin (wholeRepairWitness.T 4 d), (1 : ℝ)) = _
  simp_rw [sum_fin_one]

theorem witnessInput : T2WitnessInput := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ⟨2, by norm_num, ?_⟩, ⟨0, ?_⟩⟩
    · change IsProbabilityMeasure (Measure.dirac ())
      infer_instance
    · intro N hN d
      change 0 < (if (firstUnit d).val = 0 ∧ (secondUnit d).val = 1 then 2
        else if (firstUnit d).val = 2 ∧ (secondUnit d).val = 3 then 3 else 1)
      split_ifs <;> omega
    · intro N d t
      exact ⟨measurable_of_countable _, measurable_of_countable _⟩
    · intro N d t
      apply Filter.Eventually.of_forall
      intro uv
      constructor
      · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).2
        intro j
        fin_cases j
        change |(1 : ℝ)| ≤ 2
        norm_num
      · change |(if t.val = 0 then (0 : ℝ) else if t.val = 1 then 1 else -2)| ≤ 2
        split_ifs <;> norm_num
    · intro N d t u v
      rfl
  · intro N d
    change (if (firstUnit d).val = 0 ∧ (secondUnit d).val = 1 then 2
      else if (firstUnit d).val = 2 ∧ (secondUnit d).val = 3 then 3 else 1) ≤ 3
    split_ifs <;> omega
  · refine ⟨fun n => if n = 0 then 0 else if n = 1 then 1 else -2, ?_⟩
    intro N d t u v
    rfl
  · exact witness_count_sum
  · intro ω
    ext i j
    fin_cases i
    fin_cases j
    change (repeatedGram wholeRepairWitness ω) 0 0 = 9
    rw [witness_gram_entry]
    exact witness_count_sum
  · have hL : repeatedL wholeRepairWitness 4 = 9 := witness_count_sum
    have hG : ∀ ω : Fin 4 → Unit,
        repeatedGram wholeRepairWitness ω = !![9] := by
      intro ω
      ext i j
      fin_cases i
      fin_cases j
      change (repeatedGram wholeRepairWitness ω) 0 0 = 9
      rw [witness_gram_entry]
      exact witness_count_sum
    haveI : IsProbabilityMeasure (repeatedLaw wholeRepairWitness 4) := by
      unfold repeatedLaw wholeRepairWitness
      infer_instance
    have hH : repeatedH wholeRepairWitness 4 = !![1] := by
      ext i j
      fin_cases i
      fin_cases j
      simp [repeatedH, hL, meanMat, hG, integral_const]
    rw [hH]
    norm_num

end SAP.P018a.WH.W2.P.T2_L1

theorem SAP.P018a.WH.W2.T2_L1_proof : SAP.P018a.WH.W2.T2_L1 := by
  exact SAP.P018a.WH.W2.P.T2_L1.witnessInput
