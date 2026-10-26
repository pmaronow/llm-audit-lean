import Mathlib

namespace AronowAudit.P007
open scoped BigOperators
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- Section 3.1, p. 152: "k of the variables ... (without replacement)".
A fixed binary missingness array is represented by its set of observed columns in each row.
Membership means M_ij=0; nonmembership means M_ij=1. No stochastic row model is imposed. -/
abbrev FixedArray (n K : ℕ) := Fin n → Finset (Fin K)

/-- Section 3.1, p. 152: the unordered k-column subsets sampled uniformly without replacement. -/
noncomputable def columnSamples (K k : ℕ) : Finset (Finset (Fin K)) :=
  Finset.univ.powersetCard k

/-- Section 3.1, p. 152: "the ... proportion of remaining data observed after listwise deletion".
A row survives a selected set S exactly when S is a subset of its observed columns. -/
noncomputable def retainedProportion {n K : ℕ} (m : FixedArray n K) (S : Finset (Fin K)) : ℝ :=
  (∑ i, if S ⊆ m i then (1 : ℝ) else 0) / n

/-- Section 3.1, p. 152: "expected values ... refer to the randomness induced by our
random subsampling procedure". This is the finite uniform average over all k-column subsets. -/
noncomputable def expectedRetained {n K : ℕ} (m : FixedArray n K) (k : ℕ) : ℝ :=
  (∑ S ∈ columnSamples K k, retainedProportion m S) / (columnSamples K k).card

/-- Section 3.2, p. 153: the expected row "loss" is one minus expected retained proportion. -/
noncomputable def expectedLoss {n K : ℕ} (m : FixedArray n K) (k : ℕ) : ℝ :=
  1 - expectedRetained m k

/-- P007-T1(i), Section 3.1 sampling design: a row with r observed cells survives exactly
choose(r,k) unordered k-column draws. This is an exact counting identity, without independence. -/
theorem row_survival_count {K k : ℕ} (o : Finset (Fin K)) :
    (∑ S ∈ columnSamples K k, if S ⊆ o then (1 : ℝ) else 0) = o.card.choose k := by
  have hf : (columnSamples K k).filter (fun S => S ⊆ o) = o.powersetCard k := by
    ext S
    simp only [Finset.mem_filter, columnSamples, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    tauto
  rw [← Finset.sum_filter, hf]
  simp [Finset.card_powersetCard]

/-- P007-T1(i), exact refutation of Section 3.2, p. 153: the uniform expected
retained fraction is sum_i choose(r_i,k)/(n choose(K,k)), for the paper's actual sampling design. -/
theorem uniform_retention_counting_identity {n K k : ℕ} (m : FixedArray n K)
    (_hn : 0 < n) (_hk : k ≤ K) :
    expectedRetained m k =
      (∑ i, ((m i).card.choose k : ℝ)) / ((n : ℝ) * (K.choose k : ℝ)) := by
  unfold expectedRetained retainedProportion
  simp only [← Finset.sum_div, Finset.sum_comm, row_survival_count]
  simp [columnSamples, Finset.card_powersetCard, div_div, mul_comm]

/-- P007-T1(ii): the supporting line at r=405,406, checked for every possible row
count 0,...,1205. -/
theorem supportingLine (r : Fin 1206) :
    (1104475905 : ℤ) + ((r.val : ℤ) - 405) * 10989810 ≤
      (r.val.choose 4 : ℤ) := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  revert r
  decide +kernel

/-- P007-T1(ii): the supporting line touches choose(r,4) at both 405 and 406. -/
theorem supportingLine_equality :
    (Nat.choose 405 4 : ℤ) = 1104475905 ∧
    (Nat.choose 405 3 : ℤ) = 10989810 ∧
    (Nat.choose 406 4 : ℤ) = 1115465715 := by
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]

/-- P007-T1(iii): the total number of observed cells, sum_i r_i. -/
noncomputable def observedTotal (r : Fin 8580 → Fin 1206) : ℤ := ∑ i, ((r i).val : ℤ)

/-- P007-T1(i): the numerator sum_i choose(r_i,4) of the uniform expectation. -/
noncomputable def keptFourNumerator (r : Fin 8580 → Fin 1206) : ℤ := ∑ i, ((r i).val.choose 4 : ℤ)

/-- P007-T1(iii): summing the supporting line gives the exact lower bound on the
number of surviving (row,four-column-subset) pairs, conditional on the specified observed total. -/
theorem numeratorLowerBound (r : Fin 8580 → Fin 1206)
    (h : observedTotal r = 3482533) :
    (9560288484630 : ℤ) ≤ keptFourNumerator r := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 8580)))
    (fun i _ => supportingLine (r i))
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hs
  unfold observedTotal at h
  unfold keptFourNumerator
  rw [h] at hs
  norm_num at hs
  exact hs

/-- P007-T1(iv): the denominator n choose(K,4) for the paper's State Failure dimensions. -/
theorem denominatorValue :
    (8580 : ℤ) * (Nat.choose 1205 4 : ℤ) = 749997256908900 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

/-- Section 3.1, p. 152 and P007-T1: the observed-row count r_i extracted from the binary array; at most all 1205 cells can be observed. -/
noncomputable def stateFailureRowCounts (m : FixedArray 8580 1205) : Fin 8580 → Fin 1206 :=
  fun i => ⟨(m i).card, by have := Finset.card_le_univ (m i); simp at this; omega⟩

/-- P007-T1(v) and P007-T2(ii): for every State Failure-sized binary array with the
specified observed-cell total, expected retained fraction at four variables is at least
24513560217/1923069889510 > 1/100; expected loss is at most 98.73%, strictly below 99%.
The specified total is a hypothesis, not an independent recount of the data. -/
theorem fourVariablesCannotLoseMoreThan99Percent (m : FixedArray 8580 1205)
    (h : (∑ i, ((m i).card : ℤ)) = 3482533) :
    (24513560217 : ℝ) / 1923069889510 ≤ expectedRetained m 4 ∧
    (1 : ℝ) / 100 < expectedRetained m 4 ∧
    expectedLoss m 4 ≤ (1898556329293 : ℝ) / 1923069889510 ∧
    expectedLoss m 4 < (99 : ℝ) / 100 := by
  have hb := numeratorLowerBound (stateFailureRowCounts m) h
  have hb' : (9560288484630 : ℝ) ≤ ∑ i, ((m i).card.choose 4 : ℝ) := by
    simp only [keptFourNumerator, stateFailureRowCounts] at hb
    exact_mod_cast hb
  have hd : (8580 : ℝ) * (Nat.choose 1205 4 : ℝ) = 749997256908900 := by
    exact_mod_cast denominatorValue
  have he : (9560288484630 : ℝ)/749997256908900 ≤
      (∑ i, ((m i).card.choose 4 : ℝ))/749997256908900 :=
    div_le_div_of_nonneg_right hb' (by norm_num)
  have hret : (24513560217 : ℝ)/1923069889510 ≤ expectedRetained m 4 := by
    rw [uniform_retention_counting_identity m (by norm_num) (by norm_num)]
    simp only [Nat.cast_ofNat]
    rw [hd]
    calc
      (24513560217 : ℝ)/1923069889510 = 9560288484630/749997256908900 := by norm_num
      _ ≤ (∑ i, ((m i).card.choose 4 : ℝ))/749997256908900 := he
  have hloss : expectedLoss m 4 ≤ (1898556329293 : ℝ)/1923069889510 := by
    unfold expectedLoss
    calc
      1-expectedRetained m 4 ≤ 1-(24513560217 : ℝ)/1923069889510 := sub_le_sub_left hret 1
      _ = (1898556329293 : ℝ)/1923069889510 := by norm_num
  exact ⟨hret, (by norm_num : (1 : ℝ)/100 < 24513560217/1923069889510).trans_le hret,
    hloss, hloss.trans_lt (by norm_num)⟩

/-- P007-T2(i), P007-E010: the loose 10^-9 display tolerance for the specified
pre-removal average singles out the integer missing-cell total 7019387. -/
theorem logged_missing_count_unique (A : ℕ)
    (h : |(A : ℝ) / 10501920 - (0.668390827582004 : ℝ)| ≤ (0.000000001 : ℝ)) :
    A = 7019387 := by
  have hpair := abs_le.mp h
  have hlo : (7019386 : ℝ) < A := by linarith [hpair.1]
  have hhi : (A : ℝ) < 7019388 := by linarith [hpair.2]
  have hlo' : 7019386 < A := by exact_mod_cast hlo
  have hhi' : A < 7019388 := by exact_mod_cast hhi
  omega

/-- P007-T2(i): exact counts and rounding intervals after removing 19 wholly missing
columns. This proves the corrected 66.3% and identifies printed 66.8% as pre-removal. -/
theorem stateFailure_corrected_average :
    8580 * 1224 = (10501920 : ℕ) ∧ 8580 * 19 = (163020 : ℕ) ∧
    7019387 - 8580 * 19 = (6856367 : ℕ) ∧ 8580 * 1205 = (10338900 : ℕ) ∧
    10338900 - 6856367 = (3482533 : ℕ) ∧
    (0.6625 : ℝ) ≤ 6856367 / 10338900 ∧ (6856367 : ℝ) / 10338900 < 0.6635 ∧
    (6856367 : ℝ) / 10338900 < 0.6675 ∧
    (0.6675 : ℝ) ≤ 7019387 / 10501920 ∧ (7019387 : ℝ) / 10501920 < 0.6685 := by
  norm_num

/-- P007-T2(iii): exact arithmetic on the specified simulation estimates, not population
expectations. Among the estimates at four, five, six variables, loss first exceeds 99% at six. -/
theorem archived_simulation_threshold :
    (1 - 0.02820753 : ℝ) = 0.97179247 ∧
    (1 - 0.01365003 : ℝ) = 0.98634997 ∧
    (1 - 0.006640252 : ℝ) = 0.993359748 ∧
    (0.97179247 : ℝ) < 0.98634997 ∧
    (0.98634997 : ℝ) < 0.99 ∧ (0.99 : ℝ) < 0.993359748 := by norm_num

/-- Table 1, p. 152: "Proportion of missing values (avg.)" is the average over
columns of their missing proportions. Here true is missing, false observed. -/
noncomputable def columnMissingAverage {n : ℕ} {J : Type*} [Fintype J]
    (m : Fin n → J → Bool) : ℝ :=
  (∑ j, (∑ i, if m i j then (1 : ℝ) else 0) / n) / Fintype.card J

/-- P007-T12: the number A of missing cells before preprocessing. -/
noncomputable def missingCells {n : ℕ} {J : Type*} [Fintype J] (m : Fin n → J → Bool) : ℕ :=
  ∑ j, ∑ i, if m i j then 1 else 0

/-- P007-T12(i): the average of column proportions equals missing cells divided by
all cells, because each variable has the same n rows. -/
theorem columnAverage_count_identity {n : ℕ} {J : Type*} [Fintype J]
    (m : Fin n → J → Bool) :
    columnMissingAverage m = (missingCells m : ℝ) / ((n : ℝ) * Fintype.card J) := by
  simp [columnMissingAverage, missingCells, Nat.cast_sum, Nat.cast_ite,
    ← Finset.sum_div, div_div, mul_comm]

/-- P007-T12(i), preprocessing on pp. 151-152: removed columns may be reindexed as
Fin d, and retained columns as Fin K. The removed d columns are wholly missing.
These exact finite-sum identities describe the same array before and after removal. -/
theorem removing_fully_missing_columns {n K d : ℕ} (hn : 0 < n) (hK : 0 < K)
    (m : Fin n → (Fin K ⊕ Fin d) → Bool)
    (hfull : ∀ i j, m i (Sum.inr j) = true) :
    let A := missingCells m
    let after := fun i j => m i (Sum.inl j)
    A = missingCells after + n * d ∧
    columnMissingAverage m = (A : ℝ) / ((n : ℝ) * (K + d)) ∧
    columnMissingAverage after = ((A : ℝ) - n * d) / ((n : ℝ) * K) ∧
    ((K + d : ℕ) : ℝ) * columnMissingAverage m =
      (d : ℝ) + K * columnMissingAverage after ∧
    columnMissingAverage after =
      (((K + d : ℕ) : ℝ) * columnMissingAverage m - d) / K := by
  dsimp only
  have hc : missingCells m = missingCells (fun i j => m i (Sum.inl j)) + n * d := by
    unfold missingCells
    rw [Fintype.sum_sum_type]
    simp [hfull, mul_comm]
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
  have hRr : (K : ℝ) + (d : ℝ) ≠ 0 := by exact_mod_cast (show K+d ≠ 0 by omega)
  have hcr : (missingCells m : ℝ) =
      (missingCells (fun i j => m i (Sum.inl j)) : ℝ) + (n : ℝ) * d := by
    exact_mod_cast hc
  simp only [columnAverage_count_identity, Fintype.card_sum, Fintype.card_fin, Nat.cast_add]
  refine ⟨hc, True.intro, ?_, ?_, ?_⟩
  · congr 1
    linarith
  · field_simp [hnr, hKr, hRr]
    nlinarith [hcr]
  · field_simp [hnr, hKr, hRr]
    nlinarith [hcr]

/-- P007-T12(ii): even the printed precision of the old 66.8% excludes 66.8% for
the retained variables, by R q_before = d + K q_after. No additional last digits are needed. -/
theorem printed_average_cannot_be_retained {before after : ℝ}
    (hlo : (0.6675 : ℝ) ≤ before) (hhi : before < 0.6685)
    (hpartition : 1224 * before = 19 + 1205 * after) :
    after < (199811 : ℝ) / 301250 ∧ after < 0.6675 := by
  constructor <;> linarith

/-- P007-T12(iii): the exact difference between the pre-removal and retained averages;
multiplication by 100 gives the overstatement in percentage points. -/
theorem stateFailure_average_overstatement :
    (7019387 : ℝ) / 10501920 - 6856367 / 10338900 = 66168127 / 12654813600 ∧
    100 * ((7019387 : ℝ) / 10501920 - 6856367 / 10338900) = 66168127 / 126548136 := by
  norm_num


/-- A concrete feasible 8580×1205 binary array for P007-T1: the first 7633 rows
observe columns 0,...,405, and the remaining 947 rows observe 0,...,404.
This is a witness with the required observed-cell total, not a claim to reconstruct
State Failure. The universal bound also applies to any array with this total. -/
noncomputable def balancedStateFailureArray : FixedArray 8580 1205 :=
  fun i => Finset.univ.filter (fun j => j.val < if i.val<7633 then 406 else 405)

/-- The explicit array's row counts and observed total follow symbolically from
cardinality, so the hypothesis of the exact refutation is satisfiable.
Supporting finite lemma for the exact refutation of the four-variable threshold (Section 3.2, p. 153; P007-E010). -/
theorem balanced_array_total :
    (∀ i, (balancedStateFailureArray i).card = if i.val<7633 then 406 else 405) ∧
    (∑ i, ((balancedStateFailureArray i).card : ℤ)) = 3482533 := by
  have hc : ∀ i, (balancedStateFailureArray i).card = if i.val<7633 then 406 else 405 := by
    intro i
    unfold balancedStateFailureArray
    rw [Fin.card_filter_val_lt]
    split_ifs <;> norm_num
  refine ⟨hc,?_⟩
  calc
    (∑ i, ((balancedStateFailureArray i).card : ℤ)) =
        ∑ i : Fin 8580, ((405 : ℤ) + if i.val<7633 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hc]
      split_ifs <;> norm_num
    _ = (3482533 : ℤ) := by simp [Finset.sum_add_distrib, Fin.card_filter_val_lt]

/-- P007-T1 concrete counterexample: the specified binary array meets the required
dimensions and specified cell total, yet selecting four variables has expected loss below 99%. -/
theorem concrete_four_variable_counterexample :
    (∑ i, ((balancedStateFailureArray i).card : ℤ))=3482533 ∧
    expectedLoss balancedStateFailureArray 4 < (99 : ℝ)/100 :=
  ⟨balanced_array_total.2,
    (fourVariablesCannotLoseMoreThan99Percent balancedStateFailureArray balanced_array_total.2).2.2.2⟩


/-- Section 3.1, p. 152: a binary is.na mask (true=missing) represented by its
observed column sets. This connects preprocessing counts to the uniform sampling design. -/
def observedSets {n K : ℕ} (m : Fin n → Fin K → Bool) : FixedArray n K :=
  fun i => Finset.univ.filter (fun j => m i j=false)

/-- Every cell is either missing or observed; summing row observed counts and the
missing-cell total gives nK. This is an exact finite-sum identity for any binary mask. 
Supporting finite lemma for the corrected Table 1 average and preprocessing counts (pp. 151-152). -/
theorem observed_missing_partition {n K : ℕ} (m : Fin n → Fin K → Bool) :
    (∑ i, (observedSets m i).card) + missingCells m = n*K := by
  have hr : ∀ i, (observedSets m i).card + (∑ j, if m i j then 1 else 0) = K := by
    intro i
    have ho : (observedSets m i).card = ∑ j : Fin K, if m i j=false then (1 : ℕ) else 0 := by
      simp [observedSets]
    rw [ho, ← Finset.sum_add_distrib]
    calc
      (∑ j : Fin K, ((if m i j=false then (1 : ℕ) else 0) + if m i j then 1 else 0)) =
          ∑ _j : Fin K, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro j _
        cases m i j <;> simp
      _ = K := by simp
  unfold missingCells
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  simp only [hr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]

/-- P007-T2(i)-(ii) and P007-T12(iii): for every actual binary mask satisfying
all preprocessing and specified-average hypotheses, the pre-removal count is 7019387,
retained missing count 6856367, observed count 3482533, and retained mean rounds to
66.3%. Uniform four-variable expected loss for that same retained mask is below 99%.
No original-data reconstruction, row independence, or simulation expectation is assumed. -/
theorem logged_mask_correction (m : Fin 8580 → (Fin 1205 ⊕ Fin 19) → Bool)
    (hfull : ∀ i j, m i (Sum.inr j)=true)
    (hlog : |columnMissingAverage m-(0.668390827582004 : ℝ)| ≤ (0.000000001 : ℝ)) :
    let after := fun i j => m i (Sum.inl j)
    missingCells m=7019387 ∧ missingCells after=6856367 ∧
    (∑ i, (observedSets after i).card)=3482533 ∧
    columnMissingAverage after=(6856367 : ℝ)/10338900 ∧
    (0.6625 : ℝ)≤columnMissingAverage after ∧ columnMissingAverage after<0.6635 ∧
    expectedLoss (observedSets after) 4 ≤ (1898556329293 : ℝ)/1923069889510 ∧
    expectedLoss (observedSets after) 4 < (99 : ℝ)/100 := by
  dsimp only
  let after : Fin 8580 → Fin 1205 → Bool := fun i j => m i (Sum.inl j)
  have hmean : columnMissingAverage m=(missingCells m : ℝ)/10501920 := by
    rw [columnAverage_count_identity]
    congr 1 <;> norm_num
  have hA : missingCells m=7019387 :=
    logged_missing_count_unique _ (by rw [← hmean]; exact hlog)
  have hp := removing_fully_missing_columns (by norm_num : 0<8580) (by norm_num : 0<1205) m hfull
  have hafter : missingCells after=6856367 := by
    have hc := hp.1
    change missingCells m=missingCells after+8580*19 at hc
    rw [hA] at hc
    omega
  have hobs : (∑ i, (observedSets after i).card)=3482533 := by
    have hc := observed_missing_partition after
    rw [hafter] at hc
    omega
  have hobsz : (∑ i, ((observedSets after i).card : ℤ))=3482533 := by exact_mod_cast hobs
  have ha : columnMissingAverage after=(6856367 : ℝ)/10338900 := by
    simp only [columnAverage_count_identity,hafter,Fintype.card_fin,Nat.cast_ofNat]
    norm_num
  have hf := fourVariablesCannotLoseMoreThan99Percent (observedSets after) hobsz
  refine ⟨hA,hafter,hobs,ha,?_,?_,hf.2.2.1,hf.2.2.2⟩
  · rw [ha]; norm_num
  · rw [ha]; norm_num

end AronowAudit.P007

