import Mathlib

namespace AronowAudit.P020

open scoped BigOperators

/-- "P(Y_ij = 1) = 1 - (1 + exp(...))⁻¹": the printed logistic link,
Section 6.2, p. 61 (PDF p. 23). -/
noncomputable def logistic (eta : ℝ) : ℝ := 1 - (1 + Real.exp eta)⁻¹

/-- The logistic link printed in Section 6.2 is strictly increasing (T3(i)). -/
theorem logistic_strictMono : StrictMono logistic := by
  intro x y hxy
  have hx : 0 < 1 + Real.exp x := by positivity
  have hy : 0 < 1 + Real.exp y := by positivity
  have he : 1 + Real.exp x < 1 + Real.exp y := by
    linarith [Real.exp_strictMono hxy]
  have hi := (inv_lt_inv₀ hy hx).2 he
  unfold logistic
  linarith

/-- With the printed coefficients 0.4 and -0.9, the treatment log-odds
contrast is at most -1/2 for every cluster count at least one, p. 61 (T3(ii)). -/
theorem printed_contrast_bound (n : ℝ) (hn : 1 ≤ n) :
    (2 : ℝ) / 5 - (9 : ℝ) / 10 * n ≤ -(1 : ℝ) / 2 := by
  linarith

/-- The printed model forces a strictly negative probability difference for
any control predictor and any cluster size at least one, p. 61 (T3(iii)). -/
theorem printed_model_unit_negative (base n : ℝ) (hn : 1 ≤ n) :
    logistic (base + (2 : ℝ) / 5 - (9 : ℝ) / 10 * n) - logistic base < 0 := by
  have hb := printed_contrast_bound n hn
  have hlt : base + (2 : ℝ) / 5 - (9 : ℝ) / 10 * n < base := by linarith
  exact sub_neg.mpr (logistic_strictMono hlt)

/-- Every nonempty finite population under the printed model has a negative
average probability contrast, contradicting the reported +0.007, p. 61 (T3(iv)).
Allowing arbitrary individual control predictors and real sizes ≥ 1 is broader
than the printed cluster model and includes it. -/
theorem printed_model_average_negative
    (N : ℕ) (hN : 0 < N) (base size : Fin N → ℝ)
    (hsize : ∀ i, 1 ≤ size i) :
    (∑ i : Fin N, (logistic (base i + 2 / 5 - 9 / 10 * size i) -
      logistic (base i))) / (N : ℝ) < 0 := by
  have hne : (Finset.univ : Finset (Fin N)).Nonempty :=
    ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  have hs : (∑ i : Fin N, (logistic (base i + 2 / 5 - 9 / 10 * size i) -
      logistic (base i))) < 0 := by
    have h := Finset.sum_lt_sum_of_nonempty hne
      (fun i _ => printed_model_unit_negative (base i) (size i) (hsize i))
    simpa using h
  exact div_neg_of_neg_of_pos hs (by exact_mod_cast hN)

/-- The positive value 7/1000 in Section 6.2 cannot equal the model's expected
ATE under the printed count scale and coefficients (T3(iv)). -/
theorem printed_model_average_ne_reported
    (N : ℕ) (hN : 0 < N) (base size : Fin N → ℝ)
    (hsize : ∀ i, 1 ≤ size i) :
    (∑ i : Fin N, (logistic (base i + 2 / 5 - 9 / 10 * size i) -
      logistic (base i))) / (N : ℝ) ≠ (7 : ℝ) / 1000 := by
  have h := printed_model_average_negative N hN base size hsize
  intro heq
  rw [heq] at h
  norm_num at h

/-- Concrete instance of the refutation: one individual, cluster size one,
control predictor zero, with p_c = 1/2 and p_t = L(-1/2) < 1/2 (T3). -/
theorem logistic_concrete_counterexample :
    logistic 0 = (1 : ℝ) / 2 ∧ logistic (-(1 : ℝ) / 2) < 1 / 2 ∧
    logistic (-(1 : ℝ) / 2) - logistic 0 ≠ 7 / 1000 := by
  have hz : logistic 0 = (1 : ℝ) / 2 := by norm_num [logistic]
  have hn := logistic_strictMono (show (-(1 : ℝ) / 2) < 0 by norm_num)
  rw [hz] at hn
  refine ⟨hz, hn, ?_⟩
  rw [hz]
  linarith

/-- Conditional repair: "define s_j = n_j/1000" in the logistic display only;
P020-E003, correction of Section 6.2, p. 61. This scale is not recovered from
the publication. The treatment log-odds contrast is 0.4 - 0.0009 n_j. -/
noncomputable def repairedContrast (n : ℝ) : ℝ := 2 / 5 - 9 / 10000 * n

/-- Measuring size in thousands with slopes 1.4 and -0.9 is algebraically
equivalent to raw counts with slopes 0.0014 and -0.0009 (T4). -/
theorem repaired_scale_equivalence (alpha block n t : ℝ) :
    alpha + 2 / 5 * t + 7 / 5 * (n / 1000) - 9 / 10 * (n / 1000) * t + block =
    alpha + 2 / 5 * t + 7 / 5000 * n - 9 / 10000 * n * t + block := by ring

/-- The repaired real-valued treatment contrast is positive precisely below
4000/9 persons, and negative precisely above it, p. 61 as corrected (T4(i)). -/
theorem repaired_real_sign (n : ℝ) :
    (0 < repairedContrast n ↔ n < 4000 / 9) ∧
    (repairedContrast n < 0 ↔ 4000 / 9 < n) := by
  unfold repairedContrast
  constructor <;> constructor <;> intro h <;> linarith

/-- For integer cluster counts, the repaired contrast is positive iff n ≤ 444,
and negative iff n ≥ 445, p. 61 as corrected (T4(i)). -/
theorem repaired_integer_sign (n : ℕ) :
    (0 < repairedContrast (n : ℝ) ↔ n ≤ 444) ∧
    (repairedContrast (n : ℝ) < 0 ↔ 445 ≤ n) := by
  unfold repairedContrast
  constructor
  · constructor
    · intro h
      have h' : (n : ℝ) < 445 := by linarith
      have : n < 445 := by exact_mod_cast h'
      omega
    · intro h
      have : (n : ℝ) ≤ 444 := by exact_mod_cast h
      linarith
  · constructor
    · intro h
      have h' : (444 : ℝ) < n := by linarith
      have : 444 < n := by exact_mod_cast h'
      omega
    · intro h
      have : (445 : ℝ) ≤ n := by exact_mod_cast h
      linarith

/-- Under the conditional size-scale repair, every individual's probability
contrast has the sign determined by the 444/445 cluster-count threshold (T4(ii)). -/
theorem repaired_probability_sign (base : ℝ) (n : ℕ) :
    (logistic base < logistic (base + repairedContrast n) ↔ n ≤ 444) ∧
    (logistic (base + repairedContrast n) < logistic base ↔ 445 ≤ n) := by
  rw [logistic_strictMono.lt_iff_lt, logistic_strictMono.lt_iff_lt]
  constructor
  · have h := (repaired_integer_sign n).1
    constructor <;> intro hh
    · exact h.mp (by linarith)
    · have := h.mpr hh; linarith
  · have h := (repaired_integer_sign n).2
    constructor <;> intro hh
    · exact h.mp (by linarith)
    · have := h.mpr hh; linarith

/-- Under the conditional repair, the finite average probability difference
is positive when all clusters have at most 444 members, and negative when
all have at least 445; the sign is therefore not forced (T4(iii)). -/
theorem repaired_average_sign (N : ℕ) (hN : 0 < N)
    (base : Fin N → ℝ) (size : Fin N → ℕ) (hsize : ∀ i, 1 ≤ size i) :
    ((∀ i, size i ≤ 444) →
      0 < (∑ i, (logistic (base i + repairedContrast (size i)) - logistic (base i))) / N) ∧
    ((∀ i, 445 ≤ size i) →
      (∑ i, (logistic (base i + repairedContrast (size i)) - logistic (base i))) / N < 0) := by
  have hne : (Finset.univ : Finset (Fin N)).Nonempty :=
    ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · intro hs
    apply div_pos _ hpos
    have h := Finset.sum_lt_sum_of_nonempty hne (fun i _ =>
      sub_pos.mpr ((repaired_probability_sign (base i) (size i)).1.mpr (hs i)))
    simpa using h
  · intro hs
    apply div_neg_of_neg_of_pos _ hpos
    have h := Finset.sum_lt_sum_of_nonempty hne (fun i _ =>
      sub_neg.mpr ((repaired_probability_sign (base i) (size i)).2.mpr (hs i)))
    simpa using h

end AronowAudit.P020

