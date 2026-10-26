import AronowAudit.P002.P002_Audit
import AronowAudit.P031.P031_Variance
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.PSeries

/-!
P002-T15: Supplement Lemma 12 with the corrected square and the positive-variance
scope.

Normalize the two adjusted potential-outcome vectors by their combined standard
deviation. A fourth-moment calculation for a uniform fixed-size subset supplies
summable tails for the observed first and second moments. Borel--Cantelli gives an
eventually positive observed variance on one common full-measure event. Exact
finite-sampling second moments then bound the conditional variance-ratio error.
The argument uses the marginal laws in `RandomizationSequence`, and therefore
also covers the independent assignments specified on Supplement p. 27.

-/

namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

lemma DecisionLemma12_expectation_congr {n : ℕ} (P : Population n)
    {f g : Finset (Fin n) → ℝ} (h : ∀ S ∈ assignments P, f S = g S) :
    expectation P f = expectation P g := by
  unfold expectation
  congr 1
  exact Finset.sum_congr rfl h

lemma DecisionLemma12_expectation_add {n : ℕ} (P : Population n)
    (f g : Finset (Fin n) → ℝ) :
    expectation P (fun S => f S + g S) = expectation P f + expectation P g := by
  simp only [expectation, Finset.sum_add_distrib, add_div]

lemma DecisionLemma12_expectation_nonneg {n : ℕ} (P : Population n)
    (f : Finset (Fin n) → ℝ) (h : ∀ S ∈ assignments P, 0 ≤ f S) :
    0 ≤ expectation P f := by
  exact div_nonneg (Finset.sum_nonneg h) (Nat.cast_nonneg _)

lemma DecisionLemma12_expectation_mono {n : ℕ} (P : Population n)
    {f g : Finset (Fin n) → ℝ} (h : ∀ S ∈ assignments P, f S ≤ g S) :
    expectation P f ≤ expectation P g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

lemma DecisionLemma12_probability_nonneg {n : ℕ} (P : Population n)
    (E : Finset (Fin n) → Prop) : 0 ≤ probability P E := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)


lemma DecisionLemma12_probability_eq_expectation {n : ℕ} (P : Population n)
    (E : Finset (Fin n) → Prop) :
    probability P E = expectation P (fun S => if E S then 1 else 0) := by
  simp [probability, expectation, Finset.sum_ite]

lemma DecisionLemma12_inclusion {n : ℕ} (P : Population n)
    (R : Finset (Fin n)) (hR : R.card ≤ P.n1) :
    expectation P (fun S => if R ⊆ S then 1 else 0) =
      ((n - R.card).choose (P.n1 - R.card) : ℝ) / (n.choose P.n1 : ℝ) := by
  have he : expectation P (fun S => if R ⊆ S then 1 else 0) = probability P (fun S => R ⊆ S) := by
    simp [expectation, probability, Finset.sum_ite]
    congr! 3
    ext S
    simp
  rw [he]
  have hc := assignment_inclusion_count P R hR
  have hc' : (((assignments P).filter (fun S => R ⊆ S)).card : ℝ) =
      ((n-R.card).choose (P.n1-R.card) : ℝ) := by
    convert congrArg (fun k : ℕ => (k : ℝ)) hc using 1 <;> congr! 3
  change _ / _ = _ / _
  simp only [assignments, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  convert congrArg (fun x : ℝ => x / (n.choose P.n1 : ℝ)) hc' using 1 <;>
    congr! 3
  ext S
  simp [assignments]

lemma DecisionLemma12_four_kernel {ι : Type*} [DecidableEq ι] (a : ι → ℝ)
    (c : ℕ → ℝ) (i j k l : ι) :
    a i * a j * a k * a l * c ({i,j,k,l} : Finset ι).card =
      c 4 * (a i * a j * a k * a l) +
      (c 3 - c 4) *
        ((if i = j then a i ^ 2 * a k * a l else 0) +
         (if i = k then a i ^ 2 * a j * a l else 0) +
         (if i = l then a i ^ 2 * a j * a k else 0) +
         (if j = k then a j ^ 2 * a i * a l else 0) +
         (if j = l then a j ^ 2 * a i * a k else 0) +
         (if k = l then a k ^ 2 * a i * a j else 0)) +
      (c 2 - 3 * c 3 + 2 * c 4) *
        ((if i = j ∧ i = k then a i ^ 3 * a l else 0) +
         (if i = j ∧ i = l then a i ^ 3 * a k else 0) +
         (if i = k ∧ i = l then a i ^ 3 * a j else 0) +
         (if j = k ∧ j = l then a j ^ 3 * a i else 0)) +
      (c 2 - 2 * c 3 + c 4) *
        ((if i = j ∧ k = l then a i ^ 2 * a k ^ 2 else 0) +
         (if i = k ∧ j = l then a i ^ 2 * a j ^ 2 else 0) +
         (if i = l ∧ j = k then a i ^ 2 * a j ^ 2 else 0)) +
      (c 1 - 7 * c 2 + 12 * c 3 - 6 * c 4) *
        (if i = j ∧ i = k ∧ i = l then a i ^ 4 else 0) := by
  by_cases h1 : i = j <;> by_cases h2 : i = k <;> by_cases h3 : i = l <;>
    by_cases h4 : j = k <;> by_cases h5 : j = l <;> by_cases h6 : k = l <;>
    simp_all [Finset.card_insert_of_notMem] <;> ring

lemma DecisionLemma12_four_sum {n : ℕ} (a : Fin n → ℝ)
    (ha : ∑ i, a i = 0) (c : ℕ → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      a i * a j * a k * a l * c ({i,j,k,l} : Finset (Fin n)).card) =
      (c 1 - 7 * c 2 + 12 * c 3 - 6 * c 4) * (∑ i, a i ^ 4) +
      3 * (c 2 - 2 * c 3 + c 4) * (∑ i, a i ^ 2) ^ 2 := by
  simp_rw [DecisionLemma12_four_kernel]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, ite_self, Finset.sum_const_zero]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, ha, mul_zero, zero_mul,
    add_zero, zero_add, Finset.sum_const_zero]
  ring

lemma DecisionLemma12_four_expansion {n : ℕ} (a : Fin n → ℝ)
    (S : Finset (Fin n)) :
    (∑ i ∈ S, a i) ^ 4 = ∑ i, ∑ j, ∑ k, ∑ l,
      (a i * a j * a k * a l) * (if ({i,j,k,l} : Finset (Fin n)) ⊆ S then 1 else 0) := by
  have hs : (∑ i ∈ S, a i) = ∑ i : Fin n, if i ∈ S then a i else 0 := by simp
  rw [hs, show (∑ i : Fin n, if i ∈ S then a i else 0) ^ 4 =
    (∑ i : Fin n, if i ∈ S then a i else 0) *
    (∑ i : Fin n, if i ∈ S then a i else 0) *
    (∑ i : Fin n, if i ∈ S then a i else 0) *
    (∑ i : Fin n, if i ∈ S then a i else 0) by ring]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    by_cases hk : k ∈ S <;> by_cases hl : l ∈ S <;>
    simp [hi, hj, hk, hl, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    <;> ring

/-- A fourth-moment bound with a constant independent of the sampling fraction. -/
lemma DecisionLemma12_fourth_moment {n : ℕ} (P : Population n)
    (hP : ValidDesign P) (hm : 4 ≤ P.n1) (a : Fin n → ℝ)
    (ha : ∑ i, a i = 0) :
    expectation P (fun S => (∑ i ∈ S, a i) ^ 4) ≤
      19 * (∑ i, a i ^ 2) ^ 2 := by
  let c : ℕ → ℝ := fun k => ((n-k).choose (P.n1-k) : ℝ) / (n.choose P.n1 : ℝ)
  have hmn := hP.2.2
  have hc (k : ℕ) (hk : k ≤ 4) : 0 ≤ c k ∧ c k ≤ 1 := by
    obtain ⟨R, _, hR⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin n))) (show k ≤ Finset.univ.card by
        simpa using (show k ≤ n by omega))
    have he := DecisionLemma12_inclusion P R (show R.card ≤ P.n1 by omega)
    change expectation P _ = c R.card at he
    rw [hR] at he
    rw [← he]
    constructor
    · exact DecisionLemma12_expectation_nonneg _ _ (fun _ _ => by split_ifs <;> norm_num)
    · calc
        _ ≤ expectation P (fun _ => 1) := DecisionLemma12_expectation_mono _
          (fun _ _ => by split_ifs <;> norm_num)
        _ = 1 := expectation_const P hP 1
  have he : expectation P (fun S => (∑ i ∈ S, a i) ^ 4) =
      (c 1 - 7*c 2 + 12*c 3 - 6*c 4) * (∑ i, a i ^ 4) +
      3*(c 2 - 2*c 3 + c 4) * (∑ i, a i ^ 2) ^ 2 := by
    simp_rw [DecisionLemma12_four_expansion, expectation_sum, expectation_mul]
    have hinc (i j k l : Fin n) :
        expectation P (fun S => if ({i,j,k,l} : Finset (Fin n)) ⊆ S then 1 else 0) =
          c ({i,j,k,l} : Finset (Fin n)).card := by
      apply DecisionLemma12_inclusion
      have hb : ({i,j,k,l} : Finset (Fin n)).card ≤ 4 := by
        exact (Finset.card_insert_le _ _).trans (by
          have h := Finset.card_insert_le j ({k,l} : Finset (Fin n))
          have h' := Finset.card_insert_le k ({l} : Finset (Fin n))
          simp only [Finset.card_singleton] at h'
          omega)
      omega
    simp_rw [hinc]
    exact DecisionLemma12_four_sum a ha c
  rw [he]
  have hc1 := hc 1 (by omega)
  have hc2 := hc 2 (by omega)
  have hc3 := hc 3 (by omega)
  have hc4 := hc 4 (by omega)
  have hs4 : 0 ≤ ∑ i, a i ^ 4 := Finset.sum_nonneg fun _ _ => by positivity
  have hsq : (∑ i, a i ^ 4) ≤ (∑ i, a i ^ 2) ^ 2 := by
    simpa only [← pow_mul] using Finset.sum_sq_le_sq_sum_of_nonneg
      (s := (Finset.univ : Finset (Fin n))) (f := fun i => a i ^ 2)
      (fun _ _ => sq_nonneg _)
  have h1 := mul_le_mul_of_nonneg_right
    (show c 1 - 7*c 2 + 12*c 3 - 6*c 4 ≤ 13 by linarith) hs4
  have h2 := mul_le_mul_of_nonneg_right
    (show 3*(c 2 - 2*c 3 + c 4) ≤ 6 by linarith) (sq_nonneg (∑ i, a i ^ 2))
  linarith

lemma DecisionLemma12_markov {n : ℕ} (P : Population n)
    (E : Finset (Fin n) → Prop) (f : Finset (Fin n) → ℝ) (t : ℝ)
    (hf : ∀ S ∈ assignments P, 0 ≤ f S)
    (hE : ∀ S ∈ assignments P, E S → t ≤ f S) :
    t * probability P E ≤ expectation P f := by
  have h := DecisionLemma12_expectation_mono P (f := fun S => t * if E S then 1 else 0)
    (g := f) (fun S hS => by by_cases he : E S <;> simp only [he, ite_true, ite_false,
      mul_one, mul_zero] <;> first | exact hE S hS he | exact hf S hS)
  rw [expectation_mul, ← DecisionLemma12_probability_eq_expectation P E] at h
  exact h

lemma DecisionLemma12_sample_fourth_tail {n : ℕ} (P : Population n)
    (hP : ValidDesign P) (hm : 4 ≤ P.n1) (a : Fin n → ℝ)
    (ha : ∑ i, a i = 0) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hb : ∑ i, a i ^ 2 ≤ C * n) :
    probability P (fun S => ε ≤ |(∑ i ∈ S, a i) / (n : ℝ)|) ≤
      (19 * C ^ 2 / ε ^ 4) * (1 / (n : ℝ) ^ 2) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := hP.1; omega)
  have ht := DecisionLemma12_markov P
    (fun S => ε ≤ |(∑ i ∈ S, a i) / (n : ℝ)|)
    (fun S => ((∑ i ∈ S, a i) / (n : ℝ)) ^ 4) (ε ^ 4)
    (fun _ _ => by positivity) (fun S _ he => by
      have h := pow_le_pow_left₀ hε.le he 4
      simpa only [← abs_pow, abs_of_nonneg (by positivity :
        0 ≤ ((∑ i ∈ S, a i) / (n : ℝ)) ^ 4)] using h)
  simp_rw [div_pow] at ht
  rw [expectation_div] at ht
  have hmoment := DecisionLemma12_fourth_moment P hP hm a ha
  have hs : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb2 : (∑ i, a i ^ 2) ^ 2 ≤ (C * n) ^ 2 :=
    pow_le_pow_left₀ hs hb 2
  have hu : expectation P (fun S => (∑ i ∈ S, a i) ^ 4) / (n : ℝ) ^ 4 ≤
      19 * (C * n) ^ 2 / (n : ℝ) ^ 4 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  apply (mul_le_mul_iff_left₀ (pow_pos hε 4)).mp
  have heq : 19 * (C * n) ^ 2 / (n : ℝ) ^ 4 =
      ((19 * C ^ 2 / ε ^ 4) * (1 / (n : ℝ) ^ 2)) * ε ^ 4 := by
    field_simp
    <;> ring
  rw [← heq]
  simpa only [mul_comm] using ht.trans hu

/-- Fourth moments give summable tails; no independence between sizes is needed. -/
lemma DecisionLemma12_ae_sample_small {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ j, Population (sizes j)) (Z : ∀ j, Ω → Finset (Fin (sizes j)))
    (hP : ∀ j, ValidDesign (P j)) (hZ : RandomizationSequence P μ Z)
    (hm : ∀ᶠ j in atTop, 4 ≤ (P j).n1)
    (a : ∀ j, Fin (sizes j) → ℝ) (ha : ∀ j, ∑ i, a j i = 0)
    (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hb : ∀ j, ∑ i, a j i ^ 2 ≤ C * sizes j) :
    ∀ᵐ ω ∂μ, ∀ᶠ j in atTop, |(∑ i ∈ Z j ω, a j i) / (sizes j : ℝ)| < ε := by
  let E := fun j (S : Finset (Fin (sizes j))) => ε ≤ |(∑ i ∈ S, a j i) / (sizes j : ℝ)|
  have hs : Summable (fun j => (19 * C ^ 2 / ε ^ 4) * (1 / (sizes j : ℝ) ^ 2)) := by
    exact ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).comp_injective
      hsizes.injective).mul_left _
  have hpr : Summable (fun j => probability (P j) (E j)) := by
    apply hs.of_norm_bounded_eventually_nat
    filter_upwards [hm] with j hj
    rw [Real.norm_eq_abs, abs_of_nonneg (DecisionLemma12_probability_nonneg _ _)]
    exact DecisionLemma12_sample_fourth_tail _ (hP j) hj _ (ha j) C ε hC hε (hb j)
  have hm' : (∑' j, μ {ω | E j (Z j ω)}) ≠ ∞ := by
    simp_rw [(hZ _ _).2]
    exact hpr.tsum_ofReal_ne_top
  have h := ae_eventually_notMem hm'
  filter_upwards [h] with ω hω
  filter_upwards [hω] with j hj
  exact lt_of_not_ge hj

lemma DecisionLemma12_sum_centered {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) :
    ∑ i, (q i - mean q) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mean]
  field_simp
  <;> ring

lemma DecisionLemma12_sum_centered_sq {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) :
    (∑ i, (q i - mean q) ^ 2) = (∑ i, q i ^ 2) - (n : ℝ) * (mean q) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he (i : Fin n) : (q i - mean q) ^ 2 = q i ^ 2 - (2 * mean q) * q i + (mean q) ^ 2 := by ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mean]
  field_simp
  <;> ring

lemma DecisionLemma12_ae_assignment {Ω : Type*} [MeasurableSpace Ω]
    {sizes : ℕ → ℕ} (P : ∀ j, Population (sizes j)) (μ : Measure Ω)
    (Z : ∀ j, Ω → Finset (Fin (sizes j))) (hZ : RandomizationSequence P μ Z) :
    ∀ᵐ ω ∂μ, ∀ j, Z j ω ∈ assignments (P j) := by
  apply ae_all_iff.mpr
  intro j
  rw [ae_iff]
  change μ {ω | Z j ω ∉ assignments (P j)} = 0
  rw [(hZ j (fun S => S ∉ assignments (P j))).2]
  have he : ((assignments (P j)).filter fun S => S ∉ assignments (P j)) = ∅ := by
    ext S
    simp
  have hz : probability (P j) (fun S => S ∉ assignments (P j)) = 0 := by
    unfold probability
    apply (div_eq_zero_iff).mpr
    left
    simp only [Nat.cast_eq_zero, Finset.card_eq_zero]
    ext S
    simp
  rw [hz, ENNReal.ofReal_zero]

lemma DecisionLemma12_observed_mean {n : ℕ} (P : Population n)
    (x : Bool → Fin n → ℝ) (hx : ∑ i, x false i = 0) (S : Finset (Fin n)) :
    mean (fun i => if i ∈ S then x true i else x false i) =
      (∑ i ∈ S, (x true i - x false i)) / (n : ℝ) := by
  have he (i : Fin n) : (if i ∈ S then x true i else x false i) =
      x false i + if i ∈ S then x true i - x false i else 0 := by
    by_cases hi : i ∈ S <;> simp [hi]
  simp only [mean, he, Finset.sum_add_distrib, hx, zero_add]
  simp

lemma DecisionLemma12_observed_second {n : ℕ} (P : Population n)
    (x : Bool → Fin n → ℝ) (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    mean (fun i => (if i ∈ S then x true i else x false i) ^ 2) =
      (fraction P * (∑ i, x true i ^ 2) + (1-fraction P) * (∑ i, x false i ^ 2)) / n +
      (∑ i ∈ S, (x true i ^ 2 - x false i ^ 2 -
        mean (fun i => x true i ^ 2 - x false i ^ 2))) / (n : ℝ) := by
  have hcard := (Finset.mem_powersetCard.mp hS).2
  have he (i : Fin n) : (if i ∈ S then x true i else x false i) ^ 2 =
      x false i ^ 2 + if i ∈ S then x true i ^ 2 - x false i ^ 2 else 0 := by
    by_cases hi : i ∈ S <;> simp [hi]
  simp only [mean, he, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, hcard, fraction]
  simp only [Finset.sum_ite_mem_eq]
  simp only [Finset.sum_sub_distrib]
  ring

/-- On the normalized scale, the actual observed variance is eventually positive a.s. -/
lemma DecisionLemma12_ae_observed_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ j, Population (sizes j)) (Z : ∀ j, Ω → Finset (Fin (sizes j)))
    (hP : ∀ j, ValidDesign (P j)) (hZ : RandomizationSequence P μ Z)
    (r C : ℝ) (hr : 0 < r) (hC : 0 ≤ C)
    (hl : ∀ j, r * sizes j ≤ ((P j).n1 : ℝ))
    (hu : ∀ j, ((P j).n1 : ℝ) ≤ (1-r) * sizes j)
    (x : ∀ j, Bool → Fin (sizes j) → ℝ)
    (hx0 : ∀ j a, ∑ i, x j a i = 0)
    (hx2 : ∀ j, (∑ i, x j true i ^ 2) + (∑ i, x j false i ^ 2) = (sizes j : ℝ)-1)
    (hx4 : ∀ j, (∑ i, x j true i ^ 4) + (∑ i, x j false i ^ 4) ≤ C * sizes j) :
    ∀ᵐ ω ∂μ, ∀ᶠ j in atTop,
      let y := fun i => if i ∈ Z j ω then x j true i else x j false i
      r/4 ≤ popVar y ∧ |mean y| ≤ 1 := by
  have hn (j) : 0 < sizes j := by have := (hP j).1; omega
  have hnR (j) : (0 : ℝ) < sizes j := by exact_mod_cast hn j
  have htop : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hsizes.tendsto_atTop
  have hm : ∀ᶠ j in atTop, 4 ≤ (P j).n1 := by
    filter_upwards [(htop.const_mul_atTop hr).eventually_ge_atTop 4] with j hj
    exact_mod_cast hj.trans (hl j)
  let a : ∀ j, Fin (sizes j) → ℝ := fun j i => x j true i - x j false i
  let b : ∀ j, Fin (sizes j) → ℝ := fun j i =>
    x j true i ^ 2 - x j false i ^ 2 - mean (fun i => x j true i ^ 2 - x j false i ^ 2)
  have ha (j) : ∑ i, a j i = 0 := by simp [a, Finset.sum_sub_distrib, hx0]
  have hb (j) : ∑ i, b j i = 0 := DecisionLemma12_sum_centered (hn j) _
  have ha2 (j) : ∑ i, a j i ^ 2 ≤ 2 * sizes j := by
    calc
      _ ≤ ∑ i, (2 * x j true i ^ 2 + 2 * x j false i ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        dsimp [a]
        nlinarith [sq_nonneg (x j true i + x j false i)]
      _ = 2 * ((sizes j : ℝ)-1) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← mul_add, hx2]
      _ ≤ _ := by linarith
  have hb2 (j) : ∑ i, b j i ^ 2 ≤ (2 * C) * sizes j := by
    change (∑ i, ((x j true i ^ 2 - x j false i ^ 2) - mean _) ^ 2) ≤ _
    rw [DecisionLemma12_sum_centered_sq (hn j)]
    calc
      _ ≤ ∑ i, (x j true i ^ 2 - x j false i ^ 2) ^ 2 := by
        have := mul_nonneg (hnR j).le (sq_nonneg (mean (fun i => x j true i ^ 2 - x j false i ^ 2)))
        linarith
      _ ≤ ∑ i, (2 * x j true i ^ 4 + 2 * x j false i ^ 4) := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [sq_nonneg (x j true i ^ 2 + x j false i ^ 2)]
      _ ≤ _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← mul_add]
        linarith [hx4 j]
  have hma := DecisionLemma12_ae_sample_small μ sizes hsizes P Z hP hZ hm a ha
    2 (min 1 (r/8)) (by norm_num) (lt_min zero_lt_one (by positivity)) ha2
  have hmb := DecisionLemma12_ae_sample_small μ sizes hsizes P Z hP hZ hm b hb
    (2*C) (r/8) (by positivity) (by positivity) hb2
  filter_upwards [hma, hmb, DecisionLemma12_ae_assignment P μ Z hZ] with ω hωa hωb hωS
  filter_upwards [hωa, hωb] with j hj hj'
  dsimp only
  let y : Fin (sizes j) → ℝ := fun i => if i ∈ Z j ω then x j true i else x j false i
  have hym : |mean y| < min 1 (r/8) := by
    simpa only [y, DecisionLemma12_observed_mean (P j) (x j) (hx0 j false), a] using hj
  have hym1 : |mean y| ≤ 1 := (hym.trans_le (min_le_left _ _)).le
  have hym2 : (mean y) ^ 2 ≤ r/8 := by
    have h := hym.trans_le (min_le_right _ _)
    nlinarith [sq_abs (mean y), abs_nonneg (mean y)]
  have hpi : r ≤ fraction (P j) := (le_div_iff₀ (hnR j)).mpr (hl j)
  have hpi' : fraction (P j) ≤ 1-r := (div_le_iff₀ (hnR j)).mpr (hu j)
  have hs1 : 0 ≤ ∑ i, x j true i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hs0 : 0 ≤ ∑ i, x j false i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hd : r/2 ≤ (fraction (P j) * (∑ i, x j true i ^ 2) +
      (1-fraction (P j)) * (∑ i, x j false i ^ 2)) / (sizes j : ℝ) := by
    apply (le_div_iff₀ (hnR j)).mpr
    have h1 := mul_le_mul_of_nonneg_right hpi hs1
    have h0 := mul_le_mul_of_nonneg_right (show r ≤ 1-fraction (P j) by linarith) hs0
    have hnr : (2 : ℝ) ≤ sizes j := by exact_mod_cast (hP j).1
    nlinarith [hx2 j]
  have hsecond := DecisionLemma12_observed_second (P j) (x j) (Z j ω) (hωS j)
  have herr : -(r/8) < (∑ i ∈ Z j ω, b j i) / (sizes j : ℝ) := (abs_lt.mp hj').1
  have hgap : r/4 ≤ mean (fun i => y i ^ 2) - (mean y) ^ 2 := by
    change mean (fun i => (if i ∈ Z j ω then x j true i else x j false i) ^ 2) - _ ≥ _
    rw [hsecond]
    change r/4 ≤ _ + (∑ i ∈ Z j ω, b j i) / (sizes j : ℝ) - _
    linarith
  refine ⟨?_, hym1⟩
  unfold popVar
  rw [DecisionLemma12_sum_centered_sq (hn j)]
  have hn1 : (0 : ℝ) < (sizes j : ℝ)-1 := by
    have hnr : (2 : ℝ) ≤ sizes j := by exact_mod_cast (hP j).1
    linarith
  apply (le_div_iff₀ hn1).mpr
  have hsum : (∑ i, y i ^ 2) = (sizes j : ℝ) * mean (fun i => y i ^ 2) := by
    dsimp [mean]
    field_simp [(hnR j).ne']
  rw [hsum]
  nlinarith [mul_nonneg (hnR j).le (sub_nonneg.mpr hgap)]

lemma DecisionLemma12_mse {n : ℕ} (P : Population n) (hP : ValidDesign P)
    (hm : 2 ≤ P.n1) (q : Fin n → ℝ) :
    expectation P (fun S => (groupMean S q - mean q) ^ 2) =
      (1 / (P.n1 : ℝ) - 1 / (n : ℝ)) * popVar q := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have := hP.1; omega)
  have hmR : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast (show P.n1 ≠ 0 by omega)
  have hn1 : (n : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hP.1
    linarith
  have h := AronowAudit.P031.sample_mean_squared_error (ι := Fin n) P.n1 hm
    (by simpa using hP.2.2.le) q
  change expectation P (fun S => (groupMean S q - groupMean Finset.univ q) ^ 2) = _ at h
  have he : groupMean Finset.univ q = mean q := by simp [groupMean, mean]
  rw [he] at h
  rw [h]
  simp only [AronowAudit.P031.popVariance, AronowAudit.P031.groupMean,
    Finset.card_univ, Fintype.card_fin, popVar, mean]
  field_simp
  <;> ring

lemma DecisionLemma12_mse_arm {n : ℕ} (P : Population n) (hP : ValidDesign P)
    (hm : 2 ≤ P.n1) (hk : 2 ≤ n-P.n1) (q : Fin n → ℝ) (a : Bool) :
    expectation P (fun S => (armMean q S a - mean q) ^ 2) ≤
      popVar q / (if a then (P.n1 : ℝ) else controlSize P) := by
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast hP.1
  have hv : 0 ≤ popVar q := div_nonneg
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by linarith)
  cases a
  · let Q : Population n := {P with n1 := n-P.n1}
    have hQ : ValidDesign Q := by
      dsimp [Q, ValidDesign]
      have := hP.2.1
      have := hP.2.2
      exact ⟨hP.1, by omega, by omega⟩
    have he : expectation P (fun S => (groupMean Sᶜ q - mean q) ^ 2) =
        expectation Q (fun S => (groupMean S q - mean q) ^ 2) := by
      simpa only [AronowAudit.P031.expectation, expectation, assignments,
        Fintype.card_fin, Q] using
        AronowAudit.P031.expectation_compl (ι := Fin n) P.n1
          (by simpa using hP.2.2.le) (fun S => (groupMean S q - mean q) ^ 2)
    simp only [armMean, Bool.false_eq_true, ↓reduceIte]
    rw [he, DecisionLemma12_mse Q hQ hk]
    have hcast : ((n-P.n1 : ℕ) : ℝ) = controlSize P := by
      rw [Nat.cast_sub hP.2.2.le]
      rfl
    change (1 / ((n-P.n1 : ℕ) : ℝ) - 1 / (n : ℝ)) * popVar q ≤ _
    rw [hcast]
    have h := mul_nonneg (show 0 ≤ 1/(n : ℝ) by positivity) hv
    dsimp [controlSize] at *
    calc
      _ = popVar q / ((n : ℝ)-(P.n1 : ℝ)) - (1/(n : ℝ))*popVar q := by ring
      _ ≤ _ := sub_le_self _ h
  · simp only [armMean, ↓reduceIte]
    rw [DecisionLemma12_mse P hP hm]
    have h := mul_nonneg (show 0 ≤ 1/(n : ℝ) by positivity) hv
    calc
      _ = popVar q / (P.n1 : ℝ) - (1/(n : ℝ))*popVar q := by ring
      _ ≤ _ := sub_le_self _ h

lemma DecisionLemma12_Eabs {n : ℕ} (P : Population n) (hP : ValidDesign P)
    (f : Finset (Fin n) → ℝ) :
    expectation P (fun S => |f S|) ≤ Real.sqrt (expectation P (fun S => f S ^ 2)) := by
  have hne : (assignments P).Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    simpa using hP.2.2.le
  have hc : (0 : ℝ) < (assignments P).card := by exact_mod_cast Finset.card_pos.mpr hne
  have h := Finset.sum_mul_sq_le_sq_mul_sq (assignments P) (fun S => |f S|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
    sq_abs] at h
  have hsq : (expectation P (fun S => |f S|)) ^ 2 ≤ expectation P (fun S => f S ^ 2) := by
    unfold expectation
    rw [div_pow]
    apply (div_le_iff₀ (pow_pos hc 2)).mpr
    convert h using 1 <;> field_simp <;> ring
  have hn0 := DecisionLemma12_expectation_nonneg P (fun S => f S ^ 2) (fun _ _ => sq_nonneg _)
  have hr := Real.sq_sqrt hn0
  have hr0 := Real.sqrt_nonneg (expectation P (fun S => f S ^ 2))
  have he0 := DecisionLemma12_expectation_nonneg P (fun S => |f S|) (fun _ _ => abs_nonneg _)
  nlinarith

lemma DecisionLemma12_variance {n : ℕ} (P : Population n) (hP : ValidDesign P)
    (hm : 2 ≤ P.n1) (q : Fin n → ℝ) :
    designVariance P (rawTau P q) =
      (P.n1 : ℝ) * controlSize P / (n : ℝ) ^ 3 * popVar q := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have := hP.1; omega)
  have hsum : expectation P (fun S => ∑ i ∈ S, q i) = (P.n1 : ℝ) * mean q := by
    have h := AronowAudit.P031.expected_group_sum (ι := Fin n) P.n1 (by omega : 1 ≤ P.n1)
        (by simpa using hP.2.2.le) q
    simp only [AronowAudit.P031.expectation, AronowAudit.P031.groupMean,
      expectation, assignments, Finset.card_univ, Fintype.card_fin, mean] at h
    convert h using 1 <;> simp only [AronowAudit.P031.expectation, expectation, assignments,
      Fintype.card_fin, mean] <;> ring
  have he0 : expectation P (rawTau P q) = 0 := by
    change expectation P (fun S => rawTau P q S) = 0
    simp_rw [rawTau_sum]
    rw [expectation_div, expectation_sub, expectation_const P hP, hsum]
    dsimp [fraction, mean]
    ring
  unfold designVariance
  rw [he0]
  simp only [sub_zero]
  have he : ∀ S : Finset (Fin n), rawTau P q S ^ 2 =
      ((∑ i ∈ S, q i) - (P.n1 : ℝ) * mean q) ^ 2 / (n : ℝ) ^ 2 := by
    intro S
    rw [rawTau_sum]
    dsimp [fraction, mean]
    ring
  simp_rw [he]
  rw [expectation_div]
  have h := AronowAudit.P031.expected_group_deviation (ι := Fin n) P.n1 hm
    (by simpa using hP.2.2.le) q
  change expectation P (fun S => ((∑ i ∈ S, q i) - (P.n1 : ℝ) * groupMean Finset.univ q) ^ 2) = _ at h
  have hmean : groupMean Finset.univ q = mean q := by simp [groupMean, mean]
  rw [hmean] at h
  rw [h]
  simp only [AronowAudit.P031.popVariance, AronowAudit.P031.groupMean,
    Finset.card_univ, Fintype.card_fin, popVar, mean, controlSize]
  field_simp
  <;> ring

lemma DecisionLemma12_convex_error (p A B C D e : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D) (he : 0 ≤ e) :
    |(1-p)*(A-C) + p*(B-D) - e| ≤ |A| + |B| + C + D + e := by
  have hp0 : 0 ≤ 1-p := by linarith
  have ha := mul_le_mul_of_nonneg_left (le_abs_self A) hp0
  have ha' := mul_le_mul_of_nonneg_left (neg_abs_le A) hp0
  have hb := mul_le_mul_of_nonneg_left (le_abs_self B) hp
  have hb' := mul_le_mul_of_nonneg_left (neg_abs_le B) hp
  have ha2 := mul_le_mul_of_nonneg_right (show 1-p ≤ 1 by linarith) (abs_nonneg A)
  have hb2 := mul_le_mul_of_nonneg_right hp1 (abs_nonneg B)
  have hc := mul_le_mul_of_nonneg_right (show 1-p ≤ 1 by linarith) hC
  have hd := mul_le_mul_of_nonneg_right hp1 hD
  have hc0 := mul_nonneg hp0 hC
  have hd0 := mul_nonneg hp hD
  apply abs_le.mpr
  constructor <;> nlinarith

lemma DecisionLemma12_ratio_identity {n : ℕ} (P : Population n) (hP : ValidDesign P)
    (hm : 2 ≤ P.n1) (q : Fin n → ℝ) (hv : 0 < popVar q)
    (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    let z := fun i => q i - mean q
    let F := fun a => (armMean (fun i => z i ^ 2) S a - mean (fun i => z i ^ 2)) / popVar q
    let G := fun a => (armMean q S a - mean q) ^ 2 / popVar q
    rawSigma2 P q S / designVariance P (rawTau P q) - 1 =
      (1-fraction P)*(F true-G true) + fraction P*(F false-G false) - 1/(n : ℝ) := by
  have hcard := (Finset.mem_powersetCard.mp hS).2
  have hc : Sᶜ.card = n-P.n1 := by simp [Finset.card_compl, hcard]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := hP.1; omega)
  have hmR : (0 : ℝ) < P.n1 := by exact_mod_cast hP.2.1
  have hkR : 0 < controlSize P := by
    dsimp [controlSize]
    exact sub_pos.mpr (by exact_mod_cast hP.2.2)
  have hsn : S.Nonempty := Finset.card_pos.mp (by omega)
  have hcn : Sᶜ.Nonempty := Finset.card_pos.mp (by have := hP.2.2; omega)
  have ht := square_centering S q (mean q) hsn
  have h0 := square_centering Sᶜ q (mean q) hcn
  have hcast : ((n-P.n1 : ℕ) : ℝ) = controlSize P := by
    rw [Nat.cast_sub hP.2.2.le]
    rfl
  change (∑ i ∈ S, (q i - groupMean S q) ^ 2) / (S.card : ℝ) = _ at ht
  change (∑ i ∈ Sᶜ, (q i - groupMean Sᶜ q) ^ 2) / (Sᶜ.card : ℝ) = _ at h0
  rw [hcard] at ht
  rw [hc, hcast] at h0
  have hst := (div_eq_iff hmR.ne').mp ht
  have hsc := (div_eq_iff hkR.ne').mp h0
  dsimp only
  rw [rawSigma2, DecisionLemma12_variance P hP hm q]
  simp only [armMean, Bool.false_eq_true, ↓reduceIte]
  rw [hst, hsc]
  have hzmean : mean (fun i => (q i-mean q) ^ 2) = ((n : ℝ)-1)/(n : ℝ)*popVar q := by
    have hn1 : (n : ℝ)-1 ≠ 0 := by
      have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hP.1
      linarith
    change (∑ i, (q i-mean q)^2)/(n : ℝ) =
      ((n : ℝ)-1)/(n : ℝ)*((∑ i, (q i-mean q)^2)/((n : ℝ)-1))
    field_simp
    <;> ring
  rw [hzmean]
  dsimp [fraction, controlSize] at *
  field_simp [hnR.ne', hmR.ne', hkR.ne', hv.ne']
  <;> ring

lemma DecisionLemma12_ratio_error {n : ℕ} (P : Population n) (hP : ValidDesign P)
    (hm : 2 ≤ P.n1) (q : Fin n → ℝ) (hv : 0 < popVar q)
    (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    let z := fun i => q i - mean q
    let F := fun a => (armMean (fun i => z i ^ 2) S a - mean (fun i => z i ^ 2)) / popVar q
    let G := fun a => (armMean q S a - mean q) ^ 2 / popVar q
    |rawSigma2 P q S / designVariance P (rawTau P q) - 1| ≤
      |F true| + |F false| + G true + G false + 1/(n : ℝ) := by
  dsimp only
  rw [DecisionLemma12_ratio_identity P hP hm q hv S hS]
  apply DecisionLemma12_convex_error
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply (div_le_one (by exact_mod_cast (show 0 < n by have := hP.1; omega))).mpr
    exact_mod_cast hP.2.2.le
  · positivity
  · positivity
  · positivity

lemma DecisionLemma12_conditional_bound {n : ℕ} (P : Population n) (hP : ValidDesign P)
    (hm : 2 ≤ P.n1) (hk : 2 ≤ n-P.n1) (q : Fin n → ℝ) (hv : 0 < popVar q)
    (r D κ : ℝ) (hr : 0 < r) (hD : 0 ≤ D) (hκ : 0 < κ)
    (hl : r*n ≤ (P.n1 : ℝ)) (hu : (P.n1 : ℝ) ≤ (1-r)*n)
    (hq : ∑ i, (q i-mean q) ^ 4 ≤ D * n * (popVar q) ^ 2) :
    probability P (fun S => |rawSigma2 P q S / designVariance P (rawTau P q) - 1| ≥ κ) ≤
      (2 * Real.sqrt (2*D/(r*n)) + 2/(r*n) + 1/(n : ℝ)) / κ := by
  let z : Fin n → ℝ := fun i => q i - mean q
  let F := fun a S => (armMean (fun i => z i ^ 2) S a - mean (fun i => z i ^ 2)) / popVar q
  let G := fun a S => (armMean q S a - mean q) ^ 2 / popVar q
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast hP.1
  have hn0 : (0 : ℝ) < n := by linarith
  have hsize (a : Bool) : r*n ≤ (if a then (P.n1 : ℝ) else controlSize P) := by
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte, controlSize] <;> linarith
  have hspos (a : Bool) : 0 < (if a then (P.n1 : ℝ) else controlSize P) :=
    (mul_pos hr hn0).trans_le (hsize a)
  have hvar : popVar (fun i => z i ^ 2) ≤ 2*D*(popVar q)^2 := by
    change (∑ i, (z i ^ 2 - mean (fun i => z i ^ 2)) ^ 2) / ((n : ℝ)-1) ≤ _
    rw [DecisionLemma12_sum_centered_sq (by have := hP.1; omega)]
    apply (div_le_iff₀ (by linarith : 0 < (n : ℝ)-1)).mpr
    have hmean := mul_nonneg hn0.le (sq_nonneg (mean (fun i => z i ^ 2)))
    have hqn : (∑ i, (z i ^ 2) ^ 2) ≤ D*n*(popVar q)^2 := by simpa only [← pow_mul] using hq
    have hnonneg : 0 ≤ D*(popVar q)^2 := by positivity
    nlinarith [mul_nonneg (by linarith : 0 ≤ (n : ℝ)-2) hnonneg]
  have hF (a : Bool) : expectation P (fun S => |F a S|) ≤ Real.sqrt (2*D/(r*n)) := by
    apply (DecisionLemma12_Eabs P hP (F a)).trans
    apply Real.sqrt_le_sqrt
    have he := DecisionLemma12_mse_arm P hP hm hk (fun i => z i ^ 2) a
    change expectation P (fun S => (_ / popVar q) ^ 2) ≤ _
    simp_rw [div_pow]
    rw [expectation_div]
    calc
      _ ≤ (popVar (fun i => z i ^ 2) / (if a then (P.n1 : ℝ) else controlSize P)) / (popVar q)^2 :=
        div_le_div_of_nonneg_right he (sq_nonneg _)
      _ ≤ (2*D*(popVar q)^2 / (if a then (P.n1 : ℝ) else controlSize P)) / (popVar q)^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact div_le_div_of_nonneg_right hvar (hspos a).le
      _ = 2*D / (if a then (P.n1 : ℝ) else controlSize P) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (mul_pos hr hn0) (hsize a)
  have hG (a : Bool) : expectation P (G a) ≤ 1/(r*n) := by
    dsimp only [G]
    rw [expectation_div]
    calc
      _ ≤ (popVar q / (if a then (P.n1 : ℝ) else controlSize P)) / popVar q :=
        div_le_div_of_nonneg_right (DecisionLemma12_mse_arm P hP hm hk q a) hv.le
      _ = 1/(if a then (P.n1 : ℝ) else controlSize P) := by field_simp
      _ ≤ _ := one_div_le_one_div_of_le (mul_pos hr hn0) (hsize a)
  have he := DecisionLemma12_expectation_mono P
    (fun S hS => DecisionLemma12_ratio_error P hP hm q hv S hS)
  change expectation P (fun S => |rawSigma2 P q S / designVariance P (rawTau P q) - 1|) ≤
    expectation P (fun S => |F true S| + |F false S| + G true S + G false S + 1/(n : ℝ)) at he
  simp_rw [DecisionLemma12_expectation_add, expectation_const P hP] at he
  have hmark := DecisionLemma12_markov P
    (fun S => |rawSigma2 P q S / designVariance P (rawTau P q) - 1| ≥ κ)
    (fun S => |rawSigma2 P q S / designVariance P (rawTau P q) - 1|) κ
    (fun _ _ => abs_nonneg _) (fun _ _ h => h)
  apply (le_div_iff₀ hκ).mpr
  have h1 := hF true
  have h0 := hF false
  have hg1 := hG true
  have hg0 := hG false
  have htw : 1/(r*n)+1/(r*n) = 2/(r*n) := by ring
  nlinarith

lemma DecisionLemma12_normalized {n : ℕ} (P : Population n) (δ r A : ℝ)
    (hA : 0 < A) (hP : Theta P δ r A)
    (hpositive : ∀ a, 0 < popVar (w P a (late P))) :
    let T := popVar (w P true (late P)) + popVar (w P false (late P))
    let x := fun a i => v P a (late P) i / Real.sqrt T
    (∀ a, ∑ i, x a i = 0) ∧
    (∑ i, x true i ^ 2) + (∑ i, x false i ^ 2) = (n : ℝ)-1 ∧
    (∑ i, x true i ^ 4) + (∑ i, x false i ^ 4) ≤ (2*A^4) * n := by
  let T := popVar (w P true (late P)) + popVar (w P false (late P))
  let x := fun a i => v P a (late P) i / Real.sqrt T
  change (∀ a, ∑ i, x a i = 0) ∧ _ ∧ _
  have hT : 0 < T := add_pos (hpositive true) (hpositive false)
  have hs : Real.sqrt T ≠ 0 := (Real.sqrt_pos.mpr hT).ne'
  have hs2 : (Real.sqrt T)^2 = T := Real.sq_sqrt hT.le
  have hn : 0 < n := by have := hP.1.1; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ)-1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hP.1.1
    linarith
  have hx0 (a) : ∑ i, x a i = 0 := by
    simp only [x, ← Finset.sum_div]
    change (∑ i, (w P a (late P) i - mean (w P a (late P)))) / Real.sqrt T = 0
    rw [DecisionLemma12_sum_centered hn]
    simp
  have hsq (a) : ∑ i, x a i ^ 2 = ((n : ℝ)-1)*popVar (w P a (late P))/T := by
    simp only [x, div_pow, ← Finset.sum_div, hs2, popVar, v]
    field_simp
    <;> ring
  have hfourth (a) : ∑ i, x a i ^ 4 ≤ A^4 * n := by
    have hf := hP.2.2.2.2.2.2 a
    have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) hf 4
    change (fourthNorm (v P a (late P)))^4 ≤ (A*Real.sqrt (popVar (w P a (late P))))^4 at hp
    have hmean4 : 0 ≤ mean (fun i => v P a (late P) i ^ 4) := by
      exact div_nonneg (Finset.sum_nonneg fun _ _ => by positivity) hnR.le
    have hroot : (fourthNorm (v P a (late P))) ^ 4 = mean (fun i => v P a (late P) i ^ 4) := by
      unfold fourthNorm
      calc
        _ = ((Real.sqrt (Real.sqrt (mean (fun i => v P a (late P) i ^ 4))))^2)^2 := by ring
        _ = (Real.sqrt (mean (fun i => v P a (late P) i ^ 4)))^2 := by
          rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
        _ = _ := Real.sq_sqrt hmean4
    have hrhs : (A*Real.sqrt (popVar (w P a (late P))))^4 =
        A^4 * (popVar (w P a (late P)))^2 := by
      rw [mul_pow, show (Real.sqrt (popVar (w P a (late P))))^4 =
        ((Real.sqrt (popVar (w P a (late P))))^2)^2 by ring,
        Real.sq_sqrt (hpositive a).le]
    rw [hroot, hrhs] at hp
    have hsum : ∑ i, v P a (late P) i ^ 4 ≤ (A^4*n)*(popVar (w P a (late P)))^2 := by
      nlinarith only [(div_le_iff₀ hnR).mp hp]
    have hleT : popVar (w P a (late P)) ≤ T := by
      cases a <;> dsimp [T] <;> linarith [hpositive true, hpositive false]
    have hvar2 := pow_le_pow_left₀ (hpositive a).le hleT 2
    have hm := mul_le_mul_of_nonneg_left hvar2 (show 0 ≤ A^4*n by positivity)
    simp only [x, div_pow, ← Finset.sum_div]
    apply (div_le_iff₀ (pow_pos (Real.sqrt_pos.mpr hT) 4)).mpr
    have hroot4 : (Real.sqrt T)^4 = T^2 := by
      calc
        _ = ((Real.sqrt T)^2)^2 := by ring
        _ = _ := by rw [hs2]
    rw [hroot4]
    exact hsum.trans hm
  refine ⟨hx0, ?_, ?_⟩
  · rw [hsq, hsq]
    change ((n : ℝ)-1)*popVar (w P true (late P))/T +
      ((n : ℝ)-1)*popVar (w P false (late P))/T = _
    dsimp [T] at *
    field_simp
    <;> ring
  · linarith [hfourth true, hfourth false]

lemma DecisionLemma12_mean_affine {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (c s : ℝ) :
    mean (fun i => c+s*q i) = c+s*mean q := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [mean, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  field_simp
  <;> ring

lemma DecisionLemma12_var_affine {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (c s : ℝ) :
    popVar (fun i => c+s*q i) = s^2*popVar q := by
  unfold popVar
  rw [DecisionLemma12_mean_affine hn]
  have he (i : Fin n) : (c+s*q i - (c+s*mean q))^2 = s^2*(q i-mean q)^2 := by ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  ring

lemma DecisionLemma12_relative_fourth {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (b C c s : ℝ) (hb : 0 < b) (hC : 0 ≤ C) (hs : s ≠ 0)
    (hv : b ≤ popVar q) (hm : |mean q| ≤ 1) (hq : ∑ i, q i ^ 4 ≤ C*n) :
    0 < popVar (fun i => c+s*q i) ∧
    (∑ i, (c+s*q i-mean (fun i => c+s*q i)) ^ 4) ≤
      (8*(C+1)/b^2)*n*(popVar (fun i => c+s*q i))^2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcenter : ∑ i, (q i-mean q)^4 ≤ 8*(C+1)*n := by
    have hp (a d : ℝ) : (a-d)^4 ≤ 8*a^4+8*d^4 := by
      nlinarith [sq_nonneg (a^2-d^2), sq_nonneg ((a+d)^2)]
    have hm4 : (mean q)^4 ≤ 1 := by
      have h := pow_le_pow_left₀ (abs_nonneg (mean q)) hm 4
      simpa only [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ (mean q)^4), one_pow] using h
    calc
      _ ≤ ∑ i, (8*q i ^ 4 + 8*(mean q)^4) := Finset.sum_le_sum (fun i _ => hp _ _)
      _ ≤ _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        nlinarith [mul_le_mul_of_nonneg_left hm4 hnR.le]
  have hvar2 : b^2 ≤ (popVar q)^2 := pow_le_pow_left₀ hb.le hv 2
  have hupper : 8*(C+1)*n ≤ (8*(C+1)/b^2)*n*(popVar q)^2 := by
    calc
      _ = (8*(C+1)*n*b^2)/b^2 := by field_simp
      _ ≤ (8*(C+1)*n*(popVar q)^2)/b^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left hvar2 (by positivity)
      _ = _ := by ring
  rw [DecisionLemma12_var_affine hn]
  refine ⟨mul_pos (sq_pos_of_ne_zero hs) (hb.trans_le hv), ?_⟩
  rw [DecisionLemma12_mean_affine hn]
  have he (i : Fin n) : (c+s*q i - (c+s*mean q))^4 = s^4*(q i-mean q)^4 := by ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  have ht := mul_le_mul_of_nonneg_left (hcenter.trans hupper) (show 0 ≤ s^4 by positivity)
  convert ht using 1 <;> ring

lemma DecisionLemma12_observed_affine {n : ℕ} (P : Population n)
    (hm : MonotoneReceipt P) (hc : (compliers P).Nonempty)
    (hpositive : ∀ a, 0 < popVar (w P a (late P))) (S : Finset (Fin n)) :
    let T := popVar (w P true (late P)) + popVar (w P false (late P))
    let x := fun a i => v P a (late P) i / Real.sqrt T
    observedW P (late P) S = fun i => mean (w P false (late P)) +
      Real.sqrt T * (if i ∈ S then x true i else x false i) := by
  dsimp only
  have hT := add_pos (hpositive true) (hpositive false)
  have hs := (Real.sqrt_pos.mpr hT).ne'
  have he := mean_w_equal_at_late P hm hc
  funext i
  by_cases hi : i ∈ S
  · rw [observedW_treated P _ S i hi, if_pos hi]
    dsimp [v]
    rw [he]
    field_simp
    <;> ring
  · rw [observedW_control P _ S i (Finset.mem_compl.mpr hi), if_neg hi]
    dsimp [v]
    field_simp
    <;> ring

/-- Corrected Lemma 12 under the positive-variance hypothesis. -/
theorem corrected_lemma12_proof {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ n, Population (sizes n))
    (Z : ∀ n, Ω → Finset (Fin (sizes n))) (δ r A : ℝ)
    (hδ : δ < 1) (hr : 0 < r ∧ r ≤ 1/2) (hA : 0 < A)
    (hP : ∀ n, Theta (P n) δ r A)
    (hpositive : ∀ n a, 0 < popVar (w (P n) a (late (P n))))
    (hZ : RandomizationSequence P μ Z)
    (sub : ℕ → ℕ) (hsub : StrictMono sub) :
    ∀ᵐ ω ∂μ, ∀ κ : ℝ, 0 < κ → Tendsto (fun j =>
      let N := sub j
      let q := observedW (P N) (late (P N)) (Z N ω)
      probability (P N) (fun S => |rawSigma2 (P N) q S /
        designVariance (P N) (rawTau (P N) q) - 1| ≥ κ)) atTop (nhds 0) := by
  let T := fun j => popVar (w (P j) true (late (P j))) + popVar (w (P j) false (late (P j)))
  let x := fun j a i => v (P j) a (late (P j)) i / Real.sqrt (T j)
  have hT (j) : 0 < T j := add_pos (hpositive j true) (hpositive j false)
  have hnormal := fun j => DecisionLemma12_normalized (P j) δ r A hA (hP j) (hpositive j)
  have hlow := DecisionLemma12_ae_observed_lower μ sizes hsizes P Z (fun j => (hP j).1) hZ
    r (2*A^4) hr.1 (by positivity)
    (fun j => (hP j).2.2.2.1) (fun j => (hP j).2.2.2.2.1) x
    (fun j => (hnormal j).1) (fun j => (hnormal j).2.1) (fun j => (hnormal j).2.2)
  let C : ℝ := 2*A^4
  let D : ℝ := 8*(C+1)/(r/4)^2
  have hD : 0 ≤ D := by dsimp [D, C]; positivity
  have htop : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hsizes.tendsto_atTop
  have harmlarge : ∀ᶠ j in atTop, 2 ≤ (P j).n1 ∧ 2 ≤ sizes j-(P j).n1 := by
    filter_upwards [(htop.const_mul_atTop hr.1).eventually_ge_atTop 2] with j hj
    constructor
    · exact_mod_cast hj.trans (hP j).2.2.2.1
    · have hu := (hP j).2.2.2.2.1
      have hsize := (hP j).1.2.2.le
      have hcast : ((sizes j-(P j).n1 : ℕ) : ℝ) = (sizes j : ℝ) - ((P j).n1 : ℝ) :=
        Nat.cast_sub hsize
      exact_mod_cast (show (2 : ℝ) ≤ ((sizes j-(P j).n1 : ℕ) : ℝ) by rw [hcast]; linarith)
  filter_upwards [hlow] with ω hω
  have hgood : ∀ᶠ j in atTop,
      let q := observedW (P j) (late (P j)) (Z j ω)
      0 < popVar q ∧ (∑ i, (q i-mean q)^4) ≤ D*sizes j*(popVar q)^2 := by
    filter_upwards [hω] with j hj
    let y := fun i => if i ∈ Z j ω then x j true i else x j false i
    have hy4 : ∑ i, y i ^ 4 ≤ C*sizes j := by
      calc
        _ ≤ ∑ i, (x j true i ^ 4 + x j false i ^ 4) := by
          apply Finset.sum_le_sum
          intro i _
          dsimp [y]
          have h1 : 0 ≤ x j true i ^ 4 := by positivity
          have h0 : 0 ≤ x j false i ^ 4 := by positivity
          by_cases hi : i ∈ Z j ω <;> simp only [hi, ite_true, ite_false] <;> linarith
        _ ≤ _ := by
          rw [Finset.sum_add_distrib]
          exact (hnormal j).2.2
    have h := DecisionLemma12_relative_fourth (show 0 < sizes j by have := (hP j).1.1; omega)
      y (r/4) C (mean (w (P j) false (late (P j)))) (Real.sqrt (T j))
      (div_pos hr.1 (by norm_num)) (by dsimp [C]; positivity) (Real.sqrt_pos.mpr (hT j)).ne'
      hj.1 hj.2 hy4
    rw [DecisionLemma12_observed_affine (P j) (hP j).2.1 (hP j).2.2.1 (hpositive j)]
    exact h
  intro κ hκ
  have hN : Tendsto (fun j => (sizes (sub j) : ℝ)) atTop atTop := htop.comp hsub.tendsto_atTop
  have hinv : Tendsto (fun j => 1/(sizes (sub j) : ℝ)) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hN
  have hlin : Tendsto (fun j => 2*D/(r*(sizes (sub j) : ℝ))) atTop (nhds 0) := by
    have h := hinv.const_mul (2*D/r)
    simp only [mul_zero] at h
    convert h using 1
    funext j
    ring
  have hroot : Tendsto (fun j => Real.sqrt (2*D/(r*(sizes (sub j) : ℝ)))) atTop (nhds 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hlin
  have hlin' : Tendsto (fun j => 2/(r*(sizes (sub j) : ℝ))) atTop (nhds 0) := by
    have h := hinv.const_mul (2/r)
    simp only [mul_zero] at h
    convert h using 1
    funext j
    ring
  have hb : Tendsto (fun j =>
      (2*Real.sqrt (2*D/(r*(sizes (sub j) : ℝ))) + 2/(r*(sizes (sub j) : ℝ)) +
        1/(sizes (sub j) : ℝ))/κ) atTop (nhds 0) := by
    simpa only [mul_zero, add_zero, zero_add, zero_div] using
      (((hroot.const_mul 2).add hlin').add hinv).div_const κ
  apply squeeze_zero' (Eventually.of_forall (fun _ => DecisionLemma12_probability_nonneg _ _)) _ hb
  filter_upwards [hsub.tendsto_atTop.eventually hgood, hsub.tendsto_atTop.eventually harmlarge] with j hj ha
  dsimp only at hj ⊢
  exact DecisionLemma12_conditional_bound (P (sub j)) (hP (sub j)).1 ha.1 ha.2 _ hj.1
    r D κ hr.1 hD hκ (hP (sub j)).2.2.2.1 (hP (sub j)).2.2.2.2.1 hj.2

end
end AronowAudit.P002.Wave1
