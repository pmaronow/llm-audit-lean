import AronowAudit.P045.P045_Spillover
import AronowAudit.P002.Wave1.Gap.GLP0021B1

/-! Exact finite moments for the corrected two-stage direct-effect variance.
The complete-randomization contrast identity is from P002. The identities below
use the actual finite laws and centered variances. -/

namespace AronowAudit.P045.Wave1

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open scoped BigOperators
open Finset
noncomputable section

lemma dvc_average_congr {I : Type*} (S : Finset I) {f g : I → ℝ}
    (h : ∀ i ∈ S, f i = g i) : average S f = average S g := by
  unfold average
  rw [Finset.sum_congr rfl h]

lemma dvc_average_add {I : Type*} (S : Finset I) (f g : I → ℝ) :
    average S (fun i => f i + g i) = average S f + average S g := by
  simp [average, Finset.sum_add_distrib, add_div]

lemma dvc_average_sub {I : Type*} (S : Finset I) (f g : I → ℝ) :
    average S (fun i => f i - g i) = average S f - average S g := by
  simp [average, Finset.sum_sub_distrib, sub_div]

lemma dvc_average_mul {I : Type*} (S : Finset I) (f : I → ℝ) (c : ℝ) :
    average S (fun i => c * f i) = c * average S f := by
  simp [average, ← Finset.mul_sum, mul_div_assoc]

lemma dvc_average_div {I : Type*} (S : Finset I) (f : I → ℝ) (c : ℝ) :
    average S (fun i => f i / c) = average S f / c := by
  simp [average, Finset.sum_div, div_right_comm]

lemma dvc_expect_const {Ω : Type*} [Fintype Ω] (q : Ω → ℝ)
    (hq : ∑ w, q w = 1) (c : ℝ) : expect q (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, hq]

lemma dvc_expect_mul {Ω : Type*} [Fintype Ω] (q : Ω → ℝ) (f : Ω → ℝ) (c : ℝ) :
    expect q (fun w => c * f w) = c * expect q f := by
  simpa only [mul_comm c] using expect_mul_const q f c

/-- Uniform-subset averages and the vendored complete-randomization design
have identical masses, including the census boundary. -/
lemma dvc_subset_bridge {N s : ℕ} (hs : s ≤ N) (f : Finset (Fin N) → ℝ) :
    average (firstStageSets N s) f =
      (Causalean.Experimentation.DesignBased.completeRandomization (V := Fin N) s
        (by simpa using hs)).E (fun S => f S.val) := by
  classical
  have hmem (S : Finset (Fin N)) : S ∈ firstStageSets N s ↔ S.card = s := by
    simp [firstStageSets, Finset.mem_powersetCard]
  have hsum : (∑ S ∈ firstStageSets N s, f S) =
      ∑ S : {S : Finset (Fin N) // S.card = s}, f S.val :=
    Finset.sum_subtype _ hmem f
  have hcard : (firstStageSets N s).card =
      Fintype.card {S : Finset (Fin N) // S.card = s} := by
    rw [Causalean.Experimentation.DesignBased.completeRandomization_card]
    simp [firstStageSets]
  unfold average Causalean.Experimentation.DesignBased.FiniteDesign.E
  rw [hsum, hcard]
  simp only [Causalean.Experimentation.DesignBased.completeRandomization,
    ← Finset.mul_sum, one_div]
  ring


lemma dvc_subset_mean_square {N s : ℕ} (hs0 : 0 < s) (hs : s ≤ N) (hN : 2 ≤ N)
    (x : Fin N → ℝ) :
    average (firstStageSets N s) (fun S => (average S x - mean x)^2) =
      (1 / (s : ℝ) - 1 / (N : ℝ)) * popVar x := by
  have hf : (fun S : {S : Finset (Fin N) // S.card = s} => average S.val x) =
      Causalean.Experimentation.FinitePopulationMoments.sampleMean s x := by
    funext S
    simp [average, S.property,
      Causalean.Experimentation.FinitePopulationMoments.sampleMean,
      ← Finset.sum_filter, Finset.filter_mem_eq_inter]
  rw [dvc_subset_bridge hs]
  have hv := Causalean.Experimentation.FinitePopulationMoments.Var_sampleMean
    s (by simpa using hs) hs0 (by simpa using hN) x
  unfold Causalean.Experimentation.DesignBased.FiniteDesign.Var at hv
  rw [Causalean.Experimentation.FinitePopulationMoments.E_sampleMean s
    (by simpa using hs) hs0] at hv
  simpa only [← hf, Causalean.Experimentation.FinitePopulationMoments.popVar,
    Causalean.Experimentation.FinitePopulationMoments.popMean, mean, popVar,
    rawSampleVar, average, Finset.card_univ, Fintype.card_fin] using hv

lemma dvc_subset_sum {N s : ℕ} (hs0 : 0 < s) (hs : s ≤ N) (x : Fin N → ℝ) :
    average (firstStageSets N s) (fun S => ∑ i ∈ S, x i) =
      (s : ℝ) / N * ∑ i, x i := by
  have hn : (s : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hs0)
  have h := uniform_first_stage_mean hs0 hs x
  rw [dvc_average_div] at h
  unfold mean at h
  simp only [Fintype.card_fin] at h
  calc
    _ = (average (firstStageSets N s) (fun S => ∑ i ∈ S, x i) / s) * s :=
      (div_mul_cancel₀ _ hn).symm
    _ = _ := by rw [h]; ring

/-- Unbiased sample variance follows by recentering at the population mean
and using the exact sample-mean variance, so no extra inclusion lemma is assumed. -/
lemma dvc_subset_sample_variance {N s : ℕ} (hs2 : 2 ≤ s) (hs : s ≤ N)
    (x : Fin N → ℝ) :
    average (firstStageSets N s) (fun S => rawSampleVar S x) = popVar x := by
  have hs0 : 0 < s := by omega
  have hN : 2 ≤ N := by omega
  have hsR : (s : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hs0)
  have hNR : (N : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (by omega))
  have hs1 : (s : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ s := by exact_mod_cast hs2
    linarith
  have hform : average (firstStageSets N s) (fun S => rawSampleVar S x) =
      average (firstStageSets N s) (fun S =>
        ((∑ i ∈ S, (x i - mean x)^2) - s * (average S x - mean x)^2) / ((s : ℝ)-1)) := by
    apply dvc_average_congr
    intro S hS
    have hc := (Finset.mem_powersetCard.mp hS).2
    rw [raw_sample_variance_centered S (by omega) x (mean x), hc]
  rw [hform, dvc_average_div, dvc_average_sub, dvc_average_mul,
    dvc_subset_sum hs0 hs, dvc_subset_mean_square hs0 hs hN]
  unfold popVar rawSampleVar
  simp only [Finset.card_univ, Fintype.card_fin]
  have hav : average (univ : Finset (Fin N)) x = mean x := by
    simp [average, mean]
  rw [hav]
  change ((s : ℝ)/N * (∑ i, (x i - mean x)^2) -
      s * ((1/(s : ℝ)-1/(N : ℝ)) *
        ((∑ i, (x i - mean x)^2)/((N : ℝ)-1)))) / ((s : ℝ)-1) = _
  change _ = (∑ i, (x i - mean x)^2) / ((N : ℝ)-1)
  have hN1 : (N : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  generalize (∑ i, (x i - mean x)^2) = t
  field_simp [hsR, hNR, hs1, hN1]
  <;> ring

lemma dvc_complement_average {N s : ℕ} (hs : s ≤ N) (f : Finset (Fin N) → ℝ) :
    average (firstStageSets N s) (fun S => f (univ \ S)) =
      average (firstStageSets N (N-s)) f := by
  classical
  have hmem {S : Finset (Fin N)} {k : ℕ} :
      S ∈ firstStageSets N k ↔ S.card = k := by
    simp [firstStageSets, Finset.mem_powersetCard]
  have hc (S : Finset (Fin N)) : (univ \ S).card = N - S.card := by
    simp [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  have hinv (S : Finset (Fin N)) : univ \ (univ \ S) = S := by
    ext i
    simp
  have hsum (f : Finset (Fin N) → ℝ) :
      (∑ S ∈ firstStageSets N s, f (univ \ S)) =
        ∑ S ∈ firstStageSets N (N-s), f S := by
    apply Finset.sum_bij (fun S _ => univ \ S)
    · intro S hS
      rw [hmem, hc, hmem.mp hS]
    · intro S hS T hT he
      simpa only [hinv] using congrArg (fun U => univ \ U) he
    · intro T hT
      refine ⟨univ \ T, ?_, hinv T⟩
      rw [hmem, hc, hmem.mp hT, Nat.sub_sub_self hs]
    · intro S hS
      rfl
  have hcard : (firstStageSets N s).card = (firstStageSets N (N-s)).card := by
    have h := hsum (fun _ => 1)
    have hh : ((firstStageSets N s).card : ℝ) = (firstStageSets N (N-s)).card := by
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using h
    exact_mod_cast hh
  unfold average
  rw [hsum, hcard]

lemma dvc_treated_subset {N : ℕ} (S : Finset (Fin N)) :
    treatedSet (subsetAssignment N S) = S := by
  classical
  ext i
  simp [treatedSet, subsetAssignment]

/-- The generic Neyman contrast variance from P002.
Its population has arbitrary auxiliary schedules; only its fixed treated count matters. -/
lemma dvc_local_variance {N s : ℕ} (hs0 : 0 < s) (hs : s < N)
    (a b : Fin N → ℝ) :
    variance (crMass N s) (directGroup a b) =
      popVar a / s + popVar b / ((N-s : ℕ) : ℝ) -
        popVar (fun i => a i-b i) / N := by
  let P : AronowAudit.P002.Population N :=
    ⟨fun _ _ => 0, fun _ v => v, s⟩
  have hP : AronowAudit.P002.ValidDesign P := ⟨by omega, hs0, hs⟩
  have hmean : expect (crMass N s) (directGroup a b) =
      AronowAudit.P002.expectation P (fun S =>
        AronowAudit.P002.groupMean S a - AronowAudit.P002.groupMean Sᶜ b) := by
    rw [cr_subset_average]
    apply dvc_average_congr
    intro S hS
    simp only [directGroup, dvc_treated_subset, AronowAudit.P002.groupMean, average]
    rfl
  unfold variance
  rw [hmean, cr_subset_average]
  have hv := AronowAudit.P002.Wave1.NDS_contrast_variance P hP a b
  have hleft : average (firstStageSets N s)
      (fun S => (directGroup a b (subsetAssignment N S) -
        AronowAudit.P002.expectation P (fun T =>
          AronowAudit.P002.groupMean T a - AronowAudit.P002.groupMean Tᶜ b))^2) =
      AronowAudit.P002.designVariance P (fun S =>
        AronowAudit.P002.groupMean S a - AronowAudit.P002.groupMean Sᶜ b) := by
    apply dvc_average_congr
    intro S hS
    simp only [directGroup, dvc_treated_subset, AronowAudit.P002.groupMean, average]
    rfl
  change average (firstStageSets N s) _ = _
  rw [hleft, hv]
  simp only [AronowAudit.P002.controlSize, P]
  rw [Nat.cast_sub (Nat.le_of_lt hs)]
  simp [AronowAudit.P002.popVar, AronowAudit.P002.mean, popVar, rawSampleVar, average]

lemma dvc_local_within {N s : ℕ} (hs2 : 2 ≤ s) (hs : s+2 ≤ N)
    (a b : Fin N → ℝ) :
    expect (crMass N s) (droppedWithin a b) =
      popVar a / s + popVar b / ((N-s : ℕ) : ℝ) := by
  rw [cr_subset_average]
  calc
    _ = average (firstStageSets N s) (fun S =>
        rawSampleVar S a / s + rawSampleVar (univ \ S) b / ((N-s : ℕ) : ℝ)) := by
      apply dvc_average_congr
      intro S hS
      have hc := (Finset.mem_powersetCard.mp hS).2
      have hcc : (univ \ S).card = N-s := by
        simp [Finset.card_sdiff_of_subset (Finset.subset_univ _), hc]
      simp only [droppedWithin, dvc_treated_subset, hc, hcc,
        if_pos hs2, if_pos (show 2 ≤ N-s by omega)]
    _ = _ := by
      rw [dvc_average_add, dvc_average_div, dvc_average_div,
        dvc_complement_average (N := N) (s := s) (by omega) (fun S => rawSampleVar S b),
        dvc_subset_sample_variance hs2 (by omega),
        dvc_subset_sample_variance (by omega) (by omega)]

/-- A centered second moment about any fixed center. -/
lemma dvc_second_about {Ω : Type*} [Fintype Ω] (q : Ω → ℝ)
    (hq : ∑ w, q w = 1) (X : Ω → ℝ) (c : ℝ) :
    expect q (fun w => (X w-c)^2) = variance q X + (expect q X-c)^2 := by
  have hex (t : ℝ) : expect q (fun w => (X w-t)^2) =
      expect q (fun w => (X w)^2) - 2*t*expect q X + t^2 := by
    have hp (w : Ω) : (X w-t)^2 = (X w)^2 - 2*t*X w + t^2 := by ring
    simp_rw [hp]
    rw [expect_add, expect_sub, dvc_expect_mul, dvc_expect_const q hq]
  unfold variance
  rw [hex, hex]
  ring

lemma dvc_product_total {I : Type*} [Fintype I] [DecidableEq I] {Ω : I → Type*}
    [∀ i, Fintype (Ω i)] (q : ∀ i, Ω i → ℝ) (hq : ∀ i, ∑ w, q i w = 1) :
    (∑ w : ∀ i, Ω i, ∏ i, q i (w i)) = 1 := by
  rw [← Fintype.prod_sum]
  simp only [hq, Finset.prod_const_one]

/-- Product expectation with dependent coordinate types and heterogeneous laws. -/
lemma dvc_product_factor {I : Type*} [Fintype I] [DecidableEq I] {Ω : I → Type*}
    [∀ i, Fintype (Ω i)] (q X : ∀ i, Ω i → ℝ) :
    expect (fun w : ∀ i, Ω i => ∏ i, q i (w i)) (fun w => ∏ i, X i (w i)) =
      ∏ i, expect (q i) (X i) := by
  unfold expect
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i w => q i w * X i w)).symm

lemma dvc_product_pair {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (q : ∀ i, Ω i → ℝ)
    (hq : ∀ i, ∑ w, q i w = 1) (i j : I) (hij : i ≠ j)
    (X : Ω i → ℝ) (Y : Ω j → ℝ) :
    expect (fun w : ∀ i, Ω i => ∏ i, q i (w i)) (fun w => X (w i)*Y (w j)) =
      expect (q i) X * expect (q j) Y := by
  classical
  let F : ∀ g, Ω g → ℝ := fun g w =>
    if h : g=i then X (h ▸ w) else if h : g=j then Y (h ▸ w) else 1
  have hF (w : ∀ i, Ω i) : (∏ g, F g (w g)) = X (w i)*Y (w j) := by
    calc
      _ = ∏ g : I, if g=i then X (w i) else if g=j then Y (w j) else 1 := by
        apply Finset.prod_congr rfl
        intro g hg
        by_cases hi : g=i
        · subst g
          simp [F]
        · by_cases hj : g=j
          · subst g
            simp [F, hij.symm]
          · simp [F, hi, hj]
      _ = _ := product_two_factors i j hij _ _
  have he (g : I) : expect (q g) (F g) =
      if g=i then expect (q i) X else if g=j then expect (q j) Y else 1 := by
    by_cases hi : g=i
    · subst g
      simp [F]
    · by_cases hj : g=j
      · subst g
        simp [F, hij.symm]
      · simp [F, hi, hj, dvc_expect_const _ (hq g)]
  have h := dvc_product_factor q F
  simp_rw [hF, he] at h
  rw [h, product_two_factors i j hij]

lemma dvc_product_centered_square {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (q X : ∀ i, Ω i → ℝ)
    (hq : ∀ i, ∑ w, q i w = 1) (S : Finset I) :
    expect (fun w : ∀ i, Ω i => ∏ i, q i (w i))
      (fun w => (∑ i ∈ S, (X i (w i)-expect (q i) (X i)))^2) =
      ∑ i ∈ S, variance (q i) (X i) := by
  classical
  let Z := fun i w => X i w - expect (q i) (X i)
  have hz (i : I) : expect (q i) (Z i) = 0 := by
    simp [Z, expect_sub, dvc_expect_const _ (hq i)]
  have hp (i j : I) : expect (fun w : ∀ i, Ω i => ∏ i, q i (w i))
      (fun w => Z i (w i)*Z j (w j)) = if i=j then variance (q i) (X i) else 0 := by
    by_cases he : i=j
    · subst j
      simpa [variance, Z, pow_two] using
        independent_coordinate_expect q hq i (fun w => Z i w * Z i w)
    · rw [dvc_product_pair q hq i j he, hz, hz]
      simp [he]
  have hpoly (w : ∀ i, Ω i) : (∑ i ∈ S, Z i (w i))^2 =
      ∑ i ∈ S, ∑ j ∈ S, Z i (w i)*Z j (w j) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  change expect (fun w : ∀ i, Ω i => ∏ i, q i (w i))
    (fun w => (∑ i ∈ S, Z i (w i))^2) = _
  simp_rw [hpoly]
  rw [expect_finset_sum]
  simp_rw [expect_finset_sum, hp]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.sum_ite_eq', hi]

lemma dvc_product_mean {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (q X : ∀ i, Ω i → ℝ)
    (hq : ∀ i, ∑ w, q i w = 1) (S : Finset I) :
    expect (fun w : ∀ i, Ω i => ∏ i, q i (w i))
      (fun w => average S (fun i => X i (w i))) =
      average S (fun i => expect (q i) (X i)) := by
  unfold average
  rw [expect_div, expect_finset_sum]
  simp_rw [independent_coordinate_expect q hq]

lemma dvc_product_average_variance {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (q X : ∀ i, Ω i → ℝ)
    (hq : ∀ i, ∑ w, q i w = 1) (S : Finset I) :
    variance (fun w : ∀ i, Ω i => ∏ i, q i (w i))
      (fun w => average S (fun i => X i (w i))) =
      (∑ i ∈ S, variance (q i) (X i)) / (S.card : ℝ)^2 := by
  unfold variance
  rw [dvc_product_mean q X hq]
  have hf (w : ∀ i, Ω i) :
      (average S (fun i => X i (w i))-average S (fun i => expect (q i) (X i)))^2 =
        (∑ i ∈ S, (X i (w i)-expect (q i) (X i)))^2 / (S.card : ℝ)^2 := by
    simp only [average, Finset.sum_sub_distrib, ← sub_div, div_pow]
  simp_rw [hf]
  rw [expect_div, dvc_product_centered_square q X hq]
  rfl

lemma dvc_product_average_square {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (q X : ∀ i, Ω i → ℝ)
    (hq : ∀ i, ∑ w, q i w = 1) (S : Finset I) (c : ℝ) :
    expect (fun w : ∀ i, Ω i => ∏ i, q i (w i))
      (fun w => (average S (fun i => X i (w i))-c)^2) =
      (average S (fun i => expect (q i) (X i))-c)^2 +
        (∑ i ∈ S, variance (q i) (X i)) / (S.card : ℝ)^2 := by
  rw [dvc_second_about _ (dvc_product_total q hq),
    dvc_product_average_variance q X hq, dvc_product_mean q X hq]
  ring

lemma dvc_product_sample_variance {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (q X : ∀ i, Ω i → ℝ)
    (hq : ∀ i, ∑ w, q i w = 1) (S : Finset I) (hS : 2 ≤ S.card) :
    expect (fun w : ∀ i, Ω i => ∏ i, q i (w i))
      (fun w => rawSampleVar S (fun i => X i (w i))) =
      rawSampleVar S (fun i => expect (q i) (X i)) +
        (∑ i ∈ S, variance (q i) (X i)) / S.card := by
  have hpos : 0 < S.card := by omega
  have hn : (S.card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hpos)
  have hn1 : (S.card : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
    linarith
  simp_rw [raw_sample_variance_centered S hpos _ 0]
  simp only [sub_zero]
  rw [expect_div, expect_sub, expect_finset_sum, dvc_expect_mul]
  have hc (i : I) : expect (fun w : ∀ i, Ω i => ∏ i, q i (w i))
      (fun w => (X i (w i))^2) = expect (q i) (fun w => (X i w)^2) :=
    independent_coordinate_expect q hq i (fun w => (X i w)^2)
  simp_rw [hc]
  have hm : expect (fun w : ∀ i, Ω i => ∏ i, q i (w i))
      (fun w => (average S (fun i => X i (w i)))^2) =
      (average S (fun i => expect (q i) (X i)))^2 +
        (∑ i ∈ S, variance (q i) (X i)) / (S.card : ℝ)^2 := by
    simpa only [sub_zero] using dvc_product_average_square q X hq S 0
  rw [hm]
  have hi (i : I) : expect (q i) (fun w => (X i w)^2) =
      variance (q i) (X i) + (expect (q i) (X i))^2 := by
    simpa only [sub_zero] using dvc_second_about (q i) (hq i) (X i) 0
  simp_rw [hi]
  rw [Finset.sum_add_distrib]
  field_simp [hn, hn1]
  <;> ring

/-- Total variance under uniform group selection and heterogeneous local draws. -/
lemma dvc_selected_variance {G C : ℕ} (hC : 2 ≤ C) (hCG : C ≤ G)
    (n : Fin G → ℕ) (q X : (g : Fin G) → Assignment (n g) → ℝ)
    (hq : ∀ g, ∑ z, q g z = 1) :
    variance (selectedLaw n C q) (selectedMean C X) =
      ((1-(C : ℝ)/G)/C) * popVar (fun g => expect (q g) (X g)) +
        (∑ g, variance (q g) (X g)) / ((C : ℝ)*G) := by
  classical
  have hC0 : 0 < C := by omega
  have hCR : (C : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hC0)
  have hGR : (G : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (by omega))
  rw [variance]
  rw [selected_mean_expect hC0 hCG n q hq X, selected_expect_average]
  calc
    _ = average (firstStageSets G C) (fun H =>
        (average H (fun g => expect (q g) (X g)) -
          mean (fun g => expect (q g) (X g)))^2 +
          (∑ g ∈ H, variance (q g) (X g)) / (C : ℝ)^2) := by
      apply dvc_average_congr
      intro H hH
      have hc := (Finset.mem_powersetCard.mp hH).2
      simpa only [selectedMean, average, hc] using
        dvc_product_average_square q X hq H (mean (fun g => expect (q g) (X g)))
    _ = _ := by
      rw [dvc_average_add, dvc_average_div,
        dvc_subset_mean_square hC0 hCG (by omega), dvc_subset_sum hC0 hCG]
      field_simp [hCR, hGR]
      <;> ring

lemma dvc_selected_sample_variance {G C : ℕ} (hC : 2 ≤ C) (hCG : C ≤ G)
    (n : Fin G → ℕ) (q X : (g : Fin G) → Assignment (n g) → ℝ)
    (hq : ∀ g, ∑ z, q g z = 1) :
    expect (selectedLaw n C q)
      (fun w => rawSampleVar w.1 (fun g => X g (w.2 g))) =
      popVar (fun g => expect (q g) (X g)) +
        (∑ g, variance (q g) (X g)) / G := by
  classical
  have hC0 : 0 < C := by omega
  have hCR : (C : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hC0)
  rw [selected_expect_average]
  calc
    _ = average (firstStageSets G C) (fun H =>
        rawSampleVar H (fun g => expect (q g) (X g)) +
          (∑ g ∈ H, variance (q g) (X g)) / C) := by
      apply dvc_average_congr
      intro H hH
      have hc := (Finset.mem_powersetCard.mp hH).2
      simpa only [hc] using dvc_product_sample_variance q X hq H (by omega)
    _ = _ := by
      rw [dvc_average_add, dvc_average_div, dvc_subset_sample_variance hC hCG,
        dvc_subset_sum hC0 hCG]
      field_simp [hCR]
      <;> ring

lemma dvc_selected_sum {G C : ℕ} (hC : 0 < C) (hCG : C ≤ G)
    (n : Fin G → ℕ) (q B : (g : Fin G) → Assignment (n g) → ℝ)
    (hq : ∀ g, ∑ z, q g z = 1) :
    expect (selectedLaw n C q) (fun w => ∑ g ∈ w.1, B g (w.2 g)) =
      (C : ℝ)/G * ∑ g, expect (q g) (B g) := by
  classical
  rw [selected_expect_average]
  simp_rw [expect_finset_sum, independent_coordinate_expect q hq]
  exact dvc_subset_sum hC hCG _

/-- Exact estimator bias before imposing any local treatment-arm conditions. -/
lemma dvc_selected_bias {G C : ℕ} (hC : 2 ≤ C) (hCG : C ≤ G)
    (n : Fin G → ℕ) (q X B : (g : Fin G) → Assignment (n g) → ℝ)
    (hq : ∀ g, ∑ z, q g z = 1) :
    expect (selectedLaw n C q) (fun w =>
      ((1-(C : ℝ)/G)/C) * rawSampleVar w.1 (fun g => X g (w.2 g)) +
        (∑ g ∈ w.1, B g (w.2 g)) / ((C : ℝ)*G)) -
      variance (selectedLaw n C q) (selectedMean C X) =
      (∑ g, (expect (q g) (B g) - variance (q g) (X g))) / (G : ℝ)^2 := by
  have hC0 : 0 < C := by omega
  have hCR : (C : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hC0)
  have hGR : (G : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (by omega))
  rw [expect_add, dvc_expect_mul, expect_div,
    dvc_selected_sample_variance hC hCG n q X hq,
    dvc_selected_sum hC0 hCG n q B hq,
    dvc_selected_variance hC hCG n q X hq, Finset.sum_sub_distrib]
  field_simp [hCR, hGR]
  <;> ring

/-- Corrected direct variance: exact local and global moments, nonnegative
bias, and equality precisely for effects constant within every group. -/
theorem direct_variance_correction_proof {G C : ℕ} (hC : 2 ≤ C) (hCG : C ≤ G)
    (n m : Fin G → ℕ) (hm : ∀ g, 2 ≤ m g ∧ m g + 2 ≤ n g)
    (a b : (g : Fin G) → Fin (n g) → ℝ) :
    let q := fun g => crMass (n g) (m g)
    let law := selectedLaw n C q
    let θ := fun g => mean (a g) - mean (b g)
    let V := fun g => popVar (a g)/(m g) + popVar (b g)/((n g-m g : ℕ) : ℝ) -
      popVar (fun i => a g i-b g i)/(n g)
    let point := selectedMean C (fun g => directGroup (a g) (b g))
    let vest := directVarianceEstimate C a b
    (∀ g, expect (q g) (directGroup (a g) (b g)) = θ g ∧
      variance (q g) (directGroup (a g) (b g)) = V g) ∧
    expect law point = mean θ ∧
    variance law point = ((1-(C : ℝ)/G)/C)*popVar θ + (∑ g, V g)/((C : ℝ)*G) ∧
    expect law vest - variance law point =
      (∑ g, popVar (fun i => a g i-b g i)/(n g))/(G : ℝ)^2 ∧
    0 ≤ expect law vest - variance law point ∧
    (expect law vest = variance law point ↔ ∀ g, ∀ i j, a g i-b g i = a g j-b g j) := by
  classical
  let q := fun g => crMass (n g) (m g)
  let law := selectedLaw n C q
  let θ := fun g => mean (a g) - mean (b g)
  let V := fun g => popVar (a g)/(m g) + popVar (b g)/((n g-m g : ℕ) : ℝ) -
    popVar (fun i => a g i-b g i)/(n g)
  let point := selectedMean C (fun g => directGroup (a g) (b g))
  let vest := directVarianceEstimate C a b
  change (∀ g, expect (q g) (directGroup (a g) (b g)) = θ g ∧
      variance (q g) (directGroup (a g) (b g)) = V g) ∧
    expect law point = mean θ ∧
    variance law point = ((1-(C : ℝ)/G)/C)*popVar θ + (∑ g, V g)/((C : ℝ)*G) ∧
    expect law vest - variance law point =
      (∑ g, popVar (fun i => a g i-b g i)/(n g))/(G : ℝ)^2 ∧
    0 ≤ expect law vest - variance law point ∧
    (expect law vest = variance law point ↔ ∀ g, ∀ i j, a g i-b g i = a g j-b g j)
  have hsmall (g : Fin G) : 0 < m g ∧ m g < n g := by
    have := hm g
    omega
  have hn2 (g : Fin G) : 2 ≤ Fintype.card (Fin (n g)) := by
    simp only [Fintype.card_fin]
    have := hm g
    omega
  have hn0 (g : Fin G) : (n g : ℝ) ≠ 0 := by
    have := hn2 g
    simp only [Fintype.card_fin] at this
    exact_mod_cast (show n g ≠ 0 by omega)
  have hGR : (G : ℝ) ≠ 0 := by
    exact_mod_cast (show G ≠ 0 by omega)
  have hq (g : Fin G) : ∑ z, q g z = 1 :=
    (cr_mass_probability (le_of_lt (hsmall g).2)).2
  have he (g : Fin G) : expect (q g) (directGroup (a g) (b g)) = θ g :=
    direct_group_cr_unbiased (hsmall g).1 (hsmall g).2 (a g) (b g)
  have hv (g : Fin G) : variance (q g) (directGroup (a g) (b g)) = V g :=
    dvc_local_variance (hsmall g).1 (hsmall g).2 (a g) (b g)
  have hw (g : Fin G) : expect (q g) (droppedWithin (a g) (b g)) =
      popVar (a g)/(m g) + popVar (b g)/((n g-m g : ℕ) : ℝ) :=
    dvc_local_within (hm g).1 (hm g).2 (a g) (b g)
  have hglobalmean : expect law point = mean θ :=
    selected_direct_cr_unbiased (by omega) hCG n m hsmall a b
  have hglobalvar : variance law point =
      ((1-(C : ℝ)/G)/C)*popVar θ + (∑ g, V g)/((C : ℝ)*G) := by
    have h := dvc_selected_variance hC hCG n q (fun g => directGroup (a g) (b g)) hq
    simpa only [he, hv] using h
  have hdiff (g : Fin G) : expect (q g) (droppedWithin (a g) (b g)) -
      variance (q g) (directGroup (a g) (b g)) =
      popVar (fun i => a g i-b g i)/(n g) := by
    rw [hw, hv]
    dsimp only [V]
    ring
  have hbias : expect law vest - variance law point =
      (∑ g, popVar (fun i => a g i-b g i)/(n g))/(G : ℝ)^2 := by
    unfold vest directVarianceEstimate
    have h := dvc_selected_bias hC hCG n q
      (fun g => directGroup (a g) (b g)) (fun g => droppedWithin (a g) (b g)) hq
    simpa only [hdiff, law, vest, point, directVarianceEstimate] using h
  have ht (g : Fin G) : 0 ≤ popVar (fun i => a g i-b g i)/(n g) :=
    div_nonneg (pop_var_nonnegative (hn2 g) _) (Nat.cast_nonneg _)
  have hnonneg : 0 ≤ expect law vest - variance law point := by
    rw [hbias]
    exact div_nonneg (Finset.sum_nonneg (fun g _ => ht g)) (sq_nonneg _)
  refine ⟨fun g => ⟨he g, hv g⟩, hglobalmean, hglobalvar, hbias, hnonneg, ?_⟩
  constructor
  · intro heq
    have hzero : (∑ g, popVar (fun i => a g i-b g i)/(n g)) = 0 := by
      have hz : (∑ g, popVar (fun i => a g i-b g i)/(n g))/(G : ℝ)^2 = 0 := by
        rw [← hbias, heq, sub_self]
      exact (div_eq_zero_iff.mp hz).resolve_right (pow_ne_zero _ hGR)
    intro g
    have hg := (Finset.sum_eq_zero_iff_of_nonneg (fun g _ => ht g)).mp hzero g (mem_univ g)
    have hp : popVar (fun i => a g i-b g i) = 0 :=
      (div_eq_zero_iff.mp hg).resolve_right (hn0 g)
    exact (pop_var_zero_iff_constant (hn2 g) _).mp hp
  · intro hadd
    have hz (g : Fin G) : popVar (fun i => a g i-b g i) = 0 :=
      (pop_var_zero_iff_constant (hn2 g) _).mpr (hadd g)
    have hb : expect law vest - variance law point = 0 := by
      rw [hbias]
      simp only [hz, zero_div, Finset.sum_const_zero]
    exact sub_eq_zero.mp hb

end
end AronowAudit.P045.Wave1
