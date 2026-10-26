import AronowAudit.P042.P042_Turnout

/-! Exact moments for the labelled three-arm allocation law, including unused units. -/

namespace AronowAudit.P042.Wave1

noncomputable section

set_option autoImplicit false
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The label of one of the three observed arms. -/
def P042B1_label (g : Fin 3) : Fin 4 := Fin.castLE (by decide : 3 ≤ 4) g

/-- Inclusion indicator under the actual labelled allocation. -/
def P042B1_indicator {N : ℕ} (i : Fin N) (g : Fin 3) (z : Fin N → Fin 4) : ℝ :=
  if z i = P042B1_label g then 1 else 0

lemma P042B1_label_injective : Function.Injective P042B1_label := by
  intro g h he
  exact Fin.ext (congrArg (fun x : Fin 4 => x.val) he)

lemma P042B1_support_counts {N : ℕ} (n : Fin 3 → ℕ)
    {z : Fin N → Fin 4} (hz : z ∈ completeThreeAllocations N n) (g : Fin 3) :
    (univ.filter (fun i => z i = P042B1_label g)).card = n g := by
  exact (mem_filter.mp hz).2 g

/-- Three disjoint subsets realize the required counts; all remaining labels are 3. -/
lemma P042B1_support_nonempty {N : ℕ} (n : Fin 3 → ℕ)
    (hsizes : ∑ g, n g ≤ N) : (completeThreeAllocations N n).Nonempty := by
  classical
  have hsize : n 0 + n 1 + n 2 ≤ N := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsizes
  obtain ⟨s₀, hs₀, hc₀⟩ := exists_subset_card_eq
    (show n 0 ≤ (univ : Finset (Fin N)).card by simpa using (show n 0 ≤ N by omega))
  have hsize₁ : n 1 ≤ ((univ : Finset (Fin N)) \ s₀).card := by
    rw [card_sdiff_of_subset hs₀, card_univ, Fintype.card_fin, hc₀]
    omega
  obtain ⟨s₁, hs₁, hc₁⟩ := exists_subset_card_eq hsize₁
  have hd₀₁ : Disjoint s₀ s₁ := by
    rw [disjoint_left]
    intro i hi₀ hi₁
    exact (mem_sdiff.mp (hs₁ hi₁)).2 hi₀
  have hsize₂ : n 2 ≤ ((univ : Finset (Fin N)) \ (s₀ ∪ s₁)).card := by
    rw [card_sdiff_of_subset (subset_univ _), card_union_of_disjoint hd₀₁,
      card_univ, Fintype.card_fin, hc₀, hc₁]
    omega
  obtain ⟨s₂, hs₂, hc₂⟩ := exists_subset_card_eq hsize₂
  have h₁₀ (i : Fin N) (hi : i ∈ s₁) : i ∉ s₀ := (mem_sdiff.mp (hs₁ hi)).2
  have h₂₀ (i : Fin N) (hi : i ∈ s₂) : i ∉ s₀ := by
    exact fun h => (mem_sdiff.mp (hs₂ hi)).2 (mem_union_left _ h)
  have h₂₁ (i : Fin N) (hi : i ∈ s₂) : i ∉ s₁ := by
    exact fun h => (mem_sdiff.mp (hs₂ hi)).2 (mem_union_right _ h)
  let z : Fin N → Fin 4 := fun i =>
    if i ∈ s₀ then 0 else if i ∈ s₁ then 1 else if i ∈ s₂ then 2 else 3
  have hz₀ (i : Fin N) : z i = P042B1_label 0 ↔ i ∈ s₀ := by
    simp only [z, P042B1_label]
    split_ifs <;> simp_all <;> aesop
  have hz₁ (i : Fin N) : z i = P042B1_label 1 ↔ i ∈ s₁ := by
    simp only [z, P042B1_label]
    split_ifs <;> simp_all <;> aesop
  have hz₂ (i : Fin N) : z i = P042B1_label 2 ↔ i ∈ s₂ := by
    simp only [z, P042B1_label]
    split_ifs <;> simp_all <;> aesop
  refine ⟨z, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
  intro g
  fin_cases g
  · change (univ.filter (fun i => z i = P042B1_label 0)).card = n 0
    simpa only [hz₀, filter_mem_eq_inter, univ_inter] using hc₀
  · change (univ.filter (fun i => z i = P042B1_label 1)).card = n 1
    simpa only [hz₁, filter_mem_eq_inter, univ_inter] using hc₁
  · change (univ.filter (fun i => z i = P042B1_label 2)).card = n 2
    simpa only [hz₂, filter_mem_eq_inter, univ_inter] using hc₂

lemma P042B1_indicator_sum {N : ℕ} (n : Fin 3 → ℕ)
    {z : Fin N → Fin 4} (hz : z ∈ completeThreeAllocations N n) (g : Fin 3) :
    ∑ i, P042B1_indicator i g z = (n g : ℝ) := by
  simpa only [P042B1_indicator, sum_boole] using
    congrArg (fun k : ℕ => (k : ℝ)) (P042B1_support_counts n hz g)

/-- Precomposition by any permutation preserves the entire labelled support. -/
lemma P042B1_support_perm {N : ℕ} (n : Fin 3 → ℕ) (e : Equiv.Perm (Fin N))
    (z : Fin N → Fin 4) :
    (fun i => z (e i)) ∈ completeThreeAllocations N n ↔
      z ∈ completeThreeAllocations N n := by
  classical
  have hc (g : Fin 3) :
      (univ.filter (fun i => z (e i) = P042B1_label g)).card =
      (univ.filter (fun i => z i = P042B1_label g)).card := by
    exact card_equiv e (fun i => by simp)
  simp only [completeThreeAllocations, mem_filter, mem_univ, true_and]
  change (∀ g, (univ.filter (fun i => z (e i) = P042B1_label g)).card = n g) ↔
    (∀ g, (univ.filter (fun i => z i = P042B1_label g)).card = n g)
  simp only [hc]

lemma P042B1_expectation_congr {Ω : Type*} (s : Finset Ω) {f g : Ω → ℝ}
    (h : ∀ z ∈ s, f z = g z) : finiteExpectation s f = finiteExpectation s g := by
  unfold finiteExpectation
  rw [sum_congr rfl h]

/-- Uniform expectation is invariant under permutations of the units. -/
lemma P042B1_expectation_perm {N : ℕ} (n : Fin 3 → ℕ) (e : Equiv.Perm (Fin N))
    (f : (Fin N → Fin 4) → ℝ) :
    finiteExpectation (completeThreeAllocations N n) (fun z => f (fun i => z (e i))) =
      finiteExpectation (completeThreeAllocations N n) f := by
  classical
  unfold finiteExpectation
  congr 1
  let E : (Fin N → Fin 4) ≃ (Fin N → Fin 4) :=
    { toFun := fun z i => z (e i)
      invFun := fun z i => z (e.symm i)
      left_inv := fun z => by funext i; simp
      right_inv := fun z => by funext i; simp }
  exact sum_equiv E (fun z => (P042B1_support_perm n e z).symm) (fun _ _ => rfl)

lemma P042B1_inclusion_equal {N : ℕ} (n : Fin 3 → ℕ) (g : Fin 3) (i j : Fin N) :
    finiteExpectation (completeThreeAllocations N n) (P042B1_indicator i g) =
      finiteExpectation (completeThreeAllocations N n) (P042B1_indicator j g) := by
  calc
    _ = finiteExpectation (completeThreeAllocations N n)
        (fun z => P042B1_indicator i g (fun k => z (Equiv.swap i j k))) :=
      (P042B1_expectation_perm n (Equiv.swap i j) (P042B1_indicator i g)).symm
    _ = _ := by
      congr 1
      funext z
      simp only [P042B1_indicator, Equiv.swap_apply_left]


/-- The actual one-unit inclusion probability. -/
lemma P042B1_inclusion {N : ℕ} (hN : 0 < N) (n : Fin 3 → ℕ)
    (hsizes : ∑ g, n g ≤ N) (g : Fin 3) (i : Fin N) :
    finiteExpectation (completeThreeAllocations N n) (P042B1_indicator i g) =
      (n g : ℝ) / N := by
  have hnz : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : (N : ℝ) * finiteExpectation (completeThreeAllocations N n)
      (P042B1_indicator i g) = (n g : ℝ) := by
    calc
      _ = ∑ j, finiteExpectation (completeThreeAllocations N n)
          (P042B1_indicator j g) := by
        simp only [← P042B1_inclusion_equal n g i, sum_const, card_univ,
          Fintype.card_fin, nsmul_eq_mul]
      _ = finiteExpectation (completeThreeAllocations N n)
          (fun z => ∑ j, P042B1_indicator j g z) :=
        (finite_expectation_sum _ _).symm
      _ = finiteExpectation (completeThreeAllocations N n) (fun _ => (n g : ℝ)) :=
        P042B1_expectation_congr _ (fun z hz => P042B1_indicator_sum n hz g)
      _ = _ := finite_expectation_const _ (P042B1_support_nonempty n hsizes) _
  apply (eq_div_iff hnz).mpr
  nlinarith only [he]

/-- At a fixed unit, two distinct labels exclude one another. -/
lemma P042B1_indicator_diagonal {N : ℕ} (i : Fin N) (g h : Fin 3)
    (z : Fin N → Fin 4) :
    P042B1_indicator i g z * P042B1_indicator i h z =
      (if g = h then 1 else 0) * P042B1_indicator i g z := by
  classical
  by_cases hgh : g = h
  · subst h
    simp only [P042B1_indicator]
    split_ifs <;> norm_num
  · have hl := P042B1_label_injective.ne hgh
    unfold P042B1_indicator
    split_ifs <;> simp_all

/-- With the first unit fixed, all other units have the same pair moment. -/
lemma P042B1_pair_equal {N : ℕ} (n : Fin 3 → ℕ) (g h : Fin 3)
    (i j k : Fin N) (hij : i ≠ j) (hik : i ≠ k) :
    finiteExpectation (completeThreeAllocations N n)
      (fun z => P042B1_indicator i g z * P042B1_indicator j h z) =
    finiteExpectation (completeThreeAllocations N n)
      (fun z => P042B1_indicator i g z * P042B1_indicator k h z) := by
  have hi : Equiv.swap j k i = i := Equiv.swap_apply_of_ne_of_ne hij hik
  simpa only [P042B1_indicator, hi, Equiv.swap_apply_left] using
    (P042B1_expectation_perm n (Equiv.swap j k)
      (fun z => P042B1_indicator i g z * P042B1_indicator j h z)).symm

/-- Pair inclusion is obtained by summing over the second unit, excluding the first. -/
lemma P042B1_pair_inclusion {N : ℕ} (hN : 2 ≤ N) (n : Fin 3 → ℕ)
    (hsizes : ∑ g, n g ≤ N) (g h : Fin 3) (i j : Fin N) (hij : i ≠ j) :
    finiteExpectation (completeThreeAllocations N n)
      (fun z => P042B1_indicator i g z * P042B1_indicator j h z) =
      (n g : ℝ) * ((n h : ℝ) - if g = h then 1 else 0) /
        ((N : ℝ) * ((N : ℝ) - 1)) := by
  classical
  have hNpos : 0 < N := by omega
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  let E := finiteExpectation (completeThreeAllocations N n)
  let p := E (fun z => P042B1_indicator i g z * P042B1_indicator j h z)
  have hsum : (∑ k, E (fun z => P042B1_indicator i g z * P042B1_indicator k h z)) =
      (n h : ℝ) * ((n g : ℝ) / N) := by
    calc
      _ = E (fun z => ∑ k, P042B1_indicator i g z * P042B1_indicator k h z) :=
        (finite_expectation_sum _ _).symm
      _ = E (fun z => (n h : ℝ) * P042B1_indicator i g z) := by
        apply P042B1_expectation_congr
        intro z hz
        rw [← mul_sum, P042B1_indicator_sum n hz h, mul_comm]
      _ = _ := by
        change finiteExpectation _ _ = _
        rw [finite_expectation_mul, P042B1_inclusion hNpos n hsizes]
  have herase : (∑ k ∈ univ.erase i,
      E (fun z => P042B1_indicator i g z * P042B1_indicator k h z)) =
      ((N : ℝ) - 1) * p := by
    calc
      _ = ∑ _k ∈ univ.erase i, p := by
        apply sum_congr rfl
        intro k hk
        exact (P042B1_pair_equal n g h i j k hij
          (ne_of_mem_erase hk).symm).symm
      _ = _ := by
        simp only [sum_const, card_erase_of_mem (mem_univ i), card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  have hdiag : E (fun z => P042B1_indicator i g z * P042B1_indicator i h z) =
      (if g = h then (1 : ℝ) else 0) * ((n g : ℝ) / N) := by
    simp_rw [P042B1_indicator_diagonal]
    exact (finite_expectation_mul _ _ _).trans
      (congrArg (fun x : ℝ => (if g = h then 1 else 0) * x)
        (P042B1_inclusion hNpos n hsizes g i))
  rw [← sum_erase_add _ _ (mem_univ i), herase, hdiag] at hsum
  change p = _
  apply (eq_div_iff (mul_ne_zero hN0 hN1)).mpr
  field_simp [hN0] at hsum
  nlinarith only [hsum]

lemma P042B1_expectation_add {Ω : Type*} (s : Finset Ω) (f g : Ω → ℝ) :
    finiteExpectation s (fun z => f z + g z) =
      finiteExpectation s f + finiteExpectation s g := by
  simp only [finiteExpectation, sum_add_distrib, add_div]

lemma P042B1_covariance_eq_sub {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty)
    (f g : Ω → ℝ) : finiteCovariance s f g =
      finiteExpectation s (fun z => f z * g z) -
        finiteExpectation s f * finiteExpectation s g := by
  unfold finiteCovariance
  calc
    _ = finiteExpectation s (fun z => f z * g z - finiteExpectation s g * f z -
        finiteExpectation s f * g z + finiteExpectation s f * finiteExpectation s g) := by
      congr 1
      funext z
      ring
    _ = _ := by
      rw [P042B1_expectation_add, finite_expectation_sub, finite_expectation_sub,
        finite_expectation_mul, finite_expectation_mul, finite_expectation_const s hs]
      ring

lemma P042B1_covariance_sub_sub {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty)
    (a b c d : Ω → ℝ) :
    finiteCovariance s (fun z => a z - b z) (fun z => c z - d z) =
      finiteCovariance s a c - finiteCovariance s a d -
        finiteCovariance s b c + finiteCovariance s b d := by
  simp only [P042B1_covariance_eq_sub s hs, finite_expectation_sub]
  have he : finiteExpectation s (fun z => (a z - b z) * (c z - d z)) =
      finiteExpectation s (fun z => a z * c z) -
      finiteExpectation s (fun z => a z * d z) -
      finiteExpectation s (fun z => b z * c z) +
      finiteExpectation s (fun z => b z * d z) := by
    calc
      _ = finiteExpectation s (fun z => a z * c z - a z * d z - b z * c z + b z * d z) := by
        congr 1
        funext z
        ring
      _ = _ := by rw [P042B1_expectation_add, finite_expectation_sub, finite_expectation_sub]
  rw [he]
  ring

/-- The mean in arm g of an arbitrary fixed population vector. -/
def P042B1_armMean {N : ℕ} (n : Fin 3 → ℕ) (g : Fin 3) (U : Fin N → ℝ)
    (z : Fin N → Fin 4) : ℝ := (∑ i, P042B1_indicator i g z * U i) / (n g : ℝ)

lemma P042B1_armMean_eq {N : ℕ} (n : Fin 3 → ℕ) (Y : Fin N → Fin 3 → ℝ)
    (g : Fin 3) :
    P042B1_armMean n g (fun i => Y i g) = randomizedArmMean n Y g := by
  funext z
  unfold P042B1_armMean randomizedArmMean
  congr 1
  apply sum_congr rfl
  intro i _
  unfold P042B1_indicator P042B1_label
  split_ifs <;> simp

lemma P042B1_armMean_expectation {N : ℕ} (hN : 0 < N) (n : Fin 3 → ℕ)
    (hn : ∀ g, 0 < n g) (hsizes : ∑ g, n g ≤ N) (g : Fin 3) (U : Fin N → ℝ) :
    finiteExpectation (completeThreeAllocations N n) (P042B1_armMean n g U) =
      populationMean U := by
  have hng : (n g : ℝ) ≠ 0 := by exact_mod_cast (hn g).ne'
  unfold P042B1_armMean
  rw [finite_expectation_div, finite_expectation_sum]
  have he (i : Fin N) : finiteExpectation (completeThreeAllocations N n)
      (fun z => P042B1_indicator i g z * U i) = U i * ((n g : ℝ) / N) := by
    simp_rw [mul_comm (P042B1_indicator i g _)]
    rw [finite_expectation_mul, P042B1_inclusion hN n hsizes]
  simp_rw [he]
  rw [← sum_mul]
  unfold populationMean
  field_simp
  <;> ring

lemma P042B1_populationCovariance_raw {N : ℕ} (hN : 0 < N) (U V : Fin N → ℝ) :
    populationCovariance U V =
      ((∑ i, U i * V i) - (∑ i, U i) * (∑ i, V i) / (N : ℝ)) /
        ((N - 1 : ℕ) : ℝ) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold populationCovariance populationMean
  congr 1
  simp only [mul_sub, sub_mul, sum_sub_distrib, ← sum_mul, ← mul_sum,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  <;> ring

/-- The raw product moment, separating coincident and distinct population units. -/
lemma P042B1_armMean_product {N : ℕ} (hN : 2 ≤ N) (n : Fin 3 → ℕ)
    (hsizes : ∑ g, n g ≤ N) (g h : Fin 3) (U V : Fin N → ℝ) :
    let a := (n g : ℝ) * ((n h : ℝ) - if g = h then 1 else 0) /
      ((N : ℝ) * ((N : ℝ) - 1))
    let b := (if g = h then (1 : ℝ) else 0) * ((n g : ℝ) / N)
    finiteExpectation (completeThreeAllocations N n)
      (fun z => P042B1_armMean n g U z * P042B1_armMean n h V z) =
      (a * (∑ i, U i) * (∑ j, V j) + (b - a) * (∑ i, U i * V i)) /
        ((n g : ℝ) * (n h : ℝ)) := by
  classical
  dsimp only
  let a := (n g : ℝ) * ((n h : ℝ) - if g = h then 1 else 0) /
    ((N : ℝ) * ((N : ℝ) - 1))
  let b := (if g = h then (1 : ℝ) else 0) * ((n g : ℝ) / N)
  have he (i j : Fin N) : finiteExpectation (completeThreeAllocations N n)
      (fun z => P042B1_indicator i g z * P042B1_indicator j h z) =
      if i = j then b else a := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      simp_rw [P042B1_indicator_diagonal]
      rw [finite_expectation_mul, P042B1_inclusion (by omega) n hsizes]
    · rw [if_neg hij]
      exact P042B1_pair_inclusion hN n hsizes g h i j hij
  have hexpand : (fun z => P042B1_armMean n g U z * P042B1_armMean n h V z) =
      fun z => (∑ i, ∑ j, (U i * V j) *
        (P042B1_indicator i g z * P042B1_indicator j h z)) /
          ((n g : ℝ) * (n h : ℝ)) := by
    funext z
    unfold P042B1_armMean
    rw [div_mul_div_comm]
    congr 1
    rw [sum_mul]
    simp only [mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  rw [hexpand, finite_expectation_div]
  simp_rw [finite_expectation_sum, finite_expectation_mul, he]
  change (∑ i, ∑ j, U i * V j * (if i = j then b else a)) /
      ((n g : ℝ) * (n h : ℝ)) = _
  have hsplit (i j : Fin N) :
      U i * V j * (if i = j then b else a) =
      a * U i * V j + (if i = j then (b - a) * (U i * V i) else 0) := by
    split_ifs with hij
    · subst j
      ring
    · ring
  simp_rw [hsplit]
  have hdiag : (∑ i, ∑ j, if i = j then (b - a) * (U i * V i) else 0) =
      (b - a) * ∑ i, U i * V i := by
    simp only [sum_ite_eq, mem_univ, if_true, ← mul_sum]
  have hoff : (∑ i, ∑ j, a * U i * V j) = a * (∑ i, U i) * (∑ j, V j) := by
    simp only [← mul_sum, ← sum_mul]
  simp only [sum_add_distrib, hdiag, hoff]
  rfl

/-- Complete randomization covariance of two arbitrary arm means. -/
lemma P042B1_armMean_covariance {N : ℕ} (hN : 2 ≤ N) (n : Fin 3 → ℕ)
    (hn : ∀ g, 0 < n g) (hsizes : ∑ g, n g ≤ N) (g h : Fin 3)
    (U V : Fin N → ℝ) :
    finiteCovariance (completeThreeAllocations N n)
      (P042B1_armMean n g U) (P042B1_armMean n h V) =
      ((if g = h then (1 : ℝ) / (n g : ℝ) else 0) - 1 / (N : ℝ)) *
        populationCovariance U V := by
  classical
  have hNpos : 0 < N := by omega
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hng : (n g : ℝ) ≠ 0 := by exact_mod_cast (hn g).ne'
  have hnh : (n h : ℝ) ≠ 0 := by exact_mod_cast (hn h).ne'
  rw [P042B1_covariance_eq_sub _ (P042B1_support_nonempty n hsizes),
    P042B1_armMean_product hN n hsizes,
    P042B1_armMean_expectation hNpos n hn hsizes,
    P042B1_armMean_expectation hNpos n hn hsizes,
    P042B1_populationCovariance_raw hNpos]
  unfold populationMean
  rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  by_cases hgh : g = h
  · subst h
    simp only [ite_true, ↓reduceIte]
    field_simp
    <;> ring
  · simp only [if_neg hgh, zero_mul, sub_zero]
    field_simp
    <;> ring

theorem finite_population_shared_control_proof {N : ℕ} (hN : 2 ≤ N)
    (n : Fin 3 → ℕ) (hn : ∀ g, 0 < n g) (hsizes : ∑ g, n g ≤ N)
    (Y : Fin N → Fin 3 → ℝ) :
    let S := completeThreeAllocations N n
    let D1 := fun z => randomizedArmMean n Y 1 z - randomizedArmMean n Y 0 z
    let D2 := fun z => randomizedArmMean n Y 2 z - randomizedArmMean n Y 0 z
    let tau1 := fun i => Y i 1 - Y i 0
    let tau2 := fun i => Y i 2 - Y i 0
    finiteCovariance S D1 D2 =
      populationCovariance (fun i => Y i 0) (fun i => Y i 0)/(n 0:ℝ) -
      populationCovariance tau1 tau2/(N:ℝ) ∧
    populationCovariance tau1 tau2 =
      populationCovariance (fun i => Y i 1) (fun i => Y i 2) -
      populationCovariance (fun i => Y i 1) (fun i => Y i 0) -
      populationCovariance (fun i => Y i 0) (fun i => Y i 2) +
      populationCovariance (fun i => Y i 0) (fun i => Y i 0) ∧
    ((∀ i, Y i 1 = Y i 0 ∧ Y i 2 = Y i 0) →
      finiteCovariance S D1 D2 =
        populationCovariance (fun i => Y i 0) (fun i => Y i 0)/(n 0:ℝ)) := by
  classical
  dsimp only
  have hcov := P042B1_covariance_sub_sub (completeThreeAllocations N n)
    (P042B1_support_nonempty n hsizes)
    (randomizedArmMean n Y 1) (randomizedArmMean n Y 0)
    (randomizedArmMean n Y 2) (randomizedArmMean n Y 0)
  have harm (g h : Fin 3) :
      finiteCovariance (completeThreeAllocations N n)
        (randomizedArmMean n Y g) (randomizedArmMean n Y h) =
      ((if g = h then (1 : ℝ) / (n g : ℝ) else 0) - 1 / (N : ℝ)) *
        populationCovariance (fun i => Y i g) (fun i => Y i h) := by
    rw [← P042B1_armMean_eq n Y g, ← P042B1_armMean_eq n Y h]
    exact P042B1_armMean_covariance hN n hn hsizes g h _ _
  simp only [harm, show (1 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 0 by decide, show (0 : Fin 3) ≠ 2 by decide,
    if_false, if_true] at hcov
  have heffect := population_effect_covariance
    (fun i => Y i 0) (fun i => Y i 1) (fun i => Y i 2)
  have hmain : finiteCovariance (completeThreeAllocations N n)
      (fun z => randomizedArmMean n Y 1 z - randomizedArmMean n Y 0 z)
      (fun z => randomizedArmMean n Y 2 z - randomizedArmMean n Y 0 z) =
      populationCovariance (fun i => Y i 0) (fun i => Y i 0) / (n 0 : ℝ) -
      populationCovariance (fun i => Y i 1 - Y i 0) (fun i => Y i 2 - Y i 0) / (N : ℝ) := by
    rw [hcov, heffect]
    ring
  refine ⟨hmain, heffect, ?_⟩
  intro hzero
  have hz₁ : (fun i => Y i 1 - Y i 0) = fun _ => (0 : ℝ) := by
    funext i
    rw [(hzero i).1, sub_self]
  have hz₂ : (fun i => Y i 2 - Y i 0) = fun _ => (0 : ℝ) := by
    funext i
    rw [(hzero i).2, sub_self]
  rw [hmain, hz₁, hz₂]
  simp [populationCovariance, populationMean]

end
end AronowAudit.P042.Wave1
