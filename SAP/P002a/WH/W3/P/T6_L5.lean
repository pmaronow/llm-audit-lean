import SAP.P002a.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P002a.WH.W3.P.T6_L5
noncomputable section
open scoped BigOperators Matrix Classical

private lemma mean_add {n : ℕ} (f g : Fin n → ℝ) :
    mean (fun i => f i + g i) = mean f + mean g := by
  simp [mean, Finset.sum_add_distrib, add_div]

private lemma mean_sub {n : ℕ} (f g : Fin n → ℝ) :
    mean (fun i => f i - g i) = mean f - mean g := by
  simp [mean, Finset.sum_sub_distrib, sub_div]

private lemma mean_mul {n : ℕ} (c : ℝ) (f : Fin n → ℝ) :
    mean (fun i => c * f i) = c * mean f := by
  simp only [mean, ← Finset.mul_sum]
  ring

private lemma mean_const {n : ℕ} (hn : 0 < n) (c : ℝ) :
    mean (fun _ : Fin n => c) = c := by
  have hz : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [mean, hz]

private lemma groupMean_sub_smul {n : ℕ} (S : Finset (Fin n))
    (q d : Fin n → ℝ) (β : ℝ) :
    groupMean S (fun i => q i - β * d i) =
      groupMean S q - β * groupMean S d := by
  simp only [groupMean, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

private lemma grid_response_moments (m : ℕ) (hm : 0 < m)
    (hg : T6GridFacts m) :
    mean (fun j => t6Grid m j + (1 / 10) * (t6Grid m j ^ 2 - t6V m)) = 0 ∧
    mean (fun j => t6Grid m j *
      (t6Grid m j + (1 / 10) * (t6Grid m j ^ 2 - t6V m))) = t6V m := by
  have ht := hg.1
  have ht2 := hg.2.1
  have ht3 := hg.2.2.1
  constructor
  · rw [mean_add, mean_mul, mean_sub, mean_const hm, ht, ht2]
    ring
  · have he : (fun j : Fin m => t6Grid m j *
        (t6Grid m j + (1 / 10) * (t6Grid m j ^ 2 - t6V m))) =
        (fun j => t6Grid m j ^ 2 + (1 / 10) *
          (t6Grid m j ^ 3 - t6V m * t6Grid m j)) := by
      funext j
      ring
    rw [he, mean_add, mean_mul, mean_sub, mean_mul, ht2, ht3, ht]
    ring

private def blockSign (m : ℕ) (i : Fin (2 * m)) : ℝ :=
  if i.val < m then 1 else -1

private lemma even_sum (m : ℕ) (F : ℝ → ℝ → ℝ) :
    (∑ i : Fin (2 * m), F (blockSign m i) (t6T m i)) =
      (∑ j : Fin m, F 1 (t6Grid m j)) +
        (∑ j : Fin m, F (-1) (t6Grid m j)) := by
  simp only [t6T, t6Grid, blockSign]
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    F (if j < m then 1 else -1) ((2 * (j % m : ℕ) - (m : ℝ) + 1) / ((m : ℝ) - 1)))]
  rw [two_mul, Finset.sum_range_add]
  rw [Fin.sum_univ_eq_sum_range (fun j =>
      F 1 ((2 * (j : ℝ) - (m : ℝ) + 1) / ((m : ℝ) - 1))),
    Fin.sum_univ_eq_sum_range (fun j =>
      F (-1) ((2 * (j : ℝ) - (m : ℝ) + 1) / ((m : ℝ) - 1)))]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hjm := Finset.mem_range.mp hj
    simp [hjm, Nat.mod_eq_of_lt hjm]
  · apply Finset.sum_congr rfl
    intro j hj
    have hjm := Finset.mem_range.mp hj
    have hnot : ¬ m + j < m := by omega
    simp [hnot, Nat.mod_eq_of_lt hjm]

private lemma block_sums (m : ℕ) (F : ℝ → ℝ) :
    (∑ i ∈ t6Block m, F (t6T m i)) = ∑ j : Fin m, F (t6Grid m j) ∧
    (∑ i ∈ (t6Block m)ᶜ, F (t6T m i)) = ∑ j : Fin m, F (t6Grid m j) := by
  have hp := even_sum m (fun s t => if s = 1 then F t else 0)
  have hn := even_sum m (fun s t => if s = -1 then F t else 0)
  have hp' (i : Fin (2 * m)) :
      (if blockSign m i = 1 then F (t6T m i) else 0) =
        if i ∈ t6Block m then F (t6T m i) else 0 := by
    by_cases hi : i.val < m <;> simp [blockSign, t6Block, hi] <;> norm_num <;> omega
  have hn' (i : Fin (2 * m)) :
      (if blockSign m i = -1 then F (t6T m i) else 0) =
        if i ∈ (t6Block m)ᶜ then F (t6T m i) else 0 := by
    by_cases hi : i.val < m <;> simp [blockSign, t6Block, hi] <;> norm_num <;> omega
  have hplus : (∑ i ∈ t6Block m, F (t6T m i)) =
      ∑ j : Fin m, F (t6Grid m j) := by
    calc
      _ = ∑ i : Fin (2 * m),
          if i ∈ t6Block m then F (t6T m i) else 0 := by
        simp only [Finset.sum_ite_mem_eq]
      _ = ∑ i : Fin (2 * m),
          if blockSign m i = 1 then F (t6T m i) else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hp' i]
      _ = ∑ j : Fin m, F (t6Grid m j) := by
        norm_num at hp
        exact hp
  have hminus : (∑ i ∈ (t6Block m)ᶜ, F (t6T m i)) =
      ∑ j : Fin m, F (t6Grid m j) := by
    calc
      _ = ∑ i : Fin (2 * m),
          if i ∈ (t6Block m)ᶜ then F (t6T m i) else 0 := by
        simp only [Finset.sum_ite_mem_eq]
      _ = ∑ i : Fin (2 * m),
          if blockSign m i = -1 then F (t6T m i) else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hn' i]
      _ = ∑ j : Fin m, F (t6Grid m j) := by
        norm_num at hn
        exact hn
  exact ⟨hplus, hminus⟩

private lemma block_cards (m : ℕ) :
    (t6Block m).card = m ∧ (t6Block m)ᶜ.card = m := by
  have hs := block_sums m (fun _ => (1 : ℝ))
  constructor
  · have hc : ((t6Block m).card : ℝ) = (m : ℝ) := by simpa using hs.1
    exact_mod_cast hc
  · have hc : (((t6Block m)ᶜ).card : ℝ) = (m : ℝ) := by simpa using hs.2
    exact_mod_cast hc

private lemma block_mem (m : ℕ) :
    t6Block m ∈ assignments (nearSingularModel m).pop ∧
      (t6Block m)ᶜ ∈ assignments (nearSingularModel m).pop := by
  constructor
  · apply Finset.mem_powersetCard.mpr
    change t6Block m ⊆ Finset.univ ∧ (t6Block m).card = m
    exact ⟨Finset.subset_univ _, (block_cards m).1⟩
  · apply Finset.mem_powersetCard.mpr
    change (t6Block m)ᶜ ⊆ Finset.univ ∧ ((t6Block m)ᶜ).card = m
    exact ⟨Finset.subset_univ _, (block_cards m).2⟩

private lemma block_mean (m : ℕ) (F : ℝ → ℝ) :
    groupMean (t6Block m) (fun i => F (t6T m i)) =
        mean (fun j => F (t6Grid m j)) ∧
    groupMean (t6Block m)ᶜ (fun i => F (t6T m i)) =
        mean (fun j => F (t6Grid m j)) := by
  obtain ⟨hp, hn⟩ := block_sums m F
  obtain ⟨hcp, hcn⟩ := block_cards m
  constructor
  · change (∑ i ∈ t6Block m, F (t6T m i)) / (t6Block m).card =
      (∑ j : Fin m, F (t6Grid m j)) / (m : ℝ)
    rw [hp, hcp]
  · change (∑ i ∈ (t6Block m)ᶜ, F (t6T m i)) / ((t6Block m)ᶜ).card =
      (∑ j : Fin m, F (t6Grid m j)) / (m : ℝ)
    rw [hn, hcn]

private lemma ols_unique {n k : ℕ} (x : Fin n → Fin k → ℝ)
    (S : Finset (Fin n)) (q : Fin n → ℝ) (c : Option (Fin k) → ℝ)
    (hg : (gram x S).det ≠ 0)
    (hc : gram x S *ᵥ c = score x S q) : ols x S q = c := by
  rw [ols, if_pos hg, ← hc, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hg), Matrix.one_mulVec]

private lemma scalar_ols {n : ℕ} (x : Fin n → Fin 1 → ℝ)
    (S : Finset (Fin n)) (q : Fin n → ℝ) (hS : S.Nonempty)
    (hg : (gram x S).det ≠ 0) (a b : ℝ)
    (h0 : a + b * groupMean S (fun i => x i 0) = groupMean S q)
    (h1 : a * groupMean S (fun i => x i 0) +
      b * groupMean S (fun i => x i 0 ^ 2) =
        groupMean S (fun i => x i 0 * q i)) :
    ols x S q = t6Coef a b := by
  have hc : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  apply ols_unique _ _ _ _ hg
  ext s
  cases s with
  | none =>
      simpa [Matrix.mulVec, dotProduct, Fintype.sum_option, gram, score,
        augmented, t6Coef, groupMean, hc, ← Finset.mul_sum, mul_comm] using h0
  | some s =>
      fin_cases s
      simpa [Matrix.mulVec, dotProduct, Fintype.sum_option, gram, score,
        augmented, t6Coef, groupMean, hc, ← Finset.mul_sum, pow_two,
        mul_comm] using h1

private lemma affine_block_fit (m : ℕ) (hm : 4 ≤ m)
    (hg : T6GridFacts m) (B : Finset (Fin (2 * m)))
    (hB : B.Nonempty) (hdet : (gram (nearSingularModel m).x B).det ≠ 0)
    (s : ℝ) (hxs : ∀ i ∈ B, t6X m i = s + t6Eta m * t6T m i)
    (hmean : ∀ F : ℝ → ℝ,
      groupMean B (fun i => F (t6T m i)) = mean (fun j => F (t6Grid m j))) :
    ols (nearSingularModel m).x B (t6Y m) =
        t6Coef (-s / t6Eta m) (1 / t6Eta m) ∧
      groupMean B (fun i => t6Y m i - slopeDot ((nearSingularModel m).x i)
        (ols (nearSingularModel m).x B (t6Y m))) = -s / t6Eta m := by
  have hm0 : 0 < m := by omega
  have heta : 0 < t6Eta m := by unfold t6Eta; positivity
  have hgcopy := hg
  obtain ⟨hy, hty⟩ := grid_response_moments m hm0 hg
  obtain ⟨ht, ht2, ht3, _, _⟩ := hgcopy
  have hmx : groupMean B (fun i => (nearSingularModel m).x i 0) = s := by
    calc
      _ = groupMean B (fun i => s + t6Eta m * t6T m i) := by
        apply AronowAudit.P002.groupMean_congr
        intro i hi
        change t6X m i = _
        exact hxs i hi
      _ = mean (fun j => s + t6Eta m * t6Grid m j) :=
        hmean (fun t => s + t6Eta m * t)
      _ = s := by
        rw [mean_add, mean_const hm0, mean_mul, ht]
        ring
  have hmy : groupMean B (t6Y m) = 0 := by
    change groupMean B (fun i => t6T m i +
      (1 / 10) * (t6T m i ^ 2 - t6V m)) = 0
    rw [hmean (fun t => t + (1 / 10) * (t ^ 2 - t6V m))]
    exact hy
  have hmx2 : groupMean B (fun i => (nearSingularModel m).x i 0 ^ 2) =
      s ^ 2 + t6Eta m ^ 2 * t6V m := by
    calc
      _ = groupMean B (fun i => (s + t6Eta m * t6T m i) ^ 2) := by
        apply AronowAudit.P002.groupMean_congr
        intro i hi
        change t6X m i ^ 2 = _
        rw [hxs i hi]
      _ = mean (fun j => (s + t6Eta m * t6Grid m j) ^ 2) :=
        hmean (fun t => (s + t6Eta m * t) ^ 2)
      _ = mean (fun j =>
          (s ^ 2 + (2 * s * t6Eta m) * t6Grid m j) +
            t6Eta m ^ 2 * t6Grid m j ^ 2) := by
        congr 1
        funext j
        ring
      _ = s ^ 2 + t6Eta m ^ 2 * t6V m := by
        rw [mean_add, mean_add, mean_const hm0, mean_mul, mean_mul, ht, ht2]
        ring
  have hmxy : groupMean B (fun i => (nearSingularModel m).x i 0 * t6Y m i) =
      t6Eta m * t6V m := by
    calc
      _ = groupMean B (fun i =>
          (s + t6Eta m * t6T m i) *
            (t6T m i + (1 / 10) * (t6T m i ^ 2 - t6V m))) := by
        apply AronowAudit.P002.groupMean_congr
        intro i hi
        change t6X m i * (t6T m i +
          (1 / 10) * (t6T m i ^ 2 - t6V m)) = _
        rw [hxs i hi]
      _ = mean (fun j => (s + t6Eta m * t6Grid m j) *
          (t6Grid m j + (1 / 10) * (t6Grid m j ^ 2 - t6V m))) :=
        hmean (fun t => (s + t6Eta m * t) * (t + (1 / 10) * (t ^ 2 - t6V m)))
      _ = mean (fun j =>
          s * (t6Grid m j + (1 / 10) * (t6Grid m j ^ 2 - t6V m)) +
            t6Eta m * (t6Grid m j *
              (t6Grid m j + (1 / 10) * (t6Grid m j ^ 2 - t6V m)))) := by
        congr 1
        funext j
        ring
      _ = t6Eta m * t6V m := by
        rw [mean_add, mean_mul, mean_mul, hy, hty]
        ring
  have hfit : ols (nearSingularModel m).x B (t6Y m) =
      t6Coef (-s / t6Eta m) (1 / t6Eta m) := by
    apply scalar_ols _ _ _ hB hdet (-s / t6Eta m) (1 / t6Eta m)
    · rw [hmx, hmy]
      field_simp [heta.ne']
      <;> ring
    · rw [hmx, hmx2, hmxy]
      field_simp [heta.ne']
      <;> ring
  refine ⟨hfit, ?_⟩
  have heq : (fun i => t6Y m i - slopeDot ((nearSingularModel m).x i)
        (t6Coef (-s / t6Eta m) (1 / t6Eta m))) =
      (fun i => t6Y m i - (1 / t6Eta m) * (nearSingularModel m).x i 0) := by
    funext i
    simp [slopeDot, Fin.sum_univ_one, t6Coef]
    ring
  rw [hfit, heq, groupMean_sub_smul, hmy, hmx]
  ring

theorem prove : SAP.P002a.WH.W3.T6_L5 := by
  intro m hm hg hrank
  let A := t6Block m
  have hA : A ∈ assignments (nearSingularModel m).pop := by
    simpa [A] using (block_mem m).1
  have hAc : Aᶜ ∈ assignments (nearSingularModel m).pop := by
    simpa [A] using (block_mem m).2
  have hrankA := hrank A hA
  have hpos : A.Nonempty := by
    apply Finset.card_pos.mp
    rw [(block_cards m).1]
    omega
  have hneg : Aᶜ.Nonempty := by
    apply Finset.card_pos.mp
    rw [(block_cards m).2]
    omega
  have hpfit := affine_block_fit m hm hg A hpos hrankA.1 1
    (by
      intro i hi
      have hi' : i.val < m := (Finset.mem_filter.mp (show i ∈ t6Block m from by simpa [A] using hi)).2
      have hx : t6X m i = (if i.val < m then 1 else -1) + t6Eta m * t6T m i := rfl
      rw [hx, if_pos hi']
      )
    (fun F => (block_mean m F).1)
  have hnfit := affine_block_fit m hm hg Aᶜ hneg hrankA.2 (-1)
    (by
      intro i hi
      have hi' : ¬ i.val < m := by
        simpa [A, t6Block] using hi
      have hx : t6X m i = (if i.val < m then 1 else -1) + t6Eta m * t6T m i := rfl
      rw [hx, if_neg hi']
      )
    (fun F => (block_mean m F).2)
  refine ⟨hA, hAc, ?_, ?_⟩
  · intro a
    cases a
    · change (ols (nearSingularModel m).x (t6Block m)ᶜ (t6Y m)) (some 0) = _
      simpa [A, t6Coef] using congrFun hnfit.1 (some 0)
    · change (ols (nearSingularModel m).x (t6Block m) (t6Y m)) (some 0) = _
      simpa [A, t6Coef] using congrFun hpfit.1 (some 0)
  · change groupMean A (fun i => t6Y m i - slopeDot ((nearSingularModel m).x i)
        (ols (nearSingularModel m).x A (t6Y m))) -
      groupMean Aᶜ (fun i => t6Y m i - slopeDot ((nearSingularModel m).x i)
        (ols (nearSingularModel m).x Aᶜ (t6Y m))) = -2 / t6Eta m
    rw [hpfit.2, hnfit.2]
    ring

end
end SAP.P002a.WH.W3.P.T6_L5

theorem SAP.P002a.WH.W3.T6_L5_proof : SAP.P002a.WH.W3.T6_L5 :=
  SAP.P002a.WH.W3.P.T6_L5.prove
