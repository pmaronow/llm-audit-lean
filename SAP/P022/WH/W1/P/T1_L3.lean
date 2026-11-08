import SAP.P022.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T1_L3

open SAP.P022 Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def zeroBit (t : Bool) (i : ℕ) : ℝ :=
  if t then (if i % 4 < 2 then 1 else 0) else (if i % 2 = 0 then 1 else 0)

lemma sum_cycles (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (4 * n), f (i % 4)) =
      (n : ℝ) * (∑ i ∈ Finset.range 4, f i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have he : (∑ i ∈ Finset.range 4, f ((4 * n + i) % 4)) =
        ∑ i ∈ Finset.range 4, f i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add]
      simp [Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]
    rw [he]
    push_cast
    ring

lemma sum_prefix (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, f (i % 4)) =
      (n / 4 : ℕ) * (∑ i ∈ Finset.range 4, f i) +
        ∑ i ∈ Finset.range (n % 4), f i := by
  conv_lhs => rw [← Nat.div_add_mod n 4]
  rw [Finset.sum_range_add, sum_cycles]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi4 : i < 4 := (Finset.mem_range.mp hi).trans (Nat.mod_lt n (by decide))
  simp [Nat.add_mod, Nat.mod_eq_of_lt hi4]

lemma mean_limit (f : ℕ → ℝ) :
    Tendsto (fun q => finiteMean (fun i : Fin (q + 4) => f (i.val % 4))) atTop
      (𝓝 ((∑ i ∈ Finset.range 4, f i) / 4)) := by
  let A := (∑ i ∈ Finset.range 4, f i) / 4
  let B := (∑ i ∈ Finset.range 4, |f i|) + 4 * |A|
  have hb (q : ℕ) :
      |finiteMean (fun i : Fin (q + 4) => f (i.val % 4)) - A| ≤ B / (q + 4) := by
    have hN : (0 : ℝ) < (q : ℝ) + 4 := by positivity
    have hr : (q + 4) % 4 ≤ 4 := (Nat.mod_lt _ (by decide : 0 < 4)).le
    have htail : |∑ i ∈ Finset.range ((q + 4) % 4), f i| ≤
        ∑ i ∈ Finset.range 4, |f i| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hr)
          (fun i _ _ => abs_nonneg (f i)))
    have hcast : (q : ℝ) + 4 =
        4 * (((q + 4) / 4 : ℕ) : ℝ) + (((q + 4) % 4 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod (q + 4) 4).symm
    have heq : finiteMean (fun i : Fin (q + 4) => f (i.val % 4)) - A =
        ((∑ i ∈ Finset.range ((q + 4) % 4), f i) -
          (((q + 4) % 4 : ℕ) : ℝ) * A) / ((q : ℝ) + 4) := by
      rw [finiteMean, Fintype.expect_eq_sum_div_card, Fintype.card_fin,
        (Fin.sum_univ_eq_sum_range (fun i => f (i % 4))), sum_prefix]
      push_cast
      dsimp [A]
      field_simp
      rw [hcast]
      ring
    rw [heq, abs_div, abs_of_pos hN]
    apply div_le_div_of_nonneg_right _ hN.le
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_of_nonneg (show 0 ≤ (((q + 4) % 4 : ℕ) : ℝ) by positivity)]
    dsimp [B]
    have hrem : (((q + 4) % 4 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hr
    nlinarith [abs_nonneg A, htail]
  have hzero : Tendsto (fun q : ℕ => B / ((q : ℝ) + 4)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (show Tendsto (fun q : ℕ => (q : ℝ) + 4) atTop atTop from
        tendsto_atTop_add_const_right _ 4 tendsto_natCast_atTop_atTop)
  have habs : Tendsto (fun q =>
      |finiteMean (fun i : Fin (q + 4) => f (i.val % 4)) - A|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) hb hzero
  exact (tendsto_sub_nhds_zero_iff).mp
    ((tendsto_zero_iff_abs_tendsto_zero _).mpr habs)

lemma shifted_abs (z : Prop) [Decidable z] (d : ℝ) (hd : 0 < d)
    (hu : d ≤ 1 / 3) : |(if z then (0 : ℝ) else 1) - d| < 1 := by
  by_cases hz : z
  · have hlt : d < 1 := lt_of_le_of_lt hu (by norm_num)
    have heq : (if z then (0 : ℝ) else 1) - d = -d := by simp [hz]
    rw [heq, abs_of_nonpos (by linarith)]
    simpa using hlt
  · have hpos : 0 ≤ 1 - d := by linarith
    have hlt : 1 - d < 1 := by linarith
    rw [if_neg hz, abs_of_nonneg hpos]
    exact hlt

lemma perturbed_bound (i : ℕ) :
    |perturbedCornerWitness.y1 i| < 1 ∧ |perturbedCornerWitness.y0 i| < 1 := by
  have hdpos : 0 < (1 : ℝ) / ((i : ℝ) + 3) := by positivity
  have hdle : (1 : ℝ) / ((i : ℝ) + 3) ≤ 1 / 3 := by
    have hi : (3 : ℝ) ≤ (i : ℝ) + 3 := by exact_mod_cast (Nat.le_add_left 3 i)
    exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity) hi
  constructor
  · have h := shifted_abs (i % 4 < 2) (1 / ((i : ℝ) + 3)) hdpos hdle
    simpa [perturbedCornerWitness, cornerWitness, reciprocalWitness,
      Nat.lt_succ_iff] using h
  · have h := shifted_abs (i % 2 = 0) (1 / ((i : ℝ) + 3)) hdpos hdle
    simpa [perturbedCornerWitness, cornerWitness, reciprocalWitness] using h

lemma perturbed_indicator (z : Prop) [Decidable z] (d : ℝ) (hd : 0 < d)
    (hu : d ≤ 1 / 3) :
    (if (if z then (0 : ℝ) else 1) - d ≤ 0 then (1 : ℝ) else 0) =
      if z then 1 else 0 := by
  by_cases hz : z
  · have hp : -d ≤ 0 := by linarith
    simp [hz, hp]
  · have hn : ¬ (1 - d ≤ 0) := by linarith
    simp [hz, hn]

lemma perturbed_zero_mean (t : Bool) (q : ℕ) :
    empiricalCDF (rowOutcomes perturbedCornerWitness t q) 0 =
      finiteMean (fun i : Fin (q + 4) => zeroBit t i.val) := by
  have hN : (perturbedCornerWitness.design q).N = q + 4 := by
    simp [perturbedCornerWitness, cornerWitness, reciprocalWitness]
  rw [empiricalCDF]
  have hf : (fun i : Fin (perturbedCornerWitness.design q).N =>
      if rowOutcomes perturbedCornerWitness t q i ≤ 0 then (1 : ℝ) else 0) =
      (fun i : Fin (perturbedCornerWitness.design q).N => zeroBit t i.val) := by
    funext i
    have hdpos : 0 < (1 : ℝ) / ((i.val : ℝ) + 3) := by positivity
    have hdle : (1 : ℝ) / ((i.val : ℝ) + 3) ≤ 1 / 3 := by
      have hi : (3 : ℝ) ≤ (i.val : ℝ) + 3 := by exact_mod_cast (Nat.le_add_left 3 i.val)
      exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity) hi
    cases t
    · simpa [rowOutcomes, perturbedCornerWitness, cornerWitness, reciprocalWitness,
        zeroBit] using
        (perturbed_indicator (i.val % 2 = 0)
          (1 / ((i.val : ℝ) + 3)) hdpos hdle)
    · simpa [rowOutcomes, perturbedCornerWitness, cornerWitness, reciprocalWitness,
        zeroBit, Nat.lt_succ_iff] using
        (perturbed_indicator (i.val % 4 ≤ 1)
          (1 / ((i.val : ℝ) + 3)) hdpos hdle)
  rw [← hN, hf]

lemma zero_bit_sum (t : Bool) :
    (∑ i ∈ Finset.range 4, zeroBit t i) = 2 := by
  cases t <;> simp only [Finset.sum_range_succ, zeroBit] <;> norm_num

lemma zero_mean_tendsto (t : Bool) :
    Tendsto (fun q => finiteMean (fun i : Fin (q + 4) => zeroBit t i.val))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have h := mean_limit (zeroBit t)
  rw [zero_bit_sum] at h
  norm_num at h
  have hmod (i : ℕ) : zeroBit t (i % 4) = zeroBit t i := by
    cases t <;> simp [zeroBit, Nat.mod_mod_of_dvd i (by decide : 2 ∣ 4)]
  simpa only [hmod] using h

lemma perturbed_one_cdf (t : Bool) (q : ℕ) :
    empiricalCDF (rowOutcomes perturbedCornerWitness t q) 1 = 1 := by
  have hN : (perturbedCornerWitness.design q).N = q + 4 := by
    simp [perturbedCornerWitness, cornerWitness, reciprocalWitness]
  have hall (i : Fin (perturbedCornerWitness.design q).N) :
      rowOutcomes perturbedCornerWitness t q i ≤ 1 := by
    have ha : |rowOutcomes perturbedCornerWitness t q i| < 1 := by
      cases t
      · simpa [rowOutcomes] using (perturbed_bound i.val).2
      · simpa [rowOutcomes] using (perturbed_bound i.val).1
    exact (abs_lt.mp ha).2.le
  rw [empiricalCDF]
  have hfun : (fun i : Fin (perturbedCornerWitness.design q).N =>
      if rowOutcomes perturbedCornerWitness t q i ≤ 1 then (1 : ℝ) else 0) =
      fun _ => 1 := by
    funext i
    simp [hall i]
  rw [hfun]
  exact mean_const (by rw [hN]; omega) 1

lemma bernoulli_continuous_off_atoms (t : Bool) (x : ℝ)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) : ContinuousAt (lawCDF cornerLaw t) x := by
  have heq : lawCDF cornerLaw t = bernoulliHalfCDF := funext (corner_law_facts.1 t)
  rw [heq]
  unfold bernoulliHalfCDF
  by_cases hn : x < 0
  · have hev : ∀ᶠ y : ℝ in 𝓝 x, y < 0 := eventually_lt_nhds hn
    exact ContinuousAt.congr (f := fun _ : ℝ => (0 : ℝ)) continuousAt_const
      (hev.mono fun y hy => by simp [hy])
  · have hxnonneg : 0 < x := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hx0)
    by_cases h1 : x < 1
    · have he0 : ∀ᶠ y : ℝ in 𝓝 x, 0 ≤ y := eventually_ge_nhds hxnonneg
      have he1 : ∀ᶠ y : ℝ in 𝓝 x, y < 1 := eventually_lt_nhds h1
      have he := he0.and he1
      exact ContinuousAt.congr (f := fun _ : ℝ => (1 / 2 : ℝ)) continuousAt_const
        (he.mono fun y hy => by simp [not_lt_of_ge hy.1, hy.2])
    · have hxgt : 1 < x := lt_of_le_of_ne (le_of_not_gt h1) (Ne.symm hx1)
      have hev : ∀ᶠ y : ℝ in 𝓝 x, 1 ≤ y := eventually_ge_nhds hxgt
      exact ContinuousAt.congr (f := fun _ : ℝ => (1 : ℝ)) continuousAt_const
        (hev.mono fun y hy => by
          have hy0 : ¬ y < 0 := by linarith
          have hy1 : ¬ y < 1 := by linarith
          simp [hy0, hy1])

lemma discontinuity_at_atoms (t : Bool) (x : ℝ)
    (h : ¬ ContinuousAt (lawCDF cornerLaw t) x) : x = 0 ∨ x = 1 := by
  by_contra hn
  push_neg at hn
  exact h (bernoulli_continuous_off_atoms t x hn.1 hn.2)

end
end SAP.P022.WH.W1.P.T1_L3

open SAP.P022.WH.W1.P.T1_L3 SAP.P022.WH.W1 SAP.P022 Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

theorem SAP.P022.WH.W1.T1_L3_proof : SAP.P022.WH.W1.T1_L3 := by
  classical
  change PerturbedAtomFacts
  refine ⟨perturbed_bound, ?_, ?_, ?_, ?_⟩
  · exact bounded_one_UI perturbedCornerWitness (fun i =>
      ⟨(perturbed_bound i).1.le, (perturbed_bound i).2.le⟩)
  · intro t
    have h := zero_mean_tendsto t
    have heq : (fun q => empiricalCDF (rowOutcomes perturbedCornerWitness t q) 0) =
        (fun q => finiteMean (fun i : Fin (q + 4) => zeroBit t i.val)) := by
      funext q
      exact perturbed_zero_mean t q
    rw [heq]
    exact h
  · intro t q
    exact perturbed_one_cdf t q
  · intro t x hx
    rcases discontinuity_at_atoms t x hx with rfl | rfl
    · have h := zero_mean_tendsto t
      have heq : (fun q => empiricalCDF (rowOutcomes perturbedCornerWitness t q) 0) =
          (fun q => finiteMean (fun i : Fin (q + 4) => zeroBit t i.val)) := by
        funext q
        exact perturbed_zero_mean t q
      rw [heq]
      simpa [corner_law_facts.1, bernoulliHalfCDF] using h
    · have heq : (fun q => empiricalCDF (rowOutcomes perturbedCornerWitness t q) 1) =
        fun _ => (1 : ℝ) := by
        funext q
        exact perturbed_one_cdf t q
      rw [heq]
      simpa [corner_law_facts.1, bernoulliHalfCDF] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))

