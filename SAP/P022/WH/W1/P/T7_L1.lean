import SAP.P022.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T7_L1

open SAP.P022 Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal
noncomputable section

private lemma sum_cycles (f : ℕ → ℝ) (n : ℕ) :
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

private lemma sum_prefix (f : ℕ → ℝ) (n : ℕ) :
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

private lemma mean_limit (f : ℕ → ℝ) :
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
    have hrem : (((q + 4) % 4 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hr
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
    nlinarith [abs_nonneg A]
  have hsize : Tendsto (fun q : ℕ => (q : ℝ) + 4) atTop atTop :=
    tendsto_atTop_add_const_right _ 4 tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun q : ℕ => B / ((q : ℝ) + 4)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsize
  have habs : Tendsto (fun q =>
      |finiteMean (fun i : Fin (q + 4) => f (i.val % 4)) - A|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) hb hzero
  exact (tendsto_sub_nhds_zero_iff).mp
    ((tendsto_zero_iff_abs_tendsto_zero _).mpr habs)

private def cornerPoint (i : ℕ) : ℝ × ℝ :=
  (if i < 2 then 0 else 1, if i % 2 = 0 then 0 else 1)

private lemma corner_index (i : ℕ) :
    (cornerWitness.y1 i, cornerWitness.y0 i) = cornerPoint (i % 4) := by
  simp only [cornerWitness, cornerPoint]
  rw [Nat.mod_mod_of_dvd i (by decide : 2 ∣ 4)]

private lemma corner_cdf_zero_limit (t : Bool) :
    Tendsto (fun q => empiricalCDF (rowOutcomes cornerWitness t q) 0)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  let f : ℕ → ℝ := fun i =>
    if (if t then (cornerPoint i).1 else (cornerPoint i).2) ≤ 0 then 1 else 0
  have h := mean_limit f
  have hsum : (∑ i ∈ Finset.range 4, f i) / 4 = (1 / 2 : ℝ) := by
    cases t <;>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ] <;>
      norm_num [f, cornerPoint]
  have heq (q : ℕ) : empiricalCDF (rowOutcomes cornerWitness t q) 0 =
      finiteMean (fun i : Fin (q + 4) => f (i.val % 4)) := by
    unfold empiricalCDF
    simp only [rowOutcomes]
    change finiteMean (fun i : Fin (q + 4) =>
      if (if t then cornerWitness.y1 else cornerWitness.y0) i.val ≤ 0 then
        (1 : ℝ) else 0) = _
    unfold finiteMean
    congr 1
    funext i
    cases t with
    | false =>
        have hi : cornerWitness.y0 i.val = (cornerPoint (i.val % 4)).2 :=
          congrArg Prod.snd (corner_index i.val)
        simpa [f, cornerPoint] using
          congrArg (fun x : ℝ => if x ≤ 0 then (1 : ℝ) else 0) hi
    | true =>
        have hi : cornerWitness.y1 i.val = (cornerPoint (i.val % 4)).1 :=
          congrArg Prod.fst (corner_index i.val)
        simpa [f, cornerPoint] using
          congrArg (fun x : ℝ => if x ≤ 0 then (1 : ℝ) else 0) hi
  rw [hsum] at h
  simpa only [heq] using h

private lemma binary_outcome (q : ℕ) (t : Bool) (i : Fin (cornerWitness.design q).N) :
    rowOutcomes cornerWitness t q i = 0 ∨ rowOutcomes cornerWitness t q i = 1 := by
  cases t <;> simp [rowOutcomes, cornerWitness] <;> omega

private lemma cdf_one (q : ℕ) (t : Bool) :
    empiricalCDF (rowOutcomes cornerWitness t q) 1 = 1 := by
  have hN : 0 < (cornerWitness.design q).N := by
    have hp := (cornerWitness.design q).population_min
    omega
  unfold empiricalCDF finiteMean
  have he : (fun i : Fin (cornerWitness.design q).N =>
      if rowOutcomes cornerWitness t q i ≤ 1 then (1 : ℝ) else 0) = fun _ => 1 := by
    funext i
    rcases binary_outcome q t i with h | h <;> simp [h]
  rw [he]
  exact mean_const hN 1

private lemma left_zero (q : ℕ) (t : Bool) :
    empiricalLeftCDF (rowOutcomes cornerWitness t q) 0 = 0 := by
  have hN : 0 < (cornerWitness.design q).N := by
    have hp := (cornerWitness.design q).population_min
    omega
  unfold empiricalLeftCDF finiteMean
  have he : (fun i : Fin (cornerWitness.design q).N =>
      if rowOutcomes cornerWitness t q i < 0 then (1 : ℝ) else 0) = fun _ => 0 := by
    funext i
    rcases binary_outcome q t i with h | h <;> simp [h]
  rw [he]
  exact mean_const hN 0

private lemma left_one_eq_zero (q : ℕ) (t : Bool) :
    empiricalLeftCDF (rowOutcomes cornerWitness t q) 1 =
      empiricalCDF (rowOutcomes cornerWitness t q) 0 := by
  unfold empiricalLeftCDF empiricalCDF finiteMean
  have he : (fun i : Fin (cornerWitness.design q).N =>
      if rowOutcomes cornerWitness t q i < 1 then (1 : ℝ) else 0) =
    (fun i => if rowOutcomes cornerWitness t q i ≤ 0 then 1 else 0) := by
    funext i
    rcases binary_outcome q t i with h | h <;> simp [h]
  rw [he]

end
end SAP.P022.WH.W1.P.T7_L1

open SAP.P022.WH.W1 SAP.P022.WH.W1.P.T7_L1

theorem SAP.P022.WH.W1.T7_L1_proof : SAP.P022.WH.W1.T7_L1 := by
  change CornerEndpointFacts
  refine ⟨corner_law_facts.1, ?_⟩
  intro t
  refine ⟨corner_cdf_zero_limit t, ?_, ?_⟩
  · intro q
    exact ⟨cdf_one q t, left_zero q t, left_one_eq_zero q t⟩
  · simpa only [left_one_eq_zero] using corner_cdf_zero_limit t
