import SAP.P022.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T1_L2

open SAP.P022 SAP.P022.WH.W1 Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

def baseX (i : ℕ) : ℝ := if i % 4 < 2 then 0 else 1

def baseY (i : ℕ) : ℝ := if i % 2 = 0 then 0 else 1

def point (i : ℕ) : ℝ × ℝ :=
  (baseX i - 1 / ((i : ℝ) + 3), baseY i - 1 / ((i : ℝ) + 3))

def eval (f : BoundedContinuousFunction (ℝ × ℝ) ℝ) (i : ℕ) : ℝ := f (point i)

def block (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  u (4 * k) + u (4 * k + 1) + u (4 * k + 2) + u (4 * k + 3)

lemma index_tendsto (r : ℕ) : Tendsto (fun k : ℕ => 4 * k + r) atTop atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop b] with k hk
  exact hk.trans (by omega)

lemma eval_residue_tendsto (f : BoundedContinuousFunction (ℝ × ℝ) ℝ)
    (r : Fin 4) :
    Tendsto (fun k : ℕ => eval f (4 * k + r.val)) atTop
      (𝓝 (f ((if r.val < 2 then 0 else 1), (if r.val % 2 = 0 then 0 else 1)))) := by
  let idx : ℕ → ℕ := fun k => 4 * k + r.val
  have hidx : Tendsto (fun k : ℕ => idx k + 2) atTop atTop := by
    have h := index_tendsto r.val
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with k hk
    exact hk.trans (by simp [idx]; omega)
  have hδ : Tendsto (fun k : ℕ => 1 / ((idx k : ℝ) + 3)) atTop (𝓝 0) := by
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hidx
    convert ht using 1
    funext k
    congr 1
    simp [idx]
    ring
  have hx : Tendsto (fun k : ℕ => (if r.val < 2 then 0 else 1) -
      1 / ((idx k : ℝ) + 3)) atTop (𝓝 (if r.val < 2 then 0 else 1)) := by
    simpa using (tendsto_const_nhds.sub hδ)
  have hy : Tendsto (fun k : ℕ => (if r.val % 2 = 0 then 0 else 1) -
      1 / ((idx k : ℝ) + 3)) atTop (𝓝 (if r.val % 2 = 0 then 0 else 1)) := by
    simpa using (tendsto_const_nhds.sub hδ)
  have hp := hx.prodMk_nhds hy
  have hpoint : (fun k : ℕ => point (idx k)) = fun k =>
      ((if r.val < 2 then 0 else 1) - 1 / ((idx k : ℝ) + 3),
       (if r.val % 2 = 0 then 0 else 1) - 1 / ((idx k : ℝ) + 3)) := by
    funext k
    simp [point, baseX, baseY, idx, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt r.isLt]
  have hp' : Tendsto (fun k : ℕ => point (idx k)) atTop
      (𝓝 ((if r.val < 2 then 0 else 1), (if r.val % 2 = 0 then 0 else 1))) := by
    rw [hpoint]
    exact hp
  have hf := f.continuous.continuousAt.tendsto.comp hp'
  simpa [eval, idx, Function.comp_def] using hf

lemma block_tendsto (f : BoundedContinuousFunction (ℝ × ℝ) ℝ) :
    Tendsto (fun k : ℕ => block (eval f) k) atTop
      (𝓝 (f (0, 0) + f (0, 1) + f (1, 0) + f (1, 1))) := by
  have h0 := eval_residue_tendsto f ⟨0, by omega⟩
  have h1 := eval_residue_tendsto f ⟨1, by omega⟩
  have h2 := eval_residue_tendsto f ⟨2, by omega⟩
  have h3 := eval_residue_tendsto f ⟨3, by omega⟩
  have h := h0.add (h1.add (h2.add h3))
  convert h using 1 <;> norm_num [block] <;> ac_rfl

lemma sum_range_blocks (u : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range (4 * m), u i) = ∑ k ∈ Finset.range m, block u k := by
  induction m with
  | zero => simp [block]
  | succ m ih =>
      calc
        (∑ i ∈ Finset.range (4 * (m + 1)), u i) =
            (∑ i ∈ Finset.range (4 * m), u i) +
              ∑ j ∈ Finset.range 4, u (4 * m + j) := by
                rw [Nat.mul_succ, Finset.sum_range_add]
        _ = (∑ k ∈ Finset.range m, block u k) + block u m := by
              rw [ih]
              simp [block, Finset.sum_range_succ]
        _ = ∑ k ∈ Finset.range (m + 1), block u k := by
              rw [Finset.sum_range_succ]

def average (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, u i

def blockAverage (u : ℕ → ℝ) (m : ℕ) : ℝ :=
  (m : ℝ)⁻¹ * ∑ k ∈ Finset.range m, block u k

lemma abs_range_sum_bound (u : ℕ → ℝ) (C : ℝ)
    (hu : ∀ i, |u i| ≤ C) (n : ℕ) :
    |∑ i ∈ Finset.range n, u i| ≤ (n : ℝ) * C := by
  calc
    |∑ i ∈ Finset.range n, u i| ≤ ∑ i ∈ Finset.range n, |u i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, C := by
      apply Finset.sum_le_sum
      intro i hi
      exact hu i
    _ = (n : ℝ) * C := by simp

lemma average_close_to_blocks (u : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ i, |u i| ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      |average u n - blockAverage u (n / 4) / 4| ≤ 6 * C / (n : ℝ) := by
  filter_upwards [eventually_ge_atTop 4] with n hn
  let m := n / 4
  let r := n % 4
  have hm : 0 < m := by dsimp [m]; omega
  have hr : r < 4 := by dsimp [r]; exact Nat.mod_lt _ (by omega)
  have hnNat : 4 * m + r = n := by
    dsimp [m, r]
    exact Nat.div_add_mod n 4
  have hnReal : (n : ℝ) = 4 * (m : ℝ) + (r : ℝ) := by
    exact_mod_cast hnNat.symm
  have hnpos : 0 < (n : ℝ) := by positivity
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hrnonneg : 0 ≤ (r : ℝ) := by positivity
  have hrle : (r : ℝ) ≤ 3 := by exact_mod_cast (Nat.le_pred_of_lt hr)
  let S := ∑ i ∈ Finset.range (4 * m), u i
  let T := ∑ j ∈ Finset.range r, u (4 * m + j)
  have hsplit : (∑ i ∈ Finset.range n, u i) = S + T := by
    rw [← hnNat, Finset.sum_range_add]
  have hblocks : S = ∑ k ∈ Finset.range m, block u k := by
    exact sum_range_blocks u m
  have hS : |S| ≤ (4 * (m : ℝ)) * C := by
    dsimp [S]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      abs_range_sum_bound u C hu (4 * m)
  have hT : |T| ≤ (r : ℝ) * C := by
    dsimp [T]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      abs_range_sum_bound (fun j => u (4 * m + j)) C (fun j => hu _) r
  have herr : average u n - blockAverage u m / 4 =
      T / (n : ℝ) - S * (r : ℝ) / ((n : ℝ) * (4 * (m : ℝ))) := by
    rw [average, blockAverage, hsplit, ← hblocks]
    dsimp [S, T]
    rw [hnReal]
    field_simp
    ring
  have hfirst : |T / (n : ℝ)| ≤ (r : ℝ) * C / (n : ℝ) := by
    rw [abs_div, abs_of_pos hnpos]
    exact div_le_div_of_nonneg_right hT hnpos.le
  have hsecond : |S * (r : ℝ) / ((n : ℝ) * (4 * (m : ℝ)))| ≤
      (r : ℝ) * C / (n : ℝ) := by
    rw [abs_div, abs_mul, abs_of_nonneg hrnonneg,
      abs_of_pos (mul_pos hnpos (by positivity : 0 < 4 * (m : ℝ)))]
    calc
      |S| * (r : ℝ) / ((n : ℝ) * (4 * (m : ℝ))) ≤
          ((4 * (m : ℝ)) * C) * (r : ℝ) /
            ((n : ℝ) * (4 * (m : ℝ))) := by
              apply div_le_div_of_nonneg_right
              · exact mul_le_mul_of_nonneg_right hS hrnonneg
              · positivity
      _ = (r : ℝ) * C / (n : ℝ) := by field_simp
  calc
    |average u n - blockAverage u m / 4| =
        |T / (n : ℝ) - S * (r : ℝ) / ((n : ℝ) * (4 * (m : ℝ)))| := by rw [herr]
    _ ≤ |T / (n : ℝ)| +
          |S * (r : ℝ) / ((n : ℝ) * (4 * (m : ℝ)))| := abs_sub _ _
    _ ≤ 2 * ((r : ℝ) * C / (n : ℝ)) := by linarith [hfirst, hsecond]
    _ ≤ 6 * C / (n : ℝ) := by
      have hnC : 0 ≤ C / (n : ℝ) := div_nonneg hC hnpos.le
      have hz : 2 * ((r : ℝ) * (C / (n : ℝ))) ≤ 6 * (C / (n : ℝ)) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hrle) hnC]
      calc
        2 * ((r : ℝ) * C / (n : ℝ)) = 2 * ((r : ℝ) * (C / (n : ℝ))) := by ring
        _ ≤ 6 * (C / (n : ℝ)) := hz
        _ = 6 * C / (n : ℝ) := by ring

lemma average_tendsto_of_blocks (u : ℕ → ℝ) (C L : ℝ)
    (hC : 0 ≤ C) (hu : ∀ i, |u i| ≤ C)
    (hb : Tendsto (fun k : ℕ => block u k) atTop (𝓝 (4 * L))) :
    Tendsto (fun n : ℕ => average u n) atTop (𝓝 L) := by
  have hquot : Tendsto (fun n : ℕ => n / 4) atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop (4 * b)] with n hn
    exact Nat.le_div_iff_mul_le (by omega) |>.2 (by nlinarith)
  have hces : Tendsto (fun m : ℕ => blockAverage u m) atTop (𝓝 (4 * L)) := by
    exact hb.cesaro
  have hbase : Tendsto (fun n : ℕ => blockAverage u (n / 4) / 4) atTop (𝓝 L) := by
    have := (hces.comp hquot).div_const 4
    simpa using this
  have hsmall : Tendsto
      (fun n : ℕ => average u n - blockAverage u (n / 4) / 4) atTop (𝓝 0) := by
    have hg : Tendsto (fun n : ℕ => 6 * C / (n : ℝ)) atTop (𝓝 0) := by
      simpa using tendsto_const_div_atTop_nhds_zero_nat (6 * C : ℝ)
    apply Metric.tendsto_nhds.2
    intro ε hε
    have hevent := hg.eventually (Metric.ball_mem_nhds 0 hε)
    filter_upwards [average_close_to_blocks u C hC hu, hevent] with n hclose hnear
    have hsmall : 6 * C / (n : ℝ) < ε := by
      have hd : dist (6 * C / (n : ℝ)) 0 < ε := by simpa using hnear
      simp only [Real.dist_eq, sub_zero] at hd
      rw [abs_of_nonneg
        (div_nonneg (mul_nonneg (by norm_num : 0 ≤ (6 : ℝ)) hC) (by positivity))] at hd
      exact hd
    have hclose' : dist (average u n - blockAverage u (n / 4) / 4) 0 ≤
        6 * C / (n : ℝ) := by simpa [Real.dist_eq] using hclose
    exact lt_of_le_of_lt hclose' hsmall
  have htotal := hsmall.add hbase
  convert htotal using 1 <;> simp [sub_add_cancel]

lemma finiteMean_eq_average {N : ℕ} (u : ℕ → ℝ) :
    finiteMean (fun i : Fin N => u i.val) = average u N := by
  unfold finiteMean average
  rw [Finset.expect_eq_sum_div_card]
  simp only [Finset.card_univ, Fintype.card_fin, div_eq_inv_mul]
  congr 1
  simpa using Fin.sum_univ_eq_sum_range u N

end

end SAP.P022.WH.W1.P.T1_L2

open Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

theorem SAP.P022.WH.W1.T1_L2_proof : SAP.P022.WH.W1.T1_L2 := by
  change SAP.P022.weakPopulationConvergence
    SAP.P022.perturbedCornerWitness SAP.P022.cornerLaw
  intro f
  let u := SAP.P022.WH.W1.P.T1_L2.eval f
  have hu : ∀ i, |u i| ≤ ‖f‖ := by
    intro i
    change |f (SAP.P022.WH.W1.P.T1_L2.point i)| ≤ ‖f‖
    have h := f.norm_coe_le_norm (SAP.P022.WH.W1.P.T1_L2.point i)
    simpa only [Real.norm_eq_abs] using h
  have hcorner := SAP.P022.WH.W1.corner_integral f
  have hblocks : Tendsto (fun k : ℕ => SAP.P022.WH.W1.P.T1_L2.block
      (SAP.P022.WH.W1.P.T1_L2.eval f) k) atTop
      (𝓝 (4 * (∫ p, f p ∂(SAP.P022.cornerLaw : Measure (ℝ × ℝ))))) := by
    have h := SAP.P022.WH.W1.P.T1_L2.block_tendsto f
    have hcorner4 : 4 * (∫ p, f p ∂(SAP.P022.cornerLaw : Measure (ℝ × ℝ))) =
        f (0, 0) + f (0, 1) + f (1, 0) + f (1, 1) := by
      rw [hcorner]
      ring
    simpa only [hcorner4] using h
  have havg := SAP.P022.WH.W1.P.T1_L2.average_tendsto_of_blocks
    u ‖f‖ (∫ p, f p ∂(SAP.P022.cornerLaw : Measure (ℝ × ℝ)))
    (norm_nonneg _) hu hblocks
  have hshift : Tendsto (fun q : ℕ => q + 4) atTop atTop :=
    (tendsto_add_atTop_iff_nat 4).2 tendsto_id
  have hconv := havg.comp hshift
  change Tendsto (fun q => finiteMean (fun i : Fin (q + 4) => u i.val)) atTop
    (𝓝 (∫ p, f p ∂(SAP.P022.cornerLaw : Measure (ℝ × ℝ))))
  have hmean (q : ℕ) :
      finiteMean (fun i : Fin (q + 4) => u i.val) =
        SAP.P022.WH.W1.P.T1_L2.average u (q + 4) := by
    exact SAP.P022.WH.W1.P.T1_L2.finiteMean_eq_average u
  simpa only [hmean, Function.comp_def] using hconv

