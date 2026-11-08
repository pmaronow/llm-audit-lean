import SAP.P004b.WH.W1.Leaves
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W1.P.T26_L1

open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem centered_kernel_split {N : ℕ} (hN : 0 < N)
    (D : Fin N → Fin N → ℝ) (a : Fin N → ℝ) (K φ : ℝ → ℝ)
    (b r A C Cb L ε T : ℝ) (hb : 0 < b) (hr : 0 ≤ r)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hCb : 0 ≤ Cb) (hL : 0 ≤ L)
    (hD : ∀ i j, 0 ≤ D i j) (hcenter : ∑ i, a i = 0)
    (ha : ∀ i, |a i| ≤ A) (henv : ∀ i j, |a i| * |a j| ≤ φ (D i j))
    (hcount : ∀ i, ((ball D i r).card : ℝ) ≤ Cb * (1 + r^2))
    (hK : ∀ t, 0 ≤ t → |K t| ≤ L)
    (hnear : ∀ t, 0 ≤ t → t < ε → |K t - 1| ≤ C * |t|)
    (hre : r / b < ε)
    (htail : ∀ i, (∑ j ∈ (ball D i r)ᶜ, φ (D i j)) ≤ T) :
    |(∑ i, ∑ j, K (D i j / b) * a i * a j) / (N : ℝ)| ≤
      A^2 * C * Cb * (r / b + r^3 / b) + (L + 1) * T := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  let F := fun i j => (K (D i j / b) - 1) * a i * a j
  have hcancel : (∑ i, ∑ j, K (D i j / b) * a i * a j) = ∑ i, ∑ j, F i j := by
    have hz : (∑ i, ∑ j, a i * a j) = 0 := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul, hcenter, mul_zero, Finset.sum_const_zero]
    dsimp [F]
    simp_rw [sub_mul, one_mul]
    simp only [Finset.sum_sub_distrib]
    rw [hz, sub_zero]
  have hprod (i j : Fin N) : |a i| * |a j| ≤ A^2 := by
    simpa only [pow_two] using mul_le_mul (ha i) (ha j) (abs_nonneg _) hA
  have hrow (i : Fin N) : (∑ j, |F i j|) ≤
      A^2 * C * Cb * (r / b + r^3 / b) + (L + 1) * T := by
    have hsmall (j : Fin N) (hj : j ∈ ball D i r) :
        |F i j| ≤ (C * (r / b)) * A^2 := by
      have hd : D i j ≤ r := (Finset.mem_filter.mp hj).2
      have ht : D i j / b ≤ r / b := div_le_div_of_nonneg_right hd hb.le
      have ht0 : 0 ≤ D i j / b := div_nonneg (hD i j) hb.le
      have hk := hnear _ ht0 (ht.trans_lt hre)
      rw [abs_of_nonneg ht0] at hk
      have hk' : |K (D i j / b) - 1| ≤ C * (r / b) :=
        hk.trans (mul_le_mul_of_nonneg_left ht hC)
      dsimp [F]
      rw [abs_mul, abs_mul, mul_assoc]
      exact mul_le_mul hk' (hprod i j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (mul_nonneg hC (div_nonneg hr hb.le))
    have hlarge (j : Fin N) : |F i j| ≤ (L + 1) * φ (D i j) := by
      have hk : |K (D i j / b) - 1| ≤ L + 1 :=
        (abs_sub _ _).trans (by simpa using add_le_add (hK _ (div_nonneg (hD i j) hb.le)) (le_refl (1 : ℝ)))
      dsimp [F]
      rw [abs_mul, abs_mul, mul_assoc]
      exact mul_le_mul hk (henv i j) (by positivity) (by linarith)
    calc
      (∑ j, |F i j|) = (∑ j ∈ ball D i r, |F i j|) +
          ∑ j ∈ (ball D i r)ᶜ, |F i j| :=
        (Finset.sum_add_sum_compl (ball D i r) (fun j => |F i j|)).symm
      _ ≤ (∑ _j ∈ ball D i r, (C * (r / b)) * A^2) +
          ∑ j ∈ (ball D i r)ᶜ, (L + 1) * φ (D i j) := by
        exact add_le_add (Finset.sum_le_sum hsmall)
          (Finset.sum_le_sum (fun j _ => hlarge j))
      _ = ((ball D i r).card : ℝ) * ((C * (r / b)) * A^2) +
          (L + 1) * (∑ j ∈ (ball D i r)ᶜ, φ (D i j)) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
      _ ≤ (Cb * (1 + r^2)) * ((C * (r / b)) * A^2) + (L + 1) * T :=
        add_le_add (mul_le_mul_of_nonneg_right (hcount i) (by positivity))
          (mul_le_mul_of_nonneg_left (htail i) (by linarith))
      _ = _ := by ring
  rw [hcancel, abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    |∑ i, ∑ j, F i j| ≤ ∑ i, |∑ j, F i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |F i j| := Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin N, (A^2 * C * Cb * (r / b + r^3 / b) + (L + 1) * T) :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = _ := by simp [mul_comm] <;> ring

end
end SAP.P004b.WH.W1.P.T26_L1

open Filter
open scoped BigOperators Classical Topology

namespace SAP.P004b.WH.W1

theorem T26_L1_proof : T26_L1 := by
  intro D a K φ b hD hcenter hA hcount hK hb hφ henv htail
  obtain ⟨A, hA0, hAb⟩ := hA
  obtain ⟨Cb, hCb0, hCb⟩ := hcount
  obtain ⟨L, hL⟩ := hK.2.2.1
  obtain ⟨ε, C, hε, hε1, hC0, hnear⟩ := hK.2.2.2
  have hL0 : 0 ≤ L := by
    have hh := hL 0 (by norm_num)
    rw [hK.1] at hh
    norm_num at hh
    linarith
  let r : ℕ → ℝ := fun N => b N ^ (1 / 6 : ℝ)
  have hrdiv : Tendsto r atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp hb
  have hbpos : ∀ᶠ N in atTop, 0 < b N := hb.eventually (eventually_gt_atTop 0)
  have hid1 : (fun N => r N / b N) =ᶠ[atTop] (fun N => b N ^ (-(5 / 6 : ℝ))) := by
    filter_upwards [hbpos] with N hbp
    dsimp [r]
    rw [← Real.rpow_sub_one hbp.ne']
    norm_num
  have hid3 : (fun N => (r N)^3 / b N) =ᶠ[atTop] (fun N => b N ^ (-(1 / 2 : ℝ))) := by
    filter_upwards [hbpos] with N hbp
    dsimp [r]
    rw [← Real.rpow_mul_natCast hbp.le, ← Real.rpow_sub_one hbp.ne']
    norm_num
  have ht1 : Tendsto (fun N => r N / b N) atTop (nhds 0) := by
    refine Filter.Tendsto.congr' hid1.symm ?_
    exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5 / 6)).comp hb
  have ht3 : Tendsto (fun N => (r N)^3 / b N) atTop (nhds 0) := by
    refine Filter.Tendsto.congr' hid3.symm ?_
    exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hb
  have hbound : ∀ᶠ N in atTop, |arrayKernel D a K b N| ≤
      A^2 * C * Cb * (r N / b N + (r N)^3 / b N) +
        (L + 1) * exteriorEnvelope D φ r N := by
    filter_upwards [eventually_gt_atTop 0, hD, hcenter, hAb, hCb, henv, hbpos,
      ht1.eventually (eventually_lt_nhds hε)] with N hN hDN hcN hAN hCbN heN hbp hreN
    rw [arrayKernel]
    apply SAP.P004b.WH.W1.P.T26_L1.centered_kernel_split hN (D N) (a N) K φ (b N) (r N) A C Cb L ε
      (exteriorEnvelope D φ r N) hbp (by positivity)
      hA0 hC0.le hCb0.le hL0 hDN hcN hAN heN (fun i => hCbN i (r N) (by positivity))
      (fun t ht => (hL t ht).le) hnear hreN ?_
    · intro i
      change (∑ j ∈ (ball (D N) i (r N))ᶜ, φ (D N i j)) ≤
        rowMaximum (fun k => ∑ j ∈ (ball (D N) k (r N))ᶜ, φ (D N k j))
      rw [rowMaximum, if_pos hN]
      exact le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self i)
  have hupper : Tendsto
      (fun N => A^2 * C * Cb * (r N / b N + (r N)^3 / b N) +
        (L + 1) * exteriorEnvelope D φ r N) atTop (nhds 0) := by
    have htail' := htail r hrdiv
    simpa [mul_add, add_comm, add_left_comm, add_assoc] using
      ((ht1.add ht3).const_mul (A^2 * C * Cb)).add (htail'.const_mul (L + 1))
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  exact squeeze_zero' (Eventually.of_forall (fun N => abs_nonneg _)) hbound hupper

end SAP.P004b.WH.W1
