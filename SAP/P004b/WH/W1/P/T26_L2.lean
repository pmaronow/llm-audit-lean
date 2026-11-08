import SAP.P004b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W1.P.T26_L2

open scoped BigOperators Classical

private theorem le_rowMaximum {N : ℕ} (hN : 0 < N) (f : Fin N → ℝ) (i : Fin N) :
    f i ≤ SAP.P004b.rowMaximum f := by
  rw [SAP.P004b.rowMaximum, if_pos hN]
  exact le_csSup (Set.finite_range f).bddAbove (Set.mem_range.mpr ⟨i, rfl⟩)

private theorem rowMaximum_le {N : ℕ} (hN : 0 < N) (f : Fin N → ℝ) (c : ℝ)
    (hc : ∀ i, f i ≤ c) : SAP.P004b.rowMaximum f ≤ c := by
  rw [SAP.P004b.rowMaximum, if_pos hN]
  apply csSup_le
  · exact ⟨f ⟨0, hN⟩, Set.mem_range.mpr ⟨⟨0, hN⟩, rfl⟩⟩
  · rintro x ⟨i, rfl⟩
    exact hc i

end SAP.P004b.WH.W1.P.T26_L2

open SAP.P004b.WH.W1.P.T26_L2
open scoped BigOperators Classical

theorem SAP.P004b.WH.W1.T26_L2_proof : SAP.P004b.WH.W1.T26_L2 := by
  unfold SAP.P004b.WH.W1.T26_L2
  intro N D a K φ b L hN hD hzero hb hφ henv hsupport hK
  let rows : Fin N → ℝ := fun i => ∑ j ∈ SAP.P004b.ball D i b, φ (D i j)
  let S : ℝ := SAP.P004b.rowMaximum rows
  have hball (i : Fin N) : i ∈ SAP.P004b.ball D i b := by
    simp [SAP.P004b.ball, hzero i, le_of_lt hb]
  have hrow_nonneg (i : Fin N) : 0 ≤ rows i := by
    dsimp [rows]
    exact Finset.sum_nonneg fun j hj => hφ (D i j) (hD i j)
  have hphi_row (i : Fin N) : φ 0 ≤ rows i := by
    dsimp [rows]
    calc
      φ 0 = φ (D i i) := by rw [hzero i]
      _ ≤ ∑ j ∈ SAP.P004b.ball D i b, φ (D i j) :=
        Finset.single_le_sum (fun j hj => hφ (D i j) (hD i j)) (hball i)
  have hsquare_row (i : Fin N) : (a i)^2 ≤ rows i := by
    have hdiag : |a i| * |a i| ≤ φ 0 := by simpa [hzero i] using henv i i
    have habsq : (a i)^2 = |a i| * |a i| := by rw [← sq_abs]; ring
    rw [habsq]
    exact le_trans hdiag (hphi_row i)
  have hrow_le (i : Fin N) : rows i ≤ S := by
    exact le_rowMaximum hN rows i
  have hphi_S : φ 0 ≤ S := by
    exact le_trans (hphi_row ⟨0, hN⟩) (hrow_le ⟨0, hN⟩)
  have hsquares_S : SAP.P004b.rowMaximum (fun i => (a i)^2) ≤ S := by
    apply rowMaximum_le hN
    intro i
    exact le_trans (hsquare_row i) (hrow_le i)
  have hL : 0 ≤ L := le_trans (abs_nonneg (K 0)) (hK 0 (by norm_num))
  have hpair (i j : Fin N) :
      |K (D i j / b) * a i * a j| ≤
        if j ∈ SAP.P004b.ball D i b then L * φ (D i j) else 0 := by
    by_cases hj : j ∈ SAP.P004b.ball D i b
    · have ht : 0 ≤ D i j / b := div_nonneg (hD i j) hb.le
      simp only [if_pos hj]
      calc
        |K (D i j / b) * a i * a j| = |K (D i j / b)| * |a i| * |a j| := by
          rw [abs_mul, abs_mul]
        _ = |K (D i j / b)| * (|a i| * |a j|) := by ring
        _ ≤ L * (|a i| * |a j|) :=
          mul_le_mul_of_nonneg_right (hK (D i j / b) ht)
            (mul_nonneg (abs_nonneg (a i)) (abs_nonneg (a j)))
        _ ≤ L * φ (D i j) := mul_le_mul_of_nonneg_left (henv i j) hL
    · have hd : b < D i j := by
        have hnot : ¬ D i j ≤ b := by
          simpa [SAP.P004b.ball] using hj
        exact lt_of_not_ge hnot
      have ht : 1 < D i j / b := (one_lt_div hb).2 hd
      have hKzero : K (D i j / b) = 0 := hsupport _ ht
      simp [hj, hKzero]
  have hrow_kernel (i : Fin N) :
      |∑ j, K (D i j / b) * a i * a j| ≤ L * rows i := by
    calc
      |∑ j, K (D i j / b) * a i * a j| ≤
          ∑ j, |K (D i j / b) * a i * a j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ SAP.P004b.ball D i b, |K (D i j / b) * a i * a j| := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j hj hnot
        have hd : b < D i j := by
          have hnotball : ¬ j ∈ SAP.P004b.ball D i b := hnot
          have hnotle : ¬ D i j ≤ b := by
            simpa [SAP.P004b.ball] using hnotball
          exact lt_of_not_ge hnotle
        have ht : 1 < D i j / b := (one_lt_div hb).2 hd
        simp [hsupport _ ht]
      _ ≤ ∑ j ∈ SAP.P004b.ball D i b, L * φ (D i j) := by
        apply Finset.sum_le_sum
        intro j hj
        have := hpair i j
        simpa [hj] using this
      _ = L * rows i := by
        dsimp [rows]
        rw [Finset.mul_sum]
  have hdouble :
      |∑ i, ∑ j, K (D i j / b) * a i * a j| ≤
        L * (∑ i, rows i) := by
    calc
      |∑ i, ∑ j, K (D i j / b) * a i * a j| ≤
          ∑ i, |∑ j, K (D i j / b) * a i * a j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, L * rows i := Finset.sum_le_sum fun i hi => hrow_kernel i
      _ = L * (∑ i, rows i) := by rw [Finset.mul_sum]
  have hsumrows : (∑ i, rows i) ≤ (N : ℝ) * S := by
    calc
      (∑ i, rows i) ≤ ∑ _i : Fin N, S :=
        Finset.sum_le_sum fun i hi => hrow_le i
      _ = (N : ℝ) * S := by simp
  have htotal :
      |∑ i, ∑ j, K (D i j / b) * a i * a j| ≤ (L * S) * (N : ℝ) := by
    calc
      |∑ i, ∑ j, K (D i j / b) * a i * a j| ≤ L * (∑ i, rows i) := hdouble
      _ ≤ L * ((N : ℝ) * S) := mul_le_mul_of_nonneg_left hsumrows hL
      _ = (L * S) * (N : ℝ) := by ring
  refine ⟨hphi_S, hsquares_S, ?_⟩
  calc
    |(∑ i, ∑ j, K (D i j / b) * a i * a j) / (N : ℝ)| =
        |∑ i, ∑ j, K (D i j / b) * a i * a j| / (N : ℝ) := by
          rw [abs_div]
          apply congrArg (fun z : ℝ =>
            |∑ i, ∑ j, K (D i j / b) * a i * a j| / z)
          exact abs_of_pos (Nat.cast_pos.mpr hN)
    _ ≤ L * S := (div_le_iff₀ (Nat.cast_pos.mpr hN)).2 htotal

