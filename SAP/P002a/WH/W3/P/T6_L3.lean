import SAP.P002a.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace SAP.P002a.WH.W3.P.T6_L3

open scoped BigOperators Matrix Classical
noncomputable section

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
  have hmat : gram x S *ᵥ t6Coef a b = score x S q := by
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
  rw [ols, if_pos hg, ← hmat, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hg), Matrix.one_mulVec]

private lemma det_two (M : Matrix (Option (Fin 1)) (Option (Fin 1)) ℝ) :
    M.det = M none none * M (some 0) (some 0) -
      M none (some 0) * M (some 0) none := by
  calc
    M.det = (M.reindex (finSuccEquiv 1).symm (finSuccEquiv 1).symm).det :=
      (Matrix.det_reindex_self _ M).symm
    _ = _ := by rw [Matrix.det_fin_two]; rfl

private lemma gram_det {n : ℕ} (x : Fin n → Fin 1 → ℝ)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    (gram x S).det = groupMean S (fun i => x i 0 ^ 2) -
      (groupMean S (fun i => x i 0)) ^ 2 := by
  have hc : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  rw [det_two]
  simp [gram, augmented, groupMean, hc, pow_two]

private lemma univ_groupMean {n : ℕ} (f : Fin n → ℝ) :
    groupMean Finset.univ f = mean f := by
  simp [groupMean, mean]

end
end SAP.P002a.WH.W3.P.T6_L3

theorem SAP.P002a.WH.W3.T6_L3_proof : SAP.P002a.WH.W3.T6_L3 := by
  intro m hm hx hy hx2 hxy a
  have hm0 : 0 < m := by omega
  have hn0 : 0 < 2 * m := by omega
  have hden : 0 < 1 + t6Eta m ^ 2 * t6V m := by
    have heta : 0 < t6Eta m := by
      dsimp [t6Eta]
      positivity
    have hv : 0 < t6V m := by
      dsimp [t6V]
      have hmR : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      apply div_pos
      · linarith
      · nlinarith
    positivity
  have hgamma : t6Gamma m * (1 + t6Eta m ^ 2 * t6V m) =
      t6Eta m * t6V m := by
    dsimp [t6Gamma]
    field_simp
  have hg : (gram (nearSingularModel m).x Finset.univ).det ≠ 0 := by
    rw [SAP.P002a.WH.W3.P.T6_L3.gram_det _ _
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn0⟩⟩)]
    have hmx : groupMean Finset.univ (fun i => (nearSingularModel m).x i 0) =
        mean (t6X m) := by
      rw [SAP.P002a.WH.W3.P.T6_L3.univ_groupMean]
      rfl
    have hmx2 : groupMean Finset.univ
        (fun i => (nearSingularModel m).x i 0 ^ 2) =
        mean (fun i => t6X m i ^ 2) := by
      rw [SAP.P002a.WH.W3.P.T6_L3.univ_groupMean]
      rfl
    rw [hmx2, hmx, hx2, hx]
    simpa using ne_of_gt hden
  have hw (a : Bool) : w (nearSingularModel m).pop a 0 = t6Y m := by
    funext i
    simp [w, nearSingularModel, t6Y, t6T]
  have hmx : groupMean Finset.univ
      (fun i => (nearSingularModel m).x i 0) = mean (t6X m) := by
    rw [SAP.P002a.WH.W3.P.T6_L3.univ_groupMean]
    rfl
  have hmy : groupMean Finset.univ (t6Y m) = mean (t6Y m) := by
    exact SAP.P002a.WH.W3.P.T6_L3.univ_groupMean _
  have hfit : psi (nearSingularModel m) a 0 = t6Coef 0 (t6Gamma m) := by
    unfold psi
    rw [hw]
    apply SAP.P002a.WH.W3.P.T6_L3.scalar_ols
      (nearSingularModel m).x Finset.univ (t6Y m)
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn0⟩⟩) hg 0 (t6Gamma m)
    · rw [hmx, hmy]
      rw [hx, hy]
      ring
    · have hmx2 : groupMean Finset.univ
          (fun i => (nearSingularModel m).x i 0 ^ 2) =
          mean (fun i => t6X m i ^ 2) := by
        rw [SAP.P002a.WH.W3.P.T6_L3.univ_groupMean]
        rfl
      have hmxy : groupMean Finset.univ
          (fun i => (nearSingularModel m).x i 0 * t6Y m i) =
          mean (fun i => t6X m i * t6Y m i) := by
        rw [SAP.P002a.WH.W3.P.T6_L3.univ_groupMean]
        rfl
      rw [hmx, hmx2, hmxy]
      change 0 * mean (t6X m) + t6Gamma m *
        mean (fun i => t6X m i ^ 2) =
        mean (fun i => t6X m i * t6Y m i)
      rw [hx2, hxy]
      simpa using hgamma
  refine ⟨hfit, ?_⟩
  funext i
  rw [residual, hfit]
  simp [dotProduct, Fintype.sum_option, Fin.sum_univ_one, t6Coef,
    augmented, w, nearSingularModel, t6X, t6Y, t6Gamma, t6Error, mul_comm]
