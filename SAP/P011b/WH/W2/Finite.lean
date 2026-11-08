import SAP.P011b.Defs.WholeW2
import SAP.P011b.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b.WH.W2

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

/-- The OLS weighted-average representation is algebraic and needs no mean law. -/
theorem ols_coefficientW2 {n p : ℕ} (hn : 0 < n) (m : Model n)
    (D : Matrix (Fin n) (Fin p) ℝ) (j : Fin p)
    (hθ : ∀ i, m.theta i = olsTheta D j i) (y : Fin n → ℝ) :
    betaHat m y = ols D y j := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  simp only [betaHat, average, weighted, hθ, olsTheta, Matrix.smul_apply, smul_eq_mul]
  rw [ols, Matrix.mulVec_mulVec]
  change (∑ i, (n : ℝ) * (((Dᵀ * D)⁻¹ * Dᵀ) j i) * y i) / (n : ℝ) =
    ∑ i, (((Dᵀ * D)⁻¹ * Dᵀ) j i) * y i
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  exact mul_div_cancel_left₀ _ hn0

theorem finite_identitiesW2 : FiniteOLSIdentitiesW2 := by
  intro n p hp hpn m D b j hr hm hθ
  have ht : (∀ y, betaHat m y = ols D y j) ∧ beta m = b j :=
    AronowAudit.P011.Wave1.olsr_target (show 0 < n by omega)
      (Bridge.toModel m) D b j hr hm hθ
  refine ⟨ht.1, ht.2, ?_⟩
  intro i
  have he : expectation m (fun y => weighted m y i) = olsTheta D j i * (D *ᵥ b) i := by
    have hh := AronowAudit.P011.Wave1.rps_weighted_mean (Bridge.toModel m) D b hm i
    change expectation m (fun y => weighted m y i) = m.theta i * (D *ᵥ b) i at hh
    simpa only [hθ i] using hh
  exact ⟨he, by unfold delta; rw [he, ht.2]⟩

theorem shift_identitiesW2 : OLSShiftIdentitiesW2 := by
  intro n p hp hpn m D j hr hθ y c
  have ha : ols D (y + D *ᵥ c) = ols D y + c :=
    AronowAudit.P011.Wave1.olsr_add D hr y c
  have hq : fittedResidual m D (ols D) (y + D *ᵥ c) =
      fittedResidual m D (ols D) y := by
    ext i
    simp only [fittedResidual, ha, Matrix.mulVec_add, Pi.add_apply]
    ring
  refine ⟨ha, hq, fun A => congrArg (VResidual A) hq, ?_⟩
  have hb : average (weighted m (y + D *ᵥ c)) = average (weighted m y) + c j := by
    change betaHat m (y + D *ᵥ c) = betaHat m y + c j
    rw [ols_coefficientW2 (by omega) m D j hθ,
      ols_coefficientW2 (by omega) m D j hθ, ha]
    rfl
  ext i
  simp only [centered, hb, weighted, Pi.add_apply]
  ring

theorem intercept_identitiesW2 : InterceptShiftIdentitiesW2 := by
  intro n p hp hpn m D j j₀ hr hθ hi hj y t
  let c : Fin p → ℝ := Pi.single j₀ t
  have hc : c j = 0 := by simp [c, Pi.single_apply, hj]
  have hDc : D *ᵥ c = fun _ => t := by
    ext i
    classical
    simp only [c, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single j₀]
    · simp [hi]
    · intro a _ ha
      simp [Pi.single_eq_of_ne ha]
    · simp
  have hs := shift_identitiesW2 n p hp hpn m D j hr hθ y c
  rw [hDc] at hs
  refine ⟨?_, hs.2.1, hs.2.2.1⟩
  have hh := congrFun hs.1 j
  simpa only [Pi.add_apply, hc, add_zero] using hh

/-- Valid constraints give an attaining selection for any real objective. -/
theorem selection_existsW2 (F : Family) (hv : Valid F)
    (f : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k) → ℝ) :
    ∃ A : GraphSelectionW2 F, ∀ k y,
      Maximizes (F.model k).R (F.model k).d (f k y) (A k y) := by
  have h (k : ℕ) (y : Fin (F.size k) → ℝ) :
      ∃ A, Maximizes (F.model k).R (F.model k).d (f k y) A :=
    (AronowAudit.P011.oracle_sharp_bound _ _ _ (hv k) (f k y)).1
  exact ⟨fun k y => Classical.choose (h k y), fun k y => Classical.choose_spec (h k y)⟩

/-- Express the maximizing value as a finite supremum of measurable functions. -/
theorem maximum_measurableW2 : CompatibleMaximaMeasurableW2 := by
  classical
  intro n R G d hv f hf A hA
  let S : Finset (Graph n) := Finset.univ.filter (Compatible R d)
  have hS : S.Nonempty := ⟨G, by simp [S, hv]⟩
  have hM : Measurable (S.sup' hS f) :=
    Finset.measurable_sup' hS (fun B _ => hf B)
  have he : (fun y => f (A y) y) = S.sup' hS f := by
    funext y
    apply le_antisymm
    · have ha : A y ∈ S := by simpa [S] using (hA y).1
      exact (Finset.le_sup' (f := f) ha) y
    · have hb : S.sup' hS f ≤ fun y => f (A y) y := by
        apply (Finset.sup'_le_iff hS f).mpr
        intro B hB z
        exact (hA z).2 B (by simpa [S] using hB)
      exact hb y
  rw [he]
  exact hM

theorem raw_conclusionsW2 : RawOracleConclusionsW2 := by
  intro F c1 c2 c3 c4 h
  have hm := AronowAudit.P011.oracle_mean_conditions (Bridge.toFamily F) c1 c2 c3 c4 h
  have hmax (hv : Valid F)
      (ho : Conservative F (fun k y => V1 (F.model k).G (weighted (F.model k) y))) :
      AllRawMaxConservativeW2 F := by
    intro A hA
    exact AronowAudit.P011.CorollaryCompletion.conservative_mono (Bridge.toFamily F)
      _ _ ho (fun k y => (hA k y).2 _ (hv k))
  refine ⟨?_, hm.1, hm.2.1, ?_, ?_⟩
  · intro ε hε
    have hh := AronowAudit.P011.revised_oracle_convergence (Bridge.toFamily F)
      c1 c2 c3 c4 h ε hε
    convert hh using 1
    funext k
    congr 1
    ext y
    change (ε < |scaledOracle F k y - scaledTrue F k - meanBias (F.model k)|) ↔
      (ε < |scaledOracle F k y - (scaledTrue F k + meanBias (F.model k))|)
    rw [sub_sub]
  · intro hv
    exact ⟨selection_existsW2 F hv (fun k y B => V1 B (weighted (F.model k) y)),
      fun hb => hmax hv (hm.2.1.mpr hb)⟩
  · intro he
    have hδ : ∀ k i, delta (F.model k) i = 0 := by
      intro k i
      simp [delta, he k i]
    have ho : InProbability F (scaledOracle F) (scaledTrue F) := hm.2.2.1 hδ
    refine ⟨ho, ?_⟩
    intro hv
    apply hmax hv
    intro ε hε
    apply squeeze_zero (fun _ => measureReal_nonneg) (fun k => ?_) (ho ε hε)
    letI : IsProbabilityMeasure (F.model k).law := (F.model k).probability
    apply measureReal_mono (μ := (F.model k).law) ?_ (measure_ne_top _ _)
    intro y hy
    change ε < (F.size k : ℝ) *
      (var (F.model k) (betaHat (F.model k)) - V1 (F.model k).G (weighted (F.model k) y)) at hy
    change ε < |scaledOracle F k y - scaledTrue F k|
    dsimp [scaledOracle, scaledTrue]
    have hh := neg_le_abs (scaledOracle F k y - scaledTrue F k)
    dsimp [scaledOracle, scaledTrue] at hh
    linarith

/-- The finite slope-shift example has a diagonal Gram matrix and explicit inverse. -/
theorem slope_shift_witnessW2 : RawSlopeShiftWitnessW2 := by
  have hG : shiftDesignW2ᵀ * shiftDesignW2 = Matrix.diagonal (![2, 2] : Fin 2 → ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [shiftDesignW2, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_succ]
  have hdet : (shiftDesignW2ᵀ * shiftDesignW2).det ≠ 0 := by
    rw [hG, Matrix.det_diagonal]
    norm_num [Fin.prod_univ_succ]
  have hInv : (shiftDesignW2ᵀ * shiftDesignW2)⁻¹ =
      Matrix.diagonal (![1/2, 1/2] : Fin 2 → ℝ) := by
    apply Matrix.inv_eq_left_inv
    rw [hG]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply, Fin.sum_univ_succ]
  have hθ : ∀ i, shiftModelW2.theta i = olsTheta shiftDesignW2 1 i := by
    intro i
    unfold olsTheta
    rw [hInv]
    fin_cases i <;>
      norm_num [shiftModelW2, Matrix.mul_apply, shiftDesignW2,
        Matrix.diagonal_apply, Fin.sum_univ_succ]
  have hm : MeanModel shiftModelW2 shiftDesignW2 0 := by
    constructor
    · intro i
      exact integrable_dirac (by simp)
    · intro i
      simp [expectation, shiftModelW2]
  have hi : ∀ i, shiftDesignW2 i 0 = 1 := by intro i; fin_cases i <;> rfl
  have hs := intercept_identitiesW2 2 2 (by omega) (by omega) shiftModelW2
    shiftDesignW2 1 0 hdet hθ hi (by decide) 0 1
  refine ⟨hdet, hm, hθ, hi, ?_, ?_, ?_, ?_⟩
  · simpa using hs.1.symm
  · simpa using hs.2.1.symm
  · norm_num [V1, weighted, shiftModelW2, centered, average, quadratic, adjacency,
      emptyGraph, Fin.sum_univ_succ]
  · norm_num [V1, weighted, shiftModelW2, centered, average, quadratic, adjacency,
      emptyGraph, Fin.sum_univ_succ]

end
end SAP.P011b.WH.W2
