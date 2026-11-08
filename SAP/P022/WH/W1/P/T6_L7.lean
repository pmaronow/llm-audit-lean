import SAP.P022.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T6_L7

open SAP.P022 Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem probability_union (d : Design) {n : ℕ}
    (E : Assignment d → Prop) (F : Fin n → Assignment d → Prop)
    (hEF : ∀ π, E π → ∃ j, F j π) :
    designProbability d E ≤ ∑ j, designProbability d (F j) := by
  classical
  unfold designProbability designExpectation
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_le_expect
  intro π _
  by_cases he : E π
  · obtain ⟨j, hj⟩ := hEF π he
    rw [if_pos he]
    calc
      (1 : ℝ) = (if F j π then 1 else 0) := by simp [hj]
      _ ≤ ∑ i : Fin n, if F i π then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun i : Fin n => if F i π then (1 : ℝ) else 0)
          (fun i _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
  · simp only [if_neg he]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

theorem scaled_union {n : ℕ} (S : ExperimentSequence)
    (E : (q : ℕ) → Assignment (S.design q) → Prop)
    (F : Fin n → (q : ℕ) → Assignment (S.design q) → Prop)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hF : ∀ j, scaledProbabilityLimsup S (F j) ≤ ENNReal.ofReal (r j))
    (hEF : ∀ᶠ q in atTop, ∀ π, E q π → ∃ j, F j q π) :
    scaledProbabilityLimsup S E ≤ ENNReal.ofReal (∑ j, r j) := by
  classical
  apply ENNReal.le_of_forall_pos_le_add
  intro e he _
  let δ : ℝ := (e : ℝ) / (n + 1 : ℕ)
  have heR : 0 < (e : ℝ) := by exact_mod_cast he
  have hδ : 0 < δ := div_pos heR (by positivity)
  have hj : ∀ j, ∀ᶠ q in atTop,
      ((S.design q).N : ℝ) * designProbability (S.design q) (F j q) < r j + δ := by
    intro j
    have hlt : scaledProbabilityLimsup S (F j) < ENNReal.ofReal (r j + δ) :=
      (hF j).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith [hr j])).2
        (by linarith))
    have hv := Filter.eventually_lt_of_limsup_lt hlt
    filter_upwards [hv] with q hq
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [hr j])).1 hq
  have hall : ∀ᶠ q in atTop, ∀ j,
      ((S.design q).N : ℝ) * designProbability (S.design q) (F j q) < r j + δ :=
    Filter.eventually_all.mpr hj
  have hb : ∀ᶠ q in atTop, ENNReal.ofReal (((S.design q).N : ℝ) *
      designProbability (S.design q) (E q)) ≤ ENNReal.ofReal ((∑ j, r j) + (e : ℝ)) := by
    filter_upwards [hEF, hall] with q hq hqF
    apply ENNReal.ofReal_le_ofReal
    calc
      ((S.design q).N : ℝ) * designProbability (S.design q) (E q)
          ≤ ((S.design q).N : ℝ) * ∑ j, designProbability (S.design q) (F j q) :=
        mul_le_mul_of_nonneg_left (probability_union _ _ _ hq) (Nat.cast_nonneg _)
      _ = ∑ j, ((S.design q).N : ℝ) * designProbability (S.design q) (F j q) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ j, (r j + δ) := Finset.sum_le_sum (fun j _ => (hqF j).le)
      _ = (∑ j, r j) + n * δ := by simp [Finset.sum_add_distrib]
      _ ≤ (∑ j, r j) + (e : ℝ) := by
        have hn : (n : ℝ) / (n + 1 : ℕ) ≤ 1 :=
          (div_le_one (by positivity)).2 (by push_cast; linarith)
        have hh := mul_le_mul_of_nonneg_right hn heR.le
        have hnd : (n : ℝ) * δ ≤ (e : ℝ) := by
          calc
            (n : ℝ) * δ = ((n : ℝ) / (n + 1 : ℕ)) * (e : ℝ) := by dsimp [δ]; ring
            _ ≤ (e : ℝ) := by simpa only [one_mul] using hh
        linarith
  have hs : 0 ≤ ∑ j, r j := Finset.sum_nonneg (fun j _ => hr j)
  calc
    scaledProbabilityLimsup S E ≤ ENNReal.ofReal ((∑ j, r j) + (e : ℝ)) :=
      Filter.limsup_le_of_le (by isBoundedDefault) hb
    _ = ENNReal.ofReal (∑ j, r j) + e := by
      rw [ENNReal.ofReal_add hs heR.le]
      simp

theorem law_cdf_bounds (H : JointLaw) (t : Bool) (x : ℝ) :
    0 ≤ lawCDF H t x ∧ lawCDF H t x ≤ 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · unfold lawCDF
    have hm : (H : Measure (ℝ × ℝ))
        {p | (if t then p.1 else p.2) ≤ x} ≤ 1 := by
      simpa using (measure_mono (μ := (H : Measure (ℝ × ℝ))) (Set.subset_univ _))
    exact (ENNReal.toReal_mono (by simp) hm).trans_eq (by simp)

theorem cdf_point (A B : ℝ → ℝ)
    (hA : ∀ x, 0 ≤ A x ∧ A x ≤ 1) (hB : ∀ x, 0 ≤ B x ∧ B x ≤ 1) (x : ℝ) :
    |A x - B x| ≤ cdfDistance A B := by
  refine le_csSup ?_ (Set.mem_range_self x)
  refine ⟨1, ?_⟩
  rintro _ ⟨y, rfl⟩
  rw [abs_sub_le_iff]
  constructor <;> linarith [(hA y).1, (hA y).2, (hB y).1, (hB y).2]

theorem cdf_triangle (A P L : ℝ → ℝ)
    (hA : ∀ x, 0 ≤ A x ∧ A x ≤ 1) (hP : ∀ x, 0 ≤ P x ∧ P x ≤ 1)
    (hL : ∀ x, 0 ≤ L x ∧ L x ≤ 1) :
    cdfDistance A P ≤ cdfDistance L A + cdfDistance L P := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  calc
    |A x - P x| ≤ |A x - L x| + |L x - P x| := abs_sub_le _ _ _
    _ = |L x - A x| + |L x - P x| := by rw [abs_sub_comm (A x)]
    _ ≤ cdfDistance L A + cdfDistance L P :=
      add_le_add (cdf_point L A hL hA x) (cdf_point L P hL hP x)

theorem term_coefficients_nonneg (θ ρ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ i, 0 ≤ termRateCoefficient θ ρ i := by
  have hρ0 : 0 < 1 - ρ := by linarith
  have h1 : θ * ρ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hθ1 hρ.le
    nlinarith [hh]
  have h0 : θ * (1 - ρ) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hθ1 (by linarith : 0 ≤ 1 - ρ)
    nlinarith [hh]
  have hn1 : 0 ≤ 1 - θ * ρ := by linarith
  have hn0 : 0 ≤ 1 - θ * (1 - ρ) := by linarith
  intro i
  fin_cases i <;> simp [termRateCoefficient] <;> positivity

theorem last_lower_eventually (S : ExperimentSequence) (H : JointLaw)
    (C ε2 ε3 ξ2 ξ3 : ℝ) (hC : 0 < C) (hε2 : 0 < ε2) (hε3 : 0 < ε3)
    (hξ2 : 0 < ξ2) (hξ3 : 0 < ξ3)
    (hfinite : LowerFiniteFacts)
    (hy : ∀ i, |S.y1 i| ≤ C ∧ |S.y0 i| ≤ C)
    (hpop : ∀ t, Tendsto (fun q => cdfDistance (lawCDF H t)
      (empiricalCDF (rowOutcomes S t q))) atTop (𝓝 0)) :
    ∀ᶠ q in atTop, ∀ π,
      ε2 + ε3 ≤ |lowerLastIntegralTerm (S.design q) (rowOutcomes S true q)
        (rowOutcomes S false q) C π| →
      (ε2 / (8 * C ^ 2) - ξ2 ≤ cdfDistance (lawCDF H true)
          (sampledCDF S true q π) ∨
       ε3 / (8 * C ^ 2) - ξ3 ≤ cdfDistance (lawCDF H false)
          (sampledCDF S false q π)) := by
  let a2 : ℝ := ε2 / (8 * C ^ 2)
  let a3 : ℝ := ε3 / (8 * C ^ 2)
  have ha2 : 0 < a2 := by dsimp [a2]; positivity
  have ha3 : 0 < a3 := by dsimp [a3]; positivity
  have hshift : Tendsto (fun q : ℕ => q + 4) atTop atTop :=
    (tendsto_add_atTop_iff_nat 4).2 tendsto_id
  have hsmall2 : Tendsto (fun q => a2 / ((S.design q).N : ℝ)) atTop (𝓝 0) := by
    simpa only [S.size, Function.comp_def] using
      (tendsto_const_div_atTop_nhds_zero_nat a2).comp hshift
  have hsmall3 : Tendsto (fun q => a3 / ((S.design q).N : ℝ)) atTop (𝓝 0) := by
    simpa only [S.size, Function.comp_def] using
      (tendsto_const_div_atTop_nhds_zero_nat a3).comp hshift
  have hb2 : ∀ᶠ q in atTop,
      cdfDistance (lawCDF H true) (empiricalCDF (rowOutcomes S true q)) +
        a2 / ((S.design q).N : ℝ) < ξ2 := by
    have ht : Tendsto (fun q => cdfDistance (lawCDF H true)
        (empiricalCDF (rowOutcomes S true q)) + a2 / ((S.design q).N : ℝ))
        atTop (𝓝 0) := by simpa only [zero_add] using (hpop true).add hsmall2
    exact ht.eventually (gt_mem_nhds hξ2)
  have hb3 : ∀ᶠ q in atTop,
      cdfDistance (lawCDF H false) (empiricalCDF (rowOutcomes S false q)) +
        a3 / ((S.design q).N : ℝ) < ξ3 := by
    have ht : Tendsto (fun q => cdfDistance (lawCDF H false)
        (empiricalCDF (rowOutcomes S false q)) + a3 / ((S.design q).N : ℝ))
        atTop (𝓝 0) := by simpa only [zero_add] using (hpop false).add hsmall3
    exact ht.eventually (gt_mem_nhds hξ3)
  filter_upwards [hb2, hb3] with q hb2q hb3q
  intro π hlarge
  let d := S.design q
  have hN : 0 < (d.N : ℝ) := by
    exact_mod_cast (show 0 < d.N by have := d.population_min; omega)
  have hthreshold2 : ((d.N : ℝ) - 1) * ε2 / (8 * d.N * C ^ 2) =
      a2 - a2 / (d.N : ℝ) := by
    dsimp [a2]
    field_simp [ne_of_gt hC, ne_of_gt hN]
    <;> ring
  have hthreshold3 : ((d.N : ℝ) - 1) * ε3 / (8 * d.N * C ^ 2) =
      a3 - a3 / (d.N : ℝ) := by
    dsimp [a3]
    field_simp [ne_of_gt hC, ne_of_gt hN]
    <;> ring
  have hN1 : (1 : ℝ) < d.N := by
    exact_mod_cast (show 1 < d.N by have := d.population_min; omega)
  have hNnat : 0 < d.N := by
    exact_mod_cast hN
  have hm : 0 < d.m := by have := d.treatment_min; omega
  have hk : 0 < d.k := by have := d.control_min; omega
  have hyq : ∀ i, |rowOutcomes S true q i| ≤ C ∧ |rowOutcomes S false q i| ≤ C := by
    intro i
    simpa only [rowOutcomes, if_true, Bool.false_eq_true, if_false] using hy i.val
  have hcases := (hfinite d (rowOutcomes S true q) (rowOutcomes S false q) C hC.le hyq).2.2.2
    hC ε2 ε3 hε2 hε3 π hlarge
  have htri1 : cdfDistance (empiricalCDF
      (observedTreatment d (rowOutcomes S true q) π))
      (empiricalCDF (rowOutcomes S true q)) ≤
      cdfDistance (lawCDF H true)
        (empiricalCDF (observedTreatment d (rowOutcomes S true q) π)) +
      cdfDistance (lawCDF H true) (empiricalCDF (rowOutcomes S true q)) :=
    cdf_triangle _ _ _ (fun x => AronowAudit.P022.empirical_cdf_bounds hm _ x)
      (fun x => AronowAudit.P022.empirical_cdf_bounds hNnat _ x) (law_cdf_bounds H true)
  have htri0 : cdfDistance (empiricalCDF
      (observedControl d (rowOutcomes S false q) π))
      (empiricalCDF (rowOutcomes S false q)) ≤
      cdfDistance (lawCDF H false)
        (empiricalCDF (observedControl d (rowOutcomes S false q) π)) +
      cdfDistance (lawCDF H false) (empiricalCDF (rowOutcomes S false q)) :=
    cdf_triangle _ _ _ (fun x => AronowAudit.P022.empirical_cdf_bounds hk _ x)
      (fun x => AronowAudit.P022.empirical_cdf_bounds hNnat _ x) (law_cdf_bounds H false)
  rcases hcases with hcase2 | hcase3
  · rw [hthreshold2] at hcase2
    have hgoal : a2 - ξ2 ≤ cdfDistance (lawCDF H true)
        (empiricalCDF (observedTreatment d (rowOutcomes S true q) π)) := by
      have hpopq : cdfDistance (lawCDF H true)
          (empiricalCDF (rowOutcomes S true q)) + a2 / (d.N : ℝ) < ξ2 := by
        simpa only [d] using hb2q
      linarith
    left
    simpa only [a2, sampledCDF, if_pos] using hgoal
  · rw [hthreshold3] at hcase3
    have hgoal : a3 - ξ3 ≤ cdfDistance (lawCDF H false)
        (empiricalCDF (observedControl d (rowOutcomes S false q) π)) := by
      have hpopq : cdfDistance (lawCDF H false)
          (empiricalCDF (rowOutcomes S false q)) + a3 / (d.N : ℝ) < ξ3 := by
        simpa only [d] using hb3q
      linarith
    right
    simpa only [a3, sampledCDF, if_neg (by decide : ¬ false = true)] using hgoal

theorem proof_core : SAP.P022.WH.W1.T6_L7 := by
  intro hRates hFinite
  intro S H θ ρ C hCond hC hy hLemma
  intro ε1 ε2 ε3 ξ2 ξ3 ν hε1 hε2 hε3 hξ2pos hξ2lt hξ3pos hξ3lt hν hsum
  let η2 : ℝ := ε2 / (8 * C ^ 2) - ξ2
  let η3 : ℝ := ε3 / (8 * C ^ 2) - ξ3
  have hη2 : 0 < η2 := by dsimp [η2]; linarith
  have hη3 : 0 < η3 := by dsimp [η3]; linarith
  have hRatesAt := hRates.2.2 S H θ ρ hCond hLemma
  rcases hCond with ⟨hθ, hθ1, hρ, hρ1, _⟩
  have hlastEventually := last_lower_eventually S H C ε2 ε3 ξ2 ξ3 hC hε2 hε3
    hξ2pos hξ3pos hFinite hy hLemma.1
  let F2 : (q : ℕ) → Assignment (S.design q) → Prop := fun q π =>
    η2 ≤ cdfDistance (lawCDF H true) (sampledCDF S true q π)
  let F3 : (q : ℕ) → Assignment (S.design q) → Prop := fun q π =>
    η3 ≤ cdfDistance (lawCDF H false) (sampledCDF S false q π)
  let Fr : Fin 2 → (q : ℕ) → Assignment (S.design q) → Prop :=
    fun j => if j = 0 then F2 else F3
  let rr : Fin 2 → ℝ := fun j => if j = 0 then
    marginalTailRate θ ρ true η2 else marginalTailRate θ ρ false η3
  have hrr : ∀ j, 0 ≤ rr j := by
    intro j
    dsimp [rr]
    split_ifs with hj
    · exact marginal_rate_nonneg θ ρ hθ hθ1 hρ hρ1 true η2
    · exact marginal_rate_nonneg θ ρ hθ hθ1 hρ hρ1 false η3
  have hFr : ∀ j, scaledProbabilityLimsup S (Fr j) ≤ ENNReal.ofReal (rr j) := by
    intro j
    fin_cases j
    · simpa [Fr, F2, rr] using hRatesAt true η2 hη2
    · simpa [Fr, F3, rr] using hRatesAt false η3 hη3
  have hlast : scaledProbabilityLimsup S (fun q π => ε2 + ε3 ≤
      |lowerLastIntegralTerm (S.design q) (rowOutcomes S true q)
        (rowOutcomes S false q) C π|) ≤
      ENNReal.ofReal (marginalTailRate θ ρ true η2 + marginalTailRate θ ρ false η3) := by
    have hinc : ∀ᶠ q in atTop, ∀ π,
        ε2 + ε3 ≤ |lowerLastIntegralTerm (S.design q) (rowOutcomes S true q)
          (rowOutcomes S false q) C π| → ∃ j : Fin 2, Fr j q π := by
      filter_upwards [hlastEventually] with q hq
      intro π hp
      rcases hq π hp with h2 | h3
      · exact ⟨0, by simpa [Fr, F2, η2] using h2⟩
      · exact ⟨1, by simpa [Fr, F3, η3] using h3⟩
    have hbound := scaled_union S _ Fr rr hrr hFr hinc
    simpa [rr, Fin.sum_univ_succ] using hbound
  refine ⟨hlast, ?_⟩
  intro hEarlier
  let E : (q : ℕ) → Assignment (S.design q) → Prop := fun q π =>
    ε1 + (ε2 + ε3) ≤ rowSize S q *
      |rowEstimate S .L q π - rowBound S .L q|
  let F : Fin 7 → (q : ℕ) → Assignment (S.design q) → Prop := fun j q π =>
    lowerAllocation ν ε2 ε3 j ≤
      |lowerSevenTerms (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) C π j|
  let rlast : ℝ := marginalTailRate θ ρ true η2 + marginalTailRate θ ρ false η3
  let r : Fin 7 → ℝ := fun j => if hj : j.val < 6 then
      C ^ 4 * sixTermCoefficient θ ρ ν ⟨j.val, hj⟩ else rlast
  have hcoeff := term_coefficients_nonneg θ ρ hθ hθ1 hρ hρ1
  have hterm : ∀ i : Fin 8, 0 ≤ termRateCoefficient θ ρ i / (ν i) ^ 2 := by
    intro i
    exact div_nonneg (hcoeff i) (sq_nonneg (ν i))
  have hsix : ∀ j : Fin 6, 0 ≤ sixTermCoefficient θ ρ ν j := by
    intro j
    fin_cases j
    · simpa [sixTermCoefficient] using hterm (0 : Fin 8)
    · simpa [sixTermCoefficient] using hterm (1 : Fin 8)
    · simpa [sixTermCoefficient] using hterm (2 : Fin 8)
    · simpa [sixTermCoefficient] using hterm (3 : Fin 8)
    · simpa [sixTermCoefficient] using add_nonneg (hterm (4 : Fin 8)) (hterm (5 : Fin 8))
    · simpa [sixTermCoefficient] using add_nonneg (hterm (6 : Fin 8)) (hterm (7 : Fin 8))
  have hr : ∀ j, 0 ≤ r j := by
    intro j
    dsimp [r]
    split_ifs with hj
    · exact mul_nonneg (pow_nonneg hC.le 4) (hsix ⟨j.val, hj⟩)
    · dsimp [rlast]
      exact add_nonneg
        (marginal_rate_nonneg θ ρ hθ hθ1 hρ hρ1 true η2)
        (marginal_rate_nonneg θ ρ hθ hθ1 hρ hρ1 false η3)
  have hF : ∀ j, scaledProbabilityLimsup S (F j) ≤ ENNReal.ofReal (r j) := by
    intro j
    fin_cases j
    · simpa [F, lowerAllocation, lowerSevenTerms, r, correctedAllocation,
        sixTermCoefficient] using hEarlier ⟨0, by omega⟩
    · simpa [F, lowerAllocation, lowerSevenTerms, r, correctedAllocation,
        sixTermCoefficient] using hEarlier ⟨1, by omega⟩
    · simpa [F, lowerAllocation, lowerSevenTerms, r, correctedAllocation,
        sixTermCoefficient] using hEarlier ⟨2, by omega⟩
    · simpa [F, lowerAllocation, lowerSevenTerms, r, correctedAllocation,
        sixTermCoefficient] using hEarlier ⟨3, by omega⟩
    · simpa [F, lowerAllocation, lowerSevenTerms, r, correctedAllocation,
        sixTermCoefficient] using hEarlier ⟨4, by omega⟩
    · simpa [F, lowerAllocation, lowerSevenTerms, r, correctedAllocation,
        sixTermCoefficient] using hEarlier ⟨5, by omega⟩
    · simpa [F, lowerAllocation, lowerSevenTerms, r, rlast, η2, η3] using hlast
  have hbudget : (∑ j : Fin 7, lowerAllocation ν ε2 ε3 j) ≤ ε1 + (ε2 + ε3) := by
    have hνsum := hsum
    simp [Fin.sum_univ_succ] at hνsum
    have halloc : (∑ j : Fin 7, lowerAllocation ν ε2 ε3 j) = ε1 + (ε2 + ε3) := by
      simp [Fin.sum_univ_succ, lowerAllocation, correctedAllocation]
      linarith
    exact halloc.le
  have hinc : ∀ᶠ q in atTop, ∀ π, E q π → ∃ j : Fin 7, F j q π := by
    apply Filter.Eventually.of_forall
    intro q π hp
    let d := S.design q
    have hyq : ∀ i, |rowOutcomes S true q i| ≤ C ∧ |rowOutcomes S false q i| ≤ C := by
      intro i
      simpa only [rowOutcomes, if_true, Bool.false_eq_true, if_false] using hy i.val
    have hfiniteBudget := (hFinite d (rowOutcomes S true q) (rowOutcomes S false q) C
      hC.le hyq).2.1 (lowerAllocation ν ε2 ε3) (ε1 + (ε2 + ε3))
      (by
        intro j
        fin_cases j
        · exact hν 0
        · exact hν 1
        · exact hν 2
        · exact hν 3
        · exact add_pos (hν 4) (hν 5)
        · exact add_pos (hν 6) (hν 7)
        · exact add_pos hε2 hε3)
      hbudget
    have hp' : ε1 + (ε2 + ε3) ≤ (d.N : ℝ) *
        |estimatedVariance d (rowOutcomes S true q) (rowOutcomes S false q) .L π -
          populationBound d (rowOutcomes S true q) (rowOutcomes S false q) .L| := by
      simpa [E, rowSize, rowEstimate, rowBound, d] using hp
    exact hfiniteBudget.1 π hp'
  have hbound := scaled_union S E F r hr hF hinc
  have hsumr : (∑ j : Fin 7, r j) =
      C ^ 4 * coefficientSum θ ρ ν + rlast := by
    simp [r, coefficientSum, sixTermCoefficient, Fin.sum_univ_succ]
    <;> ring
  rw [hsumr] at hbound
  simpa [rlast, η2, η3, add_assoc] using hbound

end
end SAP.P022.WH.W1.P.T6_L7

open SAP.P022 Filter MeasureTheory SAP.P022.WH.W1.P.T6_L7
open scoped BigOperators Topology ENNReal NNReal

theorem SAP.P022.WH.W1.T6_L7_proof : SAP.P022.WH.W1.T6_L7 := by
  exact SAP.P022.WH.W1.P.T6_L7.proof_core
