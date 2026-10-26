import AronowAudit.P004.Wave1.ObservationalCoverage.O1
import AronowAudit.P004.Wave1.ObservationalCoverage.O3
import AronowAudit.P004.Wave1.ObservationalCoverage.O5
import AronowAudit.P004.Wave1.ObservationalCoverage.O12
import AronowAudit.P004.Wave1.LinePopulation.N4
import AronowAudit.P004.Wave1.LinePopulation.N5
import AronowAudit.P004.Wave1.LinePopulation.N6
import AronowAudit.P004.Wave1.LinePopulation.N7
import AronowAudit.P004.Wave1.FiniteConditioning.FC7

/-! P004-T3: the actual fitted-IPW variance and the printed SAH counterexample.

A fourth-moment estimate upgrades
the fitted-IPW approximation to mean square; this proves convergence of its actual
design variance, including assignments on which clipping is active.
-/

namespace AronowAudit.P004.Wave1

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open AronowAudit.P004.Wave1.ObservationalCoverage
open scoped BigOperators Classical

/-- An independent fair coordinate has zero expectation against any function of
the other coordinates. Zero coefficients also permit nonfair coordinates. -/
theorem T3_odd_expect {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (i : Fin N) (a : ℝ)
    (ha : a = 0 ∨ p i = 1 / 2) (f : Assignment N → ℝ)
    (hf : ∀ z b, f (Function.update z i b) = f z) :
    expect p (fun z => a * (bit (z i) - 1 / 2) * f z) = 0 := by
  rcases ha with rfl | hi
  · simp only [zero_mul, expect_const]
  have hid : (fun z => a * (bit (z i) - 1 / 2) * f z) =
      fun z => a * ((bit (z i))^1 * f z - (1 / 2) * f z) := by
    funext z
    ring
  rw [hid, expect_mul, expect_sub, expect_mul,
    bernoulli_positive_power p f i 1 (by norm_num) hp, hi]
  simp only [hf, sub_self, mul_zero]

/-- Second and fourth moments of a finite linear combination of independent fair
centered bits. This is proved directly for the finite product design. -/
theorem T3_centered_moments {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (a : Fin N → ℝ)
    (ha : ∀ i, a i = 0 ∨ p i = 1 / 2) (s : Finset (Fin N)) :
    expect p (fun z => (∑ i ∈ s, a i * (bit (z i) - 1 / 2))^2) =
        (∑ i ∈ s, (a i)^2) / 4 ∧
      expect p (fun z => (∑ i ∈ s, a i * (bit (z i) - 1 / 2))^4) ≤
        3 / 16 * (∑ i ∈ s, (a i)^2)^2 := by
  induction s using Finset.induction_on with
  | empty => norm_num [expect_const]
  | @insert i s hi ih =>
    let U : Assignment N → ℝ := fun z => ∑ j ∈ s, a j * (bit (z j) - 1 / 2)
    let X : Assignment N → ℝ := fun z => a i * (bit (z i) - 1 / 2)
    let Q : ℝ := ∑ j ∈ s, (a j)^2
    have hU (z : Assignment N) (b : Bool) : U (Function.update z i b) = U z := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
    have hodd (k : ℕ) : expect p (fun z => X z * (U z)^k) = 0 :=
      T3_odd_expect p hp i (a i) (ha i) _ (fun z b => by rw [hU])
    have hX2 (z : Assignment N) : (X z)^2 = (a i)^2 / 4 := by
      dsimp only [X]
      cases h : z i <;> simp only [h, bit, Bool.false_eq_true, if_false, if_true] <;> ring
    have hX3 (z : Assignment N) : (X z)^3 = (a i)^2 / 4 * X z := by
      calc
        (X z)^3 = (X z)^2 * X z := by ring
        _ = _ := by rw [hX2]
    have hX4 (z : Assignment N) : (X z)^4 = (a i)^4 / 16 := by
      calc
        (X z)^4 = ((X z)^2)^2 := by ring
        _ = _ := by rw [hX2]; ring
    have he2 : expect p (fun z => (U z + X z)^2) =
        expect p (fun z => (U z)^2) + (a i)^2 / 4 := by
      have he : (fun z => (U z + X z)^2) =
          fun z => (U z)^2 + 2 * (X z * (U z)^1) + (a i)^2 / 4 := by
        funext z
        rw [← hX2 z]
        ring
      rw [he, expect_add, expect_add, expect_mul, hodd, expect_const]
      ring
    have he4 : expect p (fun z => (U z + X z)^4) =
        expect p (fun z => (U z)^4) +
          (6 * (a i)^2 / 4) * expect p (fun z => (U z)^2) + (a i)^4 / 16 := by
      have he : (fun z => (U z + X z)^4) = fun z =>
          (U z)^4 + 4 * (X z * (U z)^3) +
            (6 * (a i)^2 / 4) * (U z)^2 +
            (4 * (a i)^2 / 4) * (X z * (U z)^1) + (a i)^4 / 16 := by
        funext z
        calc
          (U z + X z)^4 = (U z)^4 + 4 * (X z * (U z)^3) +
              6 * (X z)^2 * (U z)^2 + 4 * (X z)^3 * U z + (X z)^4 := by ring
          _ = _ := by rw [hX2, hX3, hX4]; ring
      rw [he, expect_add, expect_add, expect_add, expect_add,
        expect_mul, expect_mul, expect_mul, hodd, hodd, expect_const]
      ring
    have ih2 : expect p (fun z => (U z)^2) = Q / 4 := ih.1
    have ih4 : expect p (fun z => (U z)^4) ≤ 3 / 16 * Q^2 := ih.2
    have heq (z : Assignment N) :
        (∑ j ∈ insert i s, a j * (bit (z j) - 1 / 2)) = U z + X z := by
      rw [Finset.sum_insert hi]
      exact add_comm _ _
    simp only [heq, Finset.sum_insert hi]
    constructor
    · rw [he2, ih2]
      dsimp only [Q]
      ring
    · rw [he4, ih2]
      change expect p (fun z => (U z)^4) +
        (6 * (a i)^2 / 4) * (Q / 4) + (a i)^4 / 16 ≤ 3 / 16 * ((a i)^2 + Q)^2
      nlinarith only [ih4, sq_nonneg ((a i)^2)]

theorem T3_S_centered (N : ℕ) (z : Assignment N) :
    SAct N z - sAct N / 2 = ∑ i, activeSign N i * (bit (z i) - 1 / 2) := by
  simp only [SAct, sAct, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

theorem T3_K_centered (N : ℕ) (z : Assignment N) :
    KAct N z - nH N / 2 =
      ∑ i, (if activeGroup N i then (1 : ℝ) else 0) * (bit (z i) - 1 / 2) := by
  rw [oc_nH_sum, Finset.sum_div]
  unfold KAct
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : activeGroup N i <;> simp [hi]

theorem T3_S_fourth (N : ℕ) :
    expect (propensities (activeO N) activeTheta)
      (fun z => (SAct N z - sAct N / 2)^4) ≤ 3 / 16 * (nH N)^2 := by
  have ha (i : Fin N) : activeSign N i = 0 ∨
      propensities (activeO N) activeTheta i = 1 / 2 := by
    by_cases hi : activeGroup N i
    · exact Or.inr (by rw [o4_proof N]; exact if_pos hi)
    · exact Or.inl (oc_sign_eq_zero N i hi)
  simpa only [← T3_S_centered, sum_activeSign_sq] using
    (T3_centered_moments _ (oc_admissible N) (activeSign N) ha Finset.univ).2

theorem T3_K_fourth (N : ℕ) :
    expect (propensities (activeO N) activeTheta)
      (fun z => (KAct N z - nH N / 2)^4) ≤ 3 / 16 * (nH N)^2 := by
  let a : Fin N → ℝ := fun i => if activeGroup N i then 1 else 0
  have ha (i : Fin N) : a i = 0 ∨ propensities (activeO N) activeTheta i = 1 / 2 := by
    by_cases hi : activeGroup N i
    · exact Or.inr (by rw [o4_proof N]; exact if_pos hi)
    · exact Or.inl (by simp [a, hi])
  have hs : (∑ i, (a i)^2) = nH N := by
    rw [oc_nH_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : activeGroup N i <;> simp [a, hi]
  have hm := (T3_centered_moments _ (oc_admissible N) a ha Finset.univ).2
  rw [hs] at hm
  simpa only [a, ← T3_K_centered] using hm

/-- A mixed fourth moment controls the fitted-denominator error without any
conditional sampling or exchange of probability limits and variances. -/
theorem T3_mixed_moment (N : ℕ) (hN : 4 ≤ N) :
    expect (propensities (activeO N) activeTheta)
      (fun z => (SAct N z)^2 * (KAct N z - nH N / 2)^2) ≤ (nH N)^2 := by
  have hpoint (z : Assignment N) :
      (SAct N z)^2 * (KAct N z - nH N / 2)^2 ≤
        (SAct N z - sAct N / 2)^4 + (KAct N z - nH N / 2)^4 +
          (2 * (sAct N / 2)^2) * (KAct N z - nH N / 2)^2 := by
    nlinarith only [sq_nonneg ((SAct N z - sAct N) * (KAct N z - nH N / 2)),
      sq_nonneg ((SAct N z - sAct N / 2)^2 - (KAct N z - nH N / 2)^2)]
  have hm := expect_mono _ (oc_admissible N) _ _ hpoint
  rw [expect_add, expect_add, expect_mul, oc_K_centered_second] at hm
  have hn1 : 1 ≤ nH N := by
    have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
    linarith [nH_ge_quarter N]
  have hs := oc_sAct_sq_le N
  have hn2 : nH N ≤ (nH N)^2 := by nlinarith
  have hsc : (sAct N)^2 * nH N ≤ nH N :=
    mul_le_of_le_one_left (oc_nH_nonneg N) hs
  nlinarith only [hm, T3_S_fourth N, T3_K_fourth N, hsc, hn2]

/-- The bound is pointwise and retains the clipped fitted propensity. -/
theorem T3_error_pointwise (N : ℕ) (hN : 0 < N) (z : Assignment N) :
    (SAct N z / (N * pHatH N z) - 2 * SAct N z / N)^2 ≤
      (1600 / ((N : ℝ)^2 * (nH N)^2)) *
        ((SAct N z)^2 * (KAct N z - nH N / 2)^2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hn := oc_nH_pos N hN
  have hph := (oc_clip_bounds (KAct N z / nH N)).1
  change (1 : ℝ) / 20 ≤ pHatH N z at hph
  have hph0 : 0 < pHatH N z := by linarith
  have hclip : (1 - 2 * pHatH N z)^2 ≤ (1 - 2 * (KAct N z / nH N))^2 := by
    have hc := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr
      (oc_clip_contract (KAct N z / nH N))
    simpa only [pHatH, sq_abs] using hc
  have hid : 1 - 2 * (KAct N z / nH N) =
      -2 * (KAct N z - nH N / 2) / nH N := by
    field_simp [hn.ne']
    <;> ring
  have hclip2 : (1 - 2 * pHatH N z)^2 ≤
      4 * (KAct N z - nH N / 2)^2 / (nH N)^2 := by
    convert hclip using 1 <;> norm_num [hid, div_pow, mul_pow]
  have hinv : 1 / pHatH N z ≤ 20 := (div_le_iff₀ hph0).mpr (by linarith)
  have hinv0 : 0 ≤ 1 / pHatH N z := by positivity
  have hinv2 : (1 / pHatH N z)^2 ≤ 400 := by nlinarith
  calc
    (SAct N z / (N * pHatH N z) - 2 * SAct N z / N)^2 =
        ((SAct N z)^2 / (N : ℝ)^2) *
          ((1 - 2 * pHatH N z)^2 * (1 / pHatH N z)^2) := by
      field_simp [hNr.ne', hph0.ne']
      <;> ring
    _ ≤ ((SAct N z)^2 / (N : ℝ)^2) *
        ((4 * (KAct N z - nH N / 2)^2 / (nH N)^2) * 400) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hclip2 hinv2 (sq_nonneg _) (by positivity)
    _ = _ := by
      field_simp [hNr.ne', hn.ne']
      <;> ring

theorem T3_error_second (N : ℕ) (hN : 4 ≤ N) :
    expect (propensities (activeO N) activeTheta)
      (fun z => (SAct N z / (N * pHatH N z) - 2 * SAct N z / N)^2) ≤
        1600 / (N : ℝ)^2 := by
  have hNp : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hn := oc_nH_pos N hNp
  calc
    _ ≤ (1600 / ((N : ℝ)^2 * (nH N)^2)) *
        expect (propensities (activeO N) activeTheta)
          (fun z => (SAct N z)^2 * (KAct N z - nH N / 2)^2) := by
      simpa only [expect_mul] using
        expect_mono _ (oc_admissible N) _ _ (T3_error_pointwise N hNp)
    _ ≤ (1600 / ((N : ℝ)^2 * (nH N)^2)) * (nH N)^2 :=
      mul_le_mul_of_nonneg_left (T3_mixed_moment N hN) (by positivity)
    _ = _ := by field_simp [hNr.ne', hn.ne']

theorem T3_scaled_error_second :
    Tendsto (fun N => expect (propensities (activeO N) activeTheta)
      (fun z => (Real.sqrt N *
        (SAct N z / (N * pHatH N z) - 2 * SAct N z / N))^2))
      atTop (nhds (0 : ℝ)) := by
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun N => oc_expect_nonneg N _ (fun z => sq_nonneg _))
    ?_ (tendsto_const_div_atTop_nhds_zero_nat (1600 : ℝ))
  filter_upwards [eventually_ge_atTop 4] with N hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), expect_mul]
  calc
    _ ≤ (N : ℝ) * (1600 / (N : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (T3_error_second N hN) hNr.le
    _ = 1600 / (N : ℝ) := by field_simp [hNr.ne']

theorem T3_variance_scale {N : ℕ} (p : Fin N → ℝ) (U : Assignment N → ℝ) (c : ℝ) :
    variance p (fun z => c * U z) = c^2 * variance p U := by
  have he : (fun z => c * U z * (c * U z)) = fun z => c^2 * (U z * U z) := by
    funext z
    ring
  unfold variance cov
  rw [he, expect_mul, expect_mul]
  ring

theorem T3_scaled_linear_variance (N : ℕ) (hN : 0 < N) :
    variance (propensities (activeO N) activeTheta)
      (fun z => Real.sqrt N * (2 * SAct N z / N)) = nH N / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hv : variance (propensities (activeO N) activeTheta) (SAct N) = nH N / 4 := by
    unfold variance cov
    simp only [← pow_two, oc_S_second, oc_S_mean]
    ring
  have he : (fun z => Real.sqrt N * (2 * SAct N z / N)) =
      fun z => (2 * Real.sqrt N / N) * SAct N z := by funext z; ring
  rw [he, T3_variance_scale, hv]
  rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  field_simp [hNr.ne']
  <;> ring

theorem T3_scaled_linear_second (N : ℕ) (hN : 0 < N) :
    expect (propensities (activeO N) activeTheta)
      (fun z => (Real.sqrt N * (2 * SAct N z / N))^2) ≤ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have he : (fun z => (Real.sqrt N * (2 * SAct N z / N))^2) =
      fun z => (4 / N) * (SAct N z)^2 := by
    funext z
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    field_simp [hNr.ne']
    <;> ring
  rw [he, expect_mul, oc_S_second]
  have hn := oc_nH_le N
  have hs := oc_sAct_sq_le N
  have hid : 4 / (N : ℝ) * (nH N / 4 + (sAct N / 2)^2) =
      (nH N + (sAct N)^2) / N := by ring
  rw [hid]
  apply (div_le_iff₀ hNr).mpr
  nlinarith

/-- Mean-square perturbations control the actual finite-design variance. -/
theorem T3_variance_perturbation {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (V D : Assignment N → ℝ)
    (hV : l2Norm p V ≤ 2) :
    |variance p (fun z => V z + D z) - variance p V| ≤
      expect p (fun z => (D z)^2) + 4 * Real.sqrt (expect p (fun z => (D z)^2)) := by
  obtain ⟨h0, _, _, _, _, _, _, _, hcov, _⟩ := FiniteConditioning.fc7_proof p hp
  have hc : |cov p V D| ≤ 2 * l2Norm p D :=
    (hcov V D).trans (mul_le_mul_of_nonneg_right hV (h0 D))
  have hvD : |variance p D| ≤ expect p (fun z => (D z)^2) := by
    rw [abs_of_nonneg (variance_nonneg p hp D)]
    exact variance_le_second p D
  have he : variance p (fun z => V z + D z) =
      variance p V + 2 * cov p V D + variance p D := by
    have hex : (fun z => (V z + D z) * (V z + D z)) =
        fun z => V z * V z + 2 * (V z * D z) + D z * D z := by
      funext z
      ring
    unfold variance cov
    rw [hex, expect_add, expect_add, expect_mul, expect_add]
    ring
  calc
    |variance p (fun z => V z + D z) - variance p V| =
        |2 * cov p V D + variance p D| := by rw [he]; congr 1; ring
    _ ≤ |2 * cov p V D| + |variance p D| := abs_add_le _ _
    _ ≤ 2 * (2 * l2Norm p D) + expect p (fun z => (D z)^2) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact add_le_add (mul_le_mul_of_nonneg_left hc (by norm_num)) hvD
    _ = _ := by unfold l2Norm; ring

/-- The variance in the denominator is that of the actual clipped fitted IPW,
not the population projection or a probability-limit substitute. -/
theorem T3_actual_variance_limit :
    Tendsto (fun N : ℕ => (N : ℝ) * variance (propensities (activeO N) activeTheta)
      (fittedIPW (circleAverage (activePopulation N) 0) (activeO N) (activeMLE N)))
      atTop (nhds (1 / 4 : ℝ)) := by
  let p : ∀ N, Fin N → ℝ := fun N => propensities (activeO N) activeTheta
  let V : ∀ N, Assignment N → ℝ := fun N z => Real.sqrt N * (2 * SAct N z / N)
  let D : ∀ N, Assignment N → ℝ := fun N z => Real.sqrt N *
    (SAct N z / (N * pHatH N z) - 2 * SAct N z / N)
  let E : ℕ → ℝ := fun N => expect (p N) (fun z => (D N z)^2)
  have hE : Tendsto E atTop (nhds (0 : ℝ)) := T3_scaled_error_second
  have hroot : Tendsto (fun N => Real.sqrt (E N)) atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hE
  have hupper : Tendsto (fun N => E N + 4 * Real.sqrt (E N)) atTop (nhds (0 : ℝ)) := by
    simpa using hE.add (tendsto_const_nhds.mul hroot)
  have herr : Tendsto (fun N =>
      variance (p N) (fun z => V N z + D N z) - variance (p N) (V N))
      atTop (nhds (0 : ℝ)) := by
    apply squeeze_zero_norm' _ hupper
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [Real.norm_eq_abs]
    apply T3_variance_perturbation _ (oc_admissible N)
    change Real.sqrt (expect (p N) (fun z => (V N z)^2)) ≤ 2
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (T3_scaled_linear_second N hN).trans (by norm_num)
  have hlin : Tendsto (fun N => variance (p N) (V N)) atTop (nhds (1 / 4 : ℝ)) := by
    apply oc_nH_ratio_tendsto.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (T3_scaled_linear_variance N hN).symm
  have hsum : Tendsto (fun N => variance (p N) (fun z => V N z + D N z))
      atTop (nhds (1 / 4 : ℝ)) := by
    simpa only [sub_add_cancel, zero_add] using herr.add hlin
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hR : circleAverage (activePopulation N) 0 = activeTable N :=
    LinePopulation.n3_proof (activeTable N)
  have he : (fun z => V N z + D N z) =
      fun z => Real.sqrt N * fittedIPW (activeTable N) (activeO N) (activeMLE N) z := by
    funext z
    rw [o6_proof.1 N hN]
    dsimp only [V, D]
    ring
  rw [hR, he, T3_variance_scale, Real.sq_sqrt (Nat.cast_nonneg N)]

theorem T3_neighborhoods (N : ℕ) :
    spatialNeighborhoods activePopulation 0 N = fun i => {i} := by
  funext i
  exact LinePopulation.line_zero_ball (activeTable N) i

theorem T3_ratio :
    InProb (fun N => propensities (activeO N) activeTheta) (fun N z =>
      let R := circleAverage (activePopulation N) 0
      let phat := propensities (activeO N) (activeMLE N z)
      let g := fun i a => dot (activeO N i) (fittedBeta phat R (activeO N) a z)
      printedSAH phat R (fun i => {i}) g z /
        variance (propensities (activeO N) activeTheta)
          (fittedIPW R (activeO N) (activeMLE N)) - 8/25) := by
  let p : ∀ N, Fin N → ℝ := fun N => propensities (activeO N) activeTheta
  let A : ∀ N, Assignment N → ℝ := fun N z => (N : ℝ) *
    printedSAH (propensities (activeO N) (activeMLE N z))
      (circleAverage (activePopulation N) 0) (spatialNeighborhoods activePopulation 0 N)
      (fun i a => dot (activeO N i)
        (fittedBeta (propensities (activeO N) (activeMLE N z))
          (circleAverage (activePopulation N) 0) (activeO N) a z)) z
  let B : ℕ → ℝ := fun N => (N : ℝ) * variance (p N)
    (fittedIPW (circleAverage (activePopulation N) 0) (activeO N) (activeMLE N))
  let U : Fin 2 → ∀ N, Assignment N → ℝ := ![A, fun N _ => B N]
  let c : Fin 2 → ℝ := ![2/25, 1/4]
  have hU : ∀ k, InProb p (fun N z => U k N z - c k) := by
    intro k
    fin_cases k
    · change InProb p (fun N z => A N z - 2/25)
      exact o12_proof
    · change InProb p (fun N _ => B N - 1/4)
      apply (dl4_proof p oc_admissible).2.2
      simpa using T3_actual_variance_limit.sub (tendsto_const_nhds (x := (1/4 : ℝ)))
  have hF : ContinuousAt (fun x : Fin 2 → ℝ => x 0 / x 1) c := by
    apply (continuous_apply 0).continuousAt.div (continuous_apply 1).continuousAt
    norm_num [c]
  have hr : InProb p (fun N z => A N z / B N - 8/25) := by
    have hm := dl9_proof p oc_admissible U c (fun x => x 0 / x 1) hF hU
    have hc : c 0 / c 1 = (8/25 : ℝ) := by norm_num [c]
    change InProb p (fun N z => A N z / B N - c 0 / c 1) at hm
    rw [hc] at hm
    exact hm
  apply oc_inProb_congr (U := fun N z => A N z / B N - 8/25) _ hr
  filter_upwards [eventually_gt_atTop 0] with N hN
  intro z
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  dsimp only [A, B, p]
  rw [T3_neighborhoods, mul_div_mul_left _ _ hNr.ne']

theorem T3_interior : activeTheta ∈ interior activeParameterSet := by
  have hbox : activeParameterSet =
      Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-Real.log 19) (Real.log 19)) := by
    ext θ
    simp only [activeParameterSet, Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Icc]
  rw [hbox, interior_pi_set Set.finite_univ]
  simp only [Set.mem_univ_pi, interior_Icc, Set.mem_Ioo]
  have h19 : 0 < Real.log 19 := Real.log_pos (by norm_num : (1 : ℝ) < 19)
  have h9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 9)
  have hlt : Real.log 9 < Real.log 19 :=
    Real.log_lt_log (by norm_num : (0 : ℝ) < 9) (by norm_num : (9 : ℝ) < 19)
  intro j
  fin_cases j
  · change -Real.log 19 < (0 : ℝ) ∧ (0 : ℝ) < Real.log 19
    constructor <;> linarith
  · change -Real.log 19 < -Real.log 9 ∧ -Real.log 9 < Real.log 19
    constructor <;> linarith

theorem T3_spatial : SpatialLocalConditions activePopulation := by
  exact LinePopulation.spatialLocal_of LinePopulation.n5_proof LinePopulation.n6_proof
    LinePopulation.n7_proof activeTable 1 0 zero_le_one le_rfl o1_proof.1 o1_proof.2.1

theorem T3_singleton_homophily {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) : 0 ≤ homophilyQ p R (fun i => {i}) g := by
  simp only [homophilyQ, Finset.sum_singleton]
  exact div_nonneg (Finset.sum_nonneg (fun i _ => mul_self_nonneg _)) (Nat.cast_nonneg N)

theorem T3_overlap : Overlap (fun N => propensities (activeO N) activeTheta) := by
  refine ⟨1/20, by norm_num, by norm_num, ?_⟩
  intro N i
  change 1/20 < propensities (activeO N) activeTheta i ∧
    propensities (activeO N) activeTheta i < 1 - 1/20
  rw [o4_proof N]
  dsimp only
  split_ifs <;> norm_num

/-- P004-T3: the printed SAH counterexample with the constrained MLE and the
fitted-IPW design variance. -/
theorem observational_sah_counterexample_proof :
    ∃ θhat : ∀ N, Assignment N → Fin 2 → ℝ,
      LogisticConditions activeO activeTheta activeParameterSet θhat ∧
      activeTheta ∈ interior activeParameterSet ∧ SpatialLocalConditions activePopulation ∧
      (∀ N, 0 ≤ homophilyQ (propensities (activeO N) activeTheta) (circleAverage (activePopulation N) 0)
        (fun i => {i}) (printedFits (propensities (activeO N) activeTheta) (circleAverage (activePopulation N) 0) (activeO N))) ∧
      Overlap (fun N => propensities (activeO N) activeTheta) ∧
      (∀ N : ℕ, 0 < N → WellDefined (activePopulation N) 0) ∧
      Nondegenerate (fun N => variance (propensities (activeO N) activeTheta)
        (augmented (propensities (activeO N) activeTheta) (circleAverage (activePopulation N) 0)
          (printedFits (propensities (activeO N) activeTheta) (circleAverage (activePopulation N) 0) (activeO N)))) ∧
      InProb (fun N => propensities (activeO N) activeTheta) (fun N z =>
        let R := circleAverage (activePopulation N) 0
        let phat := propensities (activeO N) (θhat N z)
        let g := fun i a => dot (activeO N i) (fittedBeta phat R (activeO N) a z)
        printedSAH phat R (fun i => {i}) g z /
          variance (propensities (activeO N) activeTheta) (fittedIPW R (activeO N) (θhat N)) - 8/25) := by
  refine ⟨activeMLE, o3_proof, T3_interior, T3_spatial, ?_, T3_overlap, ?_, o5_proof,
    T3_ratio⟩
  · intro N
    exact T3_singleton_homophily _ _ _
  · intro N _
    exact LinePopulation.n4_proof (activeTable N) 0 le_rfl

end
end AronowAudit.P004.Wave1
