import SAP.P031.Defs.WholeW2
import SAP.P031.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P031.WH.W2

open scoped BigOperators Topology
open Filter Finset

noncomputable section

theorem donorHrW2 {ι : Type} [Fintype ι] [DecidableEq ι] (s : Finset ι) (Y : ι → ℝ) :
    AronowAudit.P031.hr s Y = hr s Y := rfl

theorem donorHc2W2 {ι : Type} [Fintype ι] [DecidableEq ι] (s : Finset ι) (Y : ι → ℝ) :
    AronowAudit.P031.hc2 s Y = hc2 s Y := rfl

theorem donorHc3W2 {ι : Type} [Fintype ι] [DecidableEq ι] (s : Finset ι) (Y : ι → ℝ) :
    AronowAudit.P031.hc3 s Y = hc3 s Y := rfl

theorem populationSizesW2 (Q : Population) :
    2 ≤ Q.M ∧ 2 ≤ Q.N - Q.M ∧ Q.M ≤ Q.N ∧ 4 ≤ Q.N := by
  have := Q.hM
  have := Q.hMN
  omega

theorem admissibleW2 (Q : Population) (s : Finset (Fin Q.N))
    (hs : s ∈ (univ : Finset (Fin Q.N)).powersetCard Q.M) : Admissible s :=
  AronowAudit.P031.population_assignment_admissible (Bridge.toPopulation Q) s hs

theorem hc2NeymanW2 (Q : Population) (s : Finset (Fin Q.N))
    (hs : s ∈ (univ : Finset (Fin Q.N)).powersetCard Q.M) :
    hc2Estimator Q s = neymanEstimator Q s :=
  AronowAudit.P031.hc2_eq_neyman s _ (admissibleW2 Q s hs)

theorem finiteBiasW2 (Q : Population) :
    expectation Q.M (neymanEstimator Q) - trueVariance Q =
      popVariance (fun i => Q.y1 i - Q.y0 i) / ((Q.N : ℝ) - 1) ∧
    0 ≤ expectation Q.M (neymanEstimator Q) - trueVariance Q := by
  have hsz := populationSizesW2 Q
  have hEq : expectation Q.M (neymanEstimator Q) - trueVariance Q =
      popVariance (fun i => Q.y1 i - Q.y0 i) / ((Q.N : ℝ) - 1) := by
    have he := AronowAudit.P031.neyman_bias_identity Q.M
      (by simpa using hsz.1) (by simpa using hsz.2.1)
      (by simpa using hsz.2.2.1) Q.y1 Q.y0
    have heL :
        (AronowAudit.P031.expectation Q.M (fun s => AronowAudit.P031.neyman s
          (AronowAudit.P031.observed s Q.y1 Q.y0))) -
            AronowAudit.P031.randomizationVariance Q.M Q.y1 Q.y0 =
          expectation Q.M (neymanEstimator Q) - trueVariance Q := rfl
    have heR : AronowAudit.P031.popVariance (fun i => Q.y1 i - Q.y0 i) =
        popVariance (fun i => Q.y1 i - Q.y0 i) := rfl
    rw [heL, heR, Fintype.card_fin] at he
    exact he
  refine ⟨hEq, ?_⟩
  rw [hEq]
  have hN : (4 : ℝ) ≤ Q.N := by exact_mod_cast hsz.2.2.2
  apply div_nonneg _ (by linarith)
  unfold popVariance
  positivity

theorem neymanNonnegativeW2 (Q : Population) (s : Finset (Fin Q.N))
    (hs : s ∈ (univ : Finset (Fin Q.N)).powersetCard Q.M) :
    0 ≤ neymanEstimator Q s := by
  have ha := admissibleW2 Q s hs
  have hm : (1 : ℝ) < s.card := by exact_mod_cast ha.1
  have hk : (1 : ℝ) < sᶜ.card := by exact_mod_cast ha.2
  unfold neymanEstimator neyman sampleVariance
  apply add_nonneg <;> apply div_nonneg
  · apply div_nonneg _ (by linarith)
    positivity
  · positivity
  · apply div_nonneg _ (by linarith)
    positivity
  · positivity

theorem probabilityCongrW2 (P : ℕ → Population) (f g : VarianceEstimator) (c : ℝ)
    (he : ∀ n s, s ∈ (univ : Finset (Fin (P n).N)).powersetCard (P n).M →
      f (P n) s = g (P n) s)
    (hf : ConvergesInProbability P f c) : ConvergesInProbability P g c := by
  exact AronowAudit.P031.probability_limit_congr
    (fun n => Bridge.toPopulation (P n))
    (f := fun Q => g (Bridge.fromPopulation Q))
    (g := fun Q => f (Bridge.fromPopulation Q))
    c (fun n s hs => (he n s hs).symm) hf

theorem weightedSumLimitW2 (P : ℕ → Population) (F G H : Population → ℝ)
    (e1 e0 : VarianceEstimator) (a b h : ℝ)
    (hF : Tendsto (fun n => F (P n)) atTop (𝓝 a))
    (hG : Tendsto (fun n => G (P n)) atTop (𝓝 b))
    (hH : Tendsto (fun n => H (P n)) atTop (𝓝 h))
    (he1 : ConvergesInProbability P e1 0) (he0 : ConvergesInProbability P e0 0) :
    ConvergesInProbability P (fun Q s => F Q * e1 Q s + G Q * e0 Q s + H Q) h := by
  exact AronowAudit.P031.Wave1.FootnoteThreeProbability.n8_proof
    AronowAudit.P031.Wave1.FootnoteThreeProbability.n7_proof
    (fun n => Bridge.toPopulation (P n))
    (fun Q => F (Bridge.fromPopulation Q)) (fun Q => G (Bridge.fromPopulation Q))
    (fun Q => H (Bridge.fromPopulation Q))
    (fun Q => e1 (Bridge.fromPopulation Q)) (fun Q => e0 (Bridge.fromPopulation Q))
    a b h hF hG hH he1 he0

theorem ratioLimitW2 (P : ℕ → Population) (X : VarianceEstimator) (D : Population → ℝ)
    (U D0 : ℝ) (hX : ConvergesInProbability P X U)
    (hD : Tendsto (fun n => D (P n)) atTop (𝓝 D0)) (hD0 : 0 < D0) :
    ConvergesInProbability P (fun Q s => X Q s / D Q) (U / D0) := by
  exact AronowAudit.P031.Wave1.FootnoteThreeProbability.n9_proof
    AronowAudit.P031.Wave1.FootnoteThreeProbability.n7_proof
    (fun n => Bridge.toPopulation (P n))
    (fun Q => X (Bridge.fromPopulation Q)) (fun Q => D (Bridge.fromPopulation Q))
    U D0 hX hD hD0

theorem scaledTrueLimitW2 (P : ℕ → Population) (p μ1 μ0 v1 v0 c : ℝ)
    (h : RegularRegimeW2 P p μ1 μ0 v1 v0 c) :
    Tendsto (fun n => ((P n).N : ℝ) * trueVariance (P n)) atTop
      (𝓝 (LeadingTrueVarianceW2 p v1 v0 c)) := by
  exact AronowAudit.P031.scaled_true_variance_limit
    (fun n => Bridge.toPopulation (P n)) h.growingW2 p v1 v0 c
    h.pPositiveW2 h.pLessOneW2 h.allocationW2 h.variance1W2 h.variance0W2 h.covarianceW2

theorem trueVarianceEventuallyPositiveW2 (P : ℕ → Population) (p μ1 μ0 v1 v0 c : ℝ)
    (h : RegularRegimeW2 P p μ1 μ0 v1 v0 c) :
    ∀ᶠ n in atTop, 0 < trueVariance (P n) := by
  have he := (scaledTrueLimitW2 P p μ1 μ0 v1 v0 c h).eventually
    (eventually_gt_nhds h.contrastPositiveW2)
  filter_upwards [he] with n hn
  have hN : (0 : ℝ) < (P n).N := by
    exact_mod_cast (by have := (populationSizesW2 (P n)).2.2.2; omega : 0 < (P n).N)
  exact (mul_pos_iff_of_pos_left hN).mp hn

theorem armsGrowRealW2 (P : ℕ → Population) (p : ℝ) (hN : GrowingPopulations P)
    (hp : 0 < p) (hp1 : p < 1)
    (hAlloc : Tendsto (fun n => ((P n).M : ℝ) / (P n).N) atTop (𝓝 p)) :
    Tendsto (fun n => ((P n).M : ℝ)) atTop atTop ∧
    Tendsto (fun n => ((P n).N : ℝ) - (P n).M) atTop atTop := by
  have hn : Tendsto (fun n => ((P n).N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hn0 (n : ℕ) : ((P n).N : ℝ) ≠ 0 := by
    have hh : (4 : ℝ) ≤ (P n).N := by exact_mod_cast (populationSizesW2 (P n)).2.2.2
    linarith
  constructor
  · apply (hn.atTop_mul_pos hp hAlloc).congr
    intro n
    field_simp [hn0 n]
  · have hComp := (tendsto_const_nhds (x := (1 : ℝ))).sub hAlloc
    apply (hn.atTop_mul_pos (by linarith : 0 < 1 - p) hComp).congr
    intro n
    field_simp [hn0 n]

/-- The exact observed-arm Neyman expression, expressed in fixed potential outcomes. -/
theorem neymanArmFormulaW2 (Q : Population) (s : Finset (Fin Q.N)) :
    neymanEstimator Q s = sampleVariance s Q.y1 / s.card +
      sampleVariance sᶜ Q.y0 / sᶜ.card := by
  have ht : sampleVariance s (observed s Q.y1 Q.y0) = sampleVariance s Q.y1 := by
    apply AronowAudit.P031.sample_variance_congr
    intro i hi
    simp [observed, treatment, hi]
  have hc : sampleVariance sᶜ (observed s Q.y1 Q.y0) = sampleVariance sᶜ Q.y0 := by
    apply AronowAudit.P031.sample_variance_congr
    intro i hi
    simp [observed, treatment, mem_compl.mp hi]
  exact congrArg₂ (fun a b : ℝ => a / s.card + b / sᶜ.card) ht hc

theorem scaledNeymanLimitW2 (P : ℕ → Population) (p μ1 μ0 v1 v0 c : ℝ)
    (h : RegularRegimeW2 P p μ1 μ0 v1 v0 c) (hArm : ArmSecondMomentsConverge P) :
    ConvergesInProbability P (fun Q s => (Q.N : ℝ) * neymanEstimator Q s)
      (ConservativeVarianceLimitW2 p v1 v0) := by
  let F : Population → ℝ := fun Q => (Q.N : ℝ) / Q.M
  let G : Population → ℝ := fun Q => (Q.N : ℝ) / ((Q.N : ℝ) - Q.M)
  have hF : Tendsto (fun n => F (P n)) atTop (𝓝 (1 / p)) := by
    have ht : Tendsto (fun n => 1 / (((P n).M : ℝ) / (P n).N)) atTop (𝓝 (1 / p)) :=
      (tendsto_const_nhds (x := (1 : ℝ))).div h.allocationW2 h.pPositiveW2.ne'
    apply ht.congr
    intro n
    dsimp only [F]
    rw [one_div_div]
  have hComp : Tendsto (fun n => (((P n).N : ℝ) - (P n).M) / (P n).N)
      atTop (𝓝 (1 - p)) := by
    apply (tendsto_const_nhds.sub h.allocationW2).congr
    intro n
    have hn0 : ((P n).N : ℝ) ≠ 0 := by
      have hh : (4 : ℝ) ≤ (P n).N := by exact_mod_cast (populationSizesW2 (P n)).2.2.2
      linarith
    field_simp [hn0]
  have hG : Tendsto (fun n => G (P n)) atTop (𝓝 (1 / (1 - p))) := by
    have ht : Tendsto (fun n => 1 / ((((P n).N : ℝ) - (P n).M) / (P n).N))
        atTop (𝓝 (1 / (1 - p))) :=
      (tendsto_const_nhds (x := (1 : ℝ))).div hComp (by linarith [h.pLessOneW2])
    apply ht.congr
    intro n
    dsimp only [G]
    rw [one_div_div]
  let H : Population → ℝ := fun Q => F Q * popVariance Q.y1 + G Q * popVariance Q.y0
  have hH : Tendsto (fun n => H (P n)) atTop (𝓝 (ConservativeVarianceLimitW2 p v1 v0)) := by
    have he : 1 / p * v1 + 1 / (1 - p) * v0 = ConservativeVarianceLimitW2 p v1 v0 := by
      unfold ConservativeVarianceLimitW2
      ring
    simpa only [H, he] using (hF.mul h.variance1W2).add (hG.mul h.variance0W2)
  have hW := weightedSumLimitW2 P F G H
    (fun Q s => sampleVariance s Q.y1 - popVariance Q.y1)
    (fun Q s => sampleVariance sᶜ Q.y0 - popVariance Q.y0)
    (1 / p) (1 / (1 - p)) (ConservativeVarianceLimitW2 p v1 v0)
    hF hG hH hArm.1 hArm.2
  apply probabilityCongrW2 P _ _ _ ?_ hW
  intro n s hs
  have hcard := (mem_powersetCard.mp hs).2
  have hcompl : sᶜ.card = (P n).N - (P n).M := by
    rw [card_compl, hcard, Fintype.card_fin]
  rw [neymanArmFormulaW2, hcard, hcompl, Nat.cast_sub (populationSizesW2 (P n)).2.2.1]
  dsimp only [F, G, H]
  ring

theorem conservativeLimitComparisonW2 (P : ℕ → Population) (p μ1 μ0 v1 v0 c : ℝ)
    (h : RegularRegimeW2 P p μ1 μ0 v1 v0 c) :
    LeadingTrueVarianceW2 p v1 v0 c ≤ ConservativeVarianceLimitW2 p v1 v0 := by
  have hc : 2 * c - v1 - v0 ≤ 0 := by
    apply le_of_tendsto' ((h.covarianceW2.const_mul 2).sub h.variance1W2 |>.sub h.variance0W2)
    intro n
    exact AronowAudit.P031.covariance_bound (P n).y1 (P n).y0
  have he : ConservativeVarianceLimitW2 p v1 v0 - LeadingTrueVarianceW2 p v1 v0 c =
      v1 + v0 - 2 * c := by
    unfold ConservativeVarianceLimitW2 LeadingTrueVarianceW2
    field_simp [h.pPositiveW2.ne', (by linarith [h.pLessOneW2] : 1 - p ≠ 0)]
    ring
  linarith

/-- Division of scaled estimates by the scaled true variance cancels N;
N is at least four in every row, so there is no zero-division convention. -/
theorem estimatorRatioLimitW2 (P : ℕ → Population) (A : VarianceEstimator)
    (p μ1 μ0 v1 v0 c : ℝ) (h : RegularRegimeW2 P p μ1 μ0 v1 v0 c)
    (hA : ConvergesInProbability P (fun Q s => (Q.N : ℝ) * A Q s)
      (ConservativeVarianceLimitW2 p v1 v0)) :
    ConvergesInProbability P (fun Q s => A Q s / trueVariance Q)
      (ConservativeVarianceLimitW2 p v1 v0 / LeadingTrueVarianceW2 p v1 v0 c) := by
  have hr := ratioLimitW2 P (fun Q s => (Q.N : ℝ) * A Q s)
    (fun Q => (Q.N : ℝ) * trueVariance Q) _ _ hA
    (scaledTrueLimitW2 P p μ1 μ0 v1 v0 c h) h.contrastPositiveW2
  apply probabilityCongrW2 P _ _ _ ?_ hr
  intro n s _
  have hn0 : ((P n).N : ℝ) ≠ 0 := by
    have hh : (4 : ℝ) ≤ (P n).N := by exact_mod_cast (populationSizesW2 (P n)).2.2.2
    linarith
  exact mul_div_mul_left _ _ hn0

def maxLeverageW2 (Q : Population) : ℝ :=
  max (1 / (Q.M : ℝ)) (1 / ((Q.N : ℝ) - Q.M))

theorem maxLeverageLimitW2 (P : ℕ → Population) (p : ℝ) (hN : GrowingPopulations P)
    (hp : 0 < p) (hp1 : p < 1)
    (hAlloc : Tendsto (fun n => ((P n).M : ℝ) / (P n).N) atTop (𝓝 p)) :
    Tendsto (fun n => maxLeverageW2 (P n)) atTop (𝓝 0) := by
  obtain ⟨hM, hK⟩ := armsGrowRealW2 P p hN hp hp1 hAlloc
  simpa only [maxLeverageW2, max_self] using
    (hM.const_div_atTop 1).max (hK.const_div_atTop 1)

theorem equivalenceOfBoundW2 (P : ℕ → Population) (A B : VarianceEstimator) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0))
    (hBound : ∀ᶠ n in atTop, ∀ s ∈ (univ : Finset (Fin (P n).N)).powersetCard (P n).M,
      |A (P n) s - B (P n) s| ≤ e n * |B (P n) s|) :
    FirstOrderEquivalent P A B := by
  classical
  intro ε hε
  have hSmall : ∀ᶠ n in atTop, e n < ε := (tendsto_order.mp he).2 ε hε
  apply tendsto_const_nhds.congr'
  filter_upwards [hSmall, hBound] with n hn hb
  symm
  unfold eventProbability
  have hz : ∀ s ∈ (univ : Finset (Fin (P n).N)).powersetCard (P n).M,
      ¬ ε * |B (P n) s| < |A (P n) s - B (P n) s| := by
    intro s hs hlt
    have hh := mul_le_mul_of_nonneg_right hn.le (abs_nonneg (B (P n) s))
    linarith [hb s hs]
  change expectation (P n).M _ = 0
  calc
    _ = expectation (P n).M (fun _ => 0) := by
      apply AronowAudit.P031.expectation_congr
      intro s hs
      simp [hz s hs]
    _ = 0 := by simp [expectation]

/-- Uniform finite leverage bounds include assignments with zero HC2. -/
theorem relativeBoundsW2 (Q : Population) (s : Finset (Fin Q.N))
    (hs : s ∈ (univ : Finset (Fin Q.N)).powersetCard Q.M) :
    |hrEstimator Q s - hc2Estimator Q s| ≤ maxLeverageW2 Q * |hc2Estimator Q s| ∧
    |hc3Estimator Q s - hc2Estimator Q s| ≤ (2 * maxLeverageW2 Q) * |hc2Estimator Q s| ∧
    |hc1Estimator Q s - hc2Estimator Q s| ≤
      (|(Q.N : ℝ) / ((Q.N : ℝ) - 2)| * maxLeverageW2 Q +
        |(Q.N : ℝ) / ((Q.N : ℝ) - 2) - 1|) * |hc2Estimator Q s| := by
  have ha := admissibleW2 Q s hs
  have hm : (2 : ℝ) ≤ Q.M := by exact_mod_cast (populationSizesW2 Q).1
  have hk : (2 : ℝ) ≤ (Q.N : ℝ) - Q.M := by
    have hk' : (2 : ℝ) ≤ ((Q.N - Q.M : ℕ) : ℝ) := by
      exact_mod_cast (populationSizesW2 Q).2.1
    simpa only [Nat.cast_sub (populationSizesW2 Q).2.2.1] using hk'
  have hcard := (mem_powersetCard.mp hs).2
  have hcompl : (sᶜ.card : ℝ) = (Q.N : ℝ) - Q.M := by
    rw [card_compl, hcard, Fintype.card_fin, Nat.cast_sub (populationSizesW2 Q).2.2.1]
  have hb : (1 - maxLeverageW2 Q) * hc2Estimator Q s ≤ hrEstimator Q s ∧
      hrEstimator Q s ≤ hc2Estimator Q s ∧
      hc2Estimator Q s ≤ hc3Estimator Q s ∧
      (1 - maxLeverageW2 Q) * hc3Estimator Q s ≤ hc2Estimator Q s := by
    simpa only [hrEstimator, hc2Estimator, hc3Estimator, maxLeverageW2, hcompl, hcard,
      donorHrW2, donorHc2W2, donorHc3W2]
      using AronowAudit.P031.hc_variant_bounds s (observed s Q.y1 Q.y0) ha
  have hH0 : 0 ≤ maxLeverageW2 Q :=
    le_trans (by positivity : (0 : ℝ) ≤ 1 / (Q.M : ℝ)) (le_max_left _ _)
  have hHhalf : maxLeverageW2 Q ≤ 1 / 2 := by
    apply max_le
    · apply (div_le_iff₀ (by linarith : (0 : ℝ) < Q.M)).mpr
      linarith
    · apply (div_le_iff₀ (by linarith : (0 : ℝ) < (Q.N : ℝ) - Q.M)).mpr
      linarith
  have hB0 : 0 ≤ hc2Estimator Q s := by
    rw [hc2NeymanW2 Q s hs]
    exact neymanNonnegativeW2 Q s hs
  have hHR : |hrEstimator Q s - hc2Estimator Q s| ≤ maxLeverageW2 Q * |hc2Estimator Q s| := by
    rw [abs_of_nonpos (sub_nonpos.mpr hb.2.1), abs_of_nonneg hB0]
    nlinarith [hb.1]
  have hHC3 : |hc3Estimator Q s - hc2Estimator Q s| ≤
      (2 * maxLeverageW2 Q) * |hc2Estimator Q s| := by
    have hx0 : 0 ≤ hc3Estimator Q s := hB0.trans hb.2.2.1
    have hx2 : hc3Estimator Q s ≤ 2 * hc2Estimator Q s := by
      nlinarith [mul_le_mul_of_nonneg_right hHhalf hx0, hb.2.2.2]
    rw [abs_of_nonneg (sub_nonneg.mpr hb.2.2.1), abs_of_nonneg hB0]
    nlinarith [mul_le_mul_of_nonneg_left hx2 hH0, hb.2.2.2]
  refine ⟨hHR, hHC3, ?_⟩
  let F : ℝ := (Q.N : ℝ) / ((Q.N : ℝ) - 2)
  have hc1Eq : hc1Estimator Q s = F * hrEstimator Q s := by
    simp only [hc1Estimator, hc1, Fintype.card_fin, hrEstimator, F]
  rw [hc1Eq]
  change |F * hrEstimator Q s - hc2Estimator Q s| ≤
    (|F| * maxLeverageW2 Q + |F - 1|) * |hc2Estimator Q s|
  calc
    _ = |F * (hrEstimator Q s - hc2Estimator Q s) + (F - 1) * hc2Estimator Q s| := by
      congr 1
      ring
    _ ≤ |F * (hrEstimator Q s - hc2Estimator Q s)| + |(F - 1) * hc2Estimator Q s| :=
      abs_add_le _ _
    _ = |F| * |hrEstimator Q s - hc2Estimator Q s| + |F - 1| * |hc2Estimator Q s| := by
      rw [abs_mul, abs_mul]
    _ ≤ _ := by
      nlinarith [mul_le_mul_of_nonneg_left hHR (abs_nonneg F)]

theorem robustEquivalenceW2 (P : ℕ → Population) (p μ1 μ0 v1 v0 c : ℝ)
    (h : RegularRegimeW2 P p μ1 μ0 v1 v0 c) :
    FirstOrderEquivalent P hrEstimator hc2Estimator ∧
    FirstOrderEquivalent P hc1Estimator hc2Estimator ∧
    FirstOrderEquivalent P hc3Estimator hc2Estimator := by
  have hH := maxLeverageLimitW2 P p h.growingW2 h.pPositiveW2 h.pLessOneW2 h.allocationW2
  have hF := AronowAudit.P031.population_ratio_tends_one
    (fun n => Bridge.toPopulation (P n)) h.growingW2 2 (by norm_num)
  change Tendsto (fun n => ((P n).N : ℝ) / (((P n).N : ℝ) - 2)) atTop (𝓝 1) at hF
  refine ⟨?_, ?_, ?_⟩
  · apply equivalenceOfBoundW2 P _ _ (fun n => maxLeverageW2 (P n)) hH
    exact Filter.Eventually.of_forall (fun n s hs => (relativeBoundsW2 (P n) s hs).1)
  · have he : Tendsto (fun n => |((P n).N : ℝ) / (((P n).N : ℝ) - 2)| *
        maxLeverageW2 (P n) + |((P n).N : ℝ) / (((P n).N : ℝ) - 2) - 1|)
        atTop (𝓝 0) := by
      simpa using (hF.abs.mul hH).add ((hF.sub_const 1).abs)
    apply equivalenceOfBoundW2 P _ _ _ he
    exact Filter.Eventually.of_forall (fun n s hs => (relativeBoundsW2 (P n) s hs).2.2)
  · have he : Tendsto (fun n => 2 * maxLeverageW2 (P n)) atTop (𝓝 0) := by
      simpa using hH.const_mul 2
    apply equivalenceOfBoundW2 P _ _ _ he
    exact Filter.Eventually.of_forall (fun n s hs => (relativeBoundsW2 (P n) s hs).2.1)

end
end SAP.P031.WH.W2
