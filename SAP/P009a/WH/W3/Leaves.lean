import SAP.P009a.WH.W3.Support
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SAP.P009a.WH.W3
open Filter SAP.P009a.Bridge
open scoped BigOperators Topology Classical
noncomputable section
/-- A bounded nonnegative sequence which does not tend to zero has a genuine positive real limsup. Prove boundedness above and below, use `le_liminf_of_le` and `tendsto_of_le_liminf_of_limsup_le` for positivity, and the eventual/frequent limsup characterizations for `FiniteLimsup`. Approximately 50–90 lines; no probability is involved. -/
def T6_L1 : Prop :=
  ∀ a : ℕ → ℝ, (∀ t, 0 ≤ a t ∧ a t ≤ 1) → ¬ Tendsto a atTop (nhds 0) →
    FiniteLimsup a (Filter.limsup a atTop) ∧
      0 < Filter.limsup a atTop ∧ Filter.limsup a atTop ≤ 1
/-- Complete the selected-sequence construction, using only assignment bounds. On selected indices use `finite_limsup_construction`; elsewhere the outcomes are zero. The full-cube bound gives all fixed finite moment orders with K=max(k,1/sqrt(L)), using `regularity_of_uniform_bound`. For epsilon=1/(2k), the error event has probability one on the infinite selected set. A sequence tending to zero is eventually below one half, which contradicts those probabilities. Approximately 120–200 lines. -/
def T6_L2 : Prop :=
  ∀ (S : ExperimentSequence) (k L c : ℝ),
    (∀ t, AssignmentBounds (S.experiment t) k) → 0 < L ∧ L ≤ 1 →
    0 < c → c < L → Set.Infinite {t | c ≤ interferenceDensity S t} →
    let F := selectedLimsupSequence S L c
    (∀ t i z, |(F.experiment t).outcome i z| ≤ 1 / Real.sqrt L) ∧
    (∀ q s : ℝ, 2 ≤ q → 1 ≤ s → ∃ K, 0 < K ∧ SequenceRegularity F K q s) ∧
    Set.Infinite {t | probability (F.experiment t).design
      (fun z => 1/(2*k) < |htEstimate (F.experiment t) z -
        expectedATE (F.experiment t)|) = 1} ∧
    ¬ ConvergesInProbability F
      (fun t z => htEstimate (F.experiment t) z - expectedATE (F.experiment t))
/-- Exact estimators and moments of the nonshrinking second family. Split the HT numerator with `Fin.sum_univ_succ`: the first unit contributes 2 Z1 and each other unit contributes one. `fair_first_coordinate` computes its mean and variance; Bernoulli HT unbiasedness identifies EATE. `Real.sqrt_div` and `Real.sqrt_sq` give the standardized identity. Approximately 100–170 lines, including the one-unit case. -/
def T7_L1 : Prop :=
  ∀ t, let E := nonshrinkingSequence.experiment t
    let n := sampleSize nonshrinkingSequence t
    expectedATE E = 1 ∧ expectation E.design (htEstimate E) = 1 ∧
    variance E.design (htEstimate E) = 1/n^2 ∧
    ∀ z, htEstimate E z =
      (n-1+2*treatmentValue (z ⟨0, nonshrinkingSequence.positive t⟩))/n ∧
      standardizedHT E z = 2*treatmentValue (z ⟨0, nonshrinkingSequence.positive t⟩)-1
/-- A continuous bounded function cannot approximate a CDF jump of height one half within less than one quarter. The range defining the real supremum is nonempty and bounded by one. Evaluate the error at -1 and at -1-1/(m+1); pass to the limit from below with `le_of_tendsto`, then combine the two inequalities. Continuity only at -1 suffices. Approximately 60–100 lines. -/
def T7_L2 : Prop :=
  ∀ G : ℝ → ℝ, ContinuousAt G (-1) → (∀ x, 0 ≤ G x ∧ G x ≤ 1) →
    1/4 ≤ kolmogorovDistance rademacherCDF G
theorem T14_assembly : T14WholeStatement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n E i j hij hI
    exact AronowAudit.P009.no_interference_zero_spillover (toProjectExperiment E) i j hij hI
  · intro n hn E h hp
    exact AronowAudit.P009.no_interference_B1_zero hn (toProjectExperiment E) h hp
  · obtain ⟨_, _, hi, _, _, hx⟩ := AronowAudit.P009.direct_spillover_counterexample
    exact ⟨hi, hx⟩
  · intro n E i j hij hNZ
    by_contra hI
    exact hNZ (AronowAudit.P009.no_interference_zero_spillover
      (toProjectExperiment E) i j hij hI).2.2.2
theorem T15_assembly : T15WholeStatement := by
  have hfinite : ∀ {n : ℕ}, 0 < n → let E := identityPopulation n
      ProductDesign E ∧ NoSpillovers E ∧
      (∀ q s : ℝ, 2 ≤ q → 1 ≤ s → Regularity E 2 q s) ∧
      (∀ i j, interferenceIndicator E i j = if i = j then 1 else 0) ∧
      (∀ i j, dependenceIndicator E i j = if i = j then 1 else 0) ∧
      averageDependence E = 1 ∧
      (∀ θ : ℝ, externalMixing E θ = 0 ∧ internalMixing E θ = 0) ∧
      (∀ i j, covariance E.design (fun z => treatmentValue (z i))
        (fun z => treatmentValue (z j)) = if i = j then 1/4 else 0) ∧
      (∀ i j, assignmentCovariance E i j = if i = j then 1/4 else 0) ∧
      (∀ i j, mixingCoefficient E.design (fun z => z i) (fun z => z j) =
        if i = j then 1/4 else 0) ∧
      fullAssignmentSum E = 1/(n : ℝ) ∧ offDiagonalMixingSum E = 0 ∧
      ¬ fullAssignmentSum E ≤ offDiagonalMixingSum E ∧
      variance E.design (fun z => estimatedArmSize E true z / n) = 1/(n : ℝ) := by
    intro n hn
    let E := identityPopulation n
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hBER : ProductDesign E := AronowAudit.P009.SparseCompletion.fair_BER n
      (fun i z => treatmentValue (z i))
    have hNo : NoSpillovers E := AronowAudit.P009.DiagonalCompletion.identity_noI n
    have hc (i j : Fin n) : covariance E.design (fun z => treatmentValue (z i))
        (fun z => treatmentValue (z j)) = if i = j then 1/4 else 0 :=
      AronowAudit.P009.DiagonalCompletion.coordinate_covariance n i j
    have hj (i j : Fin n) : assignmentCovariance E i j = if i = j then 1/4 else 0 := by
      rw [assignment_covariance_eq, hc]
    have hl : fullAssignmentSum E = 1/(n : ℝ) := by
      unfold fullAssignmentSum
      simp only [hj]
      simp
      field_simp
    have hr : offDiagonalMixingSum E = 0 := by
      have he (i j : Fin n) : (if j = i then (0 : ℝ) else
          mixingCoefficient E.design (fun z => z i) (fun z => z j)) = 0 := by
        by_cases hji : j = i
        · simp [hji]
        · simp [E, identityPopulation, fairPopulation, hji, coordinate_alpha, Ne.symm hji]
      simp [offDiagonalMixingSum, he]
    obtain ⟨hI, hd⟩ := no_spillovers_indicators E hNo
    refine ⟨hBER, hNo, ?_, hI, hd,
      AronowAudit.P009.SparseCompletion.noI_dAvg hn (toProjectExperiment E) hNo,
      ?_, hc, hj, coordinate_alpha n, hl, hr, ?_, ?_⟩
    · intro q s hq hs
      apply fair_all_orders n _ _ q s hq hs
      intro i z
      cases z i <;> norm_num [treatmentValue]
    · intro θ
      exact ⟨AronowAudit.P009.DiagonalCompletion.noI_alpha_ext (toProjectExperiment E) hBER hNo θ,
        AronowAudit.P009.DiagonalCompletion.noI_alpha_int (toProjectExperiment E) hBER hNo θ⟩
    · rw [hl, hr]
      exact not_le.mpr (one_div_pos.mpr hnR)
    · change AronowAudit.P009.var (AronowAudit.P009.identityExperiment n).design
        (fun z => AronowAudit.P009.nHat (AronowAudit.P009.identityExperiment n) true z / n) = _
      rw [AronowAudit.P009.BernoulliCompletion.count_variance_sum
        (AronowAudit.P009.identityExperiment n) hBER true]
      simp only [AronowAudit.P009.identityExperiment,
        AronowAudit.P009.SparseCompletion.fair_marginal]
      norm_num
      field_simp
  refine ⟨AronowAudit.P009.diagonal_omission_family, hfinite, ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hl, hr, _⟩ := hfinite (n := 4) (by norm_num)
  exact ⟨hl, hr, by norm_num⟩
theorem T8_assembly : T8WholeStatement := by
  refine ⟨?_, AronowAudit.P009.sparse_normal_counterexample⟩
  intro S k q s hReg hBER hDegree hVariance
  have hNormal : ConvergesInLaw S (fun t => standardizedHT (S.experiment t)) standardNormalCDF :=
    AronowAudit.P009.corrected_normal_approximation
      (toProjectSequence S) k q s hReg hBER hDegree hVariance
  obtain ⟨c, hc, hev⟩ := hVariance
  have hpos : ∀ᶠ t in atTop,
      0 < variance (S.experiment t).design (htEstimate (S.experiment t)) := by
    filter_upwards [hev] with t ht
    have hn : 0 < sampleSize S t := by
      change (0 : ℝ) < S.N t
      exact_mod_cast S.positive t
    by_contra h
    have hm := mul_nonpos_of_nonneg_of_nonpos hn.le (le_of_not_gt h)
    linarith
  refine ⟨hpos, ?_⟩
  intro X hX x hx
  apply Filter.Tendsto.congr' _ (hNormal x hx)
  filter_upwards [hpos] with t ht
  congr 1
  funext z
  rw [hX t ht z]
theorem T6_assembly (h1 : T6_L1) (h2 : T6_L2) : T6WholeStatement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact @AronowAudit.P009.corrected_limsup_subsequence
  · let a : ℕ → ℝ := fun t => 1 - 1/((t : ℝ)+1)
    have ha : Tendsto a atTop (nhds 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    refine ⟨a, ⟨?_, ?_⟩, ?_⟩
    · intro ε hε
      exact ha.eventually_lt tendsto_const_nhds (by linarith)
    · intro ε hε
      exact ((tendsto_const_nhds (x := 1-ε)).eventually_lt ha (by linarith)).frequently
    · intro t
      have hp : (0 : ℝ) < 1/((t : ℝ)+1) := by positivity
      dsimp [a]
      linarith
  · exact finite_limsup_construction
  · intro S k hA hNot
    obtain ⟨hFinite, hLpos, hLle⟩ := h1 (interferenceDensity S) (density_bounds S) hNot
    refine ⟨hFinite, hLpos, hLle, ?_⟩
    intro c hc hcL
    have hH : Set.Infinite {t | c ≤ interferenceDensity S t} :=
      AronowAudit.P009.corrected_limsup_subsequence
        (interferenceDensity S) (interferenceDensityLimsup S) c hFinite hc hcL
    obtain ⟨hBound, hReg, hProb, hNC⟩ := h2 S k (interferenceDensityLimsup S) c hA
      ⟨hLpos, hLle⟩ hc hcL hH
    refine ⟨hH, ?_, hBound, hReg, ?_, ?_, hProb, hNC⟩
    · intro t
      dsimp [selectedLimsupSequence]
      split_ifs <;> rfl
    · intro t ht
      exact ⟨finite_limsup_construction (S.positive t) (S.experiment t) k
          (interferenceDensityLimsup S) (hA t) ⟨hLpos, hLle⟩,
        by simp only [selectedLimsupSequence, Set.mem_setOf_eq] at ht ⊢; simp [ht]⟩
    · intro t ht
      have hNotSelected : ¬ c ≤ interferenceDensity S t := ht
      simp [selectedLimsupSequence, hNotSelected, expectedATE, assignmentATE,
        individualEffect, potentialResponse, htEstimate, estimatedArmMean, expectation]
theorem fair_rademacher_law (t : ℕ) (X : TreatmentVector (t+1) → ℝ)
    (hX : ∀ z, X z = 2*treatmentValue (z 0)-1) :
    (∀ b : Bool, probability (fairDistribution (t+1))
      (fun z => X z = if b then 1 else -1) = 1/2) ∧
    (∀ x, finiteCDF (fairDistribution (t+1)) X x = rademacherCDF x) := by
  constructor
  · intro b
    unfold probability
    simp_rw [hX]
    change AronowAudit.P009.mean (AronowAudit.P009.fairLaw (t+1))
      (fun z => if 2*AronowAudit.P009.bit (z 0)-1 = (if b then 1 else -1) then 1 else 0) = _
    rw [AronowAudit.P009.fair_first_coordinate t
      (fun a => if 2*AronowAudit.P009.bit a-1 = (if b then 1 else -1) then 1 else 0)]
    cases b <;> norm_num [AronowAudit.P009.bit]
  · intro x
    unfold finiteCDF probability
    simp_rw [hX]
    change AronowAudit.P009.mean (AronowAudit.P009.fairLaw (t+1))
      (fun z => if 2*AronowAudit.P009.bit (z 0)-1 ≤ x then 1 else 0) = _
    rw [AronowAudit.P009.fair_first_coordinate t
      (fun a => if 2*AronowAudit.P009.bit a-1 ≤ x then 1 else 0)]
    norm_num [AronowAudit.P009.bit]
    unfold rademacherCDF
    split_ifs <;> norm_num <;> linarith
theorem T7_assembly (h1 : T7_L1) (h2 : T7_L2) : T7WholeStatement := by
  have hSparse : T7Statement := AronowAudit.P009.sparse_normal_counterexample
  have hb1 (t : ℕ) (i : Fin (t+1)) (z : TreatmentVector (t+1)) :
      |(sparseSequence.experiment t).outcome i z| ≤ 1 := by
    change |if i.val = 0 then treatmentValue (z i) else 0| ≤ 1
    split_ifs <;> cases hz : z i <;> norm_num [treatmentValue, hz]
  have hb2 (t : ℕ) (i : Fin (t+1)) (z : TreatmentVector (t+1)) :
      |(nonshrinkingSequence.experiment t).outcome i z| ≤ 1 := by
    change |if i.val = 0 then treatmentValue (z i) else treatmentValue (z i)-1/2| ≤ 1
    split_ifs <;> cases hz : z i <;> norm_num [treatmentValue, hz]
  have hNo1 (t : ℕ) : NoSpillovers (sparseSequence.experiment t) :=
    (hSparse.2.2.1 t).2.1
  have hNo2 (t : ℕ) : NoSpillovers (nonshrinkingSequence.experiment t) := by
    intro i z w hi
    change (if i.val = 0 then treatmentValue (z i) else treatmentValue (z i)-1/2) =
      (if i.val = 0 then treatmentValue (w i) else treatmentValue (w i)-1/2)
    rw [hi]
  have hstd1 (t : ℕ) (z : TreatmentVector (t+1)) :
      standardizedHT (sparseSequence.experiment t) z = 2*treatmentValue (z 0)-1 :=
    AronowAudit.P009.SparseCompletion.sparse_statistic t z
  have hstd2 (t : ℕ) (z : TreatmentVector (t+1)) :
      standardizedHT (nonshrinkingSequence.experiment t) z = 2*treatmentValue (z 0)-1 :=
    (h1 t).2.2.2 z |>.2
  have hLaw1 (t : ℕ) := fair_rademacher_law t _ (hstd1 t)
  have hLaw2 (t : ℕ) := fair_rademacher_law t _ (hstd2 t)
  have hLimit2 : Tendsto (fun t => sampleSize nonshrinkingSequence t *
      variance (nonshrinkingSequence.experiment t).design
        (htEstimate (nonshrinkingSequence.experiment t))) atTop (nhds 0) := by
    convert hSparse.2.2.2.1 using 1
    funext t
    change ((t+1 : ℕ) : ℝ) * variance (nonshrinkingSequence.experiment t).design
      (htEstimate (nonshrinkingSequence.experiment t)) =
      ((t+1 : ℕ) : ℝ) * variance (sparseSequence.experiment t).design
        (htEstimate (sparseSequence.experiment t))
    rw [(h1 t).2.2.1]
    exact congrArg (fun v : ℝ => ((t+1 : ℕ) : ℝ)*v)
      (AronowAudit.P009.sparse_moments_finite t).2.1.symm
  refine ⟨hSparse, ?_, ?_, ?_, ?_⟩
  · intro q s hq hs
    constructor <;> intro t
    · apply fair_all_orders (t+1) _ _ q s hq hs
      intro i z
      exact (hb1 t i z).trans (by norm_num)
    · apply fair_all_orders (t+1) _ _ q s hq hs
      intro i z
      exact (hb2 t i z).trans (by norm_num)
  · intro t
    obtain ⟨hI, hd⟩ := no_spillovers_indicators (sparseSequence.experiment t) (hNo1 t)
    refine ⟨hb1 t, hI, hd, AronowAudit.P009.SparseCompletion.sparse_eate t,
      (AronowAudit.P009.sparse_moments_finite t).1,
      (AronowAudit.P009.sparse_moments_finite t).2.1, ?_⟩
    intro z
    exact ⟨(AronowAudit.P009.sparse_estimators_finite t z).1, hstd1 t z⟩
  · intro t
    obtain ⟨hI, hd⟩ := no_spillovers_indicators (nonshrinkingSequence.experiment t) (hNo2 t)
    refine ⟨AronowAudit.P009.SparseCompletion.fair_BER (t+1)
        (fun i z => if i.val = 0 then treatmentValue (z i) else treatmentValue (z i)-1/2),
      hNo2 t, hb2 t, hI, hd,
      AronowAudit.P009.SparseCompletion.noI_dAvg (nonshrinkingSequence.positive t)
        (toProjectExperiment (nonshrinkingSequence.experiment t)) (hNo2 t),
      AronowAudit.P009.SparseCompletion.noI_dMax (nonshrinkingSequence.positive t)
        (toProjectExperiment (nonshrinkingSequence.experiment t)) (hNo2 t),
      (h1 t).1, (h1 t).2.1, (h1 t).2.2.1, ?_, (h1 t).2.2.2⟩
    rw [(h1 t).2.2.1]
    change (0 : ℝ) < 1 / ((t+1 : ℕ) : ℝ)^2
    positivity
  · intro S hS
    have hcases : S = sparseSequence ∨ S = nonshrinkingSequence := by simpa using hS
    rcases hcases with rfl | rfl
    · refine ⟨fun t => (hLaw1 t).1, fun t => (hLaw1 t).2, ?_,
        hSparse.2.2.2.1, hSparse.2.2.2.2.2⟩
      intro G hG t
      have he : finiteCDF (sparseSequence.experiment t).design
          (standardizedHT (sparseSequence.experiment t)) = rademacherCDF :=
        funext (hLaw1 t).2
      rw [he]
      exact h2 G hG.1.continuousAt hG.2.2.1
    · refine ⟨fun t => (hLaw2 t).1, fun t => (hLaw2 t).2, ?_, hLimit2, ?_⟩
      · intro G hG t
        have he : finiteCDF (nonshrinkingSequence.experiment t).design
            (standardizedHT (nonshrinkingSequence.experiment t)) = rademacherCDF :=
          funext (hLaw2 t).2
        rw [he]
        exact h2 G hG.1.continuousAt hG.2.2.1
      · intro hc
        apply hSparse.2.2.2.2.2
        intro x hx
        have ht := hc x hx
        change Tendsto (fun t => finiteCDF (sparseSequence.experiment t).design
          (standardizedHT (sparseSequence.experiment t)) x) atTop (nhds (standardNormalCDF x))
        change Tendsto (fun t => finiteCDF (nonshrinkingSequence.experiment t).design
          (standardizedHT (nonshrinkingSequence.experiment t)) x) atTop (nhds (standardNormalCDF x)) at ht
        apply Filter.Tendsto.congr' _ ht
        exact Eventually.of_forall (fun t => ((hLaw2 t).2 x).trans ((hLaw1 t).2 x).symm)
end
end SAP.P009a.WH.W3
