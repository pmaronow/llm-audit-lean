import SAP.P061a.WH.W1.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a.WH.W1

open scoped BigOperators Topology Classical BoundedContinuousFunction ENNReal
open Filter MeasureTheory

/-- Flattening pairs is a bijection onto the entire binary cube, exchanges partners correctly,
and sends raw paired replacement to coordinate update. Prove by the inverse that reads bits
at finProdFinEquiv (k,0) and (k,1); use Fin 2 case analysis and equivalence inverse identities.
The statement includes K=0, where both function spaces have their unique empty function. -/
def T4_L1 : Prop := ∀ K : ℕ, PairEncodingW1 K

/-- Exactly the partners have dependent assignment bits. Identify the mass-specified design
with localDesign through Bridge.toProject and extensionality. Outside a pair, project the
existing independence from the entire outside vector. For partners, enumerate their four
joint masses: P(1,1)=(1+1/m)/4 differs from the product 1/4. This is about assignments,
not response dependence; m>=2 makes the correlation strictly positive. -/
def T4_L2 : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ D : AtomicDesign (Fin (m^8) → BitPair),
    (∀ z, D.mass z = ∏ k : Fin (m^8),
      if (z k).1 = (z k).2 then (1+pairParameter m)/4 else (1-pairParameter m)/4) →
    ∀ i j, assignmentEdgeW1 D i j ↔ j = partnerIndexW1 (m^8) i

/-- Exactly the partner assignment influences a unit's raw outcome. Expand the partner-only
response; use the flattening bijection to change just that bit. Its change is 1/m>0.
Conversely, agreement at the partner forces equal responses. The direct paired replacement
formulas and Fin 2 case analysis suffice; no other leaf is a premise. -/
def T4_L3 : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ i j,
    interferenceEdgeW1 m i j ↔ j = partnerIndexW1 (m^8) i

/-- Assemble all existing exact probability and coverage results, adding the three new
combinatorial/graph facts. Square-root algebra proves the positive divergence and scale
normalizations directly; no asymptotic normality is required. -/
theorem T4_assembly (h1 : T4_L1) (h2 : T4_L2) (h3 : T4_L3) : T4WholeStatement := by
  obtain ⟨D, hmass, hfinite, hlimits⟩ := Bridge.pair_inference_correspondence
  have hbase : PairBaseW1 D := ⟨hmass, hfinite, hlimits⟩
  refine ⟨D, hbase, ?_, ?_, ?_⟩
  · intro m hm
    have hdep := h2 m hm (D m) (hmass m)
    have hinf := h3 m hm
    have hK : 0 < m^8 := Nat.pow_pos (by omega : 0 < m)
    have hd := matching_degreesW1 (m^8) hK (assignmentEdgeW1 (D m)) hdep
    have hi := matching_degreesW1 (m^8) hK (interferenceEdgeW1 m) hinf
    refine ⟨h1 (m^8), hdep, hinf, fun i => ⟨hd.1 i, hi.1 i⟩,
      hd.2, hi.2, variance_expressionW1 m, ?_⟩
    rcases (hfinite m hm).1 with ⟨_, _, _, _, _, hA, _, hT, _⟩
    rw [hA, hT, sub_zero]
    exact gap_normalizationW1 m hm
  · apply positive_of_square_atTopW1 _ _ hlimits.2.2.1
    intro n
    rcases (hfinite (n+2) (by omega)).1 with ⟨_, _, _, _, _, hA, _, hT, _⟩
    rw [hA, hT, sub_zero]
    exact div_nonneg (by positivity) (hfinite (n+2) (by omega)).2.le
  · have hs := (Real.continuous_sqrt.tendsto (4 : ℝ)).comp hlimits.2.1
    have he : (fun n : ℕ => Real.sqrt (((n+2)^8*2 : ℝ) *
        designVariance (D (n+2)) (pairEstimator (n+2) (D (n+2))))) =
        (fun n => pairStandardError (n+2) (D (n+2)) * Real.sqrt ((n+2)^8*2 : ℝ)) := by
      funext n
      rw [Real.sqrt_mul (by positivity)]
      exact mul_comm _ _
    simpa only [Function.comp_def, he, (show Real.sqrt (4 : ℝ) = 2 by norm_num)] using hs

/-- Each coordinate of the padded pair is fair, and every cube assignment has positive mass.
Normalize/sum out the independent remainder, enumerate the first pair, and use the uniform
coordinate law for the remaining bits. All indices, including n=0, are covered. -/
def T5_L1 : Prop :=
  ∀ (n : ℕ) (D : AtomicDesign (BoundarySpaceW1 n)), BoundaryMassW1 n D → BoundaryMarginsW1 n D

/-- Compute the actual finite-population targets. The partner's conditional probabilities
are 3/4 and 1/4. Only the first two EEDs are nonzero, each 1/(2(n+2)); averaging gives
1/(n+2)^2. Every own-coordinate raw hybrid contrast vanishes pointwise. Prove by two-coordinate
summation and split the unit sum into indices 0,1 and the rest. No direct target is stipulated. -/
def T5_L2 : Prop :=
  ∀ (n : ℕ) (D : AtomicDesign (BoundarySpaceW1 n)),
    BoundaryMassW1 n D → BoundaryMarginsW1 n D → BoundaryTargetsW1 n D

/-- A fair first bit gives the exact score law, estimator mean and variance, and unequal
boundary coverages. Split its two values. At score +1, [estimate-s,estimate+s] starts at the
positive target and excludes zero; at score -1 it contains zero. Both contain the target.
Use 0<1/(n+2)<=1/2, so the small positive drift is strictly below one. Bounded test functions
need no extra moment hypotheses because the assignment space is finite. -/
def T5_L3 : Prop :=
  ∀ (n : ℕ) (D : AtomicDesign (BoundarySpaceW1 n)),
    BoundaryMarginsW1 n D → BoundaryStatisticW1 n D

/-- The explicit endpoint counterexample satisfies the full printed transfer hypotheses. -/
theorem T5_assembly (h1 : T5_L1) (h2 : T5_L2) (h3 : T5_L3) :
    T5WholeStatement := by
  let : IsProbabilityMeasure fairSignLawW1 := fair_law_probabilityW1
  let D := boundaryDesignW1
  have hmass : ∀ n, BoundaryMassW1 n (D n) := fun _ _ => rfl
  have hmargin (n : ℕ) := h1 n (D n) (hmass n)
  have htarget (n : ℕ) := h2 n (D n) (hmass n) (hmargin n)
  have hstat (n : ℕ) := h3 n (D n) (hmargin n)
  have hT (n : ℕ) := (htarget n).2.2.2.1
  have hA (n : ℕ) := (htarget n).2.2.2.2
  have hfirst : weakLimit D (fun n z => (boundaryEstimatorW1 n z -
      populationContrast (D n) (boundaryExposureW1 n) (boundaryResponsesW1 n) 1 0)/
        boundaryScaleW1 n) fairSignLawW1 := by
    intro f
    simp_rw [hT]
    have he : (fun n => mean (D n) (fun z =>
        f ((boundaryEstimatorW1 n z-boundaryTargetW1 n)/boundaryScaleW1 n))) =
        fun _ => (f (-1)+f 1)/2 := funext fun n => (hstat n).2.2.1 f
    rw [he, fair_law_integralW1]
    exact tendsto_const_nhds
  have hgap : Tendsto (fun n =>
      (populationContrast (D n) (boundaryExposureW1 n) (boundaryResponsesW1 n) 1 0 -
        boundaryDirectW1 n (D n))/boundaryScaleW1 n) atTop (𝓝 0) := by
    simp_rw [hT, hA, sub_zero]
    have he (n : ℕ) : boundaryTargetW1 n / boundaryScaleW1 n = boundaryScaleW1 n := by
      simpa only [abs_of_nonneg (show 0 ≤ boundaryTargetW1 n by unfold boundaryTargetW1; positivity)]
        using boundary_gap_ratioW1 n
    simp_rw [he]
    exact boundary_scale_limitW1
  have hcoverage (n : ℕ) :
      eventProbability (D n) (fun z => |boundaryEstimatorW1 n z -
        populationContrast (D n) (boundaryExposureW1 n) (boundaryResponsesW1 n) 1 0| ≤
          boundaryScaleW1 n) = 1 ∧
      eventProbability (D n) (fun z => |boundaryEstimatorW1 n z-boundaryDirectW1 n (D n)| ≤
          boundaryScaleW1 n) = 1/2 := by
    rw [hT, hA]
    simpa only [sub_zero] using (hstat n).2.2.2
  have hscale : probabilityLimit D (fun n _ => boundaryScaleW1 n / boundaryScaleW1 n) 1 := by
    intro ε hε
    have he : (fun n => eventProbability (D n)
        (fun _ => |boundaryScaleW1 n/boundaryScaleW1 n-1| > ε)) = fun _ => 0 := by
      funext n
      simp [div_self (ne_of_gt (boundary_scale_posW1 n)), eventProbability, not_lt_of_ge hε.le]
    rw [he]
    exact tendsto_const_nhds
  refine ⟨inferInstance, D, fun n => ⟨hmass n, hmargin n, htarget n, hstat n⟩,
    boundary_scale_posW1, ?_, hfirst, hscale, ?_, ?_, hcoverage, ?_, ?_, by norm_num⟩
  · intro n
    exact ⟨fun _ => Summable.of_finite, fun _ => Summable.of_finite,
      fun _ => Summable.of_finite⟩
  · simpa only [hT, hA, sub_zero, boundary_gap_ratioW1] using boundary_scale_limitW1
  · have hd := AronowAudit.P061.inference_drift_transfer (fun n => Bridge.toProject (D n))
      boundaryEstimatorW1 (fun n _ => boundaryScaleW1 n)
      (fun n => populationContrast (D n) (boundaryExposureW1 n) (boundaryResponsesW1 n) 1 0)
      (fun n => boundaryDirectW1 n (D n)) boundaryScaleW1 fairSignLawW1 0
      boundary_scale_posW1 hfirst hscale hgap
    have he : AronowAudit.P061.shiftedLaw fairSignLawW1 0 = fairSignLawW1 := by
      unfold AronowAudit.P061.shiftedLaw
      simp only [add_zero]
      exact Measure.map_id
    rw [he] at hd
    exact hd
  · convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)) using 1
    funext n
    exact (hcoverage n).1
  · convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1/2 : ℝ)) atTop (𝓝 (1/2 : ℝ))) using 1
    funext n
    exact (hcoverage n).2

/-- A nondecaying alternating sequence of weighted atoms forces both full-domain sign
expectations to infinity. Restrict a hypothetical finite nonnegative ENNReal sum to the
injective subsequence k↦(k+1:ℝ), move the nonnegative mass inside max, and divide by c>0.
The resulting positive/negative alternating parts contradict divergent_parts_not_summable.
Equivalently use ENNReal.summable_toReal and Summable.comp_injective. The generic f need not
be integrable: extended nonnegative expectations are always defined. -/
def T7_L1 : Prop :=
  ∀ (D : AtomicDesign ℝ) (f : ℝ → ℝ) (c : ℝ), 0 < c →
    (∀ k : ℕ, D.mass ((k+1 : ℕ) : ℝ) * f ((k+1 : ℕ) : ℝ) = c*(-1 : ℝ)^k) →
    positiveExpectationW1 D f = ⊤ ∧ negativeExpectationW1 D f = ⊤

/-- The geometric witness, measure representation, ordered divergence and all existence
failures; the single new alternating-atoms lemma is reused for the raw numerator and HT. -/
theorem T7_assembly (h1 : T7_L1) : T7WholeStatement := by
  obtain ⟨D, hmass, hsupp, hpos1, hpos0, hmissing, hzero, hterm, hpartial,
    hplus, hminus, hformula, hestterm, hestplus, hestminus⟩ := Bridge.divergent_correspondence
  have hbase : GeometricBaseW1 D := ⟨hmass, hsupp, hpos1, hpos0, hmissing,
    hzero, hterm, hpartial, hplus, hminus, hformula, hestterm, hestplus, hestminus⟩
  rcases hmissing with ⟨hpi1, hpi0, hmean0, hnotnum, hnotHT⟩
  let f : ℝ → ℝ := fun z => if integerExposure 0 z = 1 then integerResponse 0 z else 0
  have hraw : positiveExpectationW1 D f = ⊤ ∧ negativeExpectationW1 D f = ⊤ := by
    apply h1 D f 1 (by norm_num)
    intro k
    have hg : integerExposure 0 ((k+1 : ℕ) : ℝ) = 1 := by
      simp only [integerExposure, Function.Injective.extend_apply Nat.cast_injective,
        Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
    simpa only [f, hg, ite_true, one_mul, integerResponseTerm] using hterm k
  have hHT : positiveExpectationW1 D (estimateExposureMean D integerExposure integerResponse 1) = ⊤ ∧
      negativeExpectationW1 D (estimateExposureMean D integerExposure integerResponse 1) = ⊤ :=
    h1 D _ 2 (by norm_num) hestterm
  have hnmean : ¬HasMean D f := by
    intro hm
    exact hnotnum (AronowAudit.P061.integrable_summable (Bridge.toProject D) hm)
  have hnoepo : ¬∃ a, OrdinaryEPOW1 D integerExposure integerResponse 0 1 a := by
    rintro ⟨a, _, hm, _⟩
    exact hnmean hm
  have hnoaepo : ¬∃ a, OrdinaryAEPOW1 D integerExposure integerResponse 1 a := by
    rintro ⟨a, _, u, hu, _⟩
    exact hnoepo ⟨u 0, hu 0⟩
  have hnoeed : ¬∃ a, OrdinaryEEDW1 D integerExposure integerResponse 0 1 0 a := by
    rintro ⟨a, u, v, hu, _, _⟩
    exact hnoepo ⟨u, hu⟩
  have hnoaeed : ¬∃ a, OrdinaryAEEDW1 D integerExposure integerResponse 1 0 a := by
    rintro ⟨a, u, v, hu, _, _⟩
    exact hnoaepo ⟨u, hu⟩
  refine ⟨D, hbase, atomic_probabilityW1 D, atomic_eventW1 D, atomic_event_realW1 D,
    real_vector_bijectiveW1, ?_, hraw.1, hraw.2, ?_, ?_, ?_, ?_, hnoepo, hnoaepo,
    hnoeed, hnoaeed, ⟨by rw [hpi0]; norm_num, hzero, hmean0⟩,
    hHT.1, hHT.2, ?_, ?_, ?_⟩
  · rintro ⟨a, ha⟩
    have heven : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
      tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
    have hodd : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
      tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
    have h0 := ha.comp heven
    have h1 := ha.comp hodd
    have e0 : (fun n : ℕ => ∑ k ∈ Finset.range (2*n), integerResponseTerm D k) = fun _ => 0 :=
      funext fun n => (hpartial n).2.2.2.1
    have e1 : (fun n : ℕ => ∑ k ∈ Finset.range (2*n+1), integerResponseTerm D k) = fun _ => 1 :=
      funext fun n => (hpartial n).2.2.2.2
    simp only [Function.comp_def, e0] at h0
    simp only [Function.comp_def, e1] at h1
    have ha0 : a = 0 := tendsto_nhds_unique h0 tendsto_const_nhds
    have ha1 : a = 1 := tendsto_nhds_unique h1 tendsto_const_nhds
    linarith
  · rw [atomic_positive_integralW1]
    exact hraw.1
  · rw [atomic_positive_integralW1]
    exact hraw.2
  · rw [conditional_positive_integralW1]
    change (ENNReal.ofReal (exposureProbability D integerExposure 0 1))⁻¹ *
      positiveExpectationW1 D f = ⊤
    rw [hpi1, hraw.1]
    norm_num
  · rw [conditional_positive_integralW1]
    have he : (fun z => if integerExposure 0 z = 1 then -integerResponse 0 z else 0) =
        fun z => -f z := by
      funext z
      dsimp [f]
      split_ifs <;> simp
    rw [he]
    change (ENNReal.ofReal (exposureProbability D integerExposure 0 1))⁻¹ *
      negativeExpectationW1 D f = ⊤
    rw [hpi1, hraw.2]
    norm_num
  · rw [atomic_positive_integralW1]
    exact hHT.1
  · rw [atomic_positive_integralW1]
    exact hHT.2
  · rintro ⟨a, hm, _⟩
    exact hnotHT hm

end SAP.P061a.WH.W1
