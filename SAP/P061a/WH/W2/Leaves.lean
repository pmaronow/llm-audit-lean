import SAP.P061a.Defs.WholeW2
import SAP.P061a.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a.WH.W2

open scoped BigOperators Topology Classical BoundedContinuousFunction MeasureTheory
open Filter

/-- Finite-support fiber calculus for an arbitrary atomic design.
If W has supported values in the finite nonempty set K, every real function
of W has a finite event-restricted absolute moment, and its expectation is
the finite sum over K of its value times the event-and-fiber probability.
Proof route: a fiber outside K has zero probability, by the support hypothesis
and zero mass off support. Thus the weighted absolute fiber masses have finite
support. Apply AronowAudit.P061.integrable_fiber_iff, then
AronowAudit.P061.expectation_fibers, and restrict the last sum to K.
This intermediate proposition does not assume finite assignment
support, a finite global alphabet, or a full product feasible set. -/
def FiniteFiberCalculusW2 : Prop :=
  ∀ (Ω B : Type) (D : AtomicDesign Ω) (W : Ω → B) (K : Finset B),
    K.Nonempty → (∀ z, supported D z → W z ∈ K) →
    ∀ (E : Ω → Prop) (f : B → ℝ),
      HasMean D (fun z => if E z then f (W z) else 0) ∧
      mean D (fun z => if E z then f (W z) else 0) =
        ∑ x : K, eventProbability D (fun z => E z ∧ W z = x.val) * f x.val

/-- Discharge the finite-support step: fibers outside K have zero mass, so
the existing unrestricted fiber theorems reduce to finite sums. -/
theorem finite_fiber_calculusW2 : FiniteFiberCalculusW2 := by
  intro Ω B D W K _hK hW E f
  have hzero (b : B) (hb : b ∉ K) :
      eventProbability D (fun z => E z ∧ W z = b) = 0 := by
    unfold eventProbability
    calc
      _ = ∑' _z : Ω, (0 : ℝ) := by
        apply tsum_congr
        intro z
        by_cases hz : supported D z
        · have hne : W z ≠ b := fun h => hb (h ▸ hW z hz)
          simp only [hne, and_false, ite_false]
        · have hm : D.mass z = 0 := le_antisymm (le_of_not_gt hz) (D.mass_nonnegative z)
          simp only [hm, ite_self]
      _ = 0 := tsum_zero
  have hs : Summable (fun b =>
      eventProbability D (fun z => E z ∧ W z = b) * |f b|) := by
    apply summable_of_ne_finset_zero (s := K)
    intro b hb
    rw [hzero b hb, zero_mul]
  have hi : HasMean D (fun z => if E z then f (W z) else 0) :=
    (AronowAudit.P061.integrable_fiber_iff (Bridge.toProject D) E W f).mpr hs
  refine ⟨hi, ?_⟩
  have he : mean D (fun z => if E z then f (W z) else 0) =
      ∑' b, eventProbability D (fun z => E z ∧ W z = b) * f b :=
    AronowAudit.P061.expectation_fibers (Bridge.toProject D) E W f hi
  rw [he]
  rw [tsum_eq_sum (s := K) (fun b hb => by rw [hzero b hb, zero_mul])]
  exact (Finset.sum_coe_sort K _).symm

/-- Existing recentering, studentization, and continuity-set results supply
all statistical conclusions, without assumptions about individual hybrid means
or the sign of each estimated scale. -/
theorem inference_conclusionsW2 {Ω : ℕ → Type} (D : ∀ n, AtomicDesign (Ω n))
    (estimate estimatedScale : ∀ n, Ω n → ℝ) (T A s : ℕ → ℝ)
    (L : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure L]
    (hs : ∀ n, 0 < s n)
    (hfirst : weakLimit D (fun n z => (estimate n z - T n) / s n) L)
    (hscale : probabilityLimit D (fun n z => estimatedScale n z / s n) 1) :
    InferenceConclusionsW2 D estimate estimatedScale T A s L := by
  have hzero : translatedLaw L 0 = L := by simp [translatedLaw]
  have transfer (B : ℕ → ℝ) (c : ℝ)
      (hrate : Tendsto (fun n => (T n - B n) / s n) atTop (𝓝 c)) :
      weakLimit D (fun n z => (estimate n z - B n) / estimatedScale n z)
        (translatedLaw L c) :=
    AronowAudit.P061.inference_drift_transfer (fun n => Bridge.toProject (D n))
      estimate estimatedScale T B s L c hs hfirst hscale hrate
  have hT : weakLimit D (fun n z => (estimate n z - T n) / estimatedScale n z) L := by
    simpa only [hzero] using transfer T 0 (by simp)
  refine ⟨AronowAudit.P061.consistent_scale_nonpositive_probability
    (fun n => Bridge.toProject (D n)) estimatedScale s hs hscale, ?_, ?_⟩
  · intro hrate
    have hsigned := AronowAudit.P061.rate_bound_suffices T A
      (fun n => |T n - A n|) s hs (fun _ => le_rfl) hrate
    have hA : weakLimit D (fun n z => (estimate n z - A n) / estimatedScale n z) L := by
      simpa only [hzero] using transfer A 0 hsigned
    refine ⟨hA, hT, ?_⟩
    intro q hq hminus hplus
    constructor
    · exact AronowAudit.P061.weakConverges_scaled_interval
        (fun n => Bridge.toProject (D n)) (fun n z => estimate n z - A n)
        estimatedScale s L hs hscale hA q hq hplus hminus
    · exact AronowAudit.P061.weakConverges_scaled_interval
        (fun n => Bridge.toProject (D n)) (fun n z => estimate n z - T n)
        estimatedScale s L hs hscale hT q hq hplus hminus
  · intro c _hc hrate
    exact transfer A c hrate

/-- Instantiate the statistical argument with the paper's actual centers. -/
theorem population_inferenceW2 : T5PopulationInferenceW2 := by
  intro S D y d d' estimate estimatedScale s L _inst _hdom hs hfirst hscale
  exact inference_conclusionsW2 D estimate estimatedScale _ _ s L hs hfirst hscale

/-- The normalization part of finite fiber calculus is just its constant-one instance. -/
theorem finite_probability_sumW2 (h1 : FiniteFiberCalculusW2)
    {Ω B : Type} (D : AtomicDesign Ω) (W : Ω → B) (K : Finset B)
    (hK : K.Nonempty) (hW : ∀ z, supported D z → W z ∈ K) (E : Ω → Prop) :
    (∑ x : K, eventProbability D (fun z => E z ∧ W z = x.val)) =
      eventProbability D E := by
  have h := (h1 Ω B D W K hK hW E (fun _ => 1)).2
  have he : mean D (fun z => if E z then (1 : ℝ) else 0) = eventProbability D E := by
    simp only [mean, eventProbability, mul_ite, mul_one, mul_zero]
  simpa only [mul_one] using h.symm.trans he

/-- In its own conditioning cell the raw hybrid is the observed response. -/
theorem hybrid_ownW2 {N : ℕ} {S : Set (Fin N → ℝ)} (y : Responses S N)
    (i : Fin N) (e : ℝ) (z : S) (hz : z.val i = e) :
    hybridResponse S y i e z = y i z := by
  have hv : insertCoordinate i e (otherCoordinates z.val i) = z.val := by
    rw [← hz]
    exact AronowAudit.P061.fromOthers_reconstruct z.val i
  simp [hybridResponse, hv]

/-- Glue for a single local response: finite fiber calculus gives the two finite-law means
and their normalizations; the existing sharp range-times-TV theorem bounds them.
Only equality on design support is used when replacing the actual response. -/
theorem unit_neighborhood_boundW2 (h1 : FiniteFiberCalculusW2) {N : ℕ}
    {S : Set (Fin N → ℝ)} (D : AtomicDesign S) (y : Responses S N)
    (i : Fin N) (e : ℝ) (H : Finset (Fin N))
    (K : Finset (Neighborhood ℝ H)) (C : Set (Neighborhood ℝ H))
    (f : Neighborhood ℝ H → ℝ) (hK : K.Nonempty)
    (hKC : ∀ x, x ∈ K → x ∈ C)
    (hW : ∀ z, supported D z → neighborhoodVectorW2 H z ∈ K)
    (hext : HasExtremaW2 f C)
    (hp : 0 < exposureProbability D (coordinateExposure S) i e)
    (hy : ∀ z, supported D z → hybridResponse S y i e z = f (neighborhoodVectorW2 H z)) :
    HasMean D (hybridResponse S y i e) ∧
    |exposureMean D (coordinateExposure S) y i e - mean D (hybridResponse S y i e)| ≤
      responseRangeOnW2 f C * variationDistance
        (fun x : K => conditionalNeighborhoodMassW2 D i H e x.val)
        (fun x : K => neighborhoodMassW2 D H x.val) := by
  let W := neighborhoodVectorW2 (S := S) H
  let E := fun z : S => z.val i = e
  let P := fun x : K => neighborhoodMassW2 D H x.val
  let Q := fun x : K => conditionalNeighborhoodMassW2 D i H e x.val
  have hall := h1 S (Neighborhood ℝ H) D W K hK hW (fun _ => True) f
  have hcond := h1 S (Neighborhood ℝ H) D W K hK hW E f
  have hf : HasMean D (fun z => f (W z)) := by simpa only [ite_true] using hall.1
  have hhy : HasMean D (hybridResponse S y i e) :=
    (AronowAudit.P061.integrable_support_congr (Bridge.toProject D) _ _ hy).mpr hf
  have hP : (∑ x : K, P x * f x.val) = mean D (hybridResponse S y i e) := by
    have hh : mean D (hybridResponse S y i e) = mean D (fun z => f (W z)) :=
      AronowAudit.P061.expectation_support_congr (Bridge.toProject D) _ _ hy
    rw [hh]
    simpa only [ite_true, true_and, P, neighborhoodMassW2, W] using hall.2.symm
  have hraw : ∀ z, supported D z →
      (if coordinateExposure S i z = e then y i z else 0) =
        (if E z then f (W z) else 0) := by
    intro z hz
    by_cases he : z.val i = e
    · simp only [coordinateExposure, E, he, ite_true]
      exact (hybrid_ownW2 y i e z he).symm.trans (hy z hz)
    · simp only [coordinateExposure, E, he, ite_false]
  have hQ : (∑ x : K, Q x * f x.val) = exposureMean D (coordinateExposure S) y i e := by
    unfold exposureMean
    have hh : mean D (fun z => if coordinateExposure S i z = e then y i z else 0) =
        mean D (fun z => if E z then f (W z) else 0) :=
      AronowAudit.P061.expectation_support_congr (Bridge.toProject D) _ _ hraw
    rw [hh, hcond.2]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _hx
    dsimp [Q, conditionalNeighborhoodMassW2, E, W]
    ring
  have hPsum : ∑ x : K, P x = 1 := by
    have hh := finite_probability_sumW2 h1 D W K hK hW (fun _ => True)
    have ht : eventProbability D (fun _ => True) = 1 := by
      simpa only [eventProbability, ite_true] using D.mass_total
    simpa only [true_and, P, neighborhoodMassW2, W, ht] using hh
  have hQsum : ∑ x : K, Q x = 1 := by
    have hh := finite_probability_sumW2 h1 D W K hK hW E
    change (∑ x : K, eventProbability D (fun z => E z ∧ W z = x.val) /
      exposureProbability D (coordinateExposure S) i e) = 1
    rw [← Finset.sum_div, hh]
    exact div_self hp.ne'
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hext
  have hbounds (x : K) : sInf (f '' C) ≤ f x.val ∧ f x.val ≤ sSup (f '' C) := by
    rw [ha.csInf_eq, hb.csSup_eq]
    exact ⟨ha.2 ⟨x.val, hKC x.val x.property, rfl⟩,
      hb.2 ⟨x.val, hKC x.val x.property, rfl⟩⟩
  have htv := AronowAudit.P061.expectation_total_variation Q P (fun x => f x.val)
    (sInf (f '' C)) (sSup (f '' C))
    (fun x => div_nonneg (AronowAudit.P061.probability_nonneg (Bridge.toProject D) _) hp.le)
    (fun x => AronowAudit.P061.probability_nonneg (Bridge.toProject D) _)
    hQsum hPsum hbounds
  rw [hQ, hP] at htv
  exact ⟨hhy, htv⟩

/-- Sum the two unit bounds, using the existing linearity theorem only after
the finite-neighborhood argument has supplied separate hybrid moments. -/
theorem neighborhood_boundW2 (h1 : FiniteFiberCalculusW2) : T5NeighborhoodBoundW2 := by
  intro N S D y d d' H K C f _hN _hH hK hKC hW hext hp _hfeas hy
  have hunit (i : Fin N) (e : ℝ) (he : e = d ∨ e = d') :=
    unit_neighborhood_boundW2 h1 D y i e (H i) (K i) (C i) (f i e)
      (hK i) (hKC i) (hW i) (hext i e he)
      (by rcases he with rfl | rfl; exact (hp i).1; exact (hp i).2) (hy i e he)
  have hsub (i : Fin N) :
      mean D (fun z => hybridResponse S y i d z - hybridResponse S y i d' z) =
        mean D (hybridResponse S y i d) - mean D (hybridResponse S y i d') :=
    AronowAudit.P061.expectation_sub (Bridge.toProject D)
      (hunit i d (Or.inl rfl)).1 (hunit i d' (Or.inr rfl)).1
  have halg : populationContrast D (coordinateExposure S) y d d' -
      averageDirectContrast S D y d d' =
      (N : ℝ)⁻¹ * ∑ i,
        ((exposureMean D (coordinateExposure S) y i d - mean D (hybridResponse S y i d)) -
         (exposureMean D (coordinateExposure S) y i d' - mean D (hybridResponse S y i d'))) := by
    simp only [populationContrast, populationExposureMean, averageDirectContrast,
      hsub, Finset.sum_sub_distrib]
    ring
  rw [halg, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _hi
  exact (abs_sub _ _).trans
    (add_le_add (hunit i d (Or.inl rfl)).2 (hunit i d' (Or.inr rfl)).2)

/-- The absolute-gap version of the already proved sufficient-rate inequality. -/
theorem rate_sufficesW2 : T5RateSufficesW2 := by
  intro T A bound s hs hb hr
  have h := (AronowAudit.P061.rate_bound_suffices T A bound s hs hb hr).abs
  simpa only [abs_div, abs_of_pos (hs _), abs_zero] using h

/-- Restore the T4 witness and take the square root of its diverging squared
standardized gap; positivity identifies this with the printed absolute ratio. -/
theorem rate_exampleW2 : T5RateExampleW2 := by
  obtain ⟨D, hmass, hfacts, hgap, _hvar, hsq, hcov⟩ := Bridge.pair_inference_correspondence
  refine ⟨D, hmass, hfacts, hgap, ?_, hcov⟩
  have hpos (n : ℕ) : 0 < pairStandardError (n+2) (D (n+2)) :=
    (hfacts (n+2) (by omega)).2
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_div, abs_of_pos (hpos _)] using
    Real.tendsto_sqrt_atTop.comp hsq

/-- All clauses of the corrected claim, with every step proved and no leaves
remaining for downstream writers. -/
theorem T5_assembly : T5WholeStatement_W2 := by
  refine ⟨population_inferenceW2, neighborhood_boundW2 finite_fiber_calculusW2,
    rate_sufficesW2, rate_exampleW2, ?_⟩
  intro L _inst q
  simp

end SAP.P061a.WH.W2
