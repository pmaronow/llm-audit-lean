import SAP.P008b.Defs.WholeW2
import SAP.P008b.Bridge
import AronowAudit.P008.P008_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b.WH.W2

open scoped BigOperators
open MeasureTheory Filter

noncomputable section

/-- Rational enclosures of the supplied kernel, and a value strictly below
minus 21/50 at radius one. Prove the radius-one bound with
Real.exp_one_gt_d9 and Real.exp_one_lt_d9, rewriting exp(-2) and exp(-4)
as inverse powers of exp(1). For radii 1/10, 6/5 and 2 use rational Taylor
enclosures (Real.exp_bound or Real.exp_bound'), exp_nat_mul and exp_neg,
then clear positive denominators and finish with rational arithmetic. Taylor
order 12 encloses exp(1/5) between 1.221402758 and 1.221402759, and exp(3/5)
between 1.822118800 and 1.822118801. For the four radii use inverse powers
(1,2), (2,4), (4,8), (4,8) of exp(1/5), exp(1), exp(3/5), exp(1), respectively.
This concerns values of the supplied function, without identifying a figure's
unprovided sampling weights. One enclosure per radius is sufficient. -/
def T18_L1 : Prop :=
  toyKernel 1 < -(21 / 50 : ℝ) ∧
  |toyKernel (1 / 10) - 163 / 100| < 1 / 200 ∧
  |toyKernel (6 / 5) + 55 / 100| < 1 / 200 ∧
  |toyKernel 2 + 19 / 100| < 1 / 200

/-- Finite marginalization commutes with a genuine normalized circle integral,
for any chosen distance and a circle-local measure. Generalize
AronowAudit.P008.circle_marginal_identity and circle_effect_identity: expand the
finite expectations, use weighted_integrable for zero-mass summands,
integral_finsetSum and integral_const_mul, then integral_sub. The positivity,
finiteness and concentration premises record that the average is defined;
the integral calculation itself uses only the stated integrability premises.
No ambient-field measurability or geometric property of the distance is needed. -/
def T27_L1 : Prop :=
  ∀ (N : ℕ) (P : SpatialModel N) (Q : FiniteLaw (Assignment N))
      (ρ : Plane → Plane → ℝ) (i : Fin N) (d : ℝ),
    P.validSelectedCircle ρ Q i d →
    P.selectedNodeEffect ρ Q i d = P.selectedAverage ρ i d (P.pointEffect Q i)

private theorem t17_existing : T17Statement := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact AronowAudit.P008.distance_to_circle
  · exact AronowAudit.P008.positive_radius_band_geometry
  · norm_num
  · intro N P i d
    rfl
  · intro X _ B Y
    constructor
    · intro _
      rfl
    · intro j hj hs hc
      rw [bufferRule, ite_eq_right (Nat.ne_of_gt hj)]
      exact AronowAudit.P008.nested_buffer_average (B (j - 1)) (B j) Y hs hc
  · intro X C ρ Y a b _ hab hc
    have hs : distanceBuffer C ρ a ⊆ distanceBuffer C ρ b := by
      intro x hx
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.trans hab.le⟩
    have he : distanceBuffer C ρ b \ distanceBuffer C ρ a =
        C.filter (fun x => a < ρ x ∧ ρ x ≤ b) := by
      ext x
      simp only [distanceBuffer, Finset.mem_sdiff, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hx, hb⟩, ha⟩
        exact ⟨hx, lt_of_not_ge (fun h => ha ⟨hx, h⟩), hb⟩
      · rintro ⟨hx, ha, hb⟩
        exact ⟨⟨hx, hb⟩, fun h => (not_le_of_gt ha) h.2⟩
    refine ⟨?_, by ring, by ring, by linarith, by linarith⟩
    calc
      _ = countMean (distanceBuffer C ρ b \ distanceBuffer C ρ a) Y :=
        AronowAudit.P008.nested_buffer_average _ _ Y hs hc
      _ = _ := congrArg (fun s => countMean s Y) he

/-- Assemble the circle geometry and nested-buffer donors, and prove the
polygon selector and mode reductions directly. No new mathematics is deferred. -/
theorem T17_assembly : T17WholeStatement := by
  classical
  refine ⟨t17_existing, ?_⟩
  intro X C centroid P Y r hclosed hnonempty
  have hz : polygonFullBuffer C centroid P 0 = C.filter (fun c => centroid c ∈ P) := by
    ext c
    simp only [polygonFullBuffer, distanceBuffer, Finset.mem_filter]
    have he : Metric.infDist (centroid c) P ≤ 0 ↔ centroid c ∈ P := by
      rw [hclosed.mem_iff_infDist_zero hnonempty]
      exact ⟨fun h => le_antisymm h Metric.infDist_nonneg, fun h => h.le⟩
    rw [he]
  refine ⟨hz, ?_, ?_, ?_, ?_⟩
  · intro j _
    simp [archivedPolygonSummary]
  · intro _
    simp [archivedPolygonSummary]
  · intro hr _
    simp [archivedPolygonSummary, hr, hz]
  · intro j hj _ hinc hcard
    have hs : polygonFullBuffer C centroid P (r (j - 1)) ⊆
        polygonFullBuffer C centroid P (r j) := by
      intro c hc
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hc).1, (Finset.mem_filter.mp hc).2.trans hinc.le⟩
    have hdiff : polygonFullBuffer C centroid P (r j) \
        polygonFullBuffer C centroid P (r (j - 1)) =
        C.filter (fun c => r (j - 1) < Metric.infDist (centroid c) P ∧
          Metric.infDist (centroid c) P ≤ r j) := by
      ext c
      simp only [polygonFullBuffer, distanceBuffer, Finset.mem_sdiff, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hc, hb⟩, ha⟩
        exact ⟨hc, lt_of_not_ge (fun h => ha ⟨hc, h⟩), hb⟩
      · rintro ⟨hc, ha, hb⟩
        exact ⟨⟨hc, hb⟩, fun h => (not_le_of_gt ha) h.2⟩
    have havg : archivedPolygonSummary .donut
        (fun j => polygonFullBuffer C centroid P (r j)) Y j =
        countMean (polygonFullBuffer C centroid P (r j) \
          polygonFullBuffer C centroid P (r (j - 1))) Y := by
      rw [archivedPolygonSummary, ite_eq_left ⟨rfl, Nat.ne_of_gt hj⟩]
      exact AronowAudit.P008.nested_buffer_average _ _ Y hs hcard
    exact ⟨havg, hdiff ▸ havg, by ring, by ring, by linarith, by linarith⟩

private theorem t18_existing : T18Statement := by
  refine ⟨?_, by norm_num, ?_⟩
  · intro r hr
    exact (AronowAudit.P008.toy_kernel_lower_bound r hr).1
  · intro C Q base r w hw hs hr
    obtain ⟨hswitch, hpoint, hformula, hscale, hb⟩ :=
      AronowAudit.P008.toy_raster_amr_formula (Bridge.law Q) base r w hw hs hr
    have hbound : -(384 / 437 : ℝ) < toyRasterAMR Q 1 base r w := hb
    exact ⟨hswitch, hpoint, hformula, hscale, hbound, by linarith, by linarith⟩

/-- Assemble the existing additive AMR proof and global lower bound. The
derivative, maximum, Taylor computation, nonmonotonicity and convex compatibility
are short direct arguments; only rational exponential enclosures are deferred. -/
theorem T18_assembly (h1 : T18_L1) : T18WholeStatement := by
  obtain ⟨hf1, hnum⟩ := h1
  have hf0 : toyKernel 0 = 2 := by norm_num [toyKernel]
  have hgamma : ∀ r : ℝ, 0 ≤ r → toyKernel r =
      ProbabilityTheory.gammaPDFReal 1 2 r - ProbabilityTheory.gammaPDFReal 5 4 r := by
    intro r hr
    have hg : Real.Gamma 5 = 24 := by
      convert Real.Gamma_nat_eq_factorial 4 using 1 <;> norm_num [Nat.factorial]
    norm_num [ProbabilityTheory.gammaPDFReal, hr, Real.Gamma_one, hg,
      show (5 - 1 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast, toyKernel]
  have hderiv : ∀ r : ℝ, HasDerivAt toyNegativeKernel
      ((512 / 3) * r ^ 3 * (1 - r) * Real.exp (-4 * r)) r := by
    intro r
    have h := (((hasDerivAt_id r).pow 4).const_mul (128 / 3 : ℝ)).mul
      (((hasDerivAt_id r).const_mul (-4 : ℝ)).exp)
    simp only [id_eq, Pi.pow_apply] at h
    convert h using 1 <;> first | rfl | ring
  have hone : toyNegativeKernel 1 = 128 / (3 * Real.exp 4) := by
    norm_num [toyNegativeKernel, Real.exp_neg]
    ring
  have hmax : ∀ r : ℝ, 0 ≤ r → 0 ≤ toyNegativeKernel r ∧
      toyNegativeKernel r ≤ toyNegativeKernel 1 := by
    intro r hr
    have hp : (r * Real.exp (-r)) ^ 4 ≤ (Real.exp (-1)) ^ 4 := by
      gcongr
      exact Real.mul_exp_neg_le_exp_neg_one r
    have he (x : ℝ) : (Real.exp (-x)) ^ 4 = Real.exp (-4 * x) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [mul_pow, he, he] at hp
    constructor
    · unfold toyNegativeKernel
      positivity
    · simpa only [toyNegativeKernel, one_pow, mul_one, mul_assoc] using
        mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 128 / 3)
  have htaylor : (∑ k ∈ Finset.range 7, (4 : ℝ) ^ k / (Nat.factorial k : ℝ)) = 437 / 9 ∧
      (437 / 9 : ℝ) < Real.exp 4 := by
    constructor
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num) 8
      norm_num [Finset.sum_range_succ, Nat.factorial] at h
      linarith
  have hh : ∀ r : ℝ, 0 ≤ r → toyNegativeKernel r < 384 / 437 := by
    intro r hr
    have hi : (Real.exp 4)⁻¹ < (437 / 9 : ℝ)⁻¹ := by
      simpa only [one_div] using
        one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 437 / 9) htaylor.2
    calc
      _ ≤ toyNegativeKernel 1 := (hmax r hr).2
      _ = (128 / 3 : ℝ) * (Real.exp 4)⁻¹ := by rw [hone]; ring
      _ < 384 / 437 := by norm_num at hi ⊢; linarith
  have hnonmono : ¬ MonotoneOn toyKernel (Set.Ici 0) ∧
      ¬ AntitoneOn toyKernel (Set.Ici 0) := by
    constructor
    · intro hm
      have h := hm (show (0 : ℝ) ∈ Set.Ici 0 by simp)
        (show (1 : ℝ) ∈ Set.Ici 0 by norm_num) (by norm_num : (0 : ℝ) ≤ 1)
      rw [hf0] at h
      linarith
    · intro ha
      have h := ha (show (1 : ℝ) ∈ Set.Ici 0 by norm_num)
        (show (2 : ℝ) ∈ Set.Ici 0 by norm_num) (by norm_num : (1 : ℝ) ≤ 2)
      have h2 := (abs_lt.mp hnum.2.2).1
      linarith
  have hcompat : ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      3 * (t * toyKernel 1 + (1 - t) * toyKernel 0) = -63 / 50 := by
    have hd : 0 < 2 - toyKernel 1 := by linarith
    refine ⟨(121 / 50) / (2 - toyKernel 1), by positivity, ?_, ?_⟩
    · apply (div_lt_one hd).mpr
      linarith
    · rw [hf0]
      field_simp
      ring
  exact ⟨t18_existing, hgamma, hderiv, ⟨hmax, hone⟩, htaylor, hh, hnonmono, hnum, hcompat⟩

/-- Identify additive point effects with the existing donor, then use the
single local integration leaf. Coefficients are constant on homogeneous
circles, so their normalized integral and the finite node average reduce
directly to g(d). -/
theorem T27_assembly (h1 : T27_L1) : T27WholeStatement := by
  have hadditive : ∀ (N : ℕ) (P : SpatialModel N) (Q : FiniteLaw (Assignment N))
      (ρ : Plane → Plane → ℝ) (base : Plane → ℝ) (g : Fin N → Plane → ℝ),
      (∀ x ∈ P.field, ∀ z, P.Y x z = additiveOutcome base g x z) →
      (∀ i x, x ∈ P.field → P.pointEffect Q i x = g i x) ∧
      (∀ i d, P.validSelectedCircle ρ Q i d →
        P.selectedNodeEffect ρ Q i d = P.selectedAverage ρ i d (g i)) ∧
      (∀ d, 0 < N → (∀ i, P.validSelectedCircle ρ Q i d) →
        P.selectedAMR ρ Q d = (N : ℝ)⁻¹ * ∑ i, P.selectedAverage ρ i d (g i)) := by
    intro N P Q ρ base g ha
    have hpoint : ∀ i x, x ∈ P.field → P.pointEffect Q i x = g i x := by
      intro i x hx
      exact AronowAudit.P008.additive_point_effect (Bridge.model P) (Bridge.law Q)
        base g ha i x hx
    have hnode : ∀ i d, P.validSelectedCircle ρ Q i d →
        P.selectedNodeEffect ρ Q i d = P.selectedAverage ρ i d (g i) := by
      intro i d hv
      rw [h1 N P Q ρ i d hv]
      unfold SpatialModel.selectedAverage
      congr 1
      apply integral_congr_ae
      filter_upwards [hv.2.2.1] with x hx
      exact hpoint i x hx.1
    refine ⟨hpoint, hnode, ?_⟩
    intro d _ hv
    unfold SpatialModel.selectedAMR
    simp_rw [hnode _ _ (hv _)]
  refine ⟨hadditive, ?_⟩
  intro N P Q ρ base g ha
  obtain ⟨hpoint, hnode, _⟩ := hadditive N P Q ρ base (fun i x => g (ρ (P.node i) x)) ha
  have hhom : ∀ i d, P.validSelectedCircle ρ Q i d →
      P.selectedNodeEffect ρ Q i d = g d := by
    intro i d hv
    rw [hnode i d hv]
    have he : (fun x => g (ρ (P.node i) x)) =ᵐ[P.selectedMeasure ρ i d]
        (fun _ => g d) := by
      filter_upwards [hv.2.2.1] with x hx
      exact congrArg g hx.2
    unfold SpatialModel.selectedAverage
    rw [integral_congr_ae he, integral_const]
    change ((P.selectedMeasure ρ i d) Set.univ).toReal⁻¹ *
      (((P.selectedMeasure ρ i d) Set.univ).toReal * g d) = g d
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hv.1), one_mul]
  refine ⟨hpoint, hhom, ?_⟩
  intro d hN hv
  unfold SpatialModel.selectedAMR
  simp_rw [hhom _ _ (hv _)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast (Nat.ne_zero_of_lt hN)), one_mul]

end

end SAP.P008b.WH.W2
