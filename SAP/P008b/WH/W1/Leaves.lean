import SAP.P008b.Defs.WholeW1
import SAP.P008b.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b.WH.W1

open scoped BigOperators
open MeasureTheory

noncomputable section

/-- The genuine counting-measure three-point cancellation example. Its only
existing circle averages have radii zero and one, and both averages are zero
under either assignment. Prove the distance table with
AronowAudit.P008.line_embedding_distance; identify the circles as {1} and
{0,2}, and the remaining circles as empty. Use count_apply_finite,
setIntegral_finset, and integrability on a finite set with finite singleton
masses. All assignments, including both overrides, are integrable. This is a
finite measured-field realization, not a claim about empty-circle AMRs. -/
def T26_L1 : Prop :=
  (∀ (Q : FiniteLaw (Assignment 1)) (d : ℝ),
    wholeCancellingModel.validCircle Q 0 d ↔ d = 0 ∨ d = 1) ∧
  (∀ z : Assignment 1,
    wholeCancellingModel.M 0 0 z = 0 ∧ wholeCancellingModel.M 0 1 z = 0)

/-- The specified square centers are exactly 1/8 from their actual topological
boundaries, and those boundaries are nonempty. Prove that the boundary of the
closed coordinate square is its four sides, using continuity of coordinate
projections and strict coordinate inequalities for the interior. Each side
point is at least 1/8 from the center by PiLp.norm_apply_le; the right-side
midpoint attains 1/8 by EuclideanSpace.dist_sq_eq. Conclude with
Metric.le_infDist and Metric.infDist_le_dist_of_mem. Translation handles both
centers. No assertion about external software execution is involved. -/
def T16_L1 : Prop :=
  ∀ i : Fin 2, (frontier (wholeSquare i)).Nonempty ∧
    Metric.infDist (wholeSquareCenter i) (frontier (wholeSquare i)) = 1 / 8

theorem T22_assembly : T22WholeStatement := by
  classical
  let P : SpatialModel 4 := {
    field := AronowAudit.P008.validatorRectangleModel.field
    node := AronowAudit.P008.validatorRectangleModel.node
    node_mem := AronowAudit.P008.validatorRectangleModel.node_mem
    ζ := AronowAudit.P008.validatorRectangleModel.ζ
    Y := AronowAudit.P008.validatorRectangleModel.Y }
  obtain ⟨_, _, hv, hs, hm, hstat, hq, hlo, hhi, hp, hgt⟩ :=
    AronowAudit.P008.spatial_percentile_counterexample
  have hmono (j : Fin 5) : Monotone (AronowAudit.P008.validatorRectangleStatistic j) := by
    intro a b hab
    rw [hstat j a, hstat j b]
    fin_cases a <;> fin_cases b <;> norm_num [Fin.le_def] at hab <;>
      norm_num [AronowAudit.P008.percentileExample]
  refine ⟨?_, ?_, AronowAudit.P008.printed_toy_rule_rejects⟩
  · refine ⟨P, AronowAudit.P008.sixAssignment, AronowAudit.P008.six_support.1,
      AronowAudit.P008.six_support.2.1, ?_, ?_, ?_, hm, ?_, ?_, hlo, hhi, hp, hgt⟩
    · intro k
      exact ⟨(AronowAudit.P008.contrast_is_hajek (fun _ => 0) k).1,
        (AronowAudit.P008.contrast_is_hajek (fun _ => 0) k).2.1⟩
    · intro x _ z
      exact hs x z
    · intro i j
      exact hv i j
    · intro j
      exact ⟨hmono j, (hq j).1, (hq j).2.1, (hq j).2.2⟩
    · intro a b hab
      exact Finset.sum_le_sum (fun j _ => hmono j hab)
  · intro R hR
    have hr : (1 : ℝ) ≤ R.card := by exact_mod_cast hR.card_pos
    have he : (uniformLaw (Fin 6)).prob (fun k => k ∈ R) = (R.card : ℝ) / 6 := by
      simp [FiniteLaw.prob, uniformLaw, div_eq_mul_inv]
    rw [he]
    constructor <;> linarith

theorem T25_assembly : T25WholeStatement := by
  have hlinear (X : Type) [MeasurableSpace X] (μ : Measure X) (N : ℕ)
      (Q : FiniteLaw (Assignment N)) (Y : X → Assignment N → ℝ)
      (i : Fin N) (b : Bool) (c : ℝ)
      (hint : ∀ z, Q.mass z ≠ 0 → Integrable (fun x => Y x (Function.update z i b)) μ) :
      Integrable (fun x => marginal Q (Y x) i b) μ ∧
      marginal Q (fun z => c * ∫ x, Y x z ∂μ) i b =
        c * ∫ x, marginal Q (Y x) i b ∂μ := by
    have hw (z : Assignment N) :
        Integrable (fun x => Q.mass z * Y x (Function.update z i b)) μ :=
      AronowAudit.P008.weighted_integrable μ _ _ (hint z)
    constructor
    · unfold marginal FiniteLaw.expect
      exact integrable_finsetSum _ (fun z _ => hw z)
    · unfold marginal FiniteLaw.expect
      rw [integral_finsetSum _ (fun z _ => hw z)]
      simp_rw [integral_const_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
  have hcircle (X : Type) [MeasurableSpace X] (N : ℕ) (P : MetricSpatialModel X N)
      (Q : FiniteLaw (Assignment N)) (i : Fin N) (d : ℝ) (hv : P.validCircle Q i d) :
      (∀ b, P.m Q i b d = P.regionAverage (P.circle i d) (P.marginalY Q i b)) ∧
      P.nodeEffect Q i d = P.regionAverage (P.circle i d) (P.pointEffect Q i) := by
    have hi (b : Bool) := hlinear X (P.ζ.restrict (P.circle i d)) N Q P.Y i b
      (P.ζ (P.circle i d)).toReal⁻¹ (hv.2.2.2 b)
    have hm (b : Bool) :
        P.m Q i b d = P.regionAverage (P.circle i d) (P.marginalY Q i b) := hi b |>.2
    refine ⟨hm, ?_⟩
    unfold MetricSpatialModel.nodeEffect
    rw [hm true, hm false]
    unfold MetricSpatialModel.regionAverage MetricSpatialModel.pointEffect
      MetricSpatialModel.marginalY
    rw [integral_sub (hi true).1 (hi false).1, mul_sub]
  refine ⟨hcircle, ?_, ?_, ?_⟩
  · intro X _ N P Q d _ hv
    change (N : ℝ)⁻¹ * ∑ i, P.nodeEffect Q i d = _
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact (hcircle X N P Q i d (hv i)).2
  · exact AronowAudit.P008.toy_eight_assignment_mean
  · intro Y i
    exact congrArg₂ (fun x y : ℝ => x - y)
      (AronowAudit.P008.toy_eight_assignment_mean Y i true)
      (AronowAudit.P008.toy_eight_assignment_mean Y i false)

theorem T26_assembly (h1 : T26_L1) : T26WholeStatement := by
  constructor
  · intro X _ N P hs Q
    have hy (i : Fin N) (b : Bool) (x : X) :
        P.marginalY Q i b x = P.Y x (fun _ => false) := by
      change Q.expect (fun z => P.Y x (Function.update z i b)) = _
      have he : (fun z => P.Y x (Function.update z i b)) =
          (fun _ : Assignment N => P.Y x (fun _ => false)) := funext (fun z => hs x _)
      rw [he]
      exact AronowAudit.P008.expect_const (Bridge.law Q) _
    have hm (i : Fin N) (b : Bool) (d : ℝ) :
        P.m Q i b d = P.M i d (fun _ => false) := by
      change Q.expect (fun z => P.M i d (Function.update z i b)) = _
      have he : (fun z => P.M i d (Function.update z i b)) =
          (fun _ : Assignment N => P.M i d (fun _ => false)) := by
        funext z
        unfold MetricSpatialModel.M MetricSpatialModel.regionAverage
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall (fun x => hs x _))
      rw [he]
      exact AronowAudit.P008.expect_const (Bridge.law Q) _
    have hn (i : Fin N) (d : ℝ) : P.nodeEffect Q i d = 0 := by
      unfold MetricSpatialModel.nodeEffect
      rw [hm i true d, hm i false d, sub_self]
    refine ⟨?_, fun i d _ => hn i d, ?_⟩
    · intro i x
      unfold MetricSpatialModel.pointEffect
      rw [hy i true x, hy i false x, sub_self]
    · intro d _ _
      change (N : ℝ)⁻¹ * ∑ i, P.nodeEffect Q i d = 0
      simp [hn]
  · refine ⟨?_, ?_, ?_⟩
    · intro Q
      exact ⟨(h1.1 Q 0).mpr (Or.inl rfl), (h1.1 Q 1).mpr (Or.inr rfl)⟩
    · intro Q d hd
      have hm (z : Assignment 1) : wholeCancellingModel.M 0 d z = 0 := by
        rcases (h1.1 Q d).mp hd with rfl | rfl
        · exact (h1.2 z).1
        · exact (h1.2 z).2
      have hm' (i : Fin 1) (z : Assignment 1) : wholeCancellingModel.M i d z = 0 := by
        have hi : i = 0 := Subsingleton.elim _ _
        simpa [hi] using hm z
      simp [MetricSpatialModel.amr, finiteAMR, marginal, FiniteLaw.expect, hm']
    · norm_num [wholeCancellingModel, bit]

theorem T15_assembly : T15WholeStatement := by
  intro X _ N P i d k _ _
  refine ⟨fun _ => Iff.rfl, ?_, ?_, ?_⟩
  · intro z _
    simp only [MetricSpatialModel.regionAverage, MetricSpatialModel.band, div_eq_mul_inv,
      mul_comm]
  · intro z _
    simp only [MetricSpatialModel.M, MetricSpatialModel.regionAverage,
      MetricSpatialModel.circle, div_eq_mul_inv, mul_comm]
  · intro hinner hsep
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro j hj
    change d - k ≤ P.distance (P.node i) (P.node j) ∧
      P.distance (P.node i) (P.node j) ≤ d + k at hj
    by_cases he : j = i
    · subst j
      have hz : P.distance (P.node i) (P.node i) = 0 := by
        exact @dist_self Plane P.metric.toPseudoMetricSpace (P.coord (P.node i))
      linarith [hj.1]
    · linarith [hsep j he, hj.2]

theorem T16_assembly (h1 : T16_L1) : T16WholeStatement := by
  have hmem (i : Fin 2) : wholeSquareCenter i ∈ wholeSquare i := by
    norm_num [wholeSquareCenter, wholeSquare, PiLp.toLp_apply]
  refine ⟨?_, ?_⟩
  · intro i
    refine ⟨hmem i, (h1 i).1, (h1 i).2, Metric.infDist_zero_of_mem (hmem i), ?_⟩
    rw [(h1 i).2]
    norm_num
  · intro h
    have hz := h 0
    rw [(h1 0).2] at hz
    norm_num at hz

end

end SAP.P008b.WH.W1
