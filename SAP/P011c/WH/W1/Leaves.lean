import SAP.P011c.Defs.WholeW1
import SAP.P011c.Bridge
import AronowAudit.P011.P011_ProbabilityCompletion
import AronowAudit.P011.P011_CoverageCompletion
import AronowAudit.P011.P011_CorollariesCompletion
import AronowAudit.P011.P011_SignCompletion
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SAP.P011c.WH.W1

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

/-- Rowwise bounded-degree CLT, with no observed-graph nesting. Adapt the proof of
`AronowAudit.P011.ProbabilityCompletion.dependency_graph_clt_completed`, deleting its
unused nesting premise. Use `Bridge.toFamily` fieldwise, not `Bridge.scaling_iff`.
The centered weighted coordinates are bounded a.e. by 2*c1, their closed neighborhoods
have size at most ceil(c2)+1, and their sum has variance n^2*v, eventually at least
(c3/2)*n. Apply
`Causalean.Mathlib.Probability.SteinMethod.bounded_degree_dependency_clt_ae` and use
`depSum_standardized`, `cdf_eq_real`, and `map_measureReal_apply` to transport the cdf.
About 65 lines; early zero variances are permitted by the donor's eventual bound. -/
def T38_L1 : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), WholeScaling F c1 c2 c3 c4 →
    ∀ t : ℝ, Tendsto
      (fun k => probability (F.model k) {y | standardized (F.model k) y ≤ t})
      atTop (𝓝 (Phi t))

/-- Slutsky's interval step on varying row laws. Positive scaled true variance and
standard-normal cdf convergence imply exact coverage for any Borel statistic whose
scaled error tends to zero in probability. Adapt
`AronowAudit.P011.CoverageCompletion.consistent_coverage`, replacing only its scaling
and CLT calls by the two explicit premises. Use `rowCP_moving_center`, `rowCP_det`,
`rowCP_continuous_pair`, and `row_random_width_interval`. The width map is continuous
at (c,c), since c>0. `quantile_positive`, `quantile_mass`, and `scaled_width` identify
the interval and its mass. About 65 lines. No dependence assumptions are needed here. -/
def T39_L1 : Prop :=
  ∀ (F : Family) (c : ℝ), 0 < c →
    Tendsto (scaledTrue F) atTop (𝓝 c) →
    (∀ t : ℝ, Tendsto
      (fun k => probability (F.model k) {y | standardized (F.model k) y ≤ t})
      atTop (𝓝 (Phi t))) →
    ∀ (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ), (∀ k, Measurable (V k)) →
      InProbability F (fun k y => (F.size k : ℝ) * V k y) (scaledTrue F) →
      ∀ α : ℝ, 0 < α → α < 1 → Tendsto
        (fun k => coverage (F.model k) (V k) α) atTop (𝓝 (1 - α))

/-- Finite homoskedastic oracle underestimation bound. This is a single-row lemma;
it needs neither a scaling limit nor relations between graphs. Adapt the finite part
of `AronowAudit.P011.HomoskedasticCompletion.homoskedastic_repair_completed`.
First sum the degree bounds to obtain 1 <= gFactor <= 1+c2, using `degree_row_sum`.
`weighted_memLp` supplies L2 without extra assumptions. Use `pairwise_correlation_repair`
(including its zero-variance case) and `CorrelationCompletion.meanVariance_nonneg` to
bound n*v by meanVariance*gFactor. The nonnegative mean spread gives the pointwise
underestimate bound (1+c2)*abs(varianceRemainder). Apply `remainder_memLp_two`,
`remainder_second_bound` and `second_moment_tail` at radius epsilon/(1+c2).
All integrals in this route are integrable by these donors. About 100 lines. -/
def T40_L1 : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (m : Model n) (c1 c2 : ℝ), 0 < c1 → 0 < c2 →
    Dependency m → Homoskedastic m →
    (∀ᵐ y ∂m.law, ∀ i, |weighted m y i - beta m| ≤ c1) →
    (∀ i, (degree m.G i : ℝ) ≤ c2) →
    ∀ ε : ℝ, 0 < ε →
      probability m {y |
        (n : ℝ) * (var m (betaHat m) - V2 m.G (weighted m y)) > ε} ≤
        4 * (1 + c2)^3 * c1^4 / ((n : ℝ) * ε^2)

/-- The old scaling condition entails the new rowwise one. -/
theorem wholeScaling_of_scaling (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) : WholeScaling F c1 c2 c3 c4 := h.2

/-- The positive scaled-variance limit makes the denominator meaningful eventually. -/
theorem variance_eventually_positive (F : Family) (c : ℝ) (hc : 0 < c)
    (hv : Tendsto (scaledTrue F) atTop (𝓝 c)) :
    ∀ᶠ k in atTop, 0 < var (F.model k) (betaHat (F.model k)) := by
  have he := hv.eventually (Ioi_mem_nhds hc)
  filter_upwards [he] with k hk
  have hn : 0 < (F.size k : ℝ) := by exact_mod_cast F.positive k
  change 0 < (F.size k : ℝ) * var (F.model k) (betaHat (F.model k)) at hk
  exact (mul_pos_iff_of_pos_left hn).mp hk

theorem T38_assembly (h1 : T38_L1) : T38WholeStatement := by
  intro F c1 c2 c3 c4 h
  exact ⟨variance_eventually_positive F c3 h.2.2.1 h.2.2.2.2.2.2.2.1,
    h1 F c1 c2 c3 c4 h⟩

/-- In-probability assertions are unchanged by equality a.e. separately in every row. -/
theorem inProbability_congr (F : Family)
    (T U : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (a : ℕ → ℝ)
    (h : ∀ k, T k =ᵐ[(F.model k).law] U k) :
    InProbability F T a ↔ InProbability F U a := by
  have he (k : ℕ) (ε : ℝ) :
      probability (F.model k) {y | |T k y - a k| > ε} =
      probability (F.model k) {y | |U k y - a k| > ε} := by
    apply measureReal_congr
    filter_upwards [h k] with y hy
    simp only [hy]
  unfold InProbability
  simp_rw [he]

/-- One-sided conservativeness is unchanged by rowwise a.e. equality. -/
theorem conservative_congr (F : Family)
    (V W : ∀ k, (Fin (F.size k) → ℝ) → ℝ)
    (h : ∀ k, V k =ᵐ[(F.model k).law] W k) :
    Conservative F V ↔ Conservative F W := by
  have he (k : ℕ) (ε : ℝ) :
      probability (F.model k) {y |
        (F.size k : ℝ) * (var (F.model k) (betaHat (F.model k)) - V k y) > ε} =
      probability (F.model k) {y |
        (F.size k : ℝ) * (var (F.model k) (betaHat (F.model k)) - W k y) > ε} := by
    apply measureReal_congr
    filter_upwards [h k] with y hy
    simp only [hy]
  unfold Conservative
  simp_rw [he]

/-- Clipped interval probabilities are unchanged by a.e. equality. -/
theorem coverage_congr {n : ℕ} (m : Model n) (V W : (Fin n → ℝ) → ℝ)
    (h : V =ᵐ[m.law] W) (α : ℝ) : coverage m V α = coverage m W α := by
  apply measureReal_congr
  filter_upwards [h] with y hy
  simp only [hy]

/-- The printed truncation argument needs only an exact-coverage theorem, not scaling
or graph assumptions. This short order argument is discharged here rather than a leaf. -/
theorem conservative_from_exact (F : Family)
    (hexact : ∀ (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ),
      (∀ k, Measurable (V k)) →
      InProbability F (fun k y => (F.size k : ℝ) * V k y) (scaledTrue F) →
      ∀ α : ℝ, 0 < α → α < 1 →
        Tendsto (fun k => coverage (F.model k) (V k) α) atTop (𝓝 (1 - α)))
    (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (hV : ∀ k, Measurable (V k))
    (hc : Conservative F V) : ConservativeCoverage F V := by
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  let U := fun k y => min (V k y) (var (F.model k) (betaHat (F.model k)))
  have hU : ∀ k, Measurable (U k) := fun k => (hV k).min measurable_const
  have hUc : InProbability F (fun k y => (F.size k : ℝ) * U k y) (scaledTrue F) := by
    intro ε hε
    have heq : (fun k => probability (F.model k)
        {y | |(F.size k : ℝ) * U k y - scaledTrue F k| > ε}) =
        (fun k => probability (F.model k)
          {y | (F.size k : ℝ) * (var (F.model k) (betaHat (F.model k)) - V k y) > ε}) := by
      funext k
      apply congrArg (probability (F.model k))
      ext y
      dsimp [U, scaledTrue]
      rw [(AronowAudit.P011.truncation_identity (F.size k : ℝ) _ _ (by positivity)).1]
      rw [show (F.size k : ℝ) * var (F.model k) (betaHat (F.model k)) -
          (F.size k : ℝ) * V k y =
          (F.size k : ℝ) * (var (F.model k) (betaHat (F.model k)) - V k y) by ring]
      change (ε < max ((F.size k : ℝ) *
        (var (F.model k) (betaHat (F.model k)) - V k y)) 0) ↔ _
      rw [lt_max_iff]
      simp only [show ¬ ε < 0 by linarith, or_false]
    rw [heq]
    exact hc ε hε
  have hlim := hexact U hU hUc
  intro α hα hα1
  have hz : 0 ≤ normalQuantile α :=
    (AronowAudit.P011.CoverageCompletion.quantile_positive α hα hα1).le
  have hdom (k : ℕ) : coverage (F.model k) (U k) α ≤ coverage (F.model k) (V k) α := by
    apply measureReal_mono (μ := (F.model k).law) ?_ (measure_ne_top _ _)
    intro y hy
    exact AronowAudit.P011.interval_containment _ _ _ _ hz (min_le_left _ _) hy
  have hbelow : atTop.IsBoundedUnder (· ≥ ·) (fun k => coverage (F.model k) (V k) α) :=
    isBoundedUnder_of ⟨0, fun _ => measureReal_nonneg⟩
  have habove : atTop.IsBoundedUnder (· ≤ ·) (fun k => coverage (F.model k) (V k) α) := by
    refine isBoundedUnder_of ⟨1, fun k => ?_⟩
    simpa only [coverage, probability, measureReal_def, measure_univ, ENNReal.toReal_one] using
      measureReal_mono (μ := (F.model k).law)
        (Set.subset_univ {y | |betaHat (F.model k) y - beta (F.model k)| ≤
          normalQuantile α * Real.sqrt (max (V k y) 0)})
  apply (le_liminf_iff habove.isCoboundedUnder_flip hbelow).mpr
  intro y hy
  filter_upwards [(hlim α hα hα1).eventually_const_lt hy] with k hk
  exact hk.trans_le (hdom k)

/-- T38's leaf is shared: it is proved once, then used for T39 and T40. A.e.
representatives and all transfers are glue, already proved in this assembly. -/
theorem T39_assembly (h38 : T38_L1) (h1 : T39_L1) : T39WholeStatement := by
  intro F c1 c2 c3 c4 h V hV
  have hexact := h1 F c3 h.2.2.1 h.2.2.2.2.2.2.2.1 (h38 F c1 c2 c3 c4 h)
  let W : ∀ k, (Fin (F.size k) → ℝ) → ℝ := fun k => (hV k).mk (V k)
  have hW (k : ℕ) : Measurable (W k) := (hV k).measurable_mk
  have he (k : ℕ) : V k =ᵐ[(F.model k).law] W k := (hV k).ae_eq_mk
  have hscaled (k : ℕ) :
      (fun y => (F.size k : ℝ) * V k y) =ᵐ[(F.model k).law]
        (fun y => (F.size k : ℝ) * W k y) := by
    filter_upwards [he k] with y hy
    rw [hy]
  have hcov (k : ℕ) (α : ℝ) : coverage (F.model k) (V k) α =
      coverage (F.model k) (W k) α := coverage_congr _ _ _ (he k) α
  constructor
  · intro hc α hα hα1
    have hcW := (inProbability_congr F _ _ (scaledTrue F) hscaled).mp hc
    simpa only [hcov] using hexact W hW hcW α hα hα1
  · intro hc α hα hα1
    have hcW := (conservative_congr F V W he).mp hc
    have hh := conservative_from_exact F hexact W hW hcW α hα hα1
    simpa only [hcov] using hh

/-- The sole new T40 step is its finite oracle bound. Its limit, maximizer domination,
measurability, positivity, and passage to both printed intervals are discharged here.
The T38 and T39 leaves are shared dependencies, not duplicate writer obligations. -/
theorem T40_assembly (h38 : T38_L1) (h39 : T39_L1) (h1 : T40_L1) :
    T40WholeStatement := by
  intro F c1 c2 c3 c4 h hs hv A hm
  have hOracle : Conservative F (fun k y => V2 (F.model k).G (weighted (F.model k) y)) := by
    intro ε hε
    have hN : Tendsto (fun k => (F.size k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp F.grows
    apply squeeze_zero (fun _ => measureReal_nonneg) (fun k => ?_)
      (hN.const_div_atTop (4 * (1 + c2)^3 * c1^4 / ε^2))
    calc
      _ ≤ 4 * (1 + c2)^3 * c1^4 / ((F.size k : ℝ) * ε^2) :=
        h1 (F.size k) (F.positive k) (F.model k) c1 c2 h.1 h.2.1
          (h.2.2.2.2.1 k) (hs k) (h.2.2.2.2.2.1 k) (h.2.2.2.2.2.2.1 k) ε hε
      _ = (4 * (1 + c2)^3 * c1^4 / ε^2) / (F.size k : ℝ) := by ring
  have hb (k : ℕ) (y : Fin (F.size k) → ℝ) := AronowAudit.P011.lemma_one
    (F.positive k) (F.model k).R (F.model k).G (A k y) (F.model k).d
    (hv k) (weighted (F.model k) y) (hm k y)
  have hMax : Conservative F (fun k y => V2 (A k y) (weighted (F.model k) y)) :=
    AronowAudit.P011.CorollaryCompletion.conservative_mono (Bridge.toFamily F)
      _ _ hOracle (fun k y => (hb k y).1)
  have hDeg : Conservative F (fun k y => V2prime (F.model k).d (weighted (F.model k) y)) :=
    AronowAudit.P011.CorollaryCompletion.conservative_mono (Bridge.toFamily F)
      _ _ hMax (fun k y => (hb k y).2.1)
  have hMeas (k : ℕ) :
      Measurable (fun y => V2 (A k y) (weighted (F.model k) y)) ∧
      Measurable (fun y => V2prime (F.model k).d (weighted (F.model k) y)) :=
    ⟨AronowAudit.P011.CorollaryCompletion.maximum_measurable
      (Bridge.toModel (F.model k)) (hv k) (A k) (hm k),
      AronowAudit.P011.CorollaryCompletion.V2prime_measurable (Bridge.toModel (F.model k))⟩
  have hNonneg (k : ℕ) (y : Fin (F.size k) → ℝ) :
      0 ≤ V2 (A k y) (weighted (F.model k) y) ∧
      0 ≤ V2prime (F.model k).d (weighted (F.model k) y) :=
    AronowAudit.P011.homoskedastic_estimators_nonnegative (A k y) (F.model k).d _
  have hCovMax := (T39_assembly h38 h39 F c1 c2 c3 c4 h _
    (fun k => (hMeas k).1.aemeasurable)).2 hMax
  have hCovDeg := (T39_assembly h38 h39 F c1 c2 c3 c4 h _
    (fun k => (hMeas k).2.aemeasurable)).2 hDeg
  exact ⟨hMeas, hNonneg,
    (Bridge.printedCoverage_iff F _ (fun k y => (hNonneg k y).1)).mpr hCovMax,
    (Bridge.printedCoverage_iff F _ (fun k y => (hNonneg k y).2)).mpr hCovDeg⟩

/-- All finite components, including the missing decomposition, are existing donors. -/
theorem T41_assembly : T41WholeStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro n R h
    exact AronowAudit.P011.recruitmentCapacityMatrix_decomposition R h
  · intro n R h hc
    have hp : PSD (recruitmentCapacityMatrix R h) :=
      AronowAudit.P011.recruitmentCapacityMatrix_psd R h hc
    exact ⟨hp, fun _ δ => div_nonneg (hp.2 δ) (Nat.cast_nonneg n)⟩
  · intro n R d f c A
    exact AronowAudit.P011.maximizes_add_constant_iff R d f c A

/-- In the decisive edgeless case the undefined coefficients cancel identically. -/
theorem printedAuxiliary_eq_V2_of_edgeless {n : ℕ} (A : Graph n)
    (hA : ∀ i j, A.val i j = false) (r : Fin n → ℝ) (x : Fin n → ℝ) :
    printedAuxiliary A r x = V2 A x := by
  simp [printedAuxiliary, V2, adjacency, hA]

/-- Transport the existing independent-sign counterexample and apply uniqueness of
limits. Neither the auxiliary-expression identity nor this limit contradiction needs
a writer leaf. This refutation retains the stronger nesting condition as a fact. -/
theorem T34_assembly : T34WholeStatement := by
  let F := Bridge.fromFamily AronowAudit.P011.signFamily
  have h := AronowAudit.P011.printed_sign_counterexample
  have hS : Scaling F 1 1 1 2 := h.1
  refine ⟨F, (fun _ => rfl), hS.1, wholeScaling_of_scaling F 1 1 1 2 hS, h.2.1, ?_, ?_⟩
  · intro k
    exact ⟨rfl, (fun _ => rfl), (fun _ _ => rfl), (h.2.2.1 k).1,
      (h.2.2.1 k).2.1, (h.2.2.1 k).2.2.1⟩
  · intro r ε hε
    have hid (k : ℕ) (y : Fin (F.size k) → ℝ) :
        printedAuxiliary (F.model k).G (r k) (weighted (F.model k) y) =
          V2 (F.model k).G (weighted (F.model k) y) :=
      printedAuxiliary_eq_V2_of_edgeless _ (fun _ _ => rfl) _ _
    have hscale (k : ℕ) : scaledTrue F k = 1 := (h.2.2.1 k).2.2.1
    have hl : Tendsto (fun k => probability (F.model k) {y |
        |(F.size k : ℝ) * printedAuxiliary (F.model k).G (r k)
          (weighted (F.model k) y) - scaledTrue F k| < ε}) atTop (𝓝 1) := by
      simp only [hid, hscale]
      change Tendsto (fun k => AronowAudit.P011.probability
        (AronowAudit.P011.signFamily.model k) {y |
          |((k + 1 : ℕ) : ℝ) * AronowAudit.P011.V2
            (AronowAudit.P011.signFamily.model k).G
            (AronowAudit.P011.weighted (AronowAudit.P011.signFamily.model k) y) - 1| < ε})
        atTop (𝓝 1)
      simpa only [Nat.cast_add, Nat.cast_one] using (h.2.2.2 ε hε).2
    refine ⟨hl, ?_⟩
    intro hz
    have hfalse : (1 : ℝ) = 0 := tendsto_nhds_unique hl hz
    norm_num at hfalse

end
end SAP.P011c.WH.W1
