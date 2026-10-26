import AronowAudit.P001.Wave1.Lib.TailA.MatchingFiniteEndpoints

/-! Exact matching-bootstrap endpoint theorems, without a limit hypothesis. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace AronowAudit.P001.TailA

universe u
local instance instDecidableMatchingEndpoints (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

theorem matching_endpoint_product_limits :
    Tendsto (fun (n : ℕ) => (n : ℝ)*var (MatchProduct n) hotDeck) atTop (nhds matchV) ∧
    Tendsto (fun (n : ℕ) => mean (MatchProduct n) (fun z => (n : ℝ)*bootVar hotDeck z))
      atTop (nhds matchVB) := by
  obtain ⟨hv,hb⟩ := matching_endpoint_product_moment_limits
  constructor
  · apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [matching_endpoint_scaled_original_product] using hv
  · apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [matching_endpoint_scaled_bootstrap_product] using hb

theorem matching_endpoint_bootVar_nonneg {E : Type*} {n : ℕ}
    (T : (Fin n → E) → ℝ) (z : Fin n → E) : 0 ≤ bootVar T z :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (pow_nonneg (Nat.cast_nonneg n) n)

theorem matching_endpoint_nonCP {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → MatchUnit)
    (hiid : IID μ Z) (hlaw : μ.map (Z 0) = matchingUnitLaw)
    (T : ∀ n, (Fin n → MatchUnit) → ℝ) (hT : ∀ n, Measurable (T n))
    (C : ℝ) (hbound : ∀ n z, ‖T n z‖ ≤ C)
    (hmean : Tendsto (fun (n : ℕ) => mean μ
      (fun ω => (n : ℝ)*bootVar (T n) (firstSample Z n ω))) atTop (nhds matchVB)) :
    ¬ CP μ (fun (n : ℕ) ω => (n : ℝ)*bootVar (T n) (firstSample Z n ω)) matchV := by
  apply nonnegative_expectation_gap μ _ _ _ _ matchV matchVB hmean
    hot_deck_bootstrap_constant_inequalities.2.2.2.2
  · intro n
    exact measurable_const.mul ((matching_bootVar_measurable (hT n)).comp
      (matching_endpoint_first_measurable hiid n))
  · intro n
    have hi := (matching_bootVar_memLp (MatchProduct n) (hT n) C (hbound n) 1).integrable le_rfl
    rw [← matching_finite_law μ Z hiid hlaw n] at hi
    exact ((integrable_map_measure (matching_bootVar_measurable (hT n)).aestronglyMeasurable
      (matching_endpoint_first_measurable hiid n).aemeasurable).mp hi).const_mul (n : ℝ)
  · intro n ω
    exact mul_nonneg (Nat.cast_nonneg n) (matching_endpoint_bootVar_nonneg _ _)

/-- Both matching designs have precisely the displayed variance and centered
bootstrap expectation limits, and the strict expectation deficit refutes CP. -/
theorem matching_failure_both {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → MatchUnit)
    (hiid : IID μ Z) (hlaw : μ.map (Z 0) = matchingUnitLaw) :
    MatchingFailure μ Z false ∧ MatchingFailure μ Z true := by
  obtain ⟨hv,hb⟩ := matching_endpoint_product_limits
  have hvh : Tendsto (fun (n : ℕ) => (n : ℝ)*var μ (fun ω => hotDeck (firstSample Z n ω)))
      atTop (nhds matchV) := by
    simpa only [matching_endpoint_variance_transport μ Z hiid hlaw _ (matching_hotDeck_measurable _)] using hv
  have hbh : Tendsto (fun (n : ℕ) => mean μ (fun ω => (n : ℝ)*bootVar hotDeck (firstSample Z n ω)))
      atTop (nhds matchVB) := by
    have he (n : ℕ) := matching_expectation μ Z hiid hlaw n
      (show Measurable (fun z : Fin n → MatchUnit => (n : ℝ)*bootVar hotDeck z) from
        measurable_const.mul (matching_bootVar_measurable (matching_hotDeck_measurable n)))
    simpa only [he] using hb
  have hvc : Tendsto (fun (n : ℕ) => (n : ℝ)*var μ (fun ω => causalMatch (firstSample Z n ω)))
      atTop (nhds matchV) := by
    simpa only [matching_endpoint_variance_transport μ Z hiid hlaw _ (matching_causalMatch_measurable _),
      matching_endpoint_reflection_variance] using hv
  have hbc : Tendsto (fun (n : ℕ) => mean μ (fun ω => (n : ℝ)*bootVar causalMatch (firstSample Z n ω)))
      atTop (nhds matchVB) := by
    have he (n : ℕ) := matching_expectation μ Z hiid hlaw n
      (show Measurable (fun z : Fin n → MatchUnit => (n : ℝ)*bootVar causalMatch z) from
        measurable_const.mul (matching_bootVar_measurable (matching_causalMatch_measurable n)))
    simpa only [he,matching_endpoint_reflection_bootstrap] using hb
  have hpos := matching_endpoint_constants_positive.2.2
  have hgap := hot_deck_bootstrap_constant_inequalities.2.2.2.2
  constructor
  · simp only [MatchingFailure,Bool.false_eq_true,ite_false]
    exact ⟨fun n hn => (matching_unbiased μ Z hiid hlaw n hn).1,hvh,hbh,hpos,hgap,
      matching_endpoint_nonCP μ Z hiid hlaw (fun _ => hotDeck) matching_hotDeck_measurable
        51 (fun _ => matching_hotDeck_bound) hbh⟩
  · simp only [MatchingFailure,ite_true]
    exact ⟨fun n hn => (matching_unbiased μ Z hiid hlaw n hn).2,hvc,hbc,hpos,hgap,
      matching_endpoint_nonCP μ Z hiid hlaw (fun _ => causalMatch) matching_causalMatch_measurable
        1 (fun _ => matching_causalMatch_bound) hbc⟩

/-- Lift the canonical stream to the universe of the full universal assurance. -/
def matchingCanonicalLiftedLaw : Measure (ULift.{u} (ℕ → MatchUnit)) :=
  matchingCanonicalLaw.map ULift.up

instance instProbabilityMatchingCanonicalLiftedLaw :
    IsProbabilityMeasure (matchingCanonicalLiftedLaw.{u}) := by
  unfold matchingCanonicalLiftedLaw
  exact (Measure.isProbabilityMeasure_map_iff measurable_up.aemeasurable).mpr inferInstance


end AronowAudit.P001.TailA
