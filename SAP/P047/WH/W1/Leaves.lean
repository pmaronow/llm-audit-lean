import SAP.P047.WH.W1.Helpers

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace SAP.P047.WH.W1

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

/-- The two explicit constructions of the baseline law agree. Prove that
the pushforward of uniform01 by v ↦ decide (v ≤ 1/2) is fairBool, checking
the two singleton masses with uniform01_Iic and the complement formula.
Then push this identity through the two seed products and the measurable
baseline map, using Measure.map_prod_map and Measure.map_map. The composed
map is exactly gen with both functions constant 1/2. This is an equality
of full population measures, not just of their observed marginals. -/
def T3_L1 : Prop :=
  baselineLaw = AronowAudit.P047.Wave1.Impossibility.genMeasure
    (fun _ => (1 / 2 : ℝ)) (fun _ => (1 / 2 : ℝ))

/-- Assemble the whole claim from the baseline identification and the
completed statistical impossibility donor. All model and limit comparisons
are proved order arguments; they add no statistical assumptions. -/
theorem T3_assembly (h1 : T3_L1) : T3WholeStatement.{u} := by
  obtain ⟨S, hSgen, hSprop, hSmodel⟩ := generated_half_member
  have hS : S.measure = baselineLaw := hSgen.trans h1.symm
  have hSate : ate S = 1 / 2 := by
    unfold ate
    rw [hS]
    exact AronowAudit.P047.baseline_ate
  refine ⟨⟨S, hS, hSprop, hSmodel, hSate⟩, ?_⟩
  intro M hM _hmean R _ Q _
  have hcore : T3Statement.{u} := by
    intro R' _ Q' _
    simpa only [Bridge.randRisk_eq, Bridge.randStrictRisk_eq,
      Bridge.randCoverage_eq, Bridge.widthProb_eq] using
      AronowAudit.P047.Wave1.unknown_propensity_impossibility_randomized Q'
  constructor
  · intro E hE
    obtain ⟨hfinite, hasymp⟩ := (hcore Q).1 E hE
    constructor
    · intro n hn
      have hbase : (1 / 2 : ℝ) ≤ wholeRisk unknownPopulations Q E n (1 / 12) := by
        simpa only [wholeRisk_unknown] using hfinite n hn
      exact hbase.trans (modelEventSup_mono Q unknownPopulations _ hM)
    · obtain ⟨η, hη, hlim⟩ := hasymp
      have hlim' : 0 < Filter.limsup
          (fun n => wholeStrictRisk unknownPopulations Q E n η) atTop := by
        simpa only [wholeStrictRisk_unknown] using hlim
      refine ⟨η, hη, hlim'.trans_le ?_⟩
      apply unit_limsup_mono
      · intro n
        exact (modelEventSup_bounds Q unknownPopulations _).1
      · intro n
        exact (modelEventSup_bounds Q M _).2
      · intro n
        exact modelEventSup_mono Q unknownPopulations _ hM
  · intro lo hi hlo hhi α hα0 hαhalf hhonest
    have hcoverage : Filter.liminf (wholeCoverage M Q lo hi) atTop ≤
        Filter.liminf (wholeCoverage unknownPopulations Q lo hi) atTop := by
      apply unit_liminf_mono
      · intro n
        exact (modelEventInf_bounds Q M _).1
      · intro n
        exact (modelEventInf_bounds Q unknownPopulations _).2
      · intro n
        exact modelEventInf_antitone Q unknownPopulations _ hM
    have hbasehonest : 1 - α ≤ Filter.liminf (randCoverage Q lo hi) atTop := by
      have heq : wholeCoverage unknownPopulations Q lo hi = randCoverage Q lo hi :=
        funext (wholeCoverage_unknown Q lo hi)
      rw [← heq]
      exact hhonest.trans hcoverage
    obtain ⟨hfixed, hpositive⟩ :=
      (hcore Q).2 lo hi hlo hhi α hα0 hαhalf hbasehonest
    have hwidth : ∀ n, widthProb Q lo hi n ≤ wholeWidthRisk M Q lo hi n := by
      intro n
      have hat := modelEventSup_at Q M
        (fun _ => {z | lo n (observedSample n z.1, z.2) + ((1 / 6 : ℝ) : EReal) <
          hi n (observedSample n z.1, z.2)}) (populationProbability S)
          (hM ⟨S, hSmodel, rfl⟩)
      change ((sampleLaw S.measure).prod Q).real
        {z | lo n (observedSample n z.1, z.2) + ((1 / 6 : ℝ) : EReal) <
          hi n (observedSample n z.1, z.2)} ≤ wholeWidthRisk M Q lo hi n at hat
      simpa only [hS, widthProb] using hat
    have huniform : 1 - 2 * α ≤ Filter.liminf (wholeWidthRisk M Q lo hi) atTop := by
      apply hfixed.trans
      apply unit_liminf_mono
      · intro n
        exact measureReal_nonneg
      · intro n
        exact (modelEventSup_bounds Q M _).2
      · exact hwidth
    exact ⟨hfixed, huniform, hpositive,
      not_tendsto_zero_of_liminf_pos hpositive hfixed,
      not_tendsto_zero_of_liminf_pos hpositive huniform⟩

end

end SAP.P047.WH.W1
