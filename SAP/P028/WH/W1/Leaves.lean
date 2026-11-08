import SAP.P028.WH.W1.Finite
import SAP.P028.WH.W1.Elementary
import SAP.P028.WH.W1.Late

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028.WH.W1
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open SAP.P028 SAP.P028.Bridge
noncomputable section
open Classical

/-- Positive-arm integrability lifting. If a measurable real X is independent
of a measurable Boolean Z, integrability of X on one positive arm implies global
integrability. Compose independence with the arm indicator, turn IntegrableOn into
integrability of X times that indicator, and apply
ProbabilityTheory.IndepFun.integrable_left_of_integrable_op with real multiplication
and c=1. Positivity shows the indicator is not almost surely zero. This is the only
new analytic ingredient needed for T10; no unused potential moment is assumed. -/
def T10_L1 : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (Z : Ω → Bool), Measurable X → Measurable Z → IndepFun X Z μ →
    ∀ z, 0 < μ.real {ω | Z ω = z} → IntegrableOn X {ω | Z ω = z} μ → Integrable X μ

/-- Cellwise mean ignorability does not justify the mixed formula. Construct
three uniform strata A,N,C, an independent fair assignment Z and fair coin U;
put Y(0)=0,Y(1)=1 and R=1 iff D=1 or U=true. Cell outcomes are constant,
so their response means agree. Direct finite sums give arm means (1/3,2/3),
respondent means (1/2,4/5), and true complier means (0,1); the mixed plug-in
is (1/2,7/5). All cells and respondent events used are positive. Use a product
of the uniform measure on Fin 3 and two fair Bernoulli measures. -/
def T2_L1 : Prop := wholeCellCounterexample

/-- Realize a positive normalized seventeen-atom binary table as actual causal
data and response, with measure wholeFiniteMeasure. The finiteValid monotonicity
condition excludes defiers, and its positive first stage gives relevance. Sum
positive weighted Dirac measures, or identify this sum with the product of the
latent discrete measure and the stated assignment coin. Then use indepFun_prod
for random assignment. Finite measurability and integrability are automatic.
This leaf concerns construction only, leaving the integral calculations to L3. -/
def T2_L2 : Prop :=
  ∀ B : BinaryLaw, finiteValid B →
    ∃ (M : CausalModel (Fin 17 × Bool)) (T : Response (Fin 17 × Bool)), wholeRealizes B M T

/-- Finite-to-measure moment dictionary. For a realization from L2, weighted
Dirac integration gives the complier probability and means, recorded-one moments,
and missing-cell probabilities as the rational table quantities. Pushforward the
same sum and collect its sixteen observed atoms to get wholeFiniteObservedLaw;
finiteValid supplies positivity, so ofReal commutes with the finite sums.
Use integral_finsetSum_measure, integral_smul_measure, integral_dirac and map_apply.
All normalizing denominators are positive by finiteValid and assignmentMass. -/
def T2_L3 : Prop :=
  ∀ (B : BinaryLaw) (M : CausalModel (Fin 17 × Bool)) (T : Response (Fin 17 × Bool)),
    finiteValid B → wholeRealizes B M T →
    boundedOutcomes M ∧ complierProbability M = (fpc B : ℝ) ∧
    (∀ d, complierMean M d = (fcy B d : ℝ)) ∧
    (∀ d z, recordedOutcomeMoment M T d z = (recordedCell B z d true : ℝ) ∧
      missingOutcomeProbability M T d z = (missingCell B z d : ℝ)) ∧
    wholeObservedLaw M T = wholeFiniteObservedLaw B

/-- Observed-law invariance of the ingredients of every sensitivity endpoint.
The tuple is (Z,D,R,RY). Its assignment marginal gives arm denominators; its
treatment probabilities and the already proved first-stage identity give p.
Integrate RY*1{D=d,Z=z} for recorded moments, and the indicator of
{R=false,D=d,Z=z} for missing probabilities. Apply integral_map and map_apply
to the measurable tuple. Bounded outcomes give all integrability needed here;
assignment-arm positivity is a field of both models. No response condition enters. -/
def T2_L4 : Prop :=
  ∀ (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω']
    (M : CausalModel Ω) (T : Response Ω) (M' : CausalModel Ω') (T' : Response Ω'),
    boundedOutcomes M → boundedOutcomes M' → wholeObservedLaw M T = wholeObservedLaw M' T' →
    complierProbability M = complierProbability M' ∧
    ∀ d z, recordedOutcomeMoment M T d z = recordedOutcomeMoment M' T' d z ∧
      missingOutcomeProbability M T d z = missingOutcomeProbability M' T' d z

theorem T1_assembly : T1WholeStatement := by
  exact ⟨existingT1, completionFacts, sourceTotals, mixedRounding, witnessFactorization, witnessAtomDistinct, realNonidentification⟩

theorem T5_assembly : T5WholeStatement := by
  refine ⟨AronowAudit.P028.misprinted_constraint_counterexample, by norm_num,
    printedPairs, mixturePairs, ?_, misprintRealization⟩
  intro d
  exact ⟨coordinate_eq _ _ _ printedPairs d, coordinate_eq _ _ _ mixturePairs d⟩

theorem T6_assembly : T6WholeStatement := by
  refine ⟨?_, fullComplianceWitness⟩
  intro Ω _
  refine ⟨existingT6, ?_⟩
  intro M _
  refine ⟨fullCompliance_ae M, ?_, ?_⟩
  · intro hq hr
    let A := toAudit M
    have h1 := AronowAudit.P028.weighted_cell_mean A true false
      (AronowAudit.P028.positive_cell_mass A true false hq)
    have h0 := AronowAudit.P028.weighted_cell_mean A false true
      (AronowAudit.P028.positive_cell_mass A false true hr)
    exact (AronowAudit.P028.noncomplier_contribution_observable A).trans (congrArg₂ (· + ·) h1.symm h0.symm)
  · exact AronowAudit.P028.null_cell_joint_moment (toAudit M)

theorem T10_assembly (h1 : T10_L1) : T10WholeStatement := by
  refine ⟨?_, empiricalClause, ?_⟩
  · intro Ω _ M
    rcases treatmentFacts M with ⟨hpop,hstage,hp,hp1⟩
    refine ⟨hpop,hstage,hp,hp1,?_⟩
    intro hmeans
    apply localLate M
    intro z
    apply h1 Ω M.μ (wholeX M z) M.Z (wholeX_measurable M z) M.measurableZ
      (wholeX_independent M z) z (M.armPositive z)
    exact (hmeans z).congr_fun (fun ω hω => (wholeX_on_arm M z ω hω).symm)
      (M.measurableZ (measurableSet_singleton z))
  · obtain ⟨M₀,M₁,h⟩ := AronowAudit.P028.three_figures_do_not_identify_levels
    exact ⟨fromAudit M₀,fromAudit M₁,h⟩

theorem endpoints_invariant (h4 : T2_L4)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (M : CausalModel Ω) (T : Response Ω) (M' : CausalModel Ω') (T' : Response Ω')
    (hb : boundedOutcomes M) (hb' : boundedOutcomes M') (he : wholeObservedLaw M T = wholeObservedLaw M' T') :
    ∀ d, wholeSensitivityLower M T d = wholeSensitivityLower M' T' d ∧
      wholeSensitivityUpper M T d = wholeSensitivityUpper M' T' d := by
  rcases h4 Ω Ω' M T M' T' hb hb' he with ⟨hp,hm⟩
  intro d
  cases d <;> simp only [wholeSensitivityLower, wholeSensitivityUpper, Bool.false_eq_true,
    ite_false, ite_true, (hm _ _).1, (hm _ _).2, hp] <;> trivial

theorem T2_assembly (h1 : T2_L1) (h2 : T2_L2) (h3 : T2_L3) (h4 : T2_L4) : T2WholeStatement := by
  have base := existingT1
  rcases base.2.2.2.2.2.1 with ⟨hl,hu,he,h00,h01,h10,h11,_⟩
  obtain ⟨L,TL,hL⟩ := h2 lowerLaw hl
  obtain ⟨U,TU,hU⟩ := h2 upperLaw hu
  rcases h3 lowerLaw L TL hl hL with ⟨hbL,hpL,hcL,hmL,hoL⟩
  rcases h3 upperLaw U TU hu hU with ⟨hbU,hpU,hcU,hmU,hoU⟩
  have ho : wholeFiniteObservedLaw lowerLaw = wholeFiniteObservedLaw upperLaw := by
    unfold wholeFiniteObservedLaw
    rw [he]
  have hsourceU : wholeObservedLaw U TU = wholeFiniteObservedLaw lowerLaw := hoU.trans ho.symm
  have hc : ∀ d, complierMean L d = wholeSourceLower d ∧ complierMean U d = wholeSourceUpper d := by
    intro d
    cases d <;> simp only [hcL, hcU, h00, h01, h10, h11, wholeSourceLower, wholeSourceUpper,
      Bool.false_eq_true, ite_false, ite_true] <;> norm_num
  have hsL : ∀ d, wholeSensitivityLower L TL d = wholeSourceLower d ∧
      wholeSensitivityUpper L TL d = wholeSourceUpper d := by
    have hpc : fpc lowerLaw = 2047/9999 := base.1.2.2.1
    have hrecord := base.2.2.2.2.1
    intro d
    cases d <;>
      simp only [wholeSensitivityLower, wholeSensitivityUpper, Bool.false_eq_true, ite_false, ite_true,
        (hmL _ _).1, (hmL _ _).2, hpL, hpc, (hrecord.1 _ _ _).1, (hrecord.2 _ _).1,
        wholeSourceLower, wholeSourceUpper] <;>
      norm_num [recordedCount, missingCount, armCount]
  refine ⟨?_, h1, ?_, ?_, sourceRounding⟩
  · intro Ω _
    exact ⟨existingT2, fun M => AronowAudit.P028.observed_first_stage (toAudit M)⟩
  · intro Ω Ω' _ _ M T M' T' hb hb' he'
    have h := h4 Ω Ω' M T M' T' hb hb' he'
    exact ⟨h.1, h.2, endpoints_invariant h4 M T M' T' hb hb' he'⟩
  · refine ⟨⟨L,U,TL,TU,hbL,hbU,hoL,hsourceU,hc⟩, ?_, ?_⟩
    · intro Ω _ M T hb he'
      have heq := endpoints_invariant h4 M T L TL hb hbL (he'.trans hoL.symm)
      intro d
      exact ⟨(heq d).1.trans (hsL d).1,(heq d).2.trans (hsL d).2⟩
    · intro d l u hi
      have hL' := hi _ L TL hbL hoL
      have hU' := hi _ U TU hbU hsourceU
      exact ⟨(hc d).1 ▸ hL'.1, (hc d).2 ▸ hU'.2⟩

end
end SAP.P028.WH.W1
