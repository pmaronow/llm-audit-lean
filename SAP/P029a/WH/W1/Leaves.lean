import SAP.P029a.Defs.WholeW1
import SAP.P029a.Bridge
import SAP.P029a.WH.W1.Fits
import AronowAudit.P015.P015_ConvergenceCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029a.WH.W1

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical Topology

universe u v

noncomputable section

/-- T2: derive the nonzero global first stage from the actual one-sided hypotheses.
Prove ΔD=P(C)>0: on each assignment arm observed receipt equals its fixed response;
apply `AronowAudit.P029.Wave1.LateIdentity.n1_proof` to the integrable binary responses,
using tuple independence composed with their measurable projections. One-sidedness
makes the control response zero and the treated response the complier indicator a.e.
The positive profile mass and conditional score give positive mass of C intersect {X=x};
monotonicity then gives P(C)>0. This argument must not assume relevance to prove relevance.
About 100–160 lines; only bounded binary variables and finite measures occur. -/
def T2_L1 : Prop :=
  ∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → PotentialResponse X) (Z : Ω → Bool),
    WholeIVCore μ U Z → (∀ᵐ ω ∂μ, (U ω).d0 = false) →
    ∀ x, 0 < eventProbability μ {ω | (U ω).x = x} →
      0 < complianceProbability μ U x →
      eventMean μ (fun ω => indicatorValue ((U ω).receivedTreatment (Z ω))) {ω | Z ω = true} -
        eventMean μ (fun ω => indicatorValue ((U ω).receivedTreatment (Z ω))) {ω | Z ω = false} ≠ 0

/-- T4: derive relevance from randomized assignment, no defiers, and finite-support overlap.
Use `AronowAudit.P029.Wave1.LateIdentity.n1_proof` on the bounded fixed receipt responses,
without assuming relevance. Subtract their arm means and use no defiers a.e. to obtain
ΔD=P(C). Some supported profile has positive mass because the profile masses sum to one;
its positive score implies P(C)>0 by measure monotonicity. Assemble IVConditions from
this derived nonzero first stage and the model's existing fields. Estimated size 100–160 lines. -/
def T4_L1 : Prop :=
  ∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialResponse X) (Z : Ω → Bool),
    WholeFiniteModel μ U Z → IVConditions μ U Z

/-- T4: nonzero weighted population denominators and identification of grouped cell Wald.
The IV premise is derived by L1 in the assembly. For positive profile weights, the arm
weight totals are P(Z=z)E[w(X)]>0, and their normalized receipt difference is
E[w(X)C]/E[w(X)]>0. Expand the finite profile partition and use tuple independence composed
with fixed-response maps. Strict positivity follows from the positive profile masses,
weights and scores. Finally distribute the finite profile sum through the integrals and
cancel the positive arm probabilities to identify the grouped ratio with populationWald.
All integrability follows from finite support and |Y|≤|Y0|+|Y1|. Adapt the finite-partition
and independent-arm arguments in `AronowAudit.P029.Wave1.corrected_weighted_limits_proof`.
Estimated size 160–250 lines. -/
def T4_L2 : Prop :=
  ∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialResponse X) (Z : Ω → Bool),
    WholeFiniteModel μ U Z → IVConditions μ U Z →
    ∀ w : X → ℝ, (∀ x, 0 < w x) →
      WholeWaldDomain (wholePopulationCells μ U Z) w ∧
      wholeCellWald (wholePopulationCells μ U Z) w = populationWald μ U Z (fun ω => w (U ω).x)

/-- T4: the finitely many empirical cell moments obey the LLN with only first moments.
For each (x,z,k), compose the iid joint tuple with the measurable function
1{X=x,Z=z} times (1,Y,D). Its absolute value is bounded by 1+|Y0|+|Y1|, hence integrable.
Use `ProbabilityTheory.strong_law_ae_real`, shift the sample size to n+1, and rewrite
range sums as sums over Fin (n+1). Measurability of the empirical averages permits
`MeasureTheory.tendstoInMeasure_of_tendsto_ae`. No independence from estimated scores,
second moments, or bounded outcomes may be assumed. Estimated size 100–180 lines. -/
def T4_L3 : Prop :=
  ∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ℕ → Ω → PotentialResponse X)
    (Z : ℕ → Ω → Bool), WholeFiniteModel μ (U 0) (Z 0) → WholeIID μ U Z →
    ∀ c : WholeCellIndex X,
      TendstoInMeasure μ (fun n ω => wholeEmpiricalCells U Z n ω c) atTop
        (fun _ => wholePopulationCells μ (U 0) (Z 0) c)

/-- T4: joint plug-in convergence for a finite vector of cell moments and score estimates.
Combine the two finite vectors using the index type `Sum (WholeCellIndex X) X` and
`AronowAudit.P015.ConvergenceCompletion.finite_cmt`. The map takes reciprocals of the
score coordinates, forms finite weighted sums, and divides three times. It is continuous
at the deterministic limit because all scores and the three Wald denominators there
are nonzero. `WholeWaldDomain` records exactly those conditions. The assertion concerns
totalized ratios, so no condition on denominators at finite n is needed. Measurability
is not needed by the finite CMT donor; it is supplied separately for the actual statistics.
Estimated size 80–140 lines. -/
def T4_L4 : Prop :=
  ∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [Fintype X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (a : ℕ → Ω → WholeCellIndex X → ℝ) (s : ℕ → Ω → X → ℝ)
    (A : WholeCellIndex X → ℝ) (p : X → ℝ),
    (∀ c, TendstoInMeasure μ (fun n ω => a n ω c) atTop (fun _ => A c)) →
    (∀ x, TendstoInMeasure μ (fun n ω => s n ω x) atTop (fun _ => p x)) →
    (∀ x, p x ≠ 0) → WholeWaldDomain A (fun x => 1 / p x) →
    TendstoInMeasure μ (fun n ω => wholeCellWald (a n ω) (fun x => 1 / s n ω x)) atTop
      (fun _ => wholeCellWald A (fun x => 1 / p x))

/-- The fixed witnesses and the existing one-sided theorem leave only the relevance step. -/
theorem T2_assembly (h1 : T2_L1.{u,v}) : T2WholeStatement.{u,v} := by
  refine ⟨Bridge.proveIgnorabilityWitnessFacts, Bridge.proveIgnorabilityIncomparability,
    Bridge.proveBaselineSelectionFacts, Bridge.proveBaselineEffectFacts, ?_, ?_⟩
  · intro R hR
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hR
    rcases hR with rfl | rfl
    all_goals norm_num [finiteProbability, sixAtomMass, bernoulliProductMass,
      complianceTypeMass, ignorabilityResponse, baselineResponse, PotentialResponse.isComplier,
      Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
  · intro Ω X _ _ _ μ _ U Z hcore hside x hx hc hi
    have hnd : μ {ω | (U ω).isDefier} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hside] with ω hω
      simp [PotentialResponse.isDefier, hω]
    have hiv : IVConditions μ U Z :=
      ⟨hcore.covariate_measurable, hcore.d0_measurable, hcore.d1_measurable,
        hcore.y0_measurable, hcore.y1_measurable, hcore.assignment_measurable,
        hcore.y0_integrable, hcore.y1_integrable, hcore.randomized,
        hcore.assignment_pos, hcore.assignment_lt_one, hnd,
        h1 μ U Z hcore hside x hx hc⟩
    exact Bridge.proveOneSidedImplication μ U Z hiv hside x hx hc hi

/-- Population identities are existing proofs; the four leaves add the exact finite-support
regularity bridge and sampling limits. The ATE substitutions are proved here. -/
theorem T4_assembly (h1 : T4_L1.{u,v}) (h2 : T4_L2.{u,v})
    (h3 : T4_L3.{u,v}) (h4 : T4_L4.{u,v}) :
    T4WholeStatement.{u,v} := by
  have hpop : WholeFinitePopulation.{u,v} := by
    intro Ω X _ _ _ _ μ _ U Z hm
    have hiv := h1 μ U Z hm
    have hpos : ∀ x, 0 < eventProbability μ {ω | (U ω).x = x} →
        0 < complianceProbability μ U x := fun x _ => hm.score_pos x
    constructor
    · intro w hw
      obtain ⟨ha,hb,hc,hd,he,hf,hg⟩ :=
        Bridge.proveWeightedPopulationIdentities μ U Z hiv hpos w hw
      exact ⟨ha,hb,hc,hd,he,hf,fun h => hg (fun x _ => h x)⟩
    · intro hind
      obtain ⟨ha,hb,hc,hd⟩ := Bridge.proveJointIndependenceSufficiency μ U Z hiv hpos hind
      exact ⟨⟨ha,fun x => hb x (hm.profile_mass x)⟩,hc,hd⟩
  refine ⟨hpop, Bridge.proveMarginalWitnessFacts, Bridge.proveConditionalWitnessFacts,
    Bridge.proveIndependenceWitnessMeans, ?_⟩
  intro Ω X _ _ _ _ μ _ U Z hm hi s _hsmeas hs
  have hcells := h3 μ U Z hm hi
  have hbridge := h2 μ (U 0) (Z 0) hm (h1 μ (U 0) (Z 0) hm)
  have hunit : TendstoInMeasure μ (wholeSampleWald U Z (fun _ _ _ => 1)) atTop
      (fun _ => populationWald μ (U 0) (Z 0) (fun _ => 1)) := by
    have hd := (hbridge (fun _ => 1) (by intro x; norm_num)).1
    have hlim := h4 μ (wholeEmpiricalCells U Z) (fun _ _ _ => 1)
      (wholePopulationCells μ (U 0) (Z 0)) (fun _ => 1) hcells
      (fun _ => AronowAudit.P015.ConvergenceCompletion.constant_limit μ 1)
      (by intro x; norm_num) (by simpa only [div_one] using hd)
    have heq := (hbridge (fun _ => 1) (by intro x; norm_num)).2
    change TendstoInMeasure μ (fun n ω => wholeCellWald (wholeEmpiricalCells U Z n ω)
      (fun x => 1 / (1 : ℝ))) atTop _
    simpa only [div_one, heq] using hlim
  have hinverse : TendstoInMeasure μ (wholeSampleWald U Z s) atTop
      (fun _ => populationWald μ (U 0) (Z 0)
        (fun ω => 1 / complianceProbability μ (U 0) (U 0 ω).x)) := by
    have hp : ∀ x, 0 < 1 / complianceProbability μ (U 0) x :=
      fun x => one_div_pos.mpr (hm.score_pos x)
    have hd := (hbridge _ hp).1
    have hlim := h4 μ (wholeEmpiricalCells U Z) s (wholePopulationCells μ (U 0) (Z 0))
      (complianceProbability μ (U 0)) hcells hs (fun x => (hm.score_pos x).ne') hd
    have heq := (hbridge _ hp).2
    change TendstoInMeasure μ (fun n ω => wholeCellWald (wholeEmpiricalCells U Z n ω)
      (fun x => 1 / s n ω x)) atTop _
    simpa only [heq] using hlim
  have hf := (hpop μ (U 0) (Z 0) hm).1 (fun _ => 1) (by intro x; norm_num)
  obtain ⟨_,_,_,_,_,hmarg,hcond⟩ := hf
  exact ⟨hunit, hinverse, fun h => by simpa only [hmarg h] using hunit,
    fun h => by simpa only [hcond h] using hinverse⟩

/-- The normal quantile donor and the existing strict cell-optimality theorems also
prove all the missing probit fitting certificates; this target needs no open leaves. -/
theorem T7_assembly : T7WholeStatement.{u,v} := by
  have hone : WholeOneSidedFits := by
    constructor
    · intro w _hw
      exact realize_free_fit Prod.fst treatedReceipt (fun _ => 1) specifiedUnweightedScores
        wholeBinaryProbit treated_unweighted_fit (fun β x => phi_interior _)
        (binary_saturation _ treated_unweighted_fit.1)
    · exact realize_free_fit Prod.fst treatedReceipt treatedWeight specifiedWeightedScores
        wholeBinaryProbit Bridge.treated_weighted_fit (fun β x => phi_interior _)
        (binary_saturation _ Bridge.treated_weighted_fit.1)
  have htwo : WholeTwoSidedFits := by
    have hr : ∀ β c, wholeClippedNestedProbit β c ∈ Ioo (0 : ℝ) 1 :=
      fun β c => clipped_interior _
    have he0 : ∃ β, wholeClippedNestedProbit β = specifiedInsideLogRates :=
      clipped_realization _ Bridge.proveSpecifiedTwoSidedFacts.1 (by
        rintro ⟨x,z⟩; cases x <;> cases z <;> norm_num [specifiedInsideLogRates])
    have he1 : ∃ β, wholeClippedNestedProbit β = specifiedWeightedRates :=
      clipped_realization _ Bridge.proveSpecifiedTwoSidedFacts.2.1 (by
        rintro ⟨x,z⟩; cases x <;> cases z <;> norm_num [specifiedWeightedRates])
    exact ⟨fun w hw => realize_package_fit Prod.fst twoSidedReceipt w specifiedInsideLogRates
      wholeClippedNestedProbit two_sided_unweighted_fit hr he0 hw,
      realize_free_fit Prod.fst twoSidedReceipt twoSidedObservationWeight specifiedWeightedRates
        wholeClippedNestedProbit Bridge.two_sided_weighted_fit hr he1⟩
  have hpert : WholePerturbationFits := by
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      exact realize_free_fit Prod.fst treatedReceipt (treatedPerturbationWeight t)
        (specifiedPerturbedScores t) wholeBinaryProbit (Bridge.treated_perturbed_fit t ht)
        (fun β x => phi_interior _) (binary_saturation _ (Bridge.treated_perturbed_fit t ht).1)
    · apply Bridge.provePerturbationDerivatives.1.congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
      exact (Bridge.proveSpecifiedPerturbationFacts t ht).2.2.2
    · apply Bridge.provePerturbationDerivatives.2.congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
      exact (Bridge.proveSpecifiedPerturbationFacts t ht).2.2.1
  refine ⟨Bridge.target7, binary_saturation, nested_saturation, hone, htwo, hpert, ?_⟩
  norm_num [WholeTwoSidedScoreValues, specifiedInsideLogRates]

end
end SAP.P029a.WH.W1
