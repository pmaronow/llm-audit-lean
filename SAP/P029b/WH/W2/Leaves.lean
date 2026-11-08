import SAP.P029b.Defs.WholeW2
import SAP.P029b.Bridge
import SAP.P029b.WH.W2.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b.WH.W2

universe u v

open scoped BigOperators Classical Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

/-- Construct the location-zero, scale-three logistic probability law. Prove that
`logisticCDFW2` is monotone and continuous, with limits zero/one at the two ends;
bundle it as a StieltjesFunction, use `measure_univ`, and then
`ProbabilityTheory.cdf_measure_stieltjesFunction`. No moment convention is substituted
for the CDF. This is a one-variable analysis and Stieltjes construction. -/
def T19_L1 : Prop :=
  ∃ Λ : Measure ℝ, IsProbabilityMeasure Λ ∧ ∀ t : ℝ, cdf Λ t = logisticCDFW2 t

/-- Uniform balanced assignment. The PMF already gives normalization, support, and
singleton masses. For the marginal, count k-subsets containing a specified unit
using deletion, obtaining choose(2k-1,k-1)/choose(2k,k)=1/2. Treat k=0 first: there
is no unit to quantify. Independence across assignment bits is not asserted. -/
def T19_L2 : Prop :=
  ∀ k : ℕ, IsProbabilityMeasure (balancedLawW2 k) ∧
    (∀ᵐ s ∂balancedLawW2 k, s.card = k) ∧
    (∀ s : Finset (Fin (2*k)), balancedLawW2 k {s} =
      if s.card = k then (Nat.choose (2*k) k : ℝ≥0∞)⁻¹ else 0) ∧
    (∀ i : Fin (2*k), balancedLawW2 k {s | i ∈ s} = 1/2)

/-- Construct the independent coefficient/covariate/error array and an independent
balanced assignment. Normalize the two restricted Lebesgue interval laws, use
`iIndepFun_pi`, `Measure.pi_map_eval`, and product-measure marginal identities.
The assignment law's probability certificate is an explicit premise, so this leaf
does not redo the finite combinatorics. All coordinates, including shared coefficients,
have their full laws, rather than just matching moments. -/
def T19_L3 : Prop :=
  ∀ Λ : Measure ℝ, IsProbabilityMeasure Λ → ∀ k : ℕ,
    IsProbabilityMeasure (balancedLawW2 k) → ∀ wrong : Bool,
    IsProbabilityMeasure (simLawW2 Λ k wrong) ∧
    iIndepFun (fun j (ω : SimSpaceW2 k) => ω.1 j) (simLawW2 Λ k wrong) ∧
    (∀ j, Measure.map (fun ω : SimSpaceW2 k => ω.1 j) (simLawW2 Λ k wrong) =
      simCoordinateLawW2 Λ k wrong j) ∧
    IndepFun (fun ω : SimSpaceW2 k => ω.2) (fun ω => ω.1) (simLawW2 Λ k wrong) ∧
    Measure.map (fun ω : SimSpaceW2 k => ω.2) (simLawW2 Λ k wrong) = balancedLawW2 k

theorem T19_assembly (h1 : T19_L1) (h2 : T19_L2) (h3 : T19_L3) :
    T19WholeStatement := by
  obtain ⟨Λ, hΛ, hCDF⟩ := h1
  have hpoint : T19Statement :=
    ⟨Bridge.corrected_simulation_types, Bridge.printed_simulation_equation_failure,
      Bridge.simulation_outcome_identity⟩
  refine ⟨⟨Λ, hΛ, hCDF, ?_⟩, ?_, hpoint, ?_, ?_, ?_⟩
  · intro k wrong
    obtain ⟨hB, hcard, hmass, hhalf⟩ := h2 k
    obtain ⟨hP, hind, hlaw, hassign, hmap⟩ := h3 Λ hΛ k hB wrong
    refine ⟨hP, hind, hlaw, hassign, ae_of_ae_map measurable_snd.aemeasurable (hmap.symm ▸ hcard), ?_, ?_⟩
    · intro s
      rw [← hmass s, ← hmap, Measure.map_apply measurable_snd (measurableSet_singleton s)]
      rfl
    · intro i
      rw [← hhalf i, ← hmap, Measure.map_apply measurable_snd (MeasurableSet.of_discrete)]
      congr 1
      ext ω
      simp [simAssignmentW2]
  · constructor
    · exact integral_id_gaussianReal
    · rw [variance_id_gaussianReal]
      norm_num
  · intro ac a
    have h := hpoint.1 ac a true
    have h0 : latentD ac a false = latentA ac a := by simp [latentD, bit]
    refine ⟨?_, ?_⟩
    · constructor
      · exact fun hh => h.2.2.2.2.2.2.2.2.1.mp hh.1
      · intro hA
        have hC : latentC ac a = 0 := by
          have hd := h.2.2.2.2.1
          rw [hA, one_mul] at hd
          exact hd
        simp [latentD, hA, hC, bit]
    · intro hC
      have hp := (h.2.2.2.2.2.2.2.2.2.1).mpr hC
      exact hp.2
  · intro k wrong i
    have hAC : Measurable (fun r : SimCoordinateW2 k → ℝ => simIndexACW2 wrong r i) := by
      cases wrong <;>
        simp only [simIndexACW2, Bool.false_eq_true, ite_false, ite_true,
          baselineACIndex, nonlinearACIndex] <;> fun_prop
    have hA : Measurable (fun r : SimCoordinateW2 k → ℝ => simIndexAW2 wrong r i) := by
      cases wrong <;>
        simp only [simIndexAW2, Bool.false_eq_true, ite_false, ite_true,
          baselineAIndex, nonlinearAIndex] <;> fun_prop
    refine ⟨hAC, hA, ?_, ?_⟩
    · unfold simY0W2 latentAC positiveIndicator
      exact (Measurable.ite (measurableSet_lt measurable_const hAC)
        measurable_const measurable_const).const_mul 5 |>.add (measurable_pi_apply _)
    · cases wrong <;> simp only [simTauW2, Bool.false_eq_true, ite_false, ite_true] <;> fun_prop
  · intro k wrong ω i
    exact ⟨rfl, Bridge.simulation_outcome_identity _ _ _⟩

theorem appendix_identities {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool)
    (hiv : IVAssumptions μ U Z) (c m : X → ℝ) (hv : ScoreVersions μ U c m)
    (ε : ℝ) (he : 0 < ε) (hq : ∀ᵐ ω ∂μ, ε < c (U ω).x ∧ c (U ω).x ≤ 1) :
    AppendixIdentitiesW2 μ U Z c m := by
  obtain ⟨hi, hW⟩ := AronowAudit.P029.Wave1.GP029B3b_inverse_mean
    (U := fun ω => Bridge.toUnit (U ω)) hiv hv ε he hq
  obtain ⟨hcm, hc, hy, hd, hw, hA1⟩ :=
    Bridge.appendix_population_identities_proof μ U Z hiv c m hv ε he hq
  obtain ⟨_, hITT, hC, _⟩ := Bridge.late_identity_paper_scope μ U Z hiv
  refine ⟨hi, hW, hITT.trans hC, hcm, hc, ?_, hy, hd, hw, ?_⟩
  · filter_upwards [hq] with ω hω
    have hp := ne_of_gt (lt_trans he hω.1)
    exact ⟨mul_div_cancel_left₀ _ hp, div_self hp⟩
  · intro h
    exact hw.symm.trans (hA1 h)

/-- Lift the finite population to its countable iid product. Coordinate evaluation
has law cancelLawW2; compose it with the full joint-variable tuple. Transfer IV
assumptions using map integrals and independence of assignment from the other
coordinates within each draw. Identical laws transfer the zero ATE. This leaf
does not establish conditional-expectation versions; those are isolated in L2. -/
def T27_L1 : Prop :=
  CancellationPopulationW2 →
  IsProbabilityMeasure cancelSampleLawW2 ∧
  iIndepFun (fun i => jointVariables (cancelDrawW2 i) (cancelZW2 i)) cancelSampleLawW2 ∧
  (∀ i, IdentDistrib (jointVariables (cancelDrawW2 i) (cancelZW2 i))
    (jointVariables (cancelDrawW2 0) (cancelZW2 0)) cancelSampleLawW2 cancelSampleLawW2) ∧
  (∀ i, IVAssumptions cancelSampleLawW2 (cancelDrawW2 i) (cancelZW2 i)) ∧
  (∀ i, (∫ ω, (cancelDrawW2 i ω).tau ∂cancelSampleLawW2) = 0)

/-- Conditional versions on the product: c=1/3, m=0, and A1 fails. The sigma-field
of each binary profile has just its two fibers. Check conditional expectation by
the set-integral characterization on these fibers and their unions; cylinder
pushforwards reduce the integrals to the finite certificate. Nonzero population
profile means show that the zero function cannot be the conditional mean of tau.
All fibers have mass 1/2; all complier/profile events have mass 1/6. -/
def T27_L2 : Prop :=
  CancellationPopulationW2 →
  (∀ i, ScoreVersions cancelSampleLawW2 (cancelDrawW2 i) (fun _ => 1/3) (fun _ => 0)) ∧
  (∀ i, ¬ A1Versions cancelSampleLawW2 (cancelDrawW2 i) (fun _ => 0))

/-- The empirical four-cell fit is an actual saturated nested Bernoulli MLE on
the stated interior event. Group the likelihood by profile and assignment and
maximize each cell at its success fraction. `weighted_cell_unique_max` with unit
weights, or `saturated_weighted_objective_minimum` followed by exponentiation,
supplies the optimization. The fitted rates obey 0<r0<r1<1, and hence correspond
to nested parameters (r1,r0/r1) in (0,1)^2. No optimizer existence outside this
event or numerical-solver claim is made. -/
def T27_L3 : Prop :=
  ∀ n ω, cancelFitGoodW2 n ω → ∀ q : ReceiptParameters,
    cancelLikelihoodW2 n ω q.val ≤
      cancelLikelihoodW2 n ω (fun xz => cancelRateW2 n ω xz.1 xz.2)

/-- Four finite-cell laws of large numbers. Each (X,Z) cell has probability 1/4,
and its success mass is 1/12 or 1/6 according to Z. Apply the iid strong law to
these bounded indicators, pass to convergence in probability, and use div_limit
with denominator 1/4 to get the receipt rates 1/3 and 2/3. -/
def T27_L4 : Prop := CancellationCellLimitsW2

/-- Continuous finite-cell algebra. The four receipt rates tend to strictly ordered
interior limits, so the ML event has probability tending to one. On this event
the two fitted profile scores tend to 1/3; handle evaluation at X_i by the union
of the two profile-error events. Express weighted arm sums and receipt sums using
the four cell proportions and rates. Their limiting arm masses are 3/2 and their
limiting receipt contrast is 1/3, proving sample definedness with probability
tending to one. This also certifies that the refutation is not an artifact of
undefined ratios. The score fallback occurs only on the vanishing exceptional event. -/
def T27_L5 : Prop :=
  CancellationCellLimitsW2 →
  (∀ i, TendstoInMeasure cancelSampleLawW2 (fun n => cancelFittedScoreW2 n i)
    atTop (fun _ => 1/3)) ∧
  Tendsto (fun n => cancelSampleLawW2 {ω | cancelFitGoodW2 n ω}) atTop (𝓝 1) ∧
  Tendsto (fun n => cancelSampleLawW2 {ω |
    SampleDefined (fun i : Fin (n+1) => 1/cancelFittedScoreW2 n i.val ω)
      (fun i => (cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω))
      (fun i => cancelZW2 i.val ω)}) atTop (𝓝 1)

/-- Standard-normal probit covers all interior probabilities. The variance-one
Gaussian measure is atomless (`nullSingletonClass_gaussianReal`). Show its CDF
is continuous using continuity of the measures of the half-lines (or the
Stieltjes singleton formula and absence of jumps), and apply the intermediate
value theorem with `tendsto_cdf_atBot` and `tendsto_cdf_atTop`. This certifies that
optimizing over the interior receipt pairs in L3 really is a saturated probit
fit: q_AC=q1 and q_AgivenAC=q0/q1, both in (0,1). On two binary profiles,
any two probit indices equal an intercept plus a binary-profile coefficient. -/
def T27_L6 : Prop := ProbitCompleteW2

theorem cancel_rate_measurable (n : ℕ) (x z : Bool) :
    Measurable (fun ω => cancelRateW2 n ω x z) := by
  apply Measurable.div
  · apply Finset.measurable_sum
    intro i _
    exact (Measurable.of_discrete : Measurable (fun a : CancelAtomW2 =>
      if a.1.1 = x ∧ a.2 = z then bit ((cancelUnitW2 a).receipt a.2) else 0)).comp
        (measurable_pi_apply i.val)
  · apply Finset.measurable_sum
    intro i _
    exact (Measurable.of_discrete : Measurable (fun a : CancelAtomW2 =>
      if a.1.1 = x ∧ a.2 = z then (1 : ℝ) else 0)).comp (measurable_pi_apply i.val)

theorem cancel_score_measurable (n i : ℕ) : Measurable (cancelFittedScoreW2 n i) := by
  have hg : MeasurableSet {ω | cancelFitGoodW2 n ω} := by
    simp only [cancelFitGoodW2, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro x
    exact (measurableSet_lt measurable_const (cancel_rate_measurable n x false)).inter
      ((measurableSet_lt (cancel_rate_measurable n x false) (cancel_rate_measurable n x true)).inter
        (measurableSet_lt (cancel_rate_measurable n x true) measurable_const))
  have heval (z : Bool) : Measurable (fun ω => cancelRateW2 n ω (ω i).1.1 z) := by
    have hm : Measurable (fun ω : CancelSpaceW2 => (ω i).1.1) :=
      (measurable_fst.comp measurable_fst).comp (measurable_pi_apply i)
    have heq : (fun ω : CancelSpaceW2 => cancelRateW2 n ω (ω i).1.1 z) =
        (fun ω => if (ω i).1.1 then cancelRateW2 n ω true z else cancelRateW2 n ω false z) := by
      funext ω
      cases (ω i).1.1 <;> rfl
    rw [heq]
    exact Measurable.ite (hm (measurableSet_singleton true))
      (cancel_rate_measurable n true z) (cancel_rate_measurable n false z)
  exact Measurable.ite hg ((heval true).sub (heval false)) measurable_const

theorem cancel_score_range (n i : ℕ) (ω : CancelSpaceW2) :
    0 < cancelFittedScoreW2 n i ω ∧ cancelFittedScoreW2 n i ω ≤ 1 := by
  unfold cancelFittedScoreW2
  split_ifs with h
  · have hh := h (ω i).1.1
    constructor <;> linarith [hh.1, hh.2.1, hh.2.2]
  · constructor <;> norm_num

theorem T27_assembly (hiid : T27_L1) (hversions : T27_L2)
    (hmle : T27_L3) (hcells : T27_L4) (halgebra : T27_L5) (hprobit : T27_L6) :
    T27WholeStatement := by
  have hpop : CancellationPopulationW2 := cancellation_population
  obtain ⟨hP, hind, hid, hiv, hATE⟩ := hiid hpop
  obtain ⟨hv, hfail⟩ := hversions hpop
  obtain ⟨hs, hgood, hdefined⟩ := halgebra hcells
  have hzero : ∀ n ω, icswSequence cancelDrawW2 cancelZW2 cancelFittedScoreW2 n ω = 0 := by
    intro n ω
    have hy : ∀ i : Fin (n+1), (cancelDrawW2 i.val ω).outcome (cancelZW2 i.val ω) = 0 :=
      fun i => hpop.2.2.2.2 (ω i.val)
    simp [icswSequence, sampleWald, sampleArm, hy]
  refine ⟨hprobit, hpop, hP, hind, hid, hiv, hv, hfail, hATE, ?_,
    cancel_score_measurable, cancel_score_range, hs, hgood, hdefined, hmle, hzero, ?_⟩
  · norm_num
  · rw [hATE 0]
    have heq : icswSequence cancelDrawW2 cancelZW2 cancelFittedScoreW2 =
        (fun _ _ => (0 : ℝ)) := by funext n ω; exact hzero n ω
    rw [heq]
    intro ε hε
    simpa [not_le_of_gt hε] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))

end
end SAP.P029b.WH.W2
