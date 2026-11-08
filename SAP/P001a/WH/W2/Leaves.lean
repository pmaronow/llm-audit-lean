import SAP.P001a.Defs.WholeW2
import AronowAudit.P001.Wave1.Gap.PlaceboFTest
import AronowAudit.P001.Wave1.Gap.DecideB
import AronowAudit.P001.Wave1.Gap.GLP0011B3

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P001.Wave1
open scoped BigOperators ENNReal NNReal Topology Classical Matrix

noncomputable section

namespace SAP.P001a.WH.W2

universe u v

/-- Compact unique argmax consistency using positive-index error events.
Use compact_unique_maximum_separated. For each epsilon, separate the population
maximum by delta, then contain the estimator's bad event in the uniform error
event at delta/3 and the complement of the supplied good set, outside the two
null sets for feasibility and maximization. Outer-measure subadditivity and the
two assumed error-event convergence statements finish.
No continuity of the random criterion or boundedness of its supremum is needed. -/
def T12_L1 : Prop := W2ArgmaxPrinciple.{u}

/-- QMD-free local normality, supplied consistency and the canonical regularity
structure. Adapt DecideB_scoreMatrix_cp's control argument to the Hessian bad
events in W2HessianCP; the complement gives exactly the uniform entrywise bound
used in its Taylor remainder argument. Its two controls are that bad event and
the consistency error event. Ignore n=0 by an eventual positive-index restriction.
Derive the score equation from DecideB_log_maximizer_score_zero on the common C2
set and the maximizer event. Reuse DecideB_scoreVersion_iid, the inverse-information
CLT and DecideB_linearized_normal_limit. The adaptation is about 250–350 lines;
there is no new CLT, no QMD premise, and no reference-measure premise. -/
def T12_L2 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ),
    IID μ (fun i ω => (X i ω,Y i ω)) →
    ∀ (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (θ : Fin τ → ℝ)
      (B : W2MLProblem μ X Y g θ), W2MLRegularity μ X Y g θ B →
    CP μ B.estimate θ →
    WeakLimit μ (fun n ω => Real.sqrt n • (B.estimate n ω-θ))
      (normalVectorLaw (informationMatrix μ (X 0) (Y 0) g θ)⁻¹)

/-- QMD and regularity force E[psi_j s_k]=delta_jk over an arbitrary fixed
dominating measure. Generalize GLP0011B3_coordinate_path: truncate each coordinate
path outside the positive normalization ball, take the centered L2 score's
measurable representative, and use the probability normalization to obtain L2
square roots. The weighted score representative agrees on positive true density
and vanishes off it. GLP0011B3_qmd_of_integral and the pairwise dominator identity
construct NondominatedQMDPath without s-finiteness of the original measure.
Apply GLP0011B3_regularity_forces_coordinate to that path for each j,k.
The source coordinate construction is about 110 lines; the arbitrary-reference
adapter and final invocation should fit within 200–300 lines. -/
def T12_L3 : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] {τ : ℕ} (ρ : Measure E)
    (f : (Fin τ → ℝ) → E → ℝ) (s : E → Fin τ → ℝ)
    (θ : Fin τ → ℝ) (δ : ℝ), 0 < δ →
    (∀ t ∈ Metric.ball θ δ, Measurable (f t)) →
    (∀ t ∈ Metric.ball θ δ, ∀ z, 0 ≤ f t z) →
    (∀ t ∈ Metric.ball θ δ,
      IsProbabilityMeasure (ρ.withDensity (fun z => ENNReal.ofReal (f t z)))) →
    ∀ [IsProbabilityMeasure (ρ.withDensity (fun z => ENNReal.ofReal (f θ z)))],
    (∀ j, MemLp (fun z => s z j) 2 (ρ.withDensity (fun z => ENNReal.ofReal (f θ z)))) →
    (∀ j, mean (ρ.withDensity (fun z => ENNReal.ofReal (f θ z))) (fun z => s z j) = 0) →
    W2QMD ρ f s θ →
    ∀ (T : (n : ℕ) → (Fin n → E) → Fin τ → ℝ) (ψ : E → Fin τ → ℝ),
    RegularAL (fun t => ρ.withDensity (fun z => ENNReal.ofReal (f t z))) θ T ψ →
    ∀ j k, mean (ρ.withDensity (fun z => ENNReal.ofReal (f θ z)))
      (fun z => ψ z j*s z k) = if j=k then 1 else 0

theorem mixture_nonidentification : W2MixtureNonidentification := by
  intro M K τ νX κ p g θ θ' hθ j hp hpzero heq _ _
  have he (y : ℝ) (x : Fin K → ℝ) : mixtureFamily p g y x θ=mixtureFamily p g y x θ' := by
    unfold mixtureFamily
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k=j
    · subst k; simp [← hp, hpzero]
    · rw [heq k hk, hp]
  have hlaw : conditionalModelLaw νX κ (mixtureFamily p g) θ =
      conditionalModelLaw νX κ (mixtureFamily p g) θ' := by
    unfold conditionalModelLaw
    congr 1
    funext xy
    rw [he]
  refine ⟨he, hlaw, fun n => by rw [hlaw], ?_, ?_⟩
  · unfold mean
    rw [hlaw]
    congr 1
    funext xy
    dsimp only
    rw [he]
  · intro T _ hboth
    have hother : SampleCP (conditionalModelLaw νX κ (mixtureFamily p g) θ) T θ' := by
      rw [hlaw]; exact hboth.2
    exact hθ (AronowAudit.P001.sample_probability_limit_unique _ T θ θ' hboth.1 hother)

theorem T12_assembly (h1 : T12_L1.{u}) (h2 : T12_L2.{u}) (h3 : T12_L3.{v}) :
    T12WholeStatement.{u,v} := by
  have hc : W2MLConsistency.{u} := by
    intro Ω _ μ _ K τ X Y g θ B
    exact h1 μ B.parameterSet B.compact θ B.truth_mem _ B.continuous B.unique
      _ B.estimate B.measurable B.values
      (fun n => {ω | W2LogGood X Y g B.parameterSet n ω})
      B.uniform.2 B.maximizes B.uniform.1
  refine ⟨mixture_nonidentification, hc, ?_, ?_⟩
  · intro Ω _ μ _ K τ X Y hiid g θ B R
    apply h2 μ X Y hiid g θ B R
    exact hc μ X Y g θ B
  · intro E _ τ ρ f s θ δ hδ hm hn hp _ hs2 hs0 hqm I hI hpos T ψ hreg
    exact AronowAudit.P001.Wave1.regular_influence_information_lower_bound_proof
      _ s ψ hs2 hreg.2.2.1 hs0 hreg.2.2.2.1 I hI hpos
      (h3 ρ f s θ δ hδ hm hn hp hs2 hs0 hqm T ψ hreg)

/-- The full real-valued joint and conditional mass formula of the twelve atoms.
Split x,z,d on the finite support, use zero mass off that support, and expand
fprob with Fin.sum_univ_succ on the remaining cases. The W formula follows from
the two distinct values x^2-1/2 and x^2+1/2. No singleton denominator is zero:
the displayed x support has probability 1/3. -/
def T17_L1 : Prop := W2PlaceboLawFacts

/-- Identify the law of the baseline-first product experiment. Enumerate its 24 equally
likely atoms; the threshold assignment sends three seeds to treatment at x=±1
and one at x=0. Its image masses are exactly placeboLaw. Finite cases verify
the X,Z,W and potential-outcome formulas (these latter checks are in the
assembly). This supplies a causal construction rather than inferring causal
ordering from a conditional-independence assertion. -/
def T17_L2 : Prop :=
  W2PlaceboStructuralLaw.map W2PlaceboStructuralAtom = finiteLawMeasure placeboLaw

theorem placebo_sample240_transport (s : Fin 240 → Fin 12) (hs : W2PlaceboCounts s) :
    W2PlaceboSampleFacts s := by
  let Z : ℕ → Unit → Fin 12 := fun k _ => if h : k < 240 then s ⟨k,h⟩ else 0
  have hz (i : Fin 240) : Z i.val () = s i := by simp [Z, i.isLt]
  have hfreq : placeboFTest_frequency Z 240 () = AronowAudit.P001.placeboLaw.weight := by
    ext j
    unfold placeboFTest_frequency
    rw [← Fin.sum_univ_eq_sum_range]
    simp_rw [hz]
    rw [Finset.sum_boole]
    change ((Finset.univ.filter (fun i => s i=j)).card : ℝ)/240 = placeboLaw.weight j
    rw [hs j]
    fin_cases j <;> norm_num [placeboLaw]
  have hR : IsUnit (placeboFTest_gram placeboFTest_restricted (placeboFTest_frequency Z 240 ())).det := by
    rw [hfreq, placeboFTest_determinants.1]; norm_num
  have hF : IsUnit (placeboFTest_gram AronowAudit.P001.placeboRegressor
      (placeboFTest_frequency Z 240 ())).det := by
    rw [hfreq, placeboFTest_determinants.2]; norm_num
  have hcR := placeboFTest_sample_coef Z placeboFTest_restricted 240 (by norm_num) () hR
  have hcF := placeboFTest_sample_coef Z AronowAudit.P001.placeboRegressor 240 (by norm_num) () hF
  have hrR := placeboFTest_sample_rss Z placeboFTest_restricted 240 (by norm_num) () hR
  have hrF := placeboFTest_sample_rss Z AronowAudit.P001.placeboRegressor 240 (by norm_num) () hF
  have hstat := placeboFTest_sampleF_formula Z 240 (by norm_num) () hR hF
  rw [hfreq, placeboFTest_restricted_coef] at hcR
  rw [hfreq, placeboFTest_population_coef] at hcF
  rw [hfreq, placeboFTest_population_risks.1] at hrR
  rw [hfreq, placeboFTest_population_risks.2] at hrF
  rw [hfreq, placeboFTest_population_risks.1, placeboFTest_population_risks.2] at hstat
  have co : @AronowAudit.P001.olsCoef = @SAP.P001a.olsCoef := rfl
  have rss : @AronowAudit.P001.olsRSS = @SAP.P001a.olsRSS := rfl
  have px : AronowAudit.P001.placeboX = placeboX := rfl
  have pd : AronowAudit.P001.placeboD = placeboD := rfl
  have pr : AronowAudit.P001.placeboRegressor = placeboRegressor := rfl
  dsimp only [W2PlaceboSampleFacts]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hz, placeboFTest_restricted, co, px, pd] using hcR
  · simpa only [hz, co, pr, pd] using hcF
  · norm_num only [Nat.cast_ofNat] at hrR
    simpa only [hz, placeboFTest_restricted, co, px, pd, rss] using hrR
  · norm_num only [Nat.cast_ofNat] at hrF
    simpa only [hz, co, pr, pd, rss] using hrF
  · norm_num at hstat
    have hstat' : AronowAudit.P001.placeboSampleF Z 240 () = 5056/177 := by linarith
    have hstat'' : placeboSampleF Z 240 () = 5056/177 := hstat'
    simpa only [placeboSampleF, hz] using hstat''

theorem placebo_structural (h : T17_L2) : W2PlaceboStructuralFacts := by
  refine ⟨?_, h, ?_, fun b => rfl⟩
  · constructor
    have hm : (W2PlaceboStructuralLaw.map W2PlaceboStructuralAtom) Set.univ = 1 := by
      rw [h]
      change AronowAudit.P001.finiteLawMeasure AronowAudit.P001.placeboLaw Set.univ=1
      exact measure_univ
    simpa only [Measure.map_apply (measurable_of_finite _) MeasurableSet.univ,
      Set.preimage_univ] using hm
  · rintro ⟨⟨x,z⟩,a⟩
    fin_cases x <;> cases z <;> fin_cases a <;>
      norm_num [W2PlaceboStructuralAtom, placeboX, placeboZ, placeboW,
        W2PlaceboInterventionW, W2PlaceboInterventionY, noise]

theorem placebo_sample240_counts : W2PlaceboCounts W2PlaceboSample240 := by
  intro j
  fin_cases j <;> norm_num [placeboLaw]
  all_goals decide +kernel

theorem placebo_moments : W2PlaceboMoments := by
  norm_num [W2PlaceboMoments, fmean, placeboLaw, placeboX, placeboD, placeboW,
    placeboZ, Fin.sum_univ_succ]

theorem T17_assembly (h1 : T17_L1) (h2 : T17_L2) :
    T17WholeStatement.{u} := by
  have hold : T17Statement.{u} := by
    constructor
    · intro Ω _ μ _ Z hiid hlaw
      exact AronowAudit.P001.Wave1.placebo_linear_test_counterexample_proof μ Z hiid hlaw
    · exact AronowAudit.P001.placebo_full_finite_counterexample
  refine ⟨hold, h1, placebo_structural h2, placebo_moments,
    ⟨W2PlaceboSample240, placebo_sample240_counts⟩, placebo_sample240_transport, by norm_num, ?_, ?_⟩
  · intro Ω _ μ _ Z hiid hlaw
    have h := hold.1 μ Z hiid hlaw
    constructor
    · filter_upwards [h.2.2.2.2.1] with ω hω
      exact AronowAudit.P001.Wave1.placeboFTest_divergence (by norm_num) hω
    · filter_upwards [h.2.2.2.2.2.1] with ω hω
      exact AronowAudit.P001.Wave1.placeboFTest_divergence (by norm_num) hω
  · exact ⟨AronowAudit.P001.Wave1.placeboFTest_sampleSpace, inferInstance,
      AronowAudit.P001.Wave1.placeboFTest_sampleSpace_iid,
      AronowAudit.P001.Wave1.placeboFTest_sampleSpace_law⟩

end SAP.P001a.WH.W2
