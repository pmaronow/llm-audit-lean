import SAP.P006b.Defs.WholeW1
import SAP.P006b.Bridge
import AronowAudit.P006.Wave1.Gap.RepairT6T7
import AronowAudit.P006.Wave1.Gap.GLP006B1
import AronowAudit.P006.Wave1.Gap.GP006B2
import AronowAudit.P006.Wave1.BinaryExperiment.N1
import AronowAudit.P006.Wave1.BinaryExperiment.N3
import AronowAudit.P006.Wave1.BinaryExperiment.N4
import AronowAudit.P006.Wave1.BinaryExperiment.N5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P006b.WH.W1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem outcome_design {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (h : OutcomeStanding E) {π : C → ℝ} (hπ : Admissible π) :
    AronowAudit.P006.Wave1.RepairT6T7_Design (Bridge.toProject E) π where
  px_probability := h.px_probability
  means_measurable := h.means_measurable
  means_integrable := h.means_integrable
  law_probability := h.law_probability π hπ
  measurable_units := h.measurable_units π hπ
  integrable_units := fun i => ⟨(h.integrable_units π hπ i).1,
    (h.integrable_units π hπ i).2.1⟩
  covariate_law := h.covariate_law π hπ
  conditional_means := h.conditional_means π hπ
  bernoulli := h.bernoulli π hπ
  ignorability := h.ignorability π hπ

theorem actual_welfare {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (h : OutcomeStanding E) {π : C → ℝ} (hπ : Admissible π) :
    E.V π = ∫ x, π x * E.τ x ∂E.PX :=
  AronowAudit.P006.Wave1.RepairT6T7_actual_welfare (Bridge.toProject E)
    (outcome_design E h hπ) hπ

theorem actual_TT {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (h : OutcomeStanding E) (a : C → ℝ)
    (ha : Measurable a) (hai : Integrable a E.PX) (hu : TreatedMoment E a)
    {π : C → ℝ} (hπ : Admissible π) :
    E.expectedTT π = (n : ℝ)*∫ x, π x*(E.μ1 x-a x) ∂E.PX :=
  AronowAudit.P006.Wave1.RepairT6T7_actual_treated_score (Bridge.toProject E)
    (outcome_design E h hπ) hπ ha hai (fun i => (hu π hπ i).1)
    (fun i => (hu π hπ i).2)

theorem bestValue_at {P : Type*} {S : Set P} {f : P → ℝ} {p : P} (h : IsBest S f p) :
    bestValue S f = f p := AronowAudit.P006.bestValue_eq h

theorem best_congr {P : Type*} (S : Set P) (f g : P → ℝ)
    (h : ∀ p ∈ S, f p = g p) (p : P) : IsBest S f p ↔ IsBest S g p :=
  AronowAudit.P006.Wave1.T2_best_congr S f g h p

theorem bestValue_congr {P : Type*} (S : Set P) (f g : P → ℝ)
    (h : ∀ p ∈ S, f p = g p) : bestValue S f = bestValue S g := by
  unfold bestValue
  congr 1
  ext y
  constructor <;> rintro ⟨p,hp,rfl⟩
  · exact ⟨p,hp,(h p hp).symm⟩
  · exact ⟨p,hp,h p hp⟩

theorem binary_admissible (π : BinaryPolicy) (h : binaryFeasible π) :
    Admissible (binaryRule π) := by
  refine ⟨measurable_of_finite _, ?_⟩
  intro u
  cases u
  · exact ⟨h.1,h.2.1⟩
  · exact ⟨h.2.2.1,h.2.2.2⟩

theorem integral_bool (P : Measure Bool) [IsFiniteMeasure P]
    (p : ℝ) (h : ∀ u, (P {u}).toReal = coinMass p u) (f : Bool → ℝ) :
    (∫ u, f u ∂P) = (1-p)*f false+p*f true := by
  rw [integral_fintype (Integrable.of_finite)]
  simp [Measure.real, h, coinMass, smul_eq_mul, add_comm]

theorem retained_T25 : T25Statement := by
  exact ⟨@AronowAudit.P006.T25_printed_lower_bound_family,
    @AronowAudit.P006.T25_existential_lower_bound,
    @AronowAudit.P006.T25_unique_response_variant,
    @AronowAudit.P006.T25_exact_sample_reward,
    @AronowAudit.P006.lower_bound_formulas,
    @AronowAudit.P006.lower_bound_perturbed_best_iff,
    @AronowAudit.P006.lower_bound_welfare_optimum⟩

theorem lowerBound_formulas (α β η : ℝ) (π : BinaryPolicy) :
    lowerBoundReward β η π = (β*π.1-η*π.2)/2 ∧
    lowerBoundWelfare α β η π = ((β-α)*π.1+(α-η)*π.2)/2 ∧
    (∑ u : Bool, (1/2 : ℝ)*lowerBoundY0 α u) = 0 :=
  AronowAudit.P006.lower_bound_formulas α β η π

theorem lowerBound_best_response (β : ℝ) (hβ : 0 < β) (π : BinaryPolicy) :
    IsBest binaryPolicies (lowerBoundReward β 0) π ↔ binaryFeasible π ∧ π.1 = 1 :=
  AronowAudit.P006.lower_bound_best_response_iff β hβ π

theorem lowerBound_perturbed_best (β η : ℝ) (hβ : 0 < β) (hη : 0 < η) (π : BinaryPolicy) :
    IsBest binaryPolicies (lowerBoundReward β η) π ↔ π = (1,0) :=
  AronowAudit.P006.lower_bound_perturbed_best_iff β η hβ hη π

theorem lowerBound_welfare_optimum (α β η : ℝ) (hβα : β < α) (hηα : η < α) :
    IsBest binaryPolicies (lowerBoundWelfare α β η) (0,1) ∧
    bestValue binaryPolicies (lowerBoundWelfare α β η) = (α-η)/2 :=
  AronowAudit.P006.lower_bound_welfare_optimum α β η hβα hηα

theorem scale_best {P : Type*} (S : Set P) (f : P → ℝ) (c : ℝ) (hc : 0 < c) (π : P) :
    IsBest S (fun p => c*f p) π ↔ IsBest S f π :=
  AronowAudit.P006.scale_best_iff S f c hc π

theorem retained_T29 : T29Statement := by
  refine ⟨@AronowAudit.P006.T29_ato_unbounded,
    @AronowAudit.P006.Wave1.T29_family_all_sizes_proof, ?_, ?_, ?_⟩
  · intro p _ hp
    exact AronowAudit.P006.T29_first_mode_tendsto p hp
  · intro p α
    simp [binaryWelfare]
  · intro p hp hp1
    apply (AronowAudit.P006.T29_first_mode_tendsto p hp1).congr'
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with α hα
    exact (AronowAudit.P006.T29_first_mode_welfare p α ⟨hp,hp1⟩ hα).2.2.symm

theorem fairPrivateLaw_eq : fairPrivateLaw =
    AronowAudit.P006.Wave1.BinaryExperiment.fairLaw := by
  unfold fairPrivateLaw AronowAudit.P006.Wave1.BinaryExperiment.fairLaw
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

theorem fairPrivateLaw_probability : IsProbabilityMeasure fairPrivateLaw := by
  rw [fairPrivateLaw_eq]
  exact AronowAudit.P006.Wave1.BinaryExperiment.fairLaw_probability

/-- A certified finite model used for nonvacuity and the ranking witness. -/
def constantEffectExperiment (n : ℕ) (hn : 0 < n) :
    Experiment (Fin n → Bool × Bool) Bool n :=
  Bridge.fromProject (AronowAudit.P006.Wave1.BinaryExperiment.binExp n hn
    (fun _ => 1) (fun _ _ _ => 0))

theorem constantEffect_standing (n : ℕ) (hn : 0 < n) :
    OutcomeStanding (constantEffectExperiment n hn) := by
  have h := AronowAudit.P006.Wave1.BinaryExperiment.standing_of
    AronowAudit.P006.Wave1.BinaryExperiment.n1_proof
    AronowAudit.P006.Wave1.BinaryExperiment.n3_proof
    AronowAudit.P006.Wave1.BinaryExperiment.n4_proof
    AronowAudit.P006.Wave1.BinaryExperiment.n5_proof n hn (fun _ => 1) (fun _ _ _ => 0)
  exact Bridge.standing_fromProject h

theorem constantEffect_moment (n : ℕ) (hn : 0 < n) :
    TreatedMoment (constantEffectExperiment n hn) (constantEffectExperiment n hn).μ0 := by
  intro π hπ i
  simp only [constantEffectExperiment, Bridge.fromProject,
    AronowAudit.P006.Wave1.BinaryExperiment.binExp, sub_self, mul_zero]
  exact ⟨integrable_zero _ _ _, by simp⟩

end
end SAP.P006b.WH.W1
