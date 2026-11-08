import SAP.P047.Defs.WholeW1
import SAP.P047.Bridge
import AronowAudit.P047.Wave1.Impossibility

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace SAP.P047.WH.W1

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

/-- The finite mean used by the claim exists throughout its binary model. -/
theorem unknown_integrable (L : CausalLaw) (hL : UnknownModel L) :
    Integrable (fun u => potential true u - potential false u) L.measure := by
  apply Integrable.of_bound
    ((AronowAudit.P047.measurable_potential true).sub
      (AronowAudit.P047.measurable_potential false)).aestronglyMeasurable 1
  filter_upwards [hL.2.2.1 true, hL.2.2.1 false] with u ht hf
  change |potential true u - potential false u| ≤ 1
  rcases ht with ht | ht <;> rcases hf with hf | hf <;>
    rw [ht, hf] <;> norm_num

/-- A direct specialization of the existing generator theorems, before
identifying the generated measure with the separately defined baseline. -/
theorem generated_half_member :
    ∃ S : CausalLaw,
      S.measure = AronowAudit.P047.Wave1.Impossibility.genMeasure
        (fun _ => (1 / 2 : ℝ)) (fun _ => (1 / 2 : ℝ)) ∧
      S.propensity = (fun _ => (1 / 2 : ℝ)) ∧ UnknownModel S := by
  have hm : Measurable (fun _ : ℝ => (1 / 2 : ℝ)) := measurable_const
  have hb : ∀ _w : ℝ, 0 ≤ (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) ≤ 1 := by
    intro w
    norm_num
  obtain ⟨hI, hJ⟩ := AronowAudit.P047.Wave1.Impossibility.n3_proof
    AronowAudit.P047.Wave1.Impossibility.n2_proof _ _ hm hm hb hb
  let L : AronowAudit.P047.CausalLaw := {
    measure := AronowAudit.P047.Wave1.Impossibility.genMeasure
      (fun _ => (1 / 2 : ℝ)) (fun _ => (1 / 2 : ℝ))
    probability := inferInstance
    propensity := fun _ => 1 / 2
    measurable_propensity := hm
    ignorability := hI }
  refine ⟨Bridge.fromProject L, rfl, rfl, ?_⟩
  obtain ⟨hW, hbin, hov, _hmean⟩ :=
    AronowAudit.P047.Wave1.Impossibility.n4_proof _ _ hm hm
      (by intro w; norm_num) hb
  exact ⟨hW, hJ, hbin, hov⟩

/-- The base class of probability laws is nonempty, without using any leaf. -/
theorem unknownPopulations_nonempty : unknownPopulations.Nonempty := by
  obtain ⟨S, _hmeasure, _hpropensity, hS⟩ := generated_half_member
  exact ⟨populationProbability S, S, hS, rfl⟩

/-- The mean-existence guard is automatic on the original binary model. -/
theorem unknownPopulations_integrable :
    ∀ P ∈ unknownPopulations,
      Integrable (fun u => potential true u - potential false u) (P : Measure UnitData) := by
  rintro P ⟨L, hL, rfl⟩
  exact unknown_integrable L hL

/-- Forgetting propensity bundles does not change the set of attained values. -/
theorem unknown_values_eq (value : ProbabilityMeasure UnitData → ℝ) :
    {r | ∃ P ∈ unknownPopulations, r = value P} =
      {r | ∃ L : CausalLaw, UnknownModel L ∧ r = value (populationProbability L)} := by
  ext r
  constructor
  · rintro ⟨P, ⟨L, hL, rfl⟩, hr⟩
    exact ⟨L, hL, hr⟩
  · rintro ⟨L, hL, hr⟩
    exact ⟨populationProbability L, ⟨L, hL, rfl⟩, hr⟩

section Reindex

variable {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q]

theorem wholeRisk_unknown
    (E : (n : ℕ) → ((Fin n → ObservedUnit) × R) → ℝ) (n : ℕ) (η : ℝ) :
    wholeRisk unknownPopulations Q E n η = randRisk Q E n η := by
  unfold wholeRisk modelEventSup
  rw [unknown_values_eq]
  rfl

theorem wholeStrictRisk_unknown
    (E : (n : ℕ) → ((Fin n → ObservedUnit) × R) → ℝ) (n : ℕ) (η : ℝ) :
    wholeStrictRisk unknownPopulations Q E n η = randStrictRisk Q E n η := by
  unfold wholeStrictRisk modelEventSup
  rw [unknown_values_eq]
  rfl

theorem wholeCoverage_unknown
    (lo hi : (n : ℕ) → ((Fin n → ObservedUnit) × R) → EReal) (n : ℕ) :
    wholeCoverage unknownPopulations Q lo hi n = randCoverage Q lo hi n := by
  unfold wholeCoverage modelEventInf
  rw [unknown_values_eq]
  rfl

end Reindex

section ModelOrder

variable {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q]
variable (M : Set (ProbabilityMeasure UnitData))
variable (event : ProbabilityMeasure UnitData → Set ((ℕ → UnitData) × R))

theorem modelEventSup_bounds :
    0 ≤ modelEventSup M Q event ∧ modelEventSup M Q event ≤ 1 := by
  have hb : ∀ p ∈ insert (0 : ℝ) {p | ∃ P ∈ M,
      p = ((sampleLaw (P : Measure UnitData)).prod Q).real (event P)}, p ≤ 1 := by
    rintro p (rfl | ⟨P, _hP, rfl⟩)
    · norm_num
    · exact measureReal_le_one
  exact ⟨le_csSup ⟨1, hb⟩ (Set.mem_insert _ _),
    csSup_le (Set.insert_nonempty _ _) hb⟩

theorem modelEventInf_bounds :
    0 ≤ modelEventInf M Q event ∧ modelEventInf M Q event ≤ 1 := by
  have hb : ∀ p ∈ insert (1 : ℝ) {p | ∃ P ∈ M,
      p = ((sampleLaw (P : Measure UnitData)).prod Q).real (event P)}, 0 ≤ p := by
    rintro p (rfl | ⟨P, _hP, rfl⟩)
    · norm_num
    · exact measureReal_nonneg
  exact ⟨le_csInf (Set.insert_nonempty _ _) hb,
    csInf_le ⟨0, hb⟩ (Set.mem_insert _ _)⟩

theorem modelEventSup_at (P : ProbabilityMeasure UnitData) (hP : P ∈ M) :
    ((sampleLaw (P : Measure UnitData)).prod Q).real (event P) ≤
      modelEventSup M Q event := by
  unfold modelEventSup
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro p (rfl | ⟨K, _hK, rfl⟩)
    · norm_num
    · exact measureReal_le_one
  · exact Set.mem_insert_of_mem _ ⟨P, hP, rfl⟩

theorem modelEventSup_mono {N : Set (ProbabilityMeasure UnitData)} (hMN : M ⊆ N) :
    modelEventSup M Q event ≤ modelEventSup N Q event := by
  apply csSup_le (Set.insert_nonempty _ _)
  rintro p (rfl | ⟨L, hL, rfl⟩)
  · exact (modelEventSup_bounds Q N event).1
  · exact modelEventSup_at Q N event L (hMN hL)

theorem modelEventInf_antitone {N : Set (ProbabilityMeasure UnitData)} (hMN : M ⊆ N) :
    modelEventInf N Q event ≤ modelEventInf M Q event := by
  apply csInf_le_csInf _ (Set.insert_nonempty _ _)
  · rintro p (rfl | ⟨L, hL, rfl⟩)
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨L, hMN hL, rfl⟩
  · refine ⟨0, ?_⟩
    rintro p (rfl | ⟨L, _hL, rfl⟩)
    · norm_num
    · exact measureReal_nonneg

end ModelOrder

/-- Probability bounds discharge the boundedness requirements for real limsup. -/
theorem unit_limsup_mono {f g : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, g n ≤ 1) (hfg : ∀ n, f n ≤ g n) :
    Filter.limsup f atTop ≤ Filter.limsup g atTop := by
  exact Filter.limsup_le_limsup (Eventually.of_forall hfg)
    (Filter.isCoboundedUnder_le_of_le atTop hf)
    (Filter.isBoundedUnder_of ⟨1, hg⟩)

/-- Probability bounds discharge the boundedness requirements for real liminf. -/
theorem unit_liminf_mono {f g : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, g n ≤ 1) (hfg : ∀ n, f n ≤ g n) :
    Filter.liminf f atTop ≤ Filter.liminf g atTop := by
  exact Filter.liminf_le_liminf (Eventually.of_forall hfg)
    (Filter.isBoundedUnder_of ⟨0, hf⟩)
    (Filter.isCoboundedUnder_ge_of_le atTop hg)

/-- A positive lower bound on the limit inferior rules out convergence to zero. -/
theorem not_tendsto_zero_of_liminf_pos {f : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hcf : c ≤ Filter.liminf f atTop) :
    ¬ Tendsto f atTop (𝓝 0) := by
  intro hf
  have hz : Filter.liminf f atTop = 0 := hf.liminf_eq
  rw [hz] at hcf
  exact (not_le_of_gt hc) hcf

end

end SAP.P047.WH.W1
