import SAP.P001f.WH.W1.LeavesCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001f.WH.W1

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section
universe u v
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Uniform response overlap promotes a measurable covariate function from
respondent L1 to population L1. Let H=m(X). Binarity identifies H*R with
the integrable respondent indicator. Pull H out of E[H*R|sigma(X)] without
assuming H integrable, replace E[R|X] by p(X), and obtain H*p(X) in L1.
Multiply by 1/p(X), bounded by 1/epsilon. No MAR assumption is needed for
this moment lemma. Expected size: 60–110 lines. -/
def T111_L1 : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E), Measurable X →
    ∀ (R : Ω → ℝ), Measurable R →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    ∀ p m : E → ℝ, ConditionalMean μ X R p → Measurable m →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω)) →
    Integrable (m ∘ X) (μ.restrict {ω | R ω = 1}) → Integrable (m ∘ X) μ

/-- Integrate a countably ranged covariate function over its positive-mass
support, including absolute summability. Reindex to `Set.range X`, invoke
`MarDiscrete.n1_proof` (or `hasSum_integral_iUnion`) for m and |m|, and
delete zero-mass cells. No countability assumption on the ambient E is made.
Expected size: 100–180 lines. -/
def T111_L2 : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E), Measurable X →
    Set.Countable (Set.range X) → ∀ m : E → ℝ, Measurable m →
    Integrable (m ∘ X) μ →
    Summable (fun x : wholeMassSupport μ X => m x * (μ {ω | X ω = x}).toReal) ∧
    Summable (fun x : wholeMassSupport μ X => |m x| * (μ {ω | X ω = x}).toReal) ∧
    (∫ ω, m (X ω) ∂μ) =
      ∑' x : wholeMassSupport μ X, m x * (μ {ω | X ω = x}).toReal

theorem T111_assembly (h1 : T111_L1.{u, 0}) (h2 : T111_L2.{u, 0}) :
    T111WholeStatement.{u} := by
  classical
  refine ⟨AronowAudit.P001.Wave1.mcar_paper_support_mean, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ω _ K μ _ X hX Y R hY hR hYi hb hR0 hR1 p m hp hpos hCI hm
    have hmi := h1 μ X hX R hR hb p m hp hm.1 hpos hm.2.2.1
    obtain ⟨hpop, hmean⟩ := AronowAudit.P001.Wave1.mar_vector_paper_support_cef
      μ X hX Y R hY hR hYi hb hR0 hR1 p m hp hpos hCI hm hmi
    refine ⟨hmi, hpop, hmean, ?_⟩
    intro hcount
    obtain ⟨hs, habs, heq⟩ := h2 μ X hX hcount m hm.1 hmi
    exact ⟨hs, habs, hmean.trans heq⟩
  · intros
    rfl
  · intro n K _ y r X _ _
    simp only [wholeResponsePlugin, wholeTreatedSum, wholeTreatedCount, wholeCellSize]
    congr 1
    funext x
    congr 2
    all_goals
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : X i = x <;> simp [h]
  · exact AronowAudit.P001.missing_mcar_mar_sample_estimates.1
  · have hs : wholeObservedCells exampleCovariate = ({0, 1} : Finset (Fin 2)) := by
      ext x
      fin_cases x <;> norm_num [wholeObservedCells, exampleCovariate, Fin.exists_fin_succ]
    unfold wholeResponsePlugin
    rw [hs]
    simp only [wholeTreatedSum,
      wholeTreatedCount, wholeCellSize, exampleCensored, exampleIndicator,
      exampleCovariate, Fin.sum_univ_succ]
    norm_num
  · have hs : wholeObservedCells exampleCovariate = ({0, 1} : Finset (Fin 2)) := by
      ext x
      fin_cases x <;> norm_num [wholeObservedCells, exampleCovariate, Fin.exists_fin_succ]
    unfold wholeResponsePlugin
    rw [hs]
    simp only [wholeTreatedSum,
      wholeTreatedCount, wholeCellSize, exampleCensored, exampleIndicator,
      exampleCovariate, Fin.sum_univ_succ]
    norm_num

/-- Residual orthogonality with only a square-integrable residual.
From the CEF integral contract obtain the zero CEF of R=Y-m(X), then
identify E[R|sigma(X)]=0 with
`isCEF_condExp`. Pull the measurable d(X) out of E[d(X)*R|sigma(X)]; its
product is integrable by Cauchy–Schwarz. Integrate the conditional expectation.
Do not assume Y or m(X) belongs to L2. Expected size: 40–80 lines. -/
def T107_L1V2 : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E), Measurable X →
    ∀ Y : Ω → ℝ, Measurable Y → ∀ m : E → ℝ, ConditionalMean μ X Y m →
    Integrable (fun ω => (Y ω - m (X ω)) ^ 2) μ →
    ∀ d : E → ℝ, Measurable d → MemLp (d ∘ X) 2 μ →
      (∫ ω, d (X ω) * (Y ω - m (X ω)) ∂μ) = 0

theorem T107_assembly (h1 : T107_L1V2.{u, v}) : T107WholeStatement.{u, v} := by
  intro Ω E _ _ μ _ X Y hX hY hYi m hm
  refine ⟨AronowAudit.P001.iterated_expectation μ X Y hYi m hm, ?_, ?_⟩
  · intro hY2
    have hm2 : MemLp (m ∘ X) 2 μ :=
      (memLp_congr_ae (AronowAudit.P001.isCEF_condExp μ X hX Y m hm)).mpr
        (MemLp.condExp (m := MeasurableSpace.comap X inferInstance) one_le_two hY2)
    refine ⟨hm2, ?_⟩
    intro v hv
    have horth := (AronowAudit.P001.cef_residual_orthogonality_correction
      μ X hX Y hY2 m hm hm2).2.2
    have hCov : covariance (m ∘ X) Y μ = variance (m ∘ X) μ := by
      have hc := horth m hm.1 hm2
      change covariance (m ∘ X) (Y - (m ∘ X)) μ = 0 at hc
      rw [covariance_sub_right hm2 hY2 hm2, covariance_self hm2.aemeasurable] at hc
      exact sub_eq_zero.mp hc
    have hres := (AronowAudit.P001.cef_residual_conditional_variance
      μ X hX Y hY2 m v hm hm2 hv).2
    change variance (Y - (m ∘ X)) μ = (∫ ω, v (X ω) ∂μ) at hres
    have hvar := variance_sub hY2 hm2
    rw [covariance_comm Y (m ∘ X), hCov, hres] at hvar
    change (∫ ω, v (X ω) ∂μ) = variance Y μ -
      2 * variance (m ∘ X) μ + variance (m ∘ X) μ at hvar
    linarith
  · intro v hv g hg hUi
    let R : Ω → ℝ := fun ω => Y ω - m (X ω)
    let U : Ω → ℝ := fun ω => Y ω - g (X ω)
    let D : Ω → ℝ := fun ω => m (X ω) - g (X ω)
    have hR2 : MemLp R 2 μ :=
      (memLp_two_iff_integrable_sq
        ((hY.sub (hm.1.comp hX)).aestronglyMeasurable)).mpr hv.2.1
    have hU2 : MemLp U 2 μ :=
      (memLp_two_iff_integrable_sq
        ((hY.sub (hg.comp hX)).aestronglyMeasurable)).mpr hUi
    have hD : D = U - R := by funext ω; dsimp [D, U, R]; ring
    have hD2 : MemLp D 2 μ := by rw [hD]; exact hU2.sub hR2
    have hDR0 : (∫ ω, D ω * R ω ∂μ) = 0 :=
      h1 μ X hX Y hY m hm hv.2.1 (fun x => m x - g x) (hm.1.sub hg) hD2
    have hER : (∫ ω, R ω ^ 2 ∂μ) = ∫ ω, v (X ω) ∂μ :=
      AronowAudit.P001.iterated_expectation μ X _ hv.2.1 v hv
    have hfun : (fun ω => U ω ^ 2) =
        (fun ω => R ω ^ 2 + (2 * (D ω * R ω) + D ω ^ 2)) := by
      funext ω
      dsimp [U, R, D]
      ring
    have hDRi : Integrable (fun ω => D ω * R ω) μ := hD2.integrable_mul hR2
    have h2DRi := hDRi.const_mul 2
    have hDi := hD2.integrable_sq
    have hsumi : Integrable (fun ω => 2 * (D ω * R ω) + D ω ^ 2) μ :=
      h2DRi.add hDi
    have heq : (∫ ω, U ω ^ 2 ∂μ) =
        (∫ ω, v (X ω) ∂μ) + (∫ ω, D ω ^ 2 ∂μ) := by
      rw [hfun, integral_add hR2.integrable_sq hsumi,
        integral_add h2DRi hDi, integral_const_mul, hDR0, hER]
      ring
    have hnonneg : 0 ≤ (∫ ω, D ω ^ 2 ∂μ) := integral_nonneg (fun ω => sq_nonneg _)
    have hmin : (∫ ω, v (X ω) ∂μ) ≤ ∫ ω, U ω ^ 2 ∂μ := by
      rw [heq]
      exact le_add_of_nonneg_right hnonneg
    refine ⟨hDi, heq, hnonneg, ?_, hmin, hER.symm⟩
    change (∫ ω, R ω ^ 2 ∂μ) ≤ ∫ ω, U ω ^ 2 ∂μ
    rw [hER]
    exact hmin

end
end SAP.P001f.WH.W1
