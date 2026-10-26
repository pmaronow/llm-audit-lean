import AronowAudit.P006.Wave1.BinaryExperimentBlueprint

set_option autoImplicit false
namespace AronowAudit.P006.Wave1.BinaryExperiment
open AronowAudit.P006 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section

lemma unitMass_nonneg (π : Bool → ℝ) (hπ : Admissible π) (a : Bool × Bool) :
    0 ≤ (1 / 2 : ℝ) * coinMass (π a.1) a.2 :=
  mul_nonneg (by norm_num) ((coin_is_probability _ (hπ.2 a.1)).1 a.2)

lemma unitMass_coe (π : Bool → ℝ) (hπ : Admissible π) (a : Bool × Bool) :
    (unitMass π a : ℝ) = (1 / 2 : ℝ) * coinMass (π a.1) a.2 :=
  Real.coe_toNNReal _ (unitMass_nonneg π hπ a)

lemma unitMass_pair (π : Bool → ℝ) (hπ : Admissible π) (x : Bool) :
    unitMass π (x, true) + unitMass π (x, false) = (1 / 2 : ℝ≥0) := by
  apply NNReal.coe_injective
  simp only [NNReal.coe_add, unitMass_coe π hπ]
  norm_num [coinMass]
  <;> ring

lemma fairLaw_probability : IsProbabilityMeasure fairLaw := by
  constructor
  norm_num [fairLaw, Fintype.sum_bool, Measure.add_apply, Measure.smul_apply]
  exact ENNReal.inv_two_add_inv_two

theorem n1_proof : N1 := by
  classical
  intro π hπ
  have hmap : (unitLaw π).map Prod.fst = fairLaw := by
    -- Expand four atoms, then combine the two treatment atoms over each covariate.
    simp only [unitLaw, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [Measure.map_add _ _ measurable_fst,
      Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_dirac]
    simp only [← add_smul, unitMass_pair π hπ]
    simp [fairLaw, Fintype.sum_bool]
  have hprob : IsProbabilityMeasure (unitLaw π) := by
    constructor
    have h := congrArg (fun μ : Measure Bool => μ Set.univ) hmap
    haveI := fairLaw_probability
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,
      Set.preimage_univ, measure_univ] using h
  refine ⟨hprob, ?_, hmap⟩
  intro a
  have ha : unitLaw π {a} = (unitMass π a : ℝ≥0∞) := by
    rcases a with ⟨x,t⟩
    cases x <;> cases t <;>
      simp [unitLaw, Fintype.sum_prod_type, Fintype.sum_bool,
        Measure.add_apply, Measure.smul_apply, Measure.dirac_apply]
  rw [ha]
  rfl

end
end AronowAudit.P006.Wave1.BinaryExperiment
