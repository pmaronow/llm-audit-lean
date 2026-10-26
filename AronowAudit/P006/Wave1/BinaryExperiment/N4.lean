import AronowAudit.P006.Wave1.BinaryExperimentBlueprint

set_option autoImplicit false
namespace AronowAudit.P006.Wave1.BinaryExperiment
open AronowAudit.P006 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section

theorem n4_proof : N4 := by
  classical
  intro h1 n hn y1 μhat
  let E := binExp n hn y1 μhat
  have hfair : IsProbabilityMeasure fairLaw := by
    constructor
    norm_num [fairLaw, Fintype.sum_bool, Measure.add_apply, Measure.smul_apply]
    exact ENNReal.inv_two_add_inv_two
  haveI : IsProbabilityMeasure E.PX := hfair
  have hstate (π : Bool → ℝ) (hπ : Admissible π) (i : Fin n) :
      IdentDistrib (fun ω : Fin n → Bool × Bool => ω i) id (E.law π) (unitLaw π) := by
    haveI : IsProbabilityMeasure (unitLaw π) := (h1 π hπ).1
    refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa [E, binExp] using (measurePreserving_eval (fun _ : Fin n => unitLaw π) i).map_eq
  have hX (π : Bool → ℝ) (hπ : Admissible π) (i : Fin n) :
      IdentDistrib (E.X i) id (E.law π) E.PX := by
    refine ⟨(measurable_of_finite _).aemeasurable, measurable_id.aemeasurable, ?_⟩
    have h := (hstate π hπ i).comp measurable_fst
    simpa [Function.comp_def, E, binExp, (h1 π hπ).2.2] using h.map_eq
  have htriple (π : Bool → ℝ) (hπ : Admissible π) (i : Fin n) :
      IdentDistrib (fun ω => (E.X i ω, E.Y0 i ω, E.Y1 i ω))
        (fun x : Bool => (x, (0 : ℝ), y1 x)) (E.law π) fairLaw := by
    simpa [Function.comp_def, E, binExp] using
      (hX π hπ i).comp (measurable_of_finite (fun x : Bool => (x, (0 : ℝ), y1 x)))
  have hall (π : Bool → ℝ) (hπ : Admissible π) (i : Fin n) :
      IdentDistrib (fun ω => (E.X i ω, E.Y0 i ω, E.Y1 i ω, E.T π i ω))
        (fun a : Bool × Bool => (a.1, (0 : ℝ), y1 a.1, a.2)) (E.law π) (unitLaw π) := by
    simpa [Function.comp_def, E, binExp] using
      (hstate π hπ i).comp
        (measurable_of_finite (fun a : Bool × Bool => (a.1, (0 : ℝ), y1 a.1, a.2)))
  have hprob (π : Bool → ℝ) (hπ : Admissible π) : IsProbabilityMeasure (E.law π) := by
    haveI : IsProbabilityMeasure (unitLaw π) := (h1 π hπ).1
    dsimp [E, binExp]
    infer_instance
  refine ⟨hfair, ⟨measurable_of_finite _, measurable_of_finite _⟩,
    ⟨Integrable.of_finite, Integrable.of_finite⟩, hprob, ?_, ?_, hX, ?_, ?_, ?_⟩
  · intro π hπ i
    exact ⟨measurable_of_finite _, measurable_of_finite _,
      measurable_of_finite _, measurable_of_finite _⟩
  · intro π hπ i
    haveI := hprob π hπ
    exact ⟨Integrable.of_finite, Integrable.of_finite, Integrable.of_finite⟩
  · intro π π' hπ hπ' i
    exact (htriple π hπ i).trans (htriple π' hπ' i).symm
  · intro π hπ
    haveI : IsProbabilityMeasure (unitLaw π) := (h1 π hπ).1
    exact iIndepFun_pi (fun _ => (measurable_of_finite
      (fun a : Bool × Bool => (a.1, (0 : ℝ), y1 a.1, a.2))).aemeasurable)
  · intro π hπ i j
    exact (hall π hπ i).trans (hall π hπ j).symm

end
end AronowAudit.P006.Wave1.BinaryExperiment
