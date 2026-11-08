import SAP.P010.Bridge.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P010.Bridge

open MeasureTheory Set
open AronowAudit.P010

/-- Standard finite-sum, finite-scaling and Dirac integrability, followed by
restriction, certify every real integrand on the existing six-atom witness. -/
theorem selection_integrableOn (q : ℝ) (f : State 2 1 → ℝ) (E : Set (State 2 1)) :
    Integrable f ((selectionLaw q).restrict E) := by
  apply Integrable.restrict
  rw [selectionLaw, finiteLaw, Measure.sum_fintype]
  apply integrable_finsetSum_measure.mpr
  intro i hi
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- Each selected arm has two of the six equally weighted atoms. -/
theorem selection_selected_mass (a : Fin 2) :
    selectionLaw (1/2) (passEvent ∩ armEvent a) = 1/3 := by
  letI : IsProbabilityMeasure (selectionLaw (1/2)) :=
    (selection_counterexample_corrected (1/2) (by norm_num) (by norm_num)).1.1
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by norm_num)).mp
  rw [selectionLaw, finiteLaw_apply_real _ _ (by intro i; split_ifs <;> norm_num)]
  fin_cases a <;>
    norm_num [selectionAtoms, passEvent, armEvent, observedS, potentialS,
      assignment, Fin.sum_univ_succ]

/-- The covariate of every displayed atom is the zero vector. -/
theorem selection_zero_covariates (q : ℝ) :
    covariates =ᵐ[selectionLaw q] fun _ => (fun _ => (0 : ℝ)) := by
  apply finiteLaw_ae
  intro i
  fin_cases i <;> rfl

/-- Conditioning additionally on the witness's zero covariate changes no event. -/
theorem selection_covariate_event (q : ℝ) (E : Set (State 2 1)) :
    (E ∩ {ω | covariates ω = fun _ => 0}) =ᵐ[selectionLaw q] E := by
  filter_upwards [selection_zero_covariates q] with ω hω
  simp [hω]

end SAP.P010.Bridge
