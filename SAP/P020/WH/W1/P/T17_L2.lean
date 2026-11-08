import SAP.P020.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P020.WH.W1.P.T17_L2

open scoped BigOperators
open MeasureTheory ProbabilityTheory SAP.P020.WH.W1

theorem fullLaw_errorProbability_eq_card_ratio
    (Ω : Type*) [Fintype Ω] [Nonempty Ω] (T : Ω → ℝ) (d ε : ℝ) :
    errorProbability (SAP.P020.WH.W1.fullLaw Ω) T d ε =
      ((Finset.univ.filter fun ω => ε < |T ω - d|).card : ℝ) /
        (Fintype.card Ω : ℝ) := by
  classical
  let s : Finset Ω := Finset.univ.filter fun ω => ε < |T ω - d|
  simp only [errorProbability, SAP.P020.WH.W1.fullLaw, uniformLaw]
  have hs :
      (∑ ω : Ω, if ε < |T ω - d| then 1 / ((Finset.univ : Finset Ω).card : ℝ) else 0) =
        ∑ ω ∈ s, 1 / ((Finset.univ : Finset Ω).card : ℝ) := by
    simpa [s] using
      (Finset.sum_filter (s := (Finset.univ : Finset Ω))
        (p := fun ω : Ω => ε < |T ω - d|)
        (f := fun _ : Ω => 1 / ((Finset.univ : Finset Ω).card : ℝ))).symm
  have hconst :
      (∑ ω ∈ s, 1 / ((Finset.univ : Finset Ω).card : ℝ)) =
        (s.card : ℝ) * (1 / ((Finset.univ : Finset Ω).card : ℝ)) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.univ : Finset Ω).card : ℝ) = (Fintype.card Ω : ℝ) := by simp
  rw [hs, hconst, hcard, one_div, div_eq_mul_inv]

end SAP.P020.WH.W1.P.T17_L2

theorem SAP.P020.WH.W1.T17_L2_proof : SAP.P020.WH.W1.T17_L2 := by
  classical
  intro Ω hF hN m hS T d ε
  let s : Finset Ω := Finset.univ.filter fun ω => ε < |T ω - d|
  have hs : (s : Set Ω) = {ω | ε < |T ω - d|} := by
    ext ω
    simp [s]
  rw [← hs]
  calc
    (MeasureTheory.Measure.real (ProbabilityTheory.uniformOn Set.univ) (s : Set Ω)) =
        (s.card : ℝ) / (Fintype.card Ω : ℝ) := by
      simp [MeasureTheory.Measure.real, ProbabilityTheory.uniformOn_univ,
        MeasureTheory.Measure.count_apply_finset]
    _ = errorProbability (SAP.P020.WH.W1.fullLaw Ω) T d ε :=
      (SAP.P020.WH.W1.P.T17_L2.fullLaw_errorProbability_eq_card_ratio Ω T d ε).symm
