import AronowAudit.P001.Wave1.PdaMeanNotIdentifiedBlueprint

namespace AronowAudit.P001.Wave1.PdaMeanNotIdentified

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidablePdaMeanNotIdentifiedN1 (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The two intervals used by the density are disjoint. -/
lemma gap_intervals_disjoint :
    Disjoint (Set.Icc (-2 : ℝ) (-1)) (Set.Icc (1 : ℝ) 2) := by
  refine Set.disjoint_left.mpr ?_
  intro x hx hy
  have hx' : x ≤ -1 := hx.2
  have hy' : 1 ≤ x := hy.1
  linarith

lemma gap_support_volume :
    volume (Set.Icc (-2 : ℝ) (-1) ∪ Set.Icc (1 : ℝ) 2) = 2 := by
  rw [measure_union gap_intervals_disjoint measurableSet_Icc,
    Real.volume_Icc, Real.volume_Icc]
  norm_num

lemma gapPDF_eq_indicator : gapPDF =
    (Set.Icc (-2 : ℝ) (-1) ∪ Set.Icc (1 : ℝ) 2).indicator (fun _ => (1 / 2 : ℝ)) := by
  funext x
  by_cases hx : x ∈ Set.Icc (-2 : ℝ) (-1) ∪ Set.Icc (1 : ℝ) 2 <;>
    simp [gapPDF, Set.indicator, hx]

theorem n1_proof : N1 := by
  have hs : MeasurableSet (Set.Icc (-2 : ℝ) (-1) ∪ Set.Icc (1 : ℝ) 2) :=
    measurableSet_Icc.union measurableSet_Icc
  have hm : Measurable gapPDF := by
    rw [gapPDF_eq_indicator]
    exact measurable_const.indicator hs
  have hi : Integrable gapPDF volume := by
    rw [gapPDF_eq_indicator]
    apply IntegrableOn.integrable_indicator _ hs
    exact integrableOn_const (by rw [gap_support_volume]; norm_num)
  refine ⟨hm, ?_, hi, ?_, ?_⟩
  · intro x
    unfold gapPDF
    split_ifs <;> norm_num
  · intro x hx
    have hmem : x ∈ Set.Icc (-2 : ℝ) (-1) ∪ Set.Icc (1 : ℝ) 2 := by
      by_contra h
      simp [gapPDF, h] at hx
    rcases hmem with h | h
    · have hx0 : x ≤ 0 := le_trans h.2 (by norm_num)
      rw [abs_of_nonpos hx0]
      constructor <;> linarith [h.1, h.2]
    · have hx0 : 0 ≤ x := le_trans (by norm_num) h.1
      rw [abs_of_nonneg hx0]
      exact h
  · norm_num [gapPDF]

end
end AronowAudit.P001.Wave1.PdaMeanNotIdentified
