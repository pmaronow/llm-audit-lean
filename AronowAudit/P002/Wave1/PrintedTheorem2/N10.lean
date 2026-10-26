import AronowAudit.P002.Wave1.PrintedTheorem2Blueprint
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace AronowAudit.P002.Wave1.PrintedTheorem2
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Squeeze the exact nested infimum, using the grid only for its upper bound. -/
theorem n10_proof : N10 := by
  intro hprob hcoverage hgrid α
  have hlower (n : ℕ) (hn : 2 ≤ n) :
      ENNReal.ofReal (max 0 (1 - 1548 / ((n : ℝ) - 1))) ≤
        infCoverageXi n 1 0 (1/4) 4 (1/2) (1/4) α := by
    unfold infCoverageXi
    apply le_iInf
    intro β
    apply le_iInf
    intro P
    apply ENNReal.ofReal_le_ofReal
    simpa only [P.property.2] using hcoverage n P.val α hn P.property.1
  have hupper (n : ℕ) (hn : 2 ≤ n) :
      infCoverageXi n 1 0 (1/4) 4 (1/2) (1/4) α ≤ 1 := by
    unfold infCoverageXi
    apply iInf_le_of_le (0 : ℝ)
    let P : {P : CovPopulation n 1 //
        Xi P 0 (1/4) 4 (1/2) (1/4) ∧ late P.pop = 0} :=
      ⟨degenerateCovModel n 0, hgrid n hn 0⟩
    calc
      _ ≤ ENNReal.ofReal (adjustedCoverage P.val 0 α) := iInf_le _ P
      _ ≤ ENNReal.ofReal (1 : ℝ) := by
        apply ENNReal.ofReal_le_ofReal
        exact ((hprob n P.val.pop).1 (adjustedAccepted P.val 0 α)).2
      _ = 1 := ENNReal.ofReal_one
  have hdenom : Tendsto (fun n : ℕ => (n : ℝ) - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ)
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hquot : Tendsto (fun n : ℕ => 1548 / ((n : ℝ) - 1)) atTop (nhds (0 : ℝ)) :=
    hdenom.const_div_atTop 1548
  have hone : Tendsto (fun n : ℕ => 1 - 1548 / ((n : ℝ) - 1)) atTop (nhds (1 : ℝ)) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hquot
  have hmax : Tendsto (fun n : ℕ => max 0 (1 - 1548 / ((n : ℝ) - 1)))
      atTop (nhds (1 : ℝ)) := by
    simpa only [max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)] using
      (tendsto_const_nhds (x := (0 : ℝ))).max hone
  have hlim : Tendsto
      (fun n : ℕ => ENNReal.ofReal (max 0 (1 - 1548 / ((n : ℝ) - 1))))
      atTop (nhds (1 : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.tendsto_ofReal hmax
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
    (eventually_atTop.mpr ⟨2, hlower⟩) (eventually_atTop.mpr ⟨2, hupper⟩)

end
end AronowAudit.P002.Wave1.PrintedTheorem2
