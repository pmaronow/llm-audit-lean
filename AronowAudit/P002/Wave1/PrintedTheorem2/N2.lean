import AronowAudit.P002.Wave1.PrintedTheorem2Blueprint

namespace AronowAudit.P002.Wave1.PrintedTheorem2
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- The intercept normal equation centers each residual schedule before collapse. -/
theorem n2_proof : N2 := by
  intro hGram n P hXi
  have hg : (gram P.x Finset.univ).det ≠ 0 :=
    hGram n 1 P 0 (1/4) 4 (1/2) (1/4) (by norm_num) hXi
  rcases hXi with ⟨hD, _, _, _, _, _, hmoment, _, _, _⟩
  intro a
  let q : Fin n → ℝ := residual P a (late P.pop)
  have hscore : score P.x Finset.univ q = 0 := by
    change score P.x Finset.univ
      (fun i => w P.pop a (late P.pop) i -
        dotProduct (augmented P.x i)
          (ols P.x Finset.univ (w P.pop a (late P.pop)))) = 0
    rw [score_residual,
      ← ols_normal_equations P.x Finset.univ (w P.pop a (late P.pop)) hg,
      sub_self]
  have hmean : mean q = 0 := by
    have hnone := congrFun hscore none
    simpa [score, augmented, groupMean, mean] using hnone
  have hmoment' : fourthNorm q ≤
      (1/2) * Real.sqrt ((∑ i, q i ^ 2) / ((n : ℝ) - 1)) := by
    have h := hmoment a
    change fourthNorm q ≤ (1/2) * Real.sqrt (popVar q) at h
    simpa only [popVar, hmean, sub_zero] using h
  exact half_moment_collapse q hD.1 hmoment'

end
end AronowAudit.P002.Wave1.PrintedTheorem2
