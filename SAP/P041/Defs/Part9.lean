import SAP.P041.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041
open Matrix
open scoped BigOperators

/-- Mathematical content packaged for P041-T7. -/
def T7Statement : Prop :=
  ((fun j l => ∑ i : Fin 4, (50:ℝ) * citationCellDesign i j *
      citationCellDesign i l) = citationGram ∧
    (fun j => ∑ i : Fin 4, citationCellSurvivors i * citationCellDesign i j) =
      ![102,67,65] ∧
    citationGram * citationGramInverse = 1 ∧
    citationGramInverse * citationGram = 1 ∧
    citationGramInverse *ᵥ ![102,67,65] = citationBeta ∧
    citationBeta 1 = 0.320 ∧
    citationBeta 1 = (1/2)*((25-12)/50 + (42-23)/50)) ∧
  (citationGram⁻¹ = citationGramInverse) ∧
  ((fun i => citationCellDesign i ⬝ᵥ citationBeta) = ![21/100,53/100,49/100,81/100] ∧
    binaryCellSSR 50 12 (21/100) = 1833/200 ∧
    binaryCellSSR 50 25 (53/100) = 2509/200 ∧
    binaryCellSSR 50 23 (49/100) = 2493/200 ∧
    binaryCellSSR 50 42 (81/100) = 1353/200 ∧
    ((1833/200 + 2509/200 + 2493/200 + 1353/200 : ℝ)) = 2047/50 ∧
    (∀ i : Fin 4, (citationGramInverse 1 ⬝ᵥ citationCellDesign i)^2 = 1/10000) ∧
    (200/197 : ℝ) * (∑ i : Fin 4,
      binaryCellSSR 50 (citationCellSurvivors i) (citationCellDesign i ⬝ᵥ citationBeta) *
      (citationGramInverse 1 ⬝ᵥ citationCellDesign i)^2) = 2047/492500) ∧
  ((0.320/0.645 : ℝ) = 64/129 ∧ (64/129 : ℝ) < 1 ∧
    (0.0635 : ℝ)^2 ≤ 2047/492500 ∧ (2047/492500 : ℝ) < 0.0645^2 ∧
    0.0635 ≤ Real.sqrt (2047/492500) ∧ Real.sqrt (2047/492500) < 0.0645 ∧
    (0.645 : ℝ)^2 = 16641/40000 ∧ (16641/40000 : ℝ) ≠ 2047/492500 ∧
    ((8/25 : ℝ)^2 / (2047/492500)) = 50432/2047 ∧
    (24 : ℝ) < 50432/2047 ∧ (2.61 : ℝ)^2 < 24 ∧
    4.89 < (8/25 : ℝ) / Real.sqrt (2047/492500) ∧
    2.61 < (8/25 : ℝ) / Real.sqrt (2047/492500)) ∧
  ((fun i : Fin 4 => citationGramInverse 1 ⬝ᵥ citationCellDesign i) =
      ![-1/100,1/100,-1/100,1/100])

end SAP.P041
