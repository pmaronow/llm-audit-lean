import Mathlib
import SAP.P025b.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025b
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

/-- The two retained-information counterexamples, including their exact mean sets. -/
def T16Statement : Prop :=
  ((∀ i : Fin 3, inclusion omitOneDesign i = 2/3) ∧
    classTotal omitOneDesign integralityClass 0 = 2/3 ∧
    classTotal omitOneDesign integralityClass 1 = 4/3 ∧
    populationMean integralityOutcomes = 2/3) ∧
  ((∀ m : Fin 2 → ℕ, absoluteCompatible (1/2) (3/4) ![2/3,4/3] m ↔ m = ![1,2]) ∧
    classMean binaryTwo ![1,2] = 2/3 ∧
    lowerValue binaryTwo ![2/3,4/3] (3/2) 1 = 4/7 ∧
    upperValue binaryTwo ![2/3,4/3] (3/2) 1 = 3/4 ∧
    (2/3 : ℝ)-4/7 = 2/21 ∧ (3/4 : ℝ)-2/3 = 1/12 ∧
    (4/7 : ℝ) < 2/3 ∧ (2/3 : ℝ) < 3/4 ∧
    separation binaryTwo ![2/3,4/3] (3/2)) ∧
  (absoluteCompatibleMeans binaryTwo ![2/3,4/3] (1/2) (3/4) = {(2/3:ℝ)} ∧
    ¬ IsGLB (absoluteCompatibleMeans binaryTwo ![2/3,4/3] (1/2) (3/4)) (4/7) ∧
    ¬ IsLUB (absoluteCompatibleMeans binaryTwo ![2/3,4/3] (1/2) (3/4)) (3/4)) ∧
  ((∀ m : Fin 2 → ℕ,
      (absoluteCompatible (1/10) (1/5) ![50,100] m ∧ m 0+m 1=1000) ↔
      (m 0+m 1=1000 ∧ 500 ≤ m 1 ∧ m 1 ≤ 750)) ∧
    (∀ k : ℕ, 500 ≤ k → k ≤ 750 →
      absoluteCompatible (1/10) (1/5) ![50,100] ![1000-k,k]) ∧
    classMean binaryTwo ![250,750] = 3/4 ∧
    lowerValue binaryTwo ![50,100] 2 1 = 1/2 ∧
    upperValue binaryTwo ![50,100] 2 1 = 4/5 ∧
    (4/5 : ℝ)-3/4 = 1/20 ∧ (3/4 : ℝ) < 4/5) ∧
  (knownSizeCompatibleMeans binaryTwo ![50,100] (1/10) (1/5) 1000 =
      {v | ∃ k : ℕ,500 ≤ k ∧ k ≤ 750 ∧ (k:ℝ)/1000=v} ∧
    IsLeast (knownSizeCompatibleMeans binaryTwo ![50,100] (1/10) (1/5) 1000) (1/2) ∧
    IsGreatest (knownSizeCompatibleMeans binaryTwo ![50,100] (1/10) (1/5) 1000) (3/4) ∧
    upperEndpoint binaryTwo ![50,100] (1/10) (1/5) - (3/4) = 1/20) ∧
  (IsLeast (attainable binaryTwo ![2/3,4/3] (1/2) (3/4)) (4/7) ∧
    IsGreatest (attainable binaryTwo ![2/3,4/3] (1/2) (3/4)) (3/4) ∧
    IsLeast (attainable binaryTwo ![50,100] (1/10) (1/5)) (1/2) ∧
    IsGreatest (attainable binaryTwo ![50,100] (1/10) (1/5)) (4/5))

/-- Exact Table 1 rounding audit, with every gallery/exchange grid comparison. -/
def T17Statement : Prop :=
  ((∀ k : ℤ, |100*(k:ℝ)/48 - 917/10| ≤ 1/20 ↔ k = 44) ∧
    (∀ k : ℤ, |100*(k:ℝ)/160 - 675/10| ≤ 1/20 ↔ k = 108) ∧
    (∀ k : ℤ, |100*(k:ℝ)/579 - 503/10| ≤ 1/20 ↔ k = 291)) ∧
  (100*binaryLower (44/48) 2 = 1100/13 ∧
    100*binaryLower (44/48) 4 = 220/3 ∧
    100*binaryUpper (291/579) (5/4) = 48500/869 ∧
    100*binaryLower (291/579) (3/2) = 9700/241 ∧
    100*binaryUpper (291/579) (3/2) = 9700/161 ∧
    100*binaryUpper (291/579) (5/2) = 48500/677) ∧
  (List.Forall (fun c : TableCell =>
      roundsTenth (cellPercent c.1 c.2.2.1 c.2.2.2.1) c.2.2.2.2.2 ∧
      roundsTenth (cellPercent c.2.1 c.2.2.1 c.2.2.2.1) c.2.2.2.2.1)
      tableCells ∧
    tableCells.length = 42 ∧
    (tableCells.filter (fun c => c.2.2.2.2.1 != c.2.2.2.2.2)).length = 6 ∧
    List.Forall (fun c : TableCell => c.2.2.2.2.1 = c.2.2.2.2.2 ∨
      c.2.2.2.2.1 = c.2.2.2.2.2 + 1) tableCells) ∧
  (binaryLower (44/48) 3 = 11/14 ∧ binaryUpper (291/579) 3 = 291/387 ∧
    binaryLower (44/48) 3 > binaryUpper (291/579) 3 ∧
    binaryLower (44/48) 4 = 11/15 ∧ binaryUpper (291/579) 4 = 97/121 ∧
    binaryLower (44/48) 4 < binaryUpper (291/579) 4) ∧
  (∀ γ ∈ ({1, 5/4, 3/2, 2, 5/2, 3} : Finset ℝ),
    binaryUpper (291/579) γ < binaryLower (44/48) γ ∧
    binaryUpper (503/1000) γ < binaryLower (917/1000) γ) ∧
  ((4/5 : ℝ) ∈ Set.Icc (binaryLower (44/48) 4) (binaryUpper (44/48) 4) ∩
    Set.Icc (binaryLower (291/579) 4) (binaryUpper (291/579) 4)) ∧
  ((4/5 : ℝ) ∈ Set.Icc (binaryLower (917/1000) 4) (binaryUpper (917/1000) 4) ∩
    Set.Icc (binaryLower (503/1000) 4) (binaryUpper (503/1000) 4))


end
end SAP.P025b
