import Mathlib
import SAP.P008a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P008a

open MeasureTheory Filter
open scoped BigOperators Classical

noncomputable section

def printedGrid (k : Fin 5) : ℝ := 5 * (k : ℝ) / 111

def correctedGrid (k : Fin 41) : ℝ := (k : ℝ) / 222

def inUgandaRange (d : ℝ) : Prop := 1 / 111 ≤ d ∧ d ≤ 5 / 222

instance (d : ℝ) : Decidable (inUgandaRange d) := inferInstanceAs
  (Decidable (1 / 111 ≤ d ∧ d ≤ 5 / 222))

def sixAssignment (k : Fin 6) : Assignment 4 :=
  ![![true, true, false, false], ![true, false, true, false],
    ![true, false, false, true], ![false, true, true, false],
    ![false, true, false, true], ![false, false, true, true]] k

def blockedAssignment (k : Fin 4) : Assignment 4 := sixAssignment (![1, 2, 3, 4] k)

def treatedCount {N : ℕ} (z : Assignment N) : ℕ := ∑ i, if z i then 1 else 0

def contrast4 (y : Fin 4 → ℝ) (z : Assignment 4) : ℝ :=
  (∑ i, bit (z i) * y i) / 2 - (∑ i, (1 - bit (z i)) * y i) / 2

def sixComplement (k : Fin 6) : Fin 6 := ![5, 4, 3, 2, 1, 0] k

def percentileExample (k : Fin 6) : ℝ := ![-2, -1, 0, 0, 1, 2] k

def supportMass (S : Finset (Finset ℕ)) (z : Finset ℕ) : ℝ :=
  if z ∈ S then (S.card : ℝ)⁻¹ else 0

def unrestricted121 : Finset (Finset ℕ) := (Finset.range 121).powersetCard 60

def blocked121 : Finset (Finset ℕ) :=
  (((Finset.range 10).powersetCard 5).product
    ((Finset.Ico 10 121).powersetCard 55)).image (fun ab => ab.1 ∪ ab.2)

def observed121 : Finset ℕ := Finset.range 5 ∪ Finset.Ico 10 65

def alternative121 : Finset ℕ := insert 5 (observed121.erase 10)

def conditionalLaw {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (A : Ω → Prop)
    (hA : 0 < Q.prob A) : FiniteLaw Ω := by
  classical
  exact {
  mass z := if A z then Q.mass z / Q.prob A else 0
  nonneg z := by
    classical
    split_ifs
    · exact div_nonneg (Q.nonneg z) hA.le
    · exact le_rfl
  total := by
    rw [← Finset.sum_filter]
    rw [← Finset.sum_div]
    change Q.prob A / Q.prob A = 1
    exact div_self (ne_of_gt hA) }

def commonBernoulli {N : ℕ} (Q : FiniteLaw (Assignment N)) (p : ℝ) : Prop :=
  ∀ z, Q.mass z = ∏ i, if z i then p else 1 - p

def percentileNode (i : Fin 4) : ℚ := 10 * i.val

def validatorRectangle : Set Plane :=
  {x | -1 ≤ x 0 ∧ x 0 ≤ 31 ∧ -1 ≤ x 1 ∧ x 1 ≤ 1}

def validatorRectangleOutcome (x : Plane) (_z : Assignment 4) : ℝ :=
  ∑ i : Fin 4, if dist x (lineEmbedding (percentileNode i)) ≤ 1 then (i.val : ℝ) else 0

def validatorRectangleMeasure : Measure Plane :=
  ∑ a : Fin 4 × Fin 6,
    Measure.dirac (lineEmbedding (percentileNode a.1 + (a.2.val : ℚ) / 10))

def validatorRectangleModel : SpatialModel 4 where
  field := validatorRectangle
  node i := lineEmbedding (percentileNode i)
  node_mem := by
    intro i
    fin_cases i <;> norm_num [validatorRectangle, percentileNode, lineEmbedding, WithLp.toLp]
  ζ := validatorRectangleMeasure
  Y := validatorRectangleOutcome

def validatorRadius (j : Fin 5) : ℝ := (j.val + 1 : ℝ) / 10

def validatorRectangleStatistic (j : Fin 5) (k : Fin 6) : ℝ :=
  hajek (fun i z => validatorRectangleModel.M i (validatorRadius j) z) (sixAssignment k)

end
end SAP.P008a
