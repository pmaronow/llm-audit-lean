import AronowAudit.P047.Wave1.ImpossibilityBlueprint
import AronowAudit.P047.Wave1.Impossibility.N1
import AronowAudit.P047.Wave1.Impossibility.N2
import AronowAudit.P047.Wave1.Impossibility.N3
import AronowAudit.P047.Wave1.Impossibility.N4
import AronowAudit.P047.Wave1.Impossibility.N5
import AronowAudit.P047.Wave1.Impossibility.N6
import AronowAudit.P047.Wave1.Impossibility.N7
import AronowAudit.P047.Wave1.Impossibility.N8
import AronowAudit.P047.Wave1.Impossibility.N9
import AronowAudit.P047.Wave1.Impossibility.N10
import AronowAudit.P047.Wave1.Impossibility.N11
import AronowAudit.P047.Wave1.Impossibility.N12
import AronowAudit.P047.Wave1.Impossibility.N13
import AronowAudit.P047.Wave1.Impossibility.N14
import AronowAudit.P047.Wave1.Impossibility.N15
import AronowAudit.P047.Wave1.Impossibility.N16
import AronowAudit.P047.Wave1.Impossibility.N17
import AronowAudit.P047.Wave1.Impossibility.N18
import AronowAudit.P047.Wave1.Impossibility.N19
import AronowAudit.P047.Wave1.Impossibility.N20

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open Impossibility

noncomputable section

/-- Unknown propensities preclude uniform consistency, including with an arbitrary
independent auxiliary seed; honest extended-real intervals have positive width probability
under the one fixed baseline law. -/
theorem unknown_propensity_impossibility_randomized :
    ∀ {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q],
      (∀ E : (n : ℕ) → ((Fin n → ObservedUnit) × R) → ℝ,
        (∀ n, Measurable (E n)) →
          (∀ n : ℕ, 1 ≤ n → (1 / 2 : ℝ) ≤ randRisk Q E n (1 / 12)) ∧
          (∃ η : ℝ, 0 < η ∧
            0 < Filter.limsup (fun n => randStrictRisk Q E n η) atTop)) ∧
      (∀ lo hi : (n : ℕ) → ((Fin n → ObservedUnit) × R) → EReal,
        (∀ n, Measurable (lo n)) → (∀ n, Measurable (hi n)) →
          ∀ α : ℝ, 0 < α → α < 1 / 2 →
            1 - α ≤ Filter.liminf (randCoverage Q lo hi) atTop →
            (1 - 2 * α ≤ Filter.liminf (widthProb Q lo hi) atTop) ∧ 0 < 1 - 2 * α) :=
  Impossibility.assemble n1_proof n2_proof n3_proof n4_proof n5_proof
    n6_proof n7_proof n8_proof n9_proof n10_proof n11_proof n12_proof n13_proof
    n14_proof n15_proof n16_proof n17_proof n18_proof n19_proof n20_proof

end

end AronowAudit.P047.Wave1
