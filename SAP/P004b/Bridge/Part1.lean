import SAP.P004b.Defs
import AronowAudit.P004.Wave1.Gap.GP0041B1
import AronowAudit.P004.Wave1.Gap.GLP0041B2
import AronowAudit.P004.Wave1.Gap.GP0041B2
import AronowAudit.P004.Wave1.Gap.GP0041B3
import AronowAudit.P004.P004_DependencyCompletion
import AronowAudit.P004.P004_VarianceCompletion
import AronowAudit.P004.P004_RegressionCompletion
import AronowAudit.P004.Wave1.Gap.GP0042B1
import AronowAudit.P004.Wave1.Gap.GLP0042B2
import AronowAudit.P004.Wave1.Gap.TailBNedHac
import AronowAudit.P004.P004_HACCompletion
import AronowAudit.P004.P004_ConditioningCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.Bridge

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology
noncomputable section

/-- Preserve every field of the SAP population in the project representation. -/
def population {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SAP.P004b.SpatialPopulation N X) : AronowAudit.P004.SpatialPopulation N X where
  node := P.node
  node_nonempty := P.node_nonempty
  zeta := P.zeta
  outcome := P.outcome
  bands := P.bands

def sequence {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] (P : SAP.P004b.PopulationSequence Space) :
    AronowAudit.P004.PopulationSequence Space := fun N => population (P N)

theorem circleAverage_eq {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SAP.P004b.SpatialPopulation N X) (d : ℝ) :
    SAP.P004b.circleAverage P d = AronowAudit.P004.circleAverage (population P) d := rfl

theorem nodeSeparation_eq {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SAP.P004b.SpatialPopulation N X) :
    SAP.P004b.nodeSeparation P = AronowAudit.P004.nodeSeparation (population P) := rfl

theorem WellDefined_eq {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SAP.P004b.SpatialPopulation N X) (d : ℝ) :
    SAP.P004b.WellDefined P d = AronowAudit.P004.WellDefined (population P) d := rfl

theorem FiniteSourceRange_eq {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SAP.P004b.SpatialPopulation N X) (d : ℝ) :
    SAP.P004b.FiniteSourceRange P d = AronowAudit.P004.FiniteSourceRange (population P) d := rfl

theorem rectangleWitness_eq : population SAP.P004b.rectangleWitness = AronowAudit.P004.rectangleWitness := rfl

theorem polygonRangeFamily_eq (L : ℝ) (hL : 2 ≤ L) :
    population (SAP.P004b.polygonRangeFamily L hL) = AronowAudit.P004.polygonRangeFamily L hL := rfl

theorem sparsePopulation_eq : sequence SAP.P004b.sparsePopulation = AronowAudit.P004.sparsePopulation := rfl

theorem localConditions_eq {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] (P : SAP.P004b.PopulationSequence Space) :
    SAP.P004b.SpatialLocalConditions P = AronowAudit.P004.SpatialLocalConditions (sequence P) := rfl

theorem nedConditions_eq {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] (P : SAP.P004b.PopulationSequence Space) (p d : ℝ) :
    SAP.P004b.NEDConditions P p d = AronowAudit.P004.NEDConditions (sequence P) p d := rfl

/-- Finite-sum rearrangement identifies the class member with the explicit formula. -/
theorem linearFormula_eq {N : ℕ} (p : Fin N → ℝ) (R : SAP.P004b.CircleTable N)
    (hN : 0 < N) (z : SAP.P004b.Assignment N) :
    SAP.P004b.linearHajek p R z = SAP.P004b.linearFormula p R z := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hN)
  unfold SAP.P004b.linearHajek SAP.P004b.augmented SAP.P004b.linearFormula
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  change _ = SAP.P004b.ame p R + _
  rw [show SAP.P004b.ame p R = SAP.P004b.barMu p R true - SAP.P004b.barMu p R false from
    (AronowAudit.P004.barMu_difference p R).symm]
  field_simp [hn]
  <;> ring

end
end SAP.P004b.Bridge
