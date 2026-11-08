import SAP.P004b.Defs.WholeW2
import SAP.P004b.Bridge
import AronowAudit.P004.Wave1.LinePopulation.N3
import AronowAudit.P004.Wave1.LinePopulation.N4
import AronowAudit.P004.Wave1.LinePopulation.N5
import AronowAudit.P004.Wave1.LinePopulation.N6
import AronowAudit.P004.Wave1.LinePopulation.N7

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W2

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical Topology
noncomputable section

/-- Transfer a concrete donor population field by field, without changing its data. -/
def fromProject {N : ℕ} (P : AronowAudit.P004.SpatialPopulation N (EuclideanSpace ℝ (Fin 2))) :
    SpatialPopulation N (EuclideanSpace ℝ (Fin 2)) where
  node := P.node
  node_nonempty := P.node_nonempty
  zeta := P.zeta
  outcome := P.outcome
  bands := P.bands

/-- Fixed outcomes +1 on the first half and -1 on the second, at points (10i,0). -/
def balancedLine (N : ℕ) : SpatialPopulation N (EuclideanSpace ℝ (Fin 2)) :=
  fromProject (AronowAudit.P004.linePopulation (balancedTable N))

theorem balancedLine_local : SpatialLocalConditions balancedLine := by
  change AronowAudit.P004.SpatialLocalConditions
    (fun N => AronowAudit.P004.linePopulation (balancedTable N))
  apply AronowAudit.P004.Wave1.LinePopulation.spatialLocal_of
    AronowAudit.P004.Wave1.LinePopulation.n5_proof
    AronowAudit.P004.Wave1.LinePopulation.n6_proof
    AronowAudit.P004.Wave1.LinePopulation.n7_proof (fun N => balancedTable N) 1 0
    (by norm_num) (by norm_num)
  · intro N i z
    simp only [balancedTable,balancedSign]
    split_ifs <;> norm_num
  · intro N j k z b _
    rfl

theorem balancedLine_defined : ∀ N, WellDefined (balancedLine N) 0 := by
  intro N
  exact AronowAudit.P004.Wave1.LinePopulation.n4_proof (balancedTable N) 0 (by norm_num)

/-- The actual circle averages of this deterministic spatial realization. -/
theorem balancedLine_circle (N : ℕ) : circleAverage (balancedLine N) 0 = balancedTable N :=
  AronowAudit.P004.Wave1.LinePopulation.n3_proof (balancedTable N)

end
end SAP.P004b.WH.W2
