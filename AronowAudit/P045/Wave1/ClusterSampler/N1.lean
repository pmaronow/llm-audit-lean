import AronowAudit.P045.Wave1.ClusterSamplerBlueprint

/-!
P045-T29, node N1: the extended distance matrix of the four-vertex path.
-/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.ClusterSampler

open AronowAudit.P045 Finset
open scoped BigOperators

noncomputable section

theorem n1_proof : N1 := by
  have a01 : (SimpleGraph.pathGraph 4).Adj (0 : Fin 4) 1 := by
    norm_num [SimpleGraph.pathGraph_adj]
  have a12 : (SimpleGraph.pathGraph 4).Adj (1 : Fin 4) 2 := by
    norm_num [SimpleGraph.pathGraph_adj]
  have a23 : (SimpleGraph.pathGraph 4).Adj (2 : Fin 4) 3 := by
    norm_num [SimpleGraph.pathGraph_adj]
  have d01 : (SimpleGraph.pathGraph 4).edist (0 : Fin 4) 1 = 1 :=
    SimpleGraph.edist_eq_one_iff_adj.mpr a01
  have d12 : (SimpleGraph.pathGraph 4).edist (1 : Fin 4) 2 = 1 :=
    SimpleGraph.edist_eq_one_iff_adj.mpr a12
  have d23 : (SimpleGraph.pathGraph 4).edist (2 : Fin 4) 3 = 1 :=
    SimpleGraph.edist_eq_one_iff_adj.mpr a23

  -- Vertices two apart are nonadjacent and have the displayed common neighbour.
  have d02 : (SimpleGraph.pathGraph 4).edist (0 : Fin 4) 2 = 2 := by
    apply SimpleGraph.edist_eq_two_iff.mpr
    refine ⟨by decide, ?_, ?_⟩
    · norm_num [SimpleGraph.pathGraph_adj]
    · exact ⟨1, ⟨a01, a12.symm⟩⟩
  have d13 : (SimpleGraph.pathGraph 4).edist (1 : Fin 4) 3 = 2 := by
    apply SimpleGraph.edist_eq_two_iff.mpr
    refine ⟨by decide, ?_, ?_⟩
    · norm_num [SimpleGraph.pathGraph_adj]
    · exact ⟨2, ⟨a12, a23.symm⟩⟩

  -- The endpoints have neither an edge nor a common neighbour.
  have noCommon : (SimpleGraph.pathGraph 4).commonNeighbors (0 : Fin 4) 3 = ∅ := by
    ext v
    fin_cases v <;>
      norm_num [SimpleGraph.mem_commonNeighbors, SimpleGraph.pathGraph_adj]
  have two_lt : (2 : ℕ∞) < (SimpleGraph.pathGraph 4).edist (0 : Fin 4) 3 := by
    apply SimpleGraph.two_lt_edist_iff.mpr
    refine ⟨by decide, ?_, noCommon⟩
    norm_num [SimpleGraph.pathGraph_adj]
  have three_le : (3 : ℕ∞) ≤ (SimpleGraph.pathGraph 4).edist (0 : Fin 4) 3 := by
    have h : (2 : ℕ∞) + 1 ≤ (SimpleGraph.pathGraph 4).edist (0 : Fin 4) 3 :=
      (ENat.natCast_add_one_le_iff (m := 2)).mpr two_lt
    convert h using 1 <;> norm_num
  let w : (SimpleGraph.pathGraph 4).Walk (0 : Fin 4) 3 :=
    .cons a01 (.cons a12 (.cons a23 .nil))
  have le_three : (SimpleGraph.pathGraph 4).edist (0 : Fin 4) 3 ≤ (3 : ℕ∞) := by
    simpa [w] using w.edist_le
  have d03 : (SimpleGraph.pathGraph 4).edist (0 : Fin 4) 3 = 3 :=
    le_antisymm le_three three_le

  -- Keep the six reverse distances explicit, so the final simplification
  -- does not depend on the simplifier's orientation for commutativity.
  have d10 : (SimpleGraph.pathGraph 4).edist (1 : Fin 4) 0 = 1 := by
    rw [SimpleGraph.edist_comm]
    exact d01
  have d20 : (SimpleGraph.pathGraph 4).edist (2 : Fin 4) 0 = 2 := by
    rw [SimpleGraph.edist_comm]
    exact d02
  have d30 : (SimpleGraph.pathGraph 4).edist (3 : Fin 4) 0 = 3 := by
    rw [SimpleGraph.edist_comm]
    exact d03
  have d21 : (SimpleGraph.pathGraph 4).edist (2 : Fin 4) 1 = 1 := by
    rw [SimpleGraph.edist_comm]
    exact d12
  have d31 : (SimpleGraph.pathGraph 4).edist (3 : Fin 4) 1 = 2 := by
    rw [SimpleGraph.edist_comm]
    exact d13
  have d32 : (SimpleGraph.pathGraph 4).edist (3 : Fin 4) 2 = 1 := by
    rw [SimpleGraph.edist_comm]
    exact d23

  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pathDistance, Nat.dist, SimpleGraph.edist_self,
      d01, d02, d03, d10, d12, d13, d20, d21, d23, d30, d31, d32]

end

end AronowAudit.P045.Wave1.ClusterSampler
