import SAP.P026a.Defs.Part13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a
open Finset
open scoped BigOperators
noncomputable section


/-- Mathematical content of target P026-T10. -/
def T10Statement : Prop :=
  (∀ {U C : Type*} [Fintype U] [DecidableEq U]
    [Fintype C] [DecidableEq C] [Nonempty U] (E : ClusterLaw U C)
    (y : U → ℝ) (a : Bool) (w : C → Bool),
    htSum E.unitAssignmentDesign a y w = htSum E.clusterAssignmentDesign a (E.totals y) w) ∧
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype C] [DecidableEq C] (E : ClusterLaw U C) (x z : U → ℝ) (w : C → Bool),
    htContrast E.unitAssignmentDesign (Fintype.card U) x z w =
      htContrast E.clusterAssignmentDesign (Fintype.card U) (E.totals x) (E.totals z) w) ∧
  (∀ {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype C] [DecidableEq C] (E : ClusterLaw U C) (y : U → ℝ) (a : Bool) (w : C → Bool),
    let groupedUnits := ∑ c, ∑ i ∈ univ.filter (fun i => E.cluster i = c),
      armIndicator E.unitAssignmentDesign a w i * y i / inclusion E.unitAssignmentDesign a i
    let groupedClusters := ∑ c, ∑ i ∈ univ.filter (fun i => E.cluster i = c),
      armIndicator E.clusterAssignmentDesign a w c * y i / inclusion E.clusterAssignmentDesign a c
    let factored := ∑ c, armIndicator E.clusterAssignmentDesign a w c *
      (∑ i ∈ univ.filter (fun i => E.cluster i = c), y i) / inclusion E.clusterAssignmentDesign a c
    htSum E.unitAssignmentDesign a y w = groupedUnits ∧
    groupedUnits = groupedClusters ∧ groupedClusters = factored ∧
    factored = htSum E.clusterAssignmentDesign a (E.totals y) w)

end
end SAP.P026a
