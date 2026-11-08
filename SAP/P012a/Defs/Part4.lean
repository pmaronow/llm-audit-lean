import SAP.P012a.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a

open Finset
open scoped Classical
noncomputable section

/-- The lower-endpoint formula, written as the quotient in the correction. -/
def lowerQuotient (D : Data) : ℝ :=
  (4 * (a D : ℝ) * b D - ((cR D : ℝ) + totalSpare D)^2) /
    ((2 * (a D : ℝ) + cR D + totalSpare D) *
      (2 * (b D : ℝ) + cR D + totalSpare D))

def T1Statement : Prop :=
  proposal_counterexampleClaim ∧ proposal_counterexample_bClaim ∧
  cleanup_counterexampleClaim ∧ empty_trait_pool_counterexampleClaim

def T2Statement : Prop := corrected_proposal_preservesClaim

def T3Statement : Prop :=
  (∀ D : Data, Admissible D → D.sampled.card = 527 → D.seeds.card = 6 →
    (∑ i ∈ D.sampled, D.degree i) = 4487 →
    edgeCount (leafCompletion D false) true = a D ∧
    edgeCount (leafCompletion D false) false = b D ∧
    mixedCount (leafCompletion D false) = cR D + 3445 ∧
    hValue (leafCompletion D false) = lowerQuotient D) ∧
  table_counterexampleClaim ∧ uniform_leaf_boundClaim ∧
  uniform_integer_leaf_boundClaim ∧ table_numeric_gapsClaim

def T4Statement : Prop := corrected_table_boundClaim ∧ table_degree_converseClaim

def T5Statement : Prop :=
  (∀ (D : Data), Admissible D →
    (0 < totalSpare D ∨ (0 < 2*a D + cR D ∧ 0 < 2*b D + cR D)) →
    IsLeast (hValues D) (hLower D) ∧
    Compatible D (leafCompletion D false) ∧
    homophily (leafCompletion D false) = some (hLower D) ∧
    hLower D = lowerQuotient D ∧
    ∀ H, Compatible D H → HomophilyDefined H → hLower D ≤ hValue H) ∧
  (∀ (D : Data), Admissible D → D.sampled.card = 527 → D.seeds.card = 6 →
    (∑ i ∈ D.sampled, D.degree i) = 4487 →
    totalSpare D = 3445 ∧ a D + b D + cR D = 521 ∧
    hLower D ≤ -1462/1983 ∧ hLower D ≤ -178409/241987)

def T6Statement : Prop := exact_h_regionClaim ∧
  ∀ (x y c : ℝ), 2*x+c ≠ 0 → 2*y+c ≠ 0 →
    phi x y c = (4*x*y-c^2)/((2*x+c)*(2*y+c))

def T7Statement : Prop := exact_p_regionClaim ∧
  ∀ (D : Data), Admissible D → D.seeds.card < D.sampled.card →
    ∀ j ∈ nonseeds D, j ∈ laterChildren D j ∧ 0 < (laterChildren D j).card

def T8Statement : Prop := result1_proof_counterexampleClaim ∧
  result1BadEnd.vertices = sampledVertices proofStepData ∧
  result1BadEnd.edges = {{s 1,s 2},{s 2,s 3},{s 1,s 3}} ∧
  graphDegree result1BadStart (s 1) = 3 ∧
  graphDegree result1BadStart (s 2) = 2 ∧
  graphDegree result1BadStart (s 3) = 3 ∧
  graphDegree result1BadEnd (s 1) = 2 ∧
  graphDegree result1BadEnd (s 2) = 2 ∧
  graphDegree result1BadEnd (s 3) = 2

def T9Statement : Prop := result2_proof_counterexampleClaim ∧
  result2BadEnd.vertices = result2BadStart.vertices ∧
  result2BadEnd.edges = {{s 1,s 2},{s 2,s 3},{s 1,u 5 0},{s 3,u 4 0}} ∧
  graphDegree result2BadStart (s 1) = 3 ∧ graphDegree result2BadStart (s 2) = 2 ∧
  graphDegree result2BadStart (s 3) = 3 ∧ graphDegree result2BadStart (u 4 0) = 2 ∧
  graphDegree result2BadStart (u 5 0) = 2 ∧
  graphDegree result2BadEnd (s 1) = 2 ∧ graphDegree result2BadEnd (s 2) = 2 ∧
  graphDegree result2BadEnd (s 3) = 2 ∧ graphDegree result2BadEnd (u 4 0) = 1 ∧
  graphDegree result2BadEnd (u 5 0) = 1 ∧
  result2BadStart.edges.card = 6 ∧ result2BadEnd.edges.card = 4

def T10Statement : Prop := result1Claim

def T11Statement : Prop := result2Claim ∧ result2_swap_formulaClaim ∧ a1_exact_instanceClaim

def T12Statement : Prop := a2_counterexampleClaim ∧
  pValue a2Data (a2State true) = 0 ∧ pValue a2Data (a2State false) = 5/12 ∧
  (nonseeds a2Data).card = 2 ∧
  -1 / ((nonseeds a2Data).card *
    ((susceptible a2Data (a2State true) 1 2).card : ℝ)) = -1/6 ∧
  -1 / ((nonseeds a2Data).card *
    ((susceptible a2Data (a2State true) 1 3).card : ℝ)) = -1/4

end
end SAP.P012a
