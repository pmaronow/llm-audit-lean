import SAP.P012b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P012b

open Finset Filter
open scoped Topology
noncomputable section

def T22Statement : Prop :=
  (∀ (D : Data) (hD : Admissible D)
    (h0 : 0 < sampledTraitDegree D false) (h1 : 0 < sampledTraitDegree D true)
    (hN : D.seeds.card < D.sampled.card),
    ((PointIdentified (hValues D) ∧ PointIdentified (pValues D)) ↔
      ∀ i ∈ D.sampled, D.degree i = recruitmentDegree D i) ∧
    ((∀ i ∈ D.sampled, D.degree i = recruitmentDegree D i) ↔
      ∀ H, Compatible D H → H.vertices = sampledVertices D ∧
        H.edges = recruitmentEdges D) ∧
    ((∃ i ∈ D.sampled, recruitmentDegree D i < D.degree i) →
      ¬ PointIdentified (hValues D)) ∧
    ((∀ i ∈ D.sampled, D.degree i = recruitmentDegree D i) →
      ∀ H, Compatible D H → H.vertices = (recruitmentState D).vertices ∧
        H.edges = (recruitmentState D).edges ∧
        (∀ v ∈ H.vertices, H.trait v = (recruitmentState D).trait v))) ∧
    (∀ (D : Data) (hD : Admissible D)
    (h0 : 0 < sampledTraitDegree D false) (h1 : 0 < sampledTraitDegree D true)
    (i : ℕ) (hi : i ∈ D.sampled) (hdi : recruitmentDegree D i < D.degree i),
    Compatible D (leafCompletion D true) ∧
    Compatible D (flipTrait (leafCompletion D true) (u i 0)) ∧
    hValue (leafCompletion D true) ≠ hValue (flipTrait (leafCompletion D true) (u i 0))) ∧
    (∀ (D : Data) (hD : Admissible D)
    (h0 : 0 < sampledTraitDegree D false) (h1 : 0 < sampledTraitDegree D true)
    (hN : D.seeds.card < D.sampled.card),
    PointIdentified (pValues D) ↔
      ∀ i ∈ D.sampled, (children D i).Nonempty → D.degree i = recruitmentDegree D i)

def T23Statement : Prop :=
  Admissible figureData ∧
    FullHomophilyRegion figureData (-5/8) (79/105) ∧
    FullPreferentialRegion figureData (-11/80) (49/120) ∧
    (∀ H, Compatible figureData H →
      homophily H = some (hValue H) ∧ preferential figureData H = some (pValue figureData H) ∧
      hValue H ∈ Set.Icc (-5/8 : ℝ) (79/105) ∧
      pValue figureData H ∈ Set.Icc (-11/80 : ℝ) (49/120))
end
end SAP.P012b
