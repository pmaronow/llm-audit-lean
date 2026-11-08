import SAP.P012b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P012b

open Finset Filter
open scoped Topology
noncomputable section

def T13Statement : Prop :=
  (∀ (D : Data) (hD : Admissible D) (i j : ℕ)
    (hi : i ∈ D.sampled) (hj : j ∈ nonseeds D) (hr : D.parent j = i)
    (hdi : recruitmentDegree D i < D.degree i),
    ∃ H K : State, ∃ v ∈ unsampled D H,
      Compatible D H ∧ Compatible D K ∧
      v = u i 0 ∧ H.vertices = (leafCompletion D true).vertices ∧
      H.edges = (leafCompletion D true).edges ∧
      (∀ k ∈ D.sampled, {s k,v} ∈ H.edges ↔ k = i) ∧
      H.trait v = true ∧ K = flipTrait H v ∧
      (∀ ℓ ∈ nonseeds D, susceptible D H (D.parent ℓ) ℓ =
        susceptible D K (D.parent ℓ) ℓ) ∧
      (∀ ℓ ∈ nonseeds D, v ∈ susceptible D H (D.parent ℓ) ℓ ↔ D.parent ℓ = i) ∧
      pValue D H - pValue D K =
        ((if D.trait i then (-1 : ℝ) else 1) / (nonseeds D).card) *
          (∑ ℓ ∈ children D i, 1 / ((susceptible D H i ℓ).card : ℝ)) ∧
      pValue D H ≠ pValue D K ∧ ¬ PointIdentified (pValues D) ∧
      (D.trait i = true →
        pValue D H - pValue D K ≤
          -1 / ((nonseeds D).card * ((susceptible D H i j).card : ℝ)) ∧
        -1 / ((nonseeds D).card * ((susceptible D H i j).card : ℝ)) < 0 ∧
        (pValue D H - pValue D K =
          -1 / ((nonseeds D).card * ((susceptible D H i j).card : ℝ)) ↔
          children D i = {j}))) ∧
  (∀ (D : Data) (hD : Admissible D)
    (H : State) (hH : Compatible D H) (i j : ℕ) (hi : i ∈ D.sampled)
    (hj : j ∈ nonseeds D) (hr : D.parent j = i)
    (v : Vertex) (hv : v ∈ unsampled D H)
    (hprivate : ∀ k ∈ D.sampled, {s k,v} ∈ H.edges ↔ k = i)
    (htrait : H.trait v = true),
    let K := flipTrait H v;
    Compatible D K ∧
    (∀ ℓ ∈ nonseeds D, susceptible D H (D.parent ℓ) ℓ = susceptible D K (D.parent ℓ) ℓ) ∧
    (∀ ℓ ∈ nonseeds D, v ∈ susceptible D H (D.parent ℓ) ℓ ↔ D.parent ℓ = i) ∧
    pValue D H-pValue D K =
      ((if D.trait i then (-1:ℝ) else 1)/(nonseeds D).card) *
        (∑ ℓ ∈ children D i, 1/((susceptible D H i ℓ).card:ℝ)) ∧
    pValue D H ≠ pValue D K ∧
    (D.trait i = true →
      pValue D H-pValue D K ≤ -1/((nonseeds D).card*((susceptible D H i j).card:ℝ)) ∧
      -1/((nonseeds D).card*((susceptible D H i j).card:ℝ)) < 0 ∧
      (pValue D H-pValue D K = -1/((nonseeds D).card*((susceptible D H i j).card:ℝ)) ↔
        children D i = {j})))

def T14Statement : Prop :=
  (Admissible domainA ∧ Compatible domainA (dyad false false) ∧
      hNumerator (dyad false false) = 0 ∧ hDenominator (dyad false false) = 0 ∧
      homophily (dyad false false) = none ∧
      preferential domainA (dyad false false) = some 0) ∧
    (Admissible domainB ∧ Compatible domainB (dyad false true) ∧
      homophily (dyad false true) = some (-1) ∧ (nonseeds domainB).card = 0 ∧
      pSum domainB (dyad false true) = 0 ∧
      (∀ H, preferential domainB H = none)) ∧
    (Admissible domainC ∧ Compatible domainC domainCState ∧
      domainCState.edges.card = 0 ∧ homophily domainCState = none ∧
      preferential domainC domainCState = none) ∧
    (Admissible domainD ∧
      (∀ t3 t4 t5 : Bool, Compatible domainD (domainDState t3 t4 t5)) ∧
      hNumerator (domainDState true true true) = 0 ∧
      hDenominator (domainDState true true true) = 0 ∧
      homophily (domainDState true true true) = none ∧
      homophily (domainDState false false false) = some (-3/5) ∧
      homophily (domainDState true false false) = some (-1/3) ∧
      homophily (domainDState true true false) = some (-1/7) ∧
      (∀ t3 t4 t5 : Bool, preferential domainD (domainDState t3 t4 t5) = some 0))

def T15Statement : Prop :=
  (∀ (H : State) (hS : Simple H) (hm : 0 < H.edges.card),
    degreeTraitSum H = (traitDegree H true : ℝ) ∧
    traitDegree H true + traitDegree H false = 2 * H.edges.card ∧
    hDenominator H = (traitDegree H true : ℝ) -
      (traitDegree H true : ℝ)^2 / (2 * (H.edges.card : ℝ)) ∧
    hDenominator H = (traitDegree H true : ℝ) * traitDegree H false /
      (2 * (H.edges.card : ℝ)) ∧
    hDenominator H = (traitDegree H true : ℝ) *
      (2 * (H.edges.card : ℝ) - traitDegree H true) / (2 * (H.edges.card : ℝ)) ∧
    (0 < hDenominator H ↔ 0 < traitDegree H false ∧ 0 < traitDegree H true) ∧
    (HomophilyDefined H ↔ 0 < traitDegree H false ∧ 0 < traitDegree H true) ∧
    (traitDegree H true = 0 ∨ traitDegree H true = 2 * H.edges.card →
      hNumerator H = 0 ∧ hDenominator H = 0)) ∧
  (∀ (D : Data) (hD : Admissible D),
    (∀ (H : State), Compatible D H →
      (PreferentialDefined D H ↔ D.seeds.card < D.sampled.card) ∧
      (∀ j ∈ nonseeds D, s j ∈ susceptible D H (D.parent j) j ∧
        0 < (susceptible D H (D.parent j) j).card)) ∧
    ((∀ H, Compatible D H → HomophilyDefined H) ↔
      0 < sampledTraitDegree D false ∧ 0 < sampledTraitDegree D true) ∧
    ((∀ H, Compatible D H → PreferentialDefined D H) ↔
      D.seeds.card < D.sampled.card) ∧
    ((∃ i ∈ D.sampled, ∃ j ∈ D.sampled,
      recruitmentDegree D i < D.degree i ∧ recruitmentDegree D j < D.degree j ∧
      D.trait i ≠ D.trait j) →
      0 < sampledTraitDegree D false ∧ 0 < sampledTraitDegree D true) ∧
    ((∃ j ∈ nonseeds D, recruitmentDegree D (D.parent j) < D.degree (D.parent j)) →
      D.seeds.card < D.sampled.card) ∧
    ((0 < sampledTraitDegree D false ∧ 0 < sampledTraitDegree D true) →
      ∀ L U, FullHomophilyRegion D L U ↔
        IsLeast (hValues D) L ∧ IsGreatest (hValues D) U) ∧
    (D.seeds.card < D.sampled.card →
      ∀ L U, FullPreferentialRegion D L U ↔
        IsLeast (pValues D) L ∧ IsGreatest (pValues D) U) ∧
    (¬ (0 < sampledTraitDegree D false ∧ 0 < sampledTraitDegree D true) →
      ¬ ∃ L U, FullHomophilyRegion D L U))
end
end SAP.P012b
