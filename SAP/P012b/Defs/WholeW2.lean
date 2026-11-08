import Mathlib
import SAP.P012b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012b

open Finset Filter
open scoped Topology
noncomputable section

/-- Exchange the two observed trait labels, leaving the observed history fixed. -/
def wholeComplementData (D : Data) : Data :=
  {D with trait := fun i => !(D.trait i)}

/-- Exchange both trait labels on a finite graph. -/
def wholeComplementState (H : State) : State :=
  {H with trait := fun v => !(H.trait v)}

/-- Equality of augmented graphs up to a permutation fixing sampled identities.
Traits outside the displayed vertex set have no mathematical significance. -/
def wholeRelabeling (D : Data) (H K : State) : Prop :=
  ∃ e : Equiv.Perm Vertex,
    (∀ i ∈ D.sampled, e (s i) = s i) ∧ H.vertices.image e = K.vertices ∧
    H.edges.image (fun edge => edge.image e) = K.edges ∧
    ∀ v ∈ H.vertices, K.trait (e v) = H.trait v

/-- The Figure 1 data with arbitrary recruitment-time ranks. -/
def wholeFigureData (τ : ℕ → ℕ) : Data := {figureData with time := τ}

/-- Merge the private leaf at sampled vertex 5 with one at sampled vertex 3.
Those vertices have the same trait and neither is a recruiter. -/
def wholeFigureMerged : State :=
  let H := leafCompletion figureData true
  {H with
    vertices := H.vertices.erase (u 5 0)
    edges := insert {s 5, u 3 0} (H.edges.erase {s 5, u 5 0})}

/-- A single summand in Definition 2, before division by the number of events. -/
def wholePContribution (D : Data) (H : State) (j : ℕ) : ℝ :=
  (if H.trait (s j) = H.trait (s (D.parent j)) then 1 else 0) -
    (sameSusceptible D H (D.parent j) j).card /
      ((susceptible D H (D.parent j) j).card : ℝ)

/-- Homogeneous undirected edge count. -/
def wholeEdgeCount_W2 (H : State) (b : Bool) : ℕ :=
  (H.edges.filter (fun e => ∀ v ∈ e, H.trait v = b)).card

/-- Mixed undirected edge count. -/
def wholeMixedCount_W2 (H : State) : ℕ :=
  (H.edges.filter (fun e => (∃ v ∈ e, H.trait v = true) ∧
    (∃ v ∈ e, H.trait v = false))).card

/-- Spare sampled stubs of one trait; admissibility prevents truncated deficits. -/
def wholeTraitSpare (D : Data) (b : Bool) : ℕ :=
  ∑ i ∈ D.sampled.filter (fun i => D.trait i = b), spare D i

/-- The binary assortativity formula, used below only at positive stub totals. -/
def wholePhi_W2 (x y c : ℝ) : ℝ := 1 - c / (2*x+c) - c / (2*y+c)

/-- All four marginal extrema are attained, their rectangle contains every
compatible value, and the lower preferential endpoint has inequivalent witnesses. -/
def WholeFigure1Assertions (D : Data) : Prop :=
  Admissible D ∧
  FullHomophilyRegion D (-5/8) (79/105) ∧
  FullPreferentialRegion D (-11/80) (49/120) ∧
  (∀ H, Compatible D H →
    homophily H = some (hValue H) ∧ preferential D H = some (pValue D H) ∧
    hValue H ∈ Set.Icc (-5/8 : ℝ) (79/105) ∧
    pValue D H ∈ Set.Icc (-11/80 : ℝ) (49/120) ∧
    hValue H ∈ Set.Icc (-1 : ℝ) 1 ∧ pValue D H ∈ Set.Icc (-1 : ℝ) 1) ∧
  (∃ H K, Compatible D H ∧ Compatible D K ∧
    preferential D H = some (-11/80) ∧ preferential D K = some (-11/80) ∧
    ¬ wholeRelabeling D H K)

/-- Numerical data and individual endpoint summands specified with Figure 1. -/
def WholeFigure1Arithmetic (D : Data) : Prop :=
  (nonseeds D).card = 4 ∧
  0 < sampledTraitDegree D false ∧ 0 < sampledTraitDegree D true ∧
  [1,2,3,4,5].map (recruitmentDegree D) = [2,3,1,1,1] ∧
  [1,2,3,4,5].map (spare D) = [3,1,2,2,1] ∧
  wholeEdgeCount_W2 (recruitmentState D) true = 3 ∧
  wholeEdgeCount_W2 (recruitmentState D) false = 0 ∧
  wholeMixedCount_W2 (recruitmentState D) = 1 ∧
  wholeTraitSpare D true = 7 ∧ wholeTraitSpare D false = 2 ∧
  (∑ i ∈ D.sampled, spare D i) = 9 ∧
  wholePhi_W2 3 0 10 = -5/8 ∧ wholePhi_W2 10 2 1 = 79/105 ∧
  [2,3,4,5].map (wholePContribution D (leafCompletion D true)) =
    [(1/5 : ℝ),0,-3/4,0] ∧
  [2,3,4,5].map (wholePContribution D (leafCompletion D false)) =
    [(4/5 : ℝ),1/3,0,1/2]

/-- P012-T23; Figure 1 and caption, p. 156 (PDF p. 4).
For the five sampled vertices with degrees (5,4,3,3,2), recruitments
1 to 2, 2 to 3, 1 to 4, 2 to 5, and traits (1,1,1,0,1), the attained marginal
extrema are -5/8, 79/105, -11/80 and 49/120. Every compatible pair lies in
their rectangle inside [-1,1]^2. Some extremal augmented subgraphs are not
unique, even after renaming unsampled vertices. The stated recruitment degrees,
spare degrees, edge and stub counts, phi evaluations and individual preferential
summands hold. The listed trait-specific edge and stub counts use the displayed
coding (1,1,1,0,1). All arithmetic and statistical conclusions hold for every
strictly increasing recruitment time order. The extrema, bounds and nonuniqueness
conclusions hold for either coding of the binary traits; exchanging both labels
preserves compatibility and both defined statistics. -/
def T23WholeStatement : Prop :=
  ∀ τ : ℕ → ℕ, StrictMonoOn τ (↑figureData.sampled : Set ℕ) →
    WholeFigure1Arithmetic (wholeFigureData τ) ∧
    WholeFigure1Assertions (wholeFigureData τ) ∧
    WholeFigure1Assertions (wholeComplementData (wholeFigureData τ)) ∧
    ∀ H, Compatible (wholeFigureData τ) H →
      Compatible (wholeComplementData (wholeFigureData τ)) (wholeComplementState H) ∧
      homophily (wholeComplementState H) = homophily H ∧
      preferential (wholeComplementData (wholeFigureData τ)) (wholeComplementState H) =
        preferential (wholeFigureData τ) H

/-- Admissible two-subject history used to test the printed annealing process. -/
def wholeProposalData : Data :=
  ⟨{1,2}, {1}, fun _ => 1, id, fun i => if i = 1 then 2 else 1,
    fun i => i == 2⟩

/-- Edges 12 and 1a, with traits 0,1,0 at sampled 1, sampled 2, unsampled a. -/
def wholeProposalStart : State :=
  ⟨{s 1,s 2,u 3 0}, {{s 1,s 2},{s 1,u 3 0}}, fun v => decide (v = s 2)⟩

/-- The literal printed deletion branch invents trait-0 vertex b and adds
edges 1b and ab; printed cleanup retains all four vertices. -/
def wholeProposalBad : State :=
  cleanup wholeProposalData false (addEdge
    (addEdge (addVertex (removeEdge wholeProposalStart (s 1) (u 3 0)) (u 4 0) false)
      (s 1) (u 4 0)) (u 3 0) (u 4 0))

/-- The printed Metropolis acceptance expression; the statement below uses it
only at defined statistics and positive temperature and objective denominators. -/
def wholeAcceptance (ε T : ℝ) (D : Data) (H K : State) : ℝ :=
  min 1 (Real.exp ((annealingObjective ε (hValue K) (pValue D K) -
    annealingObjective ε (hValue H) (pValue D H)) / T))

/-- P012-T24; Web Appendix 1, Proposition 1, p. 2; setup on p. 1 and printed
proposal mechanisms in Web Appendix 2, pp. 2-3.
The printed claim is false: admissible sampled data with degrees (2,1), traits
(0,1), and recruitment 1 to 2 have ordinary h and p on every compatible state.
The compatible graph with edges 12 and 1a, trait(a)=0, has (h,p)=(-1/3,-1/2).
A literal printed proposal inventing trait-0 vertex b produces edges 12,1b,ab,
an incompatible graph with (h,p)=(-1/5,-1/2), accepted with strictly positive
probability at every positive epsilon and positive finite temperature. Thus the
printed proposals and acceptance rule do not define the asserted chain on the
compatible space. Independently, no positive nondecreasing temperature sequence
tends to zero, and epsilon times log(1) has no finite multiplicative reciprocal. -/
def T24WholeStatement : Prop :=
  Admissible wholeProposalData ∧
  (∀ H, Compatible wholeProposalData H → HomophilyDefined H ∧
    PreferentialDefined wholeProposalData H) ∧
  Compatible wholeProposalData wholeProposalStart ∧
  Proposal wholeProposalData false wholeProposalStart wholeProposalBad ∧
  ¬ Compatible wholeProposalData wholeProposalBad ∧
  wholeProposalBad.edges = {{s 1,s 2},{s 1,u 4 0},{u 3 0,u 4 0}} ∧
  homophily wholeProposalStart = some (-1/3) ∧
  preferential wholeProposalData wholeProposalStart = some (-1/2) ∧
  homophily wholeProposalBad = some (-1/5) ∧
  preferential wholeProposalData wholeProposalBad = some (-1/2) ∧
  (∀ ε T : ℝ, 0 < ε → 0 < T →
    0 < 1 + ε + hValue wholeProposalStart ∧
    0 < 1 + ε + hValue wholeProposalBad ∧
    0 < wholeAcceptance ε T wholeProposalData wholeProposalStart wholeProposalBad) ∧
  (∀ T : ℕ → ℝ, (∀ n, 0 < T n) → Monotone T → ¬ Tendsto T atTop (𝓝 0)) ∧
  (∀ ε : ℝ, ¬ ∃ T : ℝ, T * (ε * Real.log 1) = 1)

end
end SAP.P012b
