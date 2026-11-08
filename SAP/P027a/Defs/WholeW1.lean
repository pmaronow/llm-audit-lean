import Mathlib
import SAP.P027a.Defs.WholeW1.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable

/-- A group's representative indicator. Nonempty groups make this a genuine
member, and no full-support assumption on the ambient atoms is imposed. -/
def wholeRepDesign {G Ω : Type} (n : G → ℕ) (hn : ∀ g, 0 < n g)
    (D : Design (Σ g, Fin (n g)) Ω) : Design G Ω where
  weight := D.weight
  selected ω g := D.selected ω ⟨g,⟨0,hn g⟩⟩

/-- Probability-zero disagreement within each group. -/
def WholeAEClusters {G Ω : Type} [Fintype Ω] (n : G → ℕ)
    (D : Design (Σ g, Fin (n g)) Ω) : Prop :=
  ∀ (g : G) (i j : Fin (n g)),
    expect D (fun ω => if D.selected ω ⟨g,i⟩ = D.selected ω ⟨g,j⟩ then 0 else 1) = 0

/-- C2's design bias. -/
def wholeC2Bias {U Ω : Type} [Fintype U] [Fintype Ω]
    (D : Design U Ω) (y : U → ℝ) : ℝ :=
  expect D (c2Estimator D y) - variance D (htTotal D y)

/-- Unordered zero-edge sum represented by half the ordered sum. All summands
used below are symmetric in the two groups. This convention avoids choosing
an order on the finite group labels and retains the exact factor 1/2. -/
def wholeEdgeSum {G Ω : Type} [Fintype G] [Fintype Ω]
    (D : Design G Ω) (f : G → G → ℝ) : ℝ :=
  (∑ g, ∑ h, if g ≠ h ∧ joint D g h = 0 then f g h else 0)/2

/-- All aggregation conclusions for a general almost-sure cluster partition.
Samplewise conclusions hold on possible samples, i.e. on positive-weight atoms.
Every finite partition is represented by numbering the members of each group. -/
def AEAggregationWhole : Prop :=
  ∀ {G Ω : Type} [Fintype G] [Fintype Ω]
    (n : G → ℕ) (hn : ∀ g, 0 < n g)
    (D : Design (Σ g, Fin (n g)) Ω), Valid D → Positive D → WholeAEClusters n D →
  ∀ y : (Σ g, Fin (n g)) → ℝ,
  let Dc := wholeRepDesign n hn D
  let Y := groupTotal n y
  let S := groupSquares n y
  let Δ := wholeC2Bias D y - wholeC2Bias Dc Y
  Valid Dc ∧ Positive Dc ∧
  (∀ g i, pi D ⟨g,i⟩ = pi Dc g) ∧
  (∀ g h i j, joint D ⟨g,i⟩ ⟨h,j⟩ = joint Dc g h) ∧
  (∀ g, joint Dc g g = pi Dc g) ∧
  (∀ ω, 0 < D.weight ω → htTotal D y ω = htTotal Dc Y ω ∧
    htVarianceEstimator D y ω = htVarianceEstimator Dc Y ω) ∧
  variance D (htTotal D y) = variance Dc (htTotal Dc Y) ∧
  biasA D y = (∑ g, ∑ h, if g ≠ h ∧ joint Dc g h = 0 then Y g*Y h else 0) ∧
  biasA D y = biasA Dc Y ∧
  quadraticA D y = wholeEdgeSum Dc (fun g h => (n h:ℝ)*S g+(n g:ℝ)*S h) ∧
  quadraticA Dc Y = wholeEdgeSum Dc (fun g h => Y g^2+Y h^2) ∧
  wholeC2Bias D y = biasA D y+quadraticA D y ∧
  wholeC2Bias Dc Y = biasA Dc Y+quadraticA Dc Y ∧
  Δ = wholeEdgeSum Dc (fun g h => (n h:ℝ)*S g+(n g:ℝ)*S h-Y g^2-Y h^2) ∧
  (wholeC2Bias D y < wholeC2Bias Dc Y ↔ Δ < 0) ∧
  (∀ v : ℝ, (∀ k, y k = v) →
    Δ = -v^2*wholeEdgeSum Dc (fun g h => ((n g:ℝ)-n h)^2) ∧ Δ ≤ 0 ∧
    (v ≠ 0 → (∃ g h, g ≠ h ∧ joint Dc g h = 0 ∧ n g ≠ n h) → Δ < 0) ∧
    ((∀ g h, g ≠ h ∧ joint Dc g h = 0 → n g = n h) → Δ = 0)) ∧
  ((∀ g h, g ≠ h ∧ joint Dc g h = 0 → n g = n h) → 0 ≤ Δ) ∧
  ((∑ g, (zeroNeighborSize Dc n g-(zeroNeighborCount Dc g:ℝ)*(n g:ℝ))*S g) ≤ Δ) ∧
  wholeC2Bias Dc Y = wholeEdgeSum Dc (fun g h => (Y g+Y h)^2) ∧
  wholeC2Bias D y = squaredZeroPairs D y ∧
  0 ≤ wholeC2Bias Dc Y ∧ 0 ≤ wholeC2Bias D y

/-- Lagrange's finite identity inside each numbered group, including its sign. -/
def GroupDifferencesWhole : Prop :=
  ∀ (n : ℕ) (y : Fin n → ℝ),
    (n:ℝ)*(∑ i, y i^2)-(∑ i, y i)^2 =
      (∑ i, ∑ j, if i < j then (y i-y j)^2 else 0) ∧
    0 ≤ (n:ℝ)*(∑ i, y i^2)-(∑ i, y i)^2

/-- The four-unit reduction example in sigma coordinates: the two clusters are
{(0,0),(0,1)} and {(1,0),(1,1)}, with outcomes (1,-1,2,-2). -/
def fourClusterOutcome (k : Σ _ : Fin 2, Fin 2) : ℝ :=
  if k.1 = 0 then (if k.2 = 0 then 1 else -1) else (if k.2 = 0 then 2 else -2)

def AggregationReductionWhole : Prop :=
  let D := liftDesign cluster2 (fun _ => 2)
  let Y := groupTotal (fun _ : Fin 2 => 2) fourClusterOutcome
  Valid D ∧ Positive D ∧ (∀ g, Y g = 0) ∧
  wholeC2Bias D fourClusterOutcome = 20 ∧ wholeC2Bias cluster2 Y = 0

/-- P027-T4, main p. 237, Section 3.1:
for every partition into nonempty almost-sure clusters, totalling preserves the
HT total and the uncorrected estimator on every possible sample, and preserves
variance and A. In the exponent-2 setting both A-star formulas and the exact
ordered-pair-factor-1/2 bias change hold. Constant outcomes, strict increase for
unequal linked sizes, the equal-size sufficient condition, the degree bound,
the within-group squared-difference identity and both conservativeness formulas
are included. The explicit examples reduce C2 bias from 20 to 0 and increase it
from 8 to 9. The usual measure-theoretic conditions are assumed. -/
def T4WholeStatement : Prop :=
  AEAggregationWhole ∧ GroupDifferencesWhole ∧ AggregationReductionWhole ∧ ClusterBiasIncrease

/-- The unoffset negative-binomial vector producing the positive sizes (1,3,...). -/
def wholeRandomSizeAtom (k : Fin 8) : ℕ := if k.val % 2 = 0 then 0 else 2

/-- Connection of the size witness to the normalized independent size generator. -/
def RandomSizeSupportWhole : Prop :=
  IsProbabilityMeasure nbProductLaw ∧
  (∀ k, 1+(wholeRandomSizeAtom k:ℝ) = randomSize8 k) ∧
  (nbProductLaw {wholeRandomSizeAtom}).toReal = nbMass 0^4*nbMass 2^4 ∧
  0 < (nbProductLaw {wholeRandomSizeAtom}).toReal

/-- Remaining deterministic claims of the random-size witness. The residual
representation is algebraic; the exact continuous outcome vector is not claimed
to be a positive-mass Gaussian atom. -/
def Random8WholeDetails : Prop :=
  (∀ k, cumulativeLeft randomSize8 k =
    (![0,1,4,5,8,9,12,13] : Fin 8 → ℝ) k) ∧
  (∀ k, randomSize8 k ≤ 3) ∧ randomSize8 1 = 3 ∧
  (2:ℝ)*3 ≤ ∑ k, randomSize8 k ∧
  (∀ β : ℝ, ∀ k, randomOutcome8 k = β*randomSize8 k +
    (randomOutcome8 k-β*randomSize8 k)) ∧
  (∀ k, pi random8 k = randomSize8 k/8) ∧
  (∀ k l, joint random8 k l = if k.val % 4 = l.val % 4 then pi random8 k else 0) ∧
  (Finset.univ.filter (fun kl : Fin 8 × Fin 8 =>
    kl.1 ≠ kl.2 ∧ joint random8 kl.1 kl.2 = 0)).card = 48 ∧
  variance random8 (htTotal random8 randomOutcome8) ≤
    expect random8 (c2Estimator random8 randomOutcome8) ∧ (-13/4:ℝ) < 0

/-- P027-T10, Supplement p. A3, Section C and Table A2:
the full positive-size witness (1,3,...) has the specified cumulative-size
uniform-start law, marginal and joint probabilities, 48 ordered zero pairs,
samplewise estimates, total/mean moments and downward bias. Its sizes have
positive probability under the normalized offset negative-binomial generator
and obey the PPS feasibility inequality; its outcomes have the additive residual
representation for every beta. The entire stated open box has negative A,
while C2 remains conservative. The usual measure-theoretic conditions are assumed.
This witness refutes the inference from x_k >= 1 and the noisy model
y_k = beta*x_k + epsilon_k to conservativity for every realized finite
population. It does not refute the literal assertion for outcomes
proportional to the positive size vector. -/
def T10WholeStatement : Prop :=
  Random8Witness ∧ FourPhaseStartWhole random8 randomSize8 1 3 ∧
  Random8WholeDetails ∧ RandomSizeSupportWhole

end
end SAP.P027a
