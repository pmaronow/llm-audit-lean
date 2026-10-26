import AronowAudit.P004.P004_Spatial

/-! # Counting-measure line populations (P004)

The population `linePopulation R` has Euclidean nodes `(10 i, 0)`, a spatial measure equal
to the sum of unit Dirac masses at those nodes, outcome field `R i z` at the `i`-th node
and zero elsewhere, and band `[0,d]` of radius `d`.

The raw outcome bound requires `0 ≤ B`: at `N = 0` the table bound is vacuous.
The separation formula uses real subtraction. The propositions `N1`–`N7` describe
separation, averaging, well-definedness, boundedness, spacing, and locality.
`spatialLocal_of` assembles `SpatialLocalConditions` from `N5`, `N6`, and `N7`.
-/

namespace AronowAudit.P004.Wave1.LinePopulation

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- The node separation of a line population is `10 * |(i : ℝ) - (j : ℝ)|`,
with subtraction computed in `ℝ`. -/
def N1 : Prop :=
  ∀ {N : ℕ} (R : CircleTable N) (i j : Fin N),
    nodeSeparation (linePopulation R) i j = 10 * |(i : ℝ) - (j : ℝ)|

/-- At any band `d ≥ 0`, the spatial average is the arithmetic mean of the
table over the line ball of radius `d`. The ball contains `i`, so its count is positive. -/
def N2 : Prop :=
  ∀ {N : ℕ} (R : CircleTable N) (d : ℝ), 0 ≤ d → ∀ (i : Fin N) (z : Assignment N),
    circleAverage (linePopulation R) d i z =
      (∑ j ∈ ball (nodeSeparation (linePopulation R)) i d, R j z) /
        ((ball (nodeSeparation (linePopulation R)) i d).card : ℝ)

/-- At radius zero, the spatial average equals the table as a function of the
node and assignment, for every `N`, including `N = 0`. -/
def N3 : Prop :=
  ∀ {N : ℕ} (R : CircleTable N), circleAverage (linePopulation R) 0 = R

/-- Every nonnegative band of a line population satisfies `WellDefined`. -/
def N4 : Prop :=
  ∀ {N : ℕ} (R : CircleTable N) (d : ℝ), 0 ≤ d → WellDefined (linePopulation R) d

/-- A nonnegative uniform bound on table entries also bounds the outcome
field everywhere, including off the nodes, where it is zero. -/
def N5 : Prop :=
  ∀ {N : ℕ} (R : CircleTable N) (B : ℝ), 0 ≤ B → (∀ i z, |R i z| ≤ B) →
    ∀ x z, |(linePopulation R).outcome x z| ≤ B

/-- A ball of nonnegative radius `r` has at most `r / 5 + 1` nodes,
uniformly in the population size. -/
def N6 : Prop :=
  ∀ {N : ℕ} (R : CircleTable N) (i : Fin N) (r : ℝ), 0 ≤ r →
    ((ball (nodeSeparation (linePopulation R)) i r).card : ℝ) ≤ r / 5 + 1

/-- If changing a coordinate farther than `ρ` from `j` leaves `R j` unchanged,
then the band-`d` averages satisfy `LocalAt` with cutoff `2d + 2ρ`, for
nonnegative `ρ` and `d`. A shared source for averages at `i` and `j` therefore
forces their separation to be at most `2d + 2ρ`. -/
def N7 : Prop :=
  ∀ {N : ℕ} (R : CircleTable N) (ρ d : ℝ), 0 ≤ ρ → 0 ≤ d →
    (∀ (j k : Fin N) (z : Assignment N) (b : Bool),
      ρ < 10 * |(j : ℝ) - (k : ℝ)| → R j (Function.update z k b) = R j z) →
    LocalAt (circleAverage (linePopulation R) d) (nodeSeparation (linePopulation R))
      (2 * d + 2 * ρ)

/-- Combined conclusion: the three clauses of `SpatialLocalConditions` for a
sequence of line populations with uniformly bounded, uniformly local tables. -/
theorem spatialLocal_of (h5 : N5) (h6 : N6) (h7 : N7) (R : ∀ N, CircleTable N) (B ρ : ℝ)
    (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (hR : ∀ N i z, |R N i z| ≤ B)
    (hloc : ∀ N (j k : Fin N) (z : Assignment N) (b : Bool),
      ρ < 10 * |(j : ℝ) - (k : ℝ)| → R N j (Function.update z k b) = R N j z) :
    SpatialLocalConditions (fun N => linePopulation (R N)) := by
  refine ⟨⟨B + 1, by linarith, Filter.Eventually.of_forall fun N x z => ?_⟩,
    ⟨fun d => 2 * d + 2 * ρ, fun d hd => by positivity, fun d hd =>
      Filter.Eventually.of_forall fun N => h7 (R N) ρ d hρ hd (hloc N)⟩,
    ⟨fun r => r / 5 + 1, fun r hr => Filter.Eventually.of_forall fun N i =>
      h6 (R N) i r hr⟩⟩
  have := h5 (R N) B hB (hR N) x z
  linarith

end
end AronowAudit.P004.Wave1.LinePopulation
