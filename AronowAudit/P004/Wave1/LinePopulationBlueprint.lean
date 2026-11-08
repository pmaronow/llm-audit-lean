import AronowAudit.P004.P004_Spatial

/-! # Shared blueprint module: counting-measure line populations (P004, wave 1)

Shared by the two T35 refutations (`IpwBoundCoverage`, `IpwProposition`) and the T36
refutation (`ObservationalCoverage`). It concerns the existing project definition
`AronowAudit.P004.linePopulation R` (nodes are the Euclidean points `(10 i, 0)`, the spatial
measure is the sum of unit Dirac masses at those points, the outcome field equals `R i z` at
the `i`-th point and `0` elsewhere, and the band of radius `d` is `[0,d]`).

Paper-proof source: map-P004 REPORT, records 3-5, paragraphs "For every N use the Euclidean
linePopulation realization ..." and "Verify spatial conditions also away from the target
distance ...", with the referee-1 fix: the raw outcome bound needs `0 ≤ B` (at `N = 0` the
table bound is vacuous), and the separation formula is written with real subtraction.

Nodes `N1`-`N7` are leaves (no dependence on other nodes). `spatialLocal_of` (proved here)
assembles the three-clause `SpatialLocalConditions` from `N1`, `N5`, `N6`, `N7`.
-/

namespace AronowAudit.P004.Wave1.LinePopulation

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- N1 (paper proof: "nodeSeparation(i,j)=10·|i.val−j.val|"; referee-1 fix: real subtraction).
The node separation of a line population is `10 |i - j|`, computed in `ℝ`.
Use `Metric.infDist_singleton`, `EuclideanSpace.dist_eq`, `planePoint`, `Real.sqrt_sq_eq_abs`;
`nodeSeparation` is an `sInf` over a singleton set here. -/
def N1 : Prop :=
  ∀ {N : ℕ} (R : CircleTable N) (i j : Fin N),
    nodeSeparation (linePopulation R) i j = 10 * |(i : ℝ) - (j : ℝ)|

/-- N2 (paper proof: "A radius-d region about i contains only support points c_k with
distance ≤ d"): at any band `d ≥ 0` the actual spatial average is the plain average of the
table over the line ball of radius `d` (which contains `i`, so the count is positive).
Use `Measure.finsetSum_apply`, `Measure.dirac_apply`, `integral_finsetSum_measure`,
`setIntegral_dirac` (pattern: `shell_spatial_table` in `P004_Spatial.lean`), and N1. -/
def N2 : Prop :=
  ∀ {N : ℕ} (R : CircleTable N) (d : ℝ), 0 ≤ d → ∀ (i : Fin N) (z : Assignment N),
    circleAverage (linePopulation R) d i z =
      (∑ j ∈ ball (nodeSeparation (linePopulation R)) i d, R j z) /
        ((ball (nodeSeparation (linePopulation R)) i d).card : ℝ)

/-- N3 (paper proof: "At d=0 a region consists of its own point c_i and has mass one, so
circleAverage(P_N,0)=R for every assignment"). Equality of functions, for every `N`
(trivially at `N = 0`). Follows from N1, N2 (`ball i 0 = {i}`), or directly. -/
def N3 : Prop :=
  ∀ {N : ℕ} (R : CircleTable N), circleAverage (linePopulation R) 0 = R

/-- N4 (paper proof: "All bands [0,d] with d≥0 are measurable; their support masses are
positive and finite and outcomes integrable, so WellDefined ... holds for every N").
Use `Metric.infDist_singleton`, `measurableSet_Icc.preimage`, `Measure.finsetSum_apply`,
`integrable_finsetSum_measure`, `integrable_dirac` (pattern: `shell_wellDefined`). -/
def N4 : Prop :=
  ∀ {N : ℕ} (R : CircleTable N) (d : ℝ), 0 ≤ d → WellDefined (linePopulation R) d

/-- N5 (paper proof: "The field is zero off the distinct nodes and has absolute value ≤ B at
them"; referee-1 fix: assume `0 ≤ B`). At most one summand of the outcome field is nonzero
because the points `(10 i, 0)` are distinct. -/
def N5 : Prop :=
  ∀ {N : ℕ} (R : CircleTable N) (B : ℝ), 0 ≤ B → (∀ i z, |R i z| ≤ B) →
    ∀ x z, |(linePopulation R).outcome x z| ≤ B

/-- N6 (paper proof: "A radius-r ball on this line has at most 2⌊r/10⌋+1 points, uniformly
in N"): the count is at most `r/5 + 1`. Inject the ball into the integers
`{k : |k - i| ≤ r/10}` (`Finset.card_le_card_of_injOn`, `Int.card_Icc`). -/
def N6 : Prop :=
  ∀ {N : ℕ} (R : CircleTable N) (i : Fin N) (r : ℝ), 0 ≤ r →
    ((ball (nodeSeparation (linePopulation R)) i r).card : ℝ) ≤ r / 5 + 1

/-- N7 (paper proof: "Each R_k depends only on its own coin and its mate's coin ... any
treatment source affecting this average is at distance ≤ d+10 ... A shared source between
averages at i,j implies |c_i−c_j| ≤ 2(d+10)"), for a general source range `ρ`: if every table
entry `R j` is unchanged by flipping coordinates farther than `ρ` from `j`, then the band-`d`
averages satisfy `LocalAt` with cutoff `2d + 2ρ`. Use N1, N2, `interferes`, `sharesSource`,
`Function.update`. -/
def N7 : Prop :=
  ∀ {N : ℕ} (R : CircleTable N) (ρ d : ℝ), 0 ≤ ρ → 0 ≤ d →
    (∀ (j k : Fin N) (z : Assignment N) (b : Bool),
      ρ < 10 * |(j : ℝ) - (k : ℝ)| → R j (Function.update z k b) = R j z) →
    LocalAt (circleAverage (linePopulation R) d) (nodeSeparation (linePopulation R))
      (2 * d + 2 * ρ)

/-- Assembled (proved here, not a node): the three clauses of `SpatialLocalConditions` for a
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
