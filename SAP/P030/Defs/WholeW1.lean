import Mathlib
import SAP.P030.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P030

universe u

open scoped BigOperators
noncomputable section

/-- The midranks, centered ranks, centered products, exact rank-square sums,
and rational squared correlations of all six rows of Table 1. -/
def TableRankDetails : Prop :=
  averageRank tableY = ![3/2,4,3,3/2] ∧
  centeredRanks tableY = ![-1,3/2,1/2,-1] ∧
  (∀ r : Fin 6, averageRank (tableDistances r) =
    (![![1,2,3,4], ![1,2,3,4], ![1,2,3,4],
      ![5/2,1,5/2,4], ![4,1,2,3], ![4,1,2,3]] : Fin 6 → Fin 4 → ℝ) r) ∧
  (∀ r : Fin 6, centeredRanks (tableDistances r) =
    (![![-3/2,-1/2,1/2,3/2], ![-3/2,-1/2,1/2,3/2], ![-3/2,-1/2,1/2,3/2],
      ![0,-3/2,0,3/2], ![3/2,-3/2,-1/2,1/2],
      ![3/2,-3/2,-1/2,1/2]] : Fin 6 → Fin 4 → ℝ) r) ∧
  (∀ r : Fin 6, rankCross (tableDistances r) tableY =
    (![-1/2,-1/2,-1/2,-15/4,-9/2,-9/2] : Fin 6 → ℝ) r) ∧
  (∀ r : Fin 6, rankSquares (tableDistances r) =
    (![5,5,5,9/2,5,5] : Fin 6 → ℝ) r) ∧
  (∀ r : Fin 6, (tableRho r)^2 =
    (![1/90,1/90,1/90,25/36,9/10,9/10] : Fin 6 → ℝ) r) ∧
  ((1/90 : ℝ) < 25/36 ∧ (25/36 : ℝ) < 9/10)

/-- The actual observed-data lower and inclusive upper reference tails in the
constant no-effects population, with assignments counted with multiplicity. -/
def tenNullLowerP (z : Assignment 10) : ℝ :=
  uniformProbability tableΩ (fun w =>
    referenceStatistic tenS tenYnull tenG z w ≤ statistic tenS tenYnull tenG z)

def tenNullUpperP (z : Assignment 10) : ℝ :=
  uniformProbability tableΩ (fun w =>
    statistic tenS tenYnull tenG z ≤ referenceStatistic tenS tenYnull tenG z w)

/-- Fixed outcomes are constant under every binary assignment, imputation agrees
with the actual statistic, the six actual tails have the displayed values, and
the actual conditional statistic has exactly three distinct values. -/
def NullReferenceDetails : Prop :=
  (∀ z : Assignment 10, (fun i : Fin 4 => tenYnull (tenFixed i) z) = tableY) ∧
  (∀ obs z : Assignment 10,
    referenceStatistic tenS tenYnull tenG obs z = statistic tenS tenYnull tenG z) ∧
  (∀ r : Fin 6, tenNullLowerP (tenAssignment (tableTreatment r)) =
    (![1,1,1,1/2,1/3,1/3] : Fin 6 → ℝ) r) ∧
  (∀ r : Fin 6, tenNullUpperP (tenAssignment (tableTreatment r)) =
    (![1/2,1/2,1/2,2/3,1,1] : Fin 6 → ℝ) r) ∧
  (Finset.univ.image (fun r : Fin 6 =>
    statistic tenS tenYnull tenG (tenAssignment (tableTreatment r)))).card = 3

/-- P030-T2, p. 7 and Table 1, p. 9 (PDF pp. 5, 7): a genuine no-effects
ten-unit population realizes the table's six-assignment conditional law. All
midranks, centered ranks, products, square sums, squared correlations, strict
orders, roundings, and inclusive tails have their stated values. For
0 < alpha <= 2/3 the printed rule rejects exactly the three assignments with
p = 1 and has conditional size 1/2; the corrected rule rejects none. The printed
size exceeds every positive alpha < 1/2, including alpha = 1/20. -/
def T2WholeStatement : Prop :=
  T2Statement ∧ TableRankDetails ∧ NullReferenceDetails ∧
  (∀ α : ℝ, 0 < α → α ≤ 2/3 → ∀ r : Fin 6,
    (printedReject α (tenNullLowerP (tenAssignment (tableTreatment r))) ↔
      tenNullLowerP (tenAssignment (tableTreatment r)) = 1) ∧
    (printedReject α (tenNullLowerP (tenAssignment (tableTreatment r))) ↔ r.val < 3) ∧
    ¬ correctedReject α (tenNullLowerP (tenAssignment (tableTreatment r)))
      (tenNullUpperP (tenAssignment (tableTreatment r)))) ∧
  (∀ α : ℝ, 0 < α → α < 1/2 →
    α < uniformProbability tableΩ (fun z => printedReject α (tenNullLowerP z)))

/-- P030-T5, p. 7 (PDF p. 5), Equation (1): no interference, even no effects
of any kind, does not force statistic constancy. The genuine ten-unit experiment
has all the stated midranks, centered ranks, products, square sums, rational
squared correlations, exact correlations, strict orders, and roundings, and
exactly three distinct actual conditional statistics. Its observed-data p-value
at unit 7 is 1/3, rounding to 0.333. On any nonempty finite reference support, a
constant statistic instead gives a point mass at its observed value and p = 1. -/
def T5WholeStatement : Prop :=
  T5Statement.{u} ∧ TableRankDetails ∧ NullReferenceDetails ∧
  tenNullLowerP (tenAssignment 6) = 1/3 ∧
  |(1/3 : ℝ) - 0.333| < 0.0005 ∧
  (∀ {A : Type u} (Ω : Finset A), Ω.Nonempty → ∀ t : A → ℝ,
    (∀ z ∈ Ω, ∀ z' ∈ Ω, t z = t z') →
    ∀ z ∈ Ω, uniformProbability Ω (fun w => t w = t z) = 1)

/-- The observed row's explicit midranks, centered ranks, cross product, and
both exact rank-square sums for the formula counterexample. -/
def ObservedRankDetails : Prop :=
  averageRank tableY = ![3/2,4,3,3/2] ∧
  centeredRanks tableY = ![-1,3/2,1/2,-1] ∧
  averageRank (tableDistances 5) = ![4,1,2,3] ∧
  centeredRanks (tableDistances 5) = ![3/2,-3/2,-1/2,1/2] ∧
  rankCross (tableDistances 5) tableY = -9/2 ∧
  rankSquares (tableDistances 5) = 5 ∧ rankSquares tableY = 9/2

/-- Both conventional moment triples, together with the positive-divisor
invariance of the corrected Pearson expression for every table row. -/
def ObservedMomentDetails : Prop :=
  rankCov 4 (tableDistances 5) tableY = -9/8 ∧
  rankSquares (tableDistances 5) / 4 = 5/4 ∧ rankSquares tableY / 4 = 9/8 ∧
  rankCov 3 (tableDistances 5) tableY = -3/2 ∧
  rankSquares (tableDistances 5) / 3 = 5/3 ∧ rankSquares tableY / 3 = 3/2 ∧
  (∀ (r : Fin 6) (m : ℝ), 0 < m →
    rankCov m (tableDistances r) tableY /
      Real.sqrt ((rankSquares (tableDistances r) / m) * (rankSquares tableY / m)) =
        tableRho r)

/-- Midranks and rational square comparisons for the two numerical vectors
whose order is reversed by the printed formula. -/
def OrderingRankDetails : Prop :=
  averageRank (![1,2,1,1] : Fin 4 → ℝ) = ![2,4,2,2] ∧
  averageRank (![0,2,1,1] : Fin 4 → ℝ) = ![1,4,5/2,5/2] ∧
  (spearman (![1,2,1,1] : Fin 4 → ℝ) tableY)^2 = 2/3 ∧
  (spearman (![0,2,1,1] : Fin 4 → ℝ) tableY)^2 = 25/36 ∧
  ((2/3 : ℝ) < 25/36 ∧ (8/9 : ℝ) = 24/27)

/-- Explicit ranks and centered product in the nonconstant weakly monotone
example, including the three-decimal approximation of its correlation. -/
def WeakRankDetails : Prop :=
  averageRank (![1,2,3] : Fin 3 → ℝ) = ![1,2,3] ∧
  averageRank (![0,0,1] : Fin 3 → ℝ) = ![3/2,3/2,3] ∧
  centeredRanks (![1,2,3] : Fin 3 → ℝ) = ![-1,0,1] ∧
  centeredRanks (![0,0,1] : Fin 3 → ℝ) = ![-1/2,-1/2,1] ∧
  rankCross (![1,2,3] : Fin 3 → ℝ) ![0,0,1] = 3/2 ∧
  Nonconstant (![1,2,3] : Fin 3 → ℝ) ∧ Nonconstant (![0,0,1] : Fin 3 → ℝ) ∧
  |Real.sqrt 3 / 2 - 0.866| < 0.0005

/-- P030-T8, p. 8 (PDF p. 6): the printed covariance-over-product-of-variances
formula is false as a formula for rank correlation. The observed midranks,
centered ranks, products, square sums, and population and sample moments give
the two wrong values -4/5 and -3/5, with the stated rational square comparisons.
All six printed-formula values, correct correlations, and roundings are as
stated; the corrected expression is invariant under positive moment divisors.
The two explicit tied vectors reverse the printed formula's ordering, and the
nonconstant weakly monotone example has the stated ranks, products, variances,
and correlation sqrt(3)/2, rounding to 0.866 and unequal to either 1 or -1. -/
def T8WholeStatement : Prop :=
  T8Statement ∧ ObservedRankDetails ∧ ObservedMomentDetails ∧
  ((printedRho 4 (tableDistances 5) tableY)^2 = 16/25 ∧
    (printedRho 3 (tableDistances 5) tableY)^2 = 9/25 ∧
    (tableRho 5)^2 = 9/10 ∧
    (16/25 : ℝ) < 9/10 ∧ (9/25 : ℝ) < 9/10) ∧
  OrderingRankDetails ∧ WeakRankDetails

/-- The actual illustrative model's observed fixed outcomes, in unit order
1, 8, 9, 10. This is distinct from assuming no interference for that model. -/
def exampleFixedY : Fin 4 → ℝ :=
  fun i => tenYexample (tenFixed i) (tenAssignment 6)

/-- P030-T14, pp. 9-10 (PDF pp. 7-8): the actual adjacency outcome model gives
all the printed spatial, indirect, total, and fixed observations, including
fixed-outcome midranks (3/2, 4, 3, 3/2). The six conditional assignments have
the stated masses, distances, defined and unique reference correlations, exact
values, and roundings. Exactly the assignments treating units 6 and 7 lie in
the observed lower tail, giving the actual observed-data p = 2/6 = 1/3,
rounding to 0.333; every reference value is negative. -/
def T14WholeStatement : Prop := by
  classical
  exact T14Statement ∧
    averageRank exampleFixedY = ![3/2,4,3,3/2] ∧
    tableΩ.filter (fun w => referenceStatistic tenS tenYexample tenG
      (tenAssignment 6) w ≤ statistic tenS tenYexample tenG (tenAssignment 6)) =
      {tenAssignment (tableTreatment 4), tenAssignment (tableTreatment 5)} ∧
    (∀ r : Fin 6,
      0 < rankSquares (tableDistances r) ∧ 0 < rankSquares exampleFixedY ∧
      referenceStatistic tenS tenYexample tenG (tenAssignment 6)
        (tenAssignment (tableTreatment r)) *
        Real.sqrt (rankSquares (tableDistances r) * rankSquares exampleFixedY) =
          rankCross (tableDistances r) exampleFixedY ∧
      ∃! ρ : ℝ, ρ * Real.sqrt (rankSquares (tableDistances r) * rankSquares exampleFixedY) =
        rankCross (tableDistances r) exampleFixedY)

end
end SAP.P030
