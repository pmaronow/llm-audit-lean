import Mathlib
import SAP.P026b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026b
open Finset
open scoped BigOperators
noncomputable section

/-- Equation [12], with sums of observed outcomes over the original units.
The divisors `m` and `M - m` are specified constants, not realized arm sizes. -/
def T21ClusterContrast {Ω I : Type*} [Fintype I]
    (D : Design Ω I ℝ) (N M m : ℕ) (x z : I → ℝ) (w : Ω) : ℝ :=
  (M : ℝ) / N * (observedArmSum D true x z w / m -
    observedArmSum D false x z w / (M - m : ℕ))

/-- The three nonempty clusters of the four-unit bias witness. -/
def T21WitnessCluster : Fin 4 → Fin 3 := ![0, 1, 2, 2]

/-- The allocation treating just cluster `j`. -/
def T21OneHot (j : Fin 3) : Fin 3 → Bool := fun c => decide (j = c)

/-- Uniformly choose one of three clusters on the full binary allocation space.
All other allocations receive mass zero. -/
def T21WitnessWeight (w : Fin 3 → Bool) : ℝ :=
  ∑ j : Fin 3, if w = T21OneHot j then 1 / 3 else 0

/-- P026-T21, Section 4.1, equations [11]–[12], pp. 139–140 (PDF pp. 5–6).
With exactly n of N units treated and equal inclusion probabilities, HT equals
the actual difference in unit means on support, and both the displayed contrast
and that difference are unbiased. For any partition into M nonempty clusters
whose distinct treatment indicators disagree with positive probability, with
treatment and control marginals m/M and (M-m)/M, 0 < m < M, HT equals
M/N times the difference of observed unit arm totals divided by m and M-m,
at every allocation; this contrast is unbiased, without a fixed cluster count.
There is a real-valued four-unit example with clusters {1}, {2}, {3,4}, one
uniformly treated cluster, distinct cluster indicators, and both unit arms
nonempty on support: for sharp-null outcomes (1,1,0,0), the actual difference
in means has expectation 1/9, whereas the ATE and expected HT are zero. -/
def T21WholeStatement : Prop :=
  (∀ (Ω I : Type) [Fintype Ω] [Fintype I] [DecidableEq I]
    (D : Design Ω I ℝ), probabilityDesign D →
    ∀ (n : ℕ), 0 < n → n < Fintype.card I →
    (∀ i, marginal D true i = (n : ℝ) / Fintype.card I ∧
      marginal D false i = ((Fintype.card I - n : ℕ) : ℝ) / Fintype.card I) →
    (∀ w, 0 < D.weight w → (∑ i, indicator D true w i) = n) →
    ∀ (x z : I → ℝ),
    (∀ w, 0 < D.weight w →
      (∑ i, indicator D false w i) = (Fintype.card I - n : ℕ) ∧
      ht D (Fintype.card I) x z w =
        observedArmSum D true x z w / n -
          observedArmSum D false x z w / (Fintype.card I - n : ℕ) ∧
      differenceInMeans D x z w =
        observedArmSum D true x z w / n -
          observedArmSum D false x z w / (Fintype.card I - n : ℕ)) ∧
    expectation D (fun w => observedArmSum D true x z w / n -
      observedArmSum D false x z w / (Fintype.card I - n : ℕ)) =
        ate (Fintype.card I) x z ∧
    expectation D (differenceInMeans D x z) = ate (Fintype.card I) x z) ∧
  (∀ (U : Type) [Fintype U] [DecidableEq U] [Nonempty U]
    (M m : ℕ), 0 < m → m < M →
    ∀ (E : ClusterExperiment U (Fin M)),
    (∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d) →
    (∀ c, marginal E.clusterDesign true c = (m : ℝ) / M ∧
      marginal E.clusterDesign false c = ((M - m : ℕ) : ℝ) / M) →
    ∀ (x z : U → ℝ),
    (∀ w, ht E.unitDesign (Fintype.card U) x z w =
      T21ClusterContrast E.unitDesign (Fintype.card U) M m x z w) ∧
    expectation E.unitDesign (T21ClusterContrast E.unitDesign (Fintype.card U) M m x z) =
      ate (Fintype.card U) x z ∧
    expectation E.unitDesign (ht E.unitDesign (Fintype.card U) x z) =
      ate (Fintype.card U) x z) ∧
  (∃ E : ClusterExperiment (Fin 4) (Fin 3),
    E.cluster = T21WitnessCluster ∧ E.assignment.weight = T21WitnessWeight ∧
    (∀ c, marginal E.clusterDesign true c = 1 / 3 ∧
      marginal E.clusterDesign false c = 2 / 3) ∧
    (∀ i, marginal E.unitDesign true i = 1 / 3 ∧
      marginal E.unitDesign false i = 2 / 3) ∧
    (∀ c d, c ≠ d → disagreement E.clusterDesign c d = 2 / 3) ∧
    (∀ w, 0 < E.assignment.weight w →
      (∑ c, indicator E.clusterDesign true w c) = 1 ∧
      0 < ∑ i, indicator E.unitDesign true w i) ∧
    (∀ w, 0 < E.assignment.weight w → 0 < ∑ i, indicator E.unitDesign false w i) ∧
    expectation E.unitDesign
      (differenceInMeans E.unitDesign (![1, 1, 0, 0]) (![1, 1, 0, 0])) = 1 / 9 ∧
    expectation E.unitDesign
      (ht E.unitDesign 4 (![1, 1, 0, 0]) (![1, 1, 0, 0])) = 0 ∧
    ate 4 (![1, 1, 0, 0] : Fin 4 → ℝ) (![1, 1, 0, 0]) = 0 ∧
    expectation E.unitDesign
      (differenceInMeans E.unitDesign (![1, 1, 0, 0]) (![1, 1, 0, 0])) ≠
        ate 4 (![1, 1, 0, 0] : Fin 4 → ℝ) (![1, 1, 0, 0]))

end
end SAP.P026b
