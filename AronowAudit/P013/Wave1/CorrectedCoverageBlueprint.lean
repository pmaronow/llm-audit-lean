import AronowAudit.P013.P013_Audit
import AronowAudit.External.Causalean.Mathlib.Probability.SteinMethod.StandardizedDepGraphCLT

/-!
# P013-T2: corrected Proposition 6.2

For every `S : ExperimentSequence` with the nested setup, comparison-specific C3
(`ComparisonBounded`), genuine C5 (`Condition5Genuine`), C6 and the added lower-tail
condition (L) (`LowerTailCondition`), the defined real Wald interval of expression (11)
has `liminf` coverage at least `1-α` for every `0<α<1`.

Compared with Proposition 6.2 as printed, the corrected theorem replaces literal
`Condition5Printed` by `Condition5Genuine`, narrows all-exposure `Condition3` to
`ComparisonBounded`, uses the comparison positivity in `ExperimentSequence` instead of
`StandingPositivity`, keeps `NestedPopulationSetup` and `Condition6`, and adds
`LowerTailCondition`. Relative to the genuine-dependency reading of the paper, (L) is
the one new coverage premise.

The finite-design infrastructure consists of the atomic-measure identity `N1`, the
vector-independence implication `N2`, the HT score decomposition `N3`, the dependency-graph
construction `N4`, the HT CLT `N5`, the Gaussian facts `N6`, the moving-width interval
limit `N7`, and the support-relabelling lemmas. These also support the P013-T18 refutation.
-/

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.CorrectedCoverage

open AronowAudit.P013 Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-! ## Support relabelling (shared with P013-T18) -/

/-- `Experiment` requires the support type `Fin supportSize`. This relabels any finite
design along an equivalence of supports (paper p. 1914: Ω only labels the supported
assignment vectors). -/
def relabelDesign {Ω : Type*} [Fintype Ω] {m : ℕ} (P : Design Ω) (e : Ω ≃ Fin m) :
    Design (Fin m) where
  weight z := P.weight (e.symm z)
  positive z := P.positive (e.symm z)
  total := by rw [Equiv.sum_comp e.symm P.weight]; exact P.total

/-- The population carried along a support relabelling; outcomes are unchanged. -/
def relabelPopulation {Ω : Type*} [Fintype Ω] {m N K : ℕ} {P : Design Ω}
    (F : Population P N K) (e : Ω ≃ Fin m) : Population (relabelDesign P e) N K where
  exposure z := F.exposure (e.symm z)
  outcome := F.outcome

section Relabel

variable {Ω : Type*} [Fintype Ω] {m : ℕ}

/-- Design expectations are invariant under support relabelling. -/
theorem expectation_relabel (P : Design Ω) (e : Ω ≃ Fin m) (X : Fin m → ℝ) :
    expectation (relabelDesign P e) X = expectation P (fun ω => X (e ω)) := by
  unfold expectation
  rw [← Equiv.sum_comp e (fun z => (relabelDesign P e).weight z * X z)]
  simp [relabelDesign]

/-- Design probabilities are invariant under support relabelling. -/
theorem probability_relabel (P : Design Ω) (e : Ω ≃ Fin m) (A : Fin m → Prop) :
    probability (relabelDesign P e) A = probability P (fun ω => A (e ω)) := by
  classical
  unfold probability
  rw [← Equiv.sum_comp e (fun z => if A z then (relabelDesign P e).weight z else 0)]
  simp [relabelDesign]

/-- Marginal exposure probabilities are invariant under support relabelling. -/
theorem pi_relabel {N K : ℕ} {P : Design Ω} (F : Population P N K) (e : Ω ≃ Fin m)
    (i : Fin N) (d : Fin K) : pi (relabelPopulation F e) i d = pi F i d := by
  unfold pi
  rw [expectation_relabel]
  congr 1
  funext ω
  simp [indicator, relabelPopulation]

/-- Joint exposure probabilities are invariant under support relabelling. -/
theorem jointPi_relabel {N K : ℕ} {P : Design Ω} (F : Population P N K) (e : Ω ≃ Fin m)
    (i j : Fin N) (d f : Fin K) :
    jointPi (relabelPopulation F e) i j d f = jointPi F i j d f := by
  unfold jointPi
  rw [expectation_relabel]
  simp [indicator, relabelPopulation]

end Relabel

/-!
## HT scores -/

/-- Centred HT unit score:
`X_i = 1{D_i=d} y_i(d)/π_i(d) - 1{D_i=e} y_i(e)/π_i(e) - (y_i(d)-y_i(e))`. -/
def htScore {Ω : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (i : Fin N) (z : Ω) : ℝ :=
  (indicator F.exposure i d z * (F.outcome i d / pi F i d) -
    indicator F.exposure i e z * (F.outcome i e / pi F i e)) -
  (F.outcome i d - F.outcome i e)

/-!
## Corrected coverage statement -/

/-- **Target (P013-T2).** Corrected Proposition 6.2
(p. 1926; Appendix A.7, p. 1943). -/
def Target : Prop :=
  ∀ S : ExperimentSequence, NestedPopulationSetup S → ComparisonBounded S →
    Condition5Genuine S → Condition6 S → LowerTailCondition S →
    ∀ α : ℝ, 0 < α → α < 1 → 1 - α ≤ liminf (seqCoverage S α) atTop

/-!
## Supporting statements -/

/-- **N1.** On a finite discrete support, `designMeasure P = Σ_z ofReal(p_z) δ_z`
is a probability measure and its real event masses are the finite design probabilities.
The corresponding expectation identity is `integral_designMeasure`. Used also for P013-T18. -/
def N1 : Prop :=
  ∀ {Ω : Type} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (P : Design Ω),
    MeasureTheory.IsProbabilityMeasure (designMeasure P) ∧
      ∀ A : Ω → Prop, (designMeasure P).real {z | A z} = probability P A

/-- **N2.** Atom factorization of the two restricted exposure vectors
(`VectorIndependent`) gives `IndepFun` of the full restricted vectors under
`designMeasure`. Pairwise independence is not a substitute. Used also for P013-T18. -/
def N2 : Prop :=
  ∀ {Ω : Type} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {N K : ℕ},
    0 < K → ∀ (P : Design Ω) (D : Ω → Fin N → Fin K) (A B : Finset (Fin N)),
      VectorIndependent P D A B →
        ProbabilityTheory.IndepFun (fun z (i : A) => D z i.1) (fun z (j : B) => D z j.1)
          (designMeasure P)

/-- **N3.** The centred HT unit scores have design mean zero, sum to `N(τ̂-τ)`,
have sum-of-scores second moment `N² Var(τ̂)`, and are bounded by `2c₁(c₂+1)`
under the comparison bounds. Finite algebra only. -/
def N3 : Prop :=
  ∀ {Ω : Type} [Fintype Ω] {N K : ℕ} {P : Design Ω} (F : Population P N K) (d e : Fin K),
    Positivity F d → Positivity F e →
      (∀ i, expectation P (htScore F d e i) = 0) ∧
      (∀ z, ∑ i, htScore F d e i z = (N : ℝ) * (htEffect F d e z - causalEffect F d e)) ∧
      expectation P (fun z => (∑ i, htScore F d e i z) ^ 2) =
        (N : ℝ) ^ 2 * variance P (htEffect F d e) ∧
      ∀ c1 c2 : ℝ, (∀ i, |F.outcome i d| ≤ c1 ∧ |F.outcome i e| ≤ c1 ∧
          |1 / pi F i d| ≤ c2 ∧ |1 / pi F i e| ≤ c2) →
        ∀ i z, |htScore F d e i z| ≤ 2 * c1 * (c2 + 1)

/-- For a genuine C5 sequence, the centred HT scores carry a `DepGraph`
(reflexive symmetric relation, measurable entries, independence of separated tuples)
under `designMeasure`, with closed neighbourhoods uniformly bounded in size. -/
def DepGraphBridge : Prop :=
  ∀ S : ExperimentSequence, Condition5Genuine S → ∃ Dmax : ℕ, ∀ n : ℕ,
    ∃ D : Causalean.Mathlib.Probability.SteinMethod.DepGraph
        (fun (i : Fin (n + 1)) (z : Fin (S.experiment n).supportSize) =>
          htScore (seqPopulation S n) (S.treated n) (S.control n) i z)
        (designMeasure (seqLaw S n)),
      ∀ i, (D.nbhd i).card ≤ Dmax

/-- **N4.** Adding self-loops to the symmetric relation of genuine C5 gives
`G i j := i = j ∨ h i j`, with closed degree `≤ m+1`. Separated sets are disjoint
with no crossing `h`-edge (`corrected_symmetric_equivalence`), so `GenuineDependency`
and N2 give independence of the exposure tuples; `IndepFun.comp` transfers it
to the score tuples. -/
def N4 : Prop := N2 → DepGraphBridge

/-- **N5.** Under comparison C3, genuine C5 and C6, the true-variance standardized
HT contrast is asymptotically standard normal. The dependency CLT applies to the
scores of N3 on `designMeasure` (N1), with the `DepGraph` of N4, bound `2c₁(c₂+1)`,
second moment `N²V_N` and eventual floor `(c/2)N`. N1 converts CDFs back, with
`√(N²V) = N√V`. Used also for P013-T18. -/
def N5 : Prop :=
  N1 → N3 → DepGraphBridge →
    ∀ S : ExperimentSequence, ComparisonBounded S → Condition5Genuine S → Condition6 S →
      TendsNormal (seqLaw S)
        (fun n z => (seqEstimate S n z - seqTarget S n) / Real.sqrt (seqTrueVariance S n)) 0 1

/-- **N6.** The standard-normal CDF is continuous, symmetric and strictly increasing.
For `0<α<1`, `normalCritical α > 0` and
`normalCDF (normalCritical α) = 1-α/2`. The proof identifies these definitions
with the standard Gaussian CDF and quantile in `AronowAudit.P053.NormalCompletion`
using `standardNormalCDF_eq_cdf`. Used also for P013-T18. -/
def N6 : Prop :=
  Continuous normalCDF ∧ StrictMono normalCDF ∧ (∀ t, normalCDF (-t) = 1 - normalCDF t) ∧
    ∀ α : ℝ, 0 < α → α < 1 → 0 < normalCritical α ∧ normalCDF (normalCritical α) = 1 - α / 2

/-- **N7.** CDF convergence to `N(0,1)` and deterministic widths `w_n → a > 0`
give `P(|X_n| ≤ w_n) → 2Φ(a)-1`, by a CDF squeeze. Used also for P013-T18. -/
def N7 : Prop :=
  N6 → ∀ {L : ℕ → Type} [∀ n, Fintype (L n)] (P : ∀ n, Design (L n)) (X : ∀ n, L n → ℝ)
    (w : ℕ → ℝ) (a : ℝ), TendsNormal P X 0 1 → 0 < a → Tendsto w atTop (𝓝 a) →
      Tendsto (fun n => probability (P n) (fun z => |X n z| ≤ w n)) atTop
        (𝓝 (2 * normalCDF a - 1))

/-- **N8.** C6 and (L) give vanishing relative lower-tail probabilities
`P(V̂_N < (1-η)V_N) → 0` for each `0<η<1`, using `δ = ηc/2`
and eventually `(n+1)V_N ≥ c/2`. -/
def N8 : Prop :=
  ∀ S : ExperimentSequence, Condition6 S → LowerTailCondition S →
    ∀ η : ℝ, 0 < η → η < 1 →
      Tendsto (fun n => probability (seqLaw S n)
        (fun z => seqVarianceEstimate S n z < (1 - η) * seqTrueVariance S n)) atTop (𝓝 0)

/-- **N9.** For any finite-design sequence, a standard-normal limit of the
true-variance standardized statistic, eventually positive true variance and vanishing
relative lower tails give `liminf` defined Wald coverage `≥ 1-α`. The proof uses
`finite_wald_coverage_bound`, N7 at the fixed width `z√(1-η)`, then `η ↓ 0` with N6. -/
def N9 : Prop :=
  N6 → N7 → ∀ {L : ℕ → Type} [∀ n, Fintype (L n)] (P : ∀ n, Design (L n))
    (X Vhat : ∀ n, L n → ℝ) (target V : ℕ → ℝ),
    TendsNormal P (fun n z => (X n z - target n) / Real.sqrt (V n)) 0 1 →
    (∀ᶠ n in atTop, 0 < V n) →
    (∀ η : ℝ, 0 < η → η < 1 →
      Tendsto (fun n => probability (P n) (fun z => Vhat n z < (1 - η) * V n)) atTop (𝓝 0)) →
    ∀ α : ℝ, 0 < α → α < 1 →
      1 - α ≤ liminf (fun n => probability (P n) (fun z => 0 ≤ Vhat n z ∧
        |X n z - target n| ≤ normalCritical α * Real.sqrt (Vhat n z))) atTop


/-- **N10.** Independent fair own-assignment exposures with both potential outcomes
`1` satisfy every corrected premise, with `V_N = V̂_N = 4/N` at every assignment.
The finite support is relabelled using `relabelDesign`. This existence statement
is not a hypothesis of `assemble`. -/
def N10 : Prop :=
  ∃ S : ExperimentSequence, NestedPopulationSetup S ∧ StandingPositivity S ∧
    ComparisonBounded S ∧ Condition5Genuine S ∧ Condition6 S ∧ LowerTailCondition S ∧
    ∀ n z, seqTrueVariance S n = 4 / ((n : ℝ) + 1) ∧
      seqVarianceEstimate S n z = 4 / ((n : ℝ) + 1)

/-! ## Coverage implication -/

/-- C6 makes the true variance eventually positive. -/
theorem eventually_pos_of_condition6 (S : ExperimentSequence) (h : Condition6 S) :
    ∀ᶠ n in atTop, 0 < seqTrueVariance S n := by
  obtain ⟨c, hc, ht⟩ := h
  have hev : ∀ᶠ n : ℕ in atTop, c / 2 < ((n : ℝ) + 1) * seqTrueVariance S n :=
    ht.eventually (lt_mem_nhds (by linarith))
  filter_upwards [hev] with n hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  by_contra hneg
  have : ((n : ℝ) + 1) * seqTrueVariance S n ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hn1.le (not_lt.mp hneg)
  linarith

/-- The supporting statements imply the corrected coverage theorem. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6) (h7 : N7)
    (h8 : N8) (h9 : N9) : Target := by
  intro S _hnested hc3 hc5 hc6 hL α hα hα1
  exact h9 h6 h7 (seqLaw S) (seqEstimate S) (seqVarianceEstimate S) (seqTarget S)
    (seqTrueVariance S) (h5 h1 h3 (h4 h2) S hc3 hc5 hc6) (eventually_pos_of_condition6 S hc6)
    (h8 S hc6 hL) α hα hα1


end

end AronowAudit.P013.Wave1.CorrectedCoverage
