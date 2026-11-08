import AronowAudit.P011.Wave1.Gap.FidP011

/-! Compile-time bindings to the independently approved P011 fidelity records,
and the negation of the universally closed printed T20 convergence claim. -/

set_option autoImplicit false

namespace AronowAudit.P011.Wave1

open AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal

noncomputable section

namespace FidP011Contracts

/-- Approved statement copied from `map-fid-P011/map.json`, record 0 (P011-T2),
`proposed_statement_lean`. Both `ref1-fid-P011/referee.json` and
`ref2-fid-P011/referee.json` accept this record with `fixes: []`.
Only the theorem header is changed to a universally quantified proposition;
the explicit binders retain their order and kinds. -/
def approvedContract_P011_T2 : Prop := ∀
    (t : ℝ) (ht : t = 1 ∨ t = 2),
    (∀ i : Fin 3,
      pathMean (fun u v => pathBlock t u v i) =
        (![t, -2*t, t] : Fin 3 → ℝ) i) ∧
    (∀ i : Fin 3,
      expectation (pathModel t 1) (fun y => y i) =
        (![t, -2*t, t] : Fin 3 → ℝ) i) ∧
    covariance (pathModel t 1) =
      (![![1, 3/5, 0], ![3/5, 1, 4/5], ![0, 4/5, 1]] :
        Matrix (Fin 3) (Fin 3) ℝ) ∧
    quadratic (oracleMatrix pathGraph) (![t, -2*t, t] : Fin 3 → ℝ) = -2*t^2 ∧
    pathMean (fun u v => ∑ i, pathBlock t u v i) = 0 ∧
    pathMean (fun u v => (∑ i, pathBlock t u v i)^2) = 29/5 ∧
    pathMean (fun u v => quadratic (oracleMatrix pathGraph) (pathBlock t u v)) =
      29/5 - 2*t^2 ∧
    pathMean (fun u v =>
      (quadratic (oracleMatrix pathGraph) (pathBlock t u v) - (29/5 - 2*t^2))^2) =
      8*t^2 + 8836/625 ∧
    pathMean (fun u v => (∑ i, pathBlock t u v i) *
      (∑ i, ∑ j, oracleMatrix pathGraph i j * pathBlock t u v j)) = 14 ∧
    quadratic (oracleMatrix pathGraph) (fun _ => 1) = 7

example : approvedContract_P011_T2 :=
  @AronowAudit.P011.Wave1.path_block_moments_with_covariance

/-- Approved certificate statement copied from `map-fid-P011/map.json`,
record 2 (P011-T20), `proposed_statement_lean`. Both
`ref1-fid-P011/referee.json` and `ref2-fid-P011/referee.json` accept this
closed statement with `fixes: []`; there are no outer binders to add. -/
def approvedContract_P011_T20 : Prop :=
    Scaling signFamily 1 1 1 2 ∧ Valid signFamily ∧
    (∀ n : ℕ, 0 < n →
      Homoskedastic (signModel n) ∧ beta (signModel n) = 0 ∧
      (n : ℝ)*var (signModel n) (betaHat (signModel n)) = 1 ∧
      expectation (signModel n) (fun y => (betaHat (signModel n) y)^2) = 1/(n : ℝ) ∧
      (∀ y : Fin n → ℝ, (∀ i, y i = 1 ∨ y i = -1) →
        (n : ℝ)*V2star (signModel n) y = 1 - (betaHat (signModel n) y)^2 ∧
        |(n : ℝ)*V2star (signModel n) y -
          (n : ℝ)*var (signModel n) (betaHat (signModel n))| =
            (betaHat (signModel n) y)^2)) ∧
    (∀ ε : ℝ, 0 < ε →
      (∀ n : ℕ, 0 < n →
        1 - 1/((n : ℝ)*ε) ≤
          AronowAudit.P011.Wave1.signInsideProbability n ε) ∧
      Tendsto (fun k => AronowAudit.P011.Wave1.signInsideProbability (k+1) ε)
        atTop (𝓝 1)) ∧
    AronowAudit.P011.Wave1.signInsideProbability 2 (1/2) = 1/2 ∧
    AronowAudit.P011.Wave1.signInsideProbability 4 (1/2) = 7/8 ∧
    AronowAudit.P011.Wave1.signInsideProbability 16 (1/2) = 32631/32768 ∧
    ¬ (∀ ε : ℝ, 0 < ε →
      Tendsto (fun k => AronowAudit.P011.Wave1.signInsideProbability (k+1) ε)
        atTop (𝓝 0))

example : approvedContract_P011_T20 :=
  @AronowAudit.P011.Wave1.printed_sign_counterexample_full

/-- P011-T20: the strict inside-event, limit-zero display in the proof of
Proposition 2, printed p. 2246 (PDF p. 9), under its full universal closure.
Sources: `runs/P011/staged/main.txt:222-229,444-480`, `runs/P011/lean/targets.json`
(T20, T34 and standing conventions S10), `map-fid-P011/map.json` record 2,
and both `ref1-fid-P011` / `ref2-fid-P011` referee records for T20.

Conventions needed to give the printed display a proposition:
* `F` ranges over every `Family`: positive sample sizes `n = F.size k`
  tend to infinity. The limit is along `k`; no fixed family, size sequence,
  outcome law, graph, coefficient vector or positive epsilon is selected.
  `Scaling` includes nested induced graphs, vector dependency, and exactly
  Assumption 2's four fixed positive real constants, weighted almost-sure
  bound, degree bound, and nondegenerate scaled-variance limit. As in S10,
  each size has its own joint law; no projective law condition is imposed.
* `Model` records observed coordinates, with deterministic graphs, degrees
  and coefficients. `Valid` records recruitment inclusion and valid degree
  bounds. `Homoskedastic` is equality of weighted-coordinate variances on
  the observed indices (S10(g), T24); unobserved vertices are suppressed.
  The sign witness observes every vertex, so it also satisfies the literal
  printed all-vertex version of Assumption 3.
* Expectation, variance and probability use the model's single joint law;
  `beta` is its expectation of `betaHat` and may depend on size (S10(a)).
  No equal-coordinate-means condition is imposed. Double sums are ordered.
* The print leaves its single-index correlations undefined. Following T21
  and the approved mapper/referee reading, `V2star` uses pairwise weighted
  covariance divided by the common variance, with correlation zero if
  that variance is zero. This convention never affects the sign witness:
  its true adjacency matrix is zero, so the whole correlation term vanishes.
* `V2star` uses the true induced graph, the sample variance has divisor n,
  and the centering is the actual n times variance of `betaHat`. The event
  retains the printed strict `< ε`, every real `ε > 0`, and limit zero.
  All sizes are positive; no division-by-zero size is used. -/
def printedContract_P011_T20 : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ),
    Scaling F c1 c2 c3 c4 → Valid F →
    (∀ k, Homoskedastic (F.model k)) →
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun k => probability (F.model k)
        {y | |(F.size k : ℝ)*V2star (F.model k) y -
          (F.size k : ℝ)*var (F.model k) (betaHat (F.model k))| < ε})
        atTop (𝓝 0)

end FidP011Contracts

/-- The existing full fair-sign certificate refutes the entire universally
closed printed T20 contract, with no new external hypothesis. -/
theorem printed_sign_counterexample_full_printed_negation :
    ¬ FidP011Contracts.printedContract_P011_T20 := by
  intro hprinted
  rcases printed_sign_counterexample_full with
    ⟨hScaling, hValid, hMoments, hBounds, hTwo, hFour, hSixteen, hNotZero⟩
  have hHomoskedastic : ∀ k, Homoskedastic (signFamily.model k) := by
    intro k
    exact (hMoments (k+1) (Nat.succ_pos k)).1
  have hzero := hprinted signFamily 1 1 1 2 hScaling hValid hHomoskedastic
  apply hNotZero
  intro ε hε
  simpa only [signInsideProbability, SignCompletion.family_model,
    SignCompletion.family_size, Nat.cast_add, Nat.cast_one] using hzero ε hε

namespace FidP011Contracts

/-- Exact full-negation target for P011-T20. -/
abbrev Target_P011_T20 : Prop := ¬ printedContract_P011_T20

example : Target_P011_T20 :=
  AronowAudit.P011.Wave1.printed_sign_counterexample_full_printed_negation

example : Target_P011_T20 ↔ ¬ printedContract_P011_T20 := Iff.rfl

end FidP011Contracts

#print axioms AronowAudit.P011.Wave1.path_block_moments_with_covariance
#print axioms AronowAudit.P011.Wave1.printed_sign_counterexample_full
#print axioms AronowAudit.P011.Wave1.printed_sign_counterexample_full_printed_negation

end

end AronowAudit.P011.Wave1
