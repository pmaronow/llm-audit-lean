import AronowAudit.P011.Wave1.Gap.FidP011

/-! The universally closed printed P011-T20 convergence claim and its negation. -/

set_option autoImplicit false

namespace AronowAudit.P011.Wave1

open AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal

noncomputable section

namespace FidP011Contracts


/-- P011-T20: the strict inside-event, limit-zero display in the proof of
Proposition 2, printed p. 2246 (PDF p. 9), under its full universal closure.

Conventions needed to give the printed display a proposition:
* `F` ranges over every `Family`: positive sample sizes `n = F.size k`
  tend to infinity. The limit is along `k`; no fixed family, size sequence,
  outcome law, graph, coefficient vector or positive epsilon is selected.
  `Scaling` includes nested induced graphs, vector dependency, and exactly
  Assumption 2's four fixed positive real constants, weighted almost-sure
  bound, degree bound, coefficient bound, and nondegenerate scaled-variance limit.
  Each size has its own joint law; no projective law condition is imposed.
* `Model` records observed coordinates, with deterministic graphs, degrees
  and coefficients. `Valid` records recruitment inclusion and valid degree
  bounds. `Homoskedastic` is equality of weighted-coordinate variances on
  the observed indices (P011-T24); unobserved vertices are suppressed.
  The sign witness observes every vertex, so it also satisfies the literal
  printed all-vertex version of Assumption 3.
* Expectation, variance and probability use the model's single joint law;
  `beta` is its expectation of `betaHat` and may depend on size.
  No equal-coordinate-means condition is imposed. Double sums are ordered.
* The print leaves its single-index correlations undefined. Following T21,
  `V2star` uses pairwise weighted
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

/-- The fair-sign counterexample refutes the universally closed printed
P011-T20 convergence claim. -/
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


end FidP011Contracts

end

end AronowAudit.P011.Wave1
