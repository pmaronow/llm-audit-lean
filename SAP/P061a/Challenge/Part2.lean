import SAP.P061a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Asymptotics
open scoped Topology

/-- P061-T10; Supplementary Appendix p. 6, the central-limit and limitations paragraphs.
The three corrected population-indexed rate conditions have their standard little-o and big-O
characterizations for nonnegative maximum- and average-degree sequences.
Restriction: This transcribes the rate conditions on nonnegative real sequences; it identifies no
dependency graph and asserts no sequence satisfies the conditions, no CLT, and no Chebyshev
sharpness or literature attribution. Uniform quotient bounds quantify only positive population
sizes; the initial index zero is immaterial to the asymptotic assertions. -/
theorem SAP.P061a.T10 (dmax davg : ℕ → ℝ)
    (hmax : ∀ N, 0 ≤ dmax N) (havg : ∀ N, 0 ≤ davg N) :
    (IsLittleO atTop dmax (fun N => Real.rpow (N : ℝ) (1/4 : ℝ)) ↔
      Tendsto (fun N => dmax N / Real.rpow (N : ℝ) (1/4 : ℝ)) atTop (𝓝 0)) ∧
    (IsBigO atTop davg (fun _ => (1 : ℝ)) ↔ ∃ C : ℝ, ∀ N, davg N ≤ C) ∧
    (IsBigO atTop dmax (fun N => Real.rpow (N : ℝ) (1/2 : ℝ)) ↔
      ∃ C : ℝ, ∀ N : ℕ, 0 < N → dmax N / Real.rpow (N : ℝ) (1/2 : ℝ) ≤ C) := by sorry
