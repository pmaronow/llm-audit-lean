import AronowAudit.P044.P044_NetworkSpillovers

/-!
# P044-T12: a counterexample to exposure-contrast unbiasedness

P044 p. 212 (PDF p. 4) and p. 216 (PDF p. 8) state unbiasedness of HT estimates of
whole-population exposure contrasts. `PrintedUnbiasedness` requires each contrasted
label to be possible for some unit, rather than for every unit.

The counterexample is the nonisolated four-unit star `starAdj` (center 0), with design
uniform on the six treat-two profiles (`starMass`, the pushforward of the uniform law on
`Fin 6` through `starAssignments`), all outcomes 1 (`yStar`), a = d11, and b = d00.
The center never has exposure d00, so its d00 HT term is identically 0:
`E(τ̂) = 1 - 3/4 = 1/4` while `τ = 0`. The rational identity is `star_counterexample`.
-/

namespace AronowAudit.P044.Wave1.Unbiasedness

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

/-- The negation of the printed unbiasedness proposition. -/
def Target : Prop := ¬ PrintedUnbiasedness

/-- The design: pushforward of the uniform law on the six enumerated star profiles. -/
def starMass (z : Assignment 4) : ℝ :=
  ∑ r : Fin 6, if starAssignments r = z then (1 / 6 : ℝ) else 0

/-- Real outcome schedule: canonical embedding of `starA` (all ones). -/
def yStar : Fin 4 → Exposure → ℝ := fun i d => ((starA i d : ℚ) : ℝ)

/-- `starMass` is a probability law on all of `Assignment 4`, and expectations
under it are averages over the six profiles; injectivity is not needed. -/
def N1 : Prop :=
  (∀ z, 0 ≤ starMass z) ∧ (∑ z, starMass z = 1) ∧
    ∀ F : Assignment 4 → ℝ, ∑ z, starMass z * F z = (∑ r, F (starAssignments r)) / 6

/-- Given N1, both labels are possible somewhere: the center has d11 with probability
1/2 and a leaf has d00 with probability 1/6. The real expected HT contrast with the true
marginals is `1/4`, and the population effect is `0`. Transfer `star_counterexample`
(flag `true`) with N1 applied to indicators and to the HT statistic, using
`ratCast_marginal`, `ratCast_htContrast`, `ratCast_expect`, and `ratCast_tau`. -/
def N2 : Prop :=
  N1 →
    (∃ i, 0 < marginal starMass (fun z => exposure starAdj z) i .d11) ∧
    (∃ i, 0 < marginal starMass (fun z => exposure starAdj z) i .d00) ∧
    expect starMass (htContrast (fun z => exposure starAdj z) yStar
      (marginal starMass (fun z => exposure starAdj z)) .d11 .d00) = 1 / 4 ∧
    tau yStar .d11 .d00 = 0

/-- The printed proposition at the star would give `1/4 = 0`. -/
theorem assemble (h1 : N1) (h2 : N2) : Target := by
  intro h
  obtain ⟨ha, hb, hE, hτ⟩ := h2 h1
  let P : FiniteDesign (Assignment 4) := ⟨starMass, h1.1, h1.2.1⟩
  have heq := h 4 (by norm_num) P starAdj (fun i => by simp [starAdj]) yStar .d11 .d00
    (by decide) ha hb
  change expect starMass (htContrast (fun z => exposure starAdj z) yStar
    (marginal starMass (fun z => exposure starAdj z)) .d11 .d00) = tau yStar .d11 .d00 at heq
  rw [hE, hτ] at heq
  norm_num at heq

end

end AronowAudit.P044.Wave1.Unbiasedness
