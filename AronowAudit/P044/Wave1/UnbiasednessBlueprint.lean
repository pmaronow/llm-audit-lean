import AronowAudit.P044.P044_NetworkSpillovers

/-!
# Wave1 blueprint: P044-T12, `AronowAudit.P044.printed_unbiasedness_claim` (refute)

Paper: P044 p. 212 (PDF p. 4) and p. 216 (PDF p. 8): HT estimates of whole-population
exposure contrasts are said to be unbiased. The registered reading `PrintedUnbiasedness`
requires each contrasted label to be possible for SOME unit, not for every unit.
Resolution: `refute`.

Witness (mapper record 9): the nonisolated four-unit star `starAdj` (center 0), design uniform
on the six treat-two profiles (`starMass`, the pushforward of the uniform law on `Fin 6`
through `starAssignments`), all outcomes 1 (`yStar`), a = d11, b = d00. The center never has
exposure d00, so its d00 HT term is identically 0: `E(τ̂) = 1 - 3/4 = 1/4` while `τ = 0`.
The rational certificate is the safe `star_counterexample` (`decide +kernel`).

Final theorem (writers): `AronowAudit.P044.Wave1.printed_unbiasedness_claim_refuted :
¬ PrintedUnbiasedness` in `AronowAudit/P044/Wave1/Unbiasedness.lean`.
-/

namespace AronowAudit.P044.Wave1.Unbiasedness

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

/-- The frozen final statement: the exact negation of the recorded printed proposition. -/
def Target : Prop := ¬ PrintedUnbiasedness

/-- The design: pushforward of the uniform law on the six enumerated star profiles. -/
def starMass (z : Assignment 4) : ℝ :=
  ∑ r : Fin 6, if starAssignments r = z then (1 / 6 : ℝ) else 0

/-- Real outcome schedule: canonical embedding of `starA` (all ones). -/
def yStar : Fin 4 → Exposure → ℝ := fun i d => ((starA i d : ℚ) : ℝ)

/-- **Node U-N1** (`star_full_assignment_design`; mapper record 9, paper-proof steps 1 and 4,
shared lemma 4). `starMass` is a probability law on all of `Assignment 4`, and expectations
under it are averages over the six profiles (`Finset.sum_comm`, `Finset.sum_ite_eq`; no
injectivity needed). -/
def N1 : Prop :=
  (∀ z, 0 ≤ starMass z) ∧ (∑ z, starMass z = 1) ∧
    ∀ F : Assignment 4 → ℝ, ∑ z, starMass z * F z = (∑ r, F (starAssignments r)) / 6

/-- **Node U-N2** (`star_real_unbiasedness_refutation`; mapper record 9, steps 2-4). Given
U-N1: both labels are possible somewhere (center has d11 with probability 1/2; a leaf has
d00 with probability 1/6), the real expected HT contrast with the true marginals is `1/4`,
and the population effect is `0`. Transfer `star_counterexample` (flag `true`) with U-N1
applied to indicators (marginals) and to the HT statistic, then `ratCast_marginal`,
`ratCast_htContrast`, `ratCast_expect`, `ratCast_tau`. -/
def N2 : Prop :=
  N1 →
    (∃ i, 0 < marginal starMass (fun z => exposure starAdj z) i .d11) ∧
    (∃ i, 0 < marginal starMass (fun z => exposure starAdj z) i .d00) ∧
    expect starMass (htContrast (fun z => exposure starAdj z) yStar
      (marginal starMass (fun z => exposure starAdj z)) .d11 .d00) = 1 / 4 ∧
    tau yStar .d11 .d00 = 0

/-- The nodes suffice (mapper record 9, step 4): the printed proposition at the star would
give `1/4 = 0`. -/
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
