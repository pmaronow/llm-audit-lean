import AronowAudit.P011.Wave1.CorollaryOneBlueprint

/-!
# P011-T33: refutation of printed Corollary 3 (printed V̂₁ Wald interval)

Printed Corollary 3 asserts `PrintedConservativeCoverage` for the interval
`β̂ ± z √V̂₁(A)` under `Scaling`, `Valid` and an all-data maximizer. The definition
`printedCoverage` counts a negative `V̂₁` (undefined real root) as uncovered;
no clipping is substituted. `Target` is the exact negation.

The witness is the T31/T32 path family with `A(k,y) = G_k`.
Since `n V̂₁ → -11/15` in probability, `P(V̂₁ ≥ 0) → 0`; the printed coverage event
is contained in `{V̂₁ ≥ 0}`, so coverage tends to `0 < 1/2` at `α = 1/2`.
No CLT or Gaussian quantile is needed.
-/

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.CorollaryThree

open AronowAudit.P011 AronowAudit.P011.Wave1.PropositionOne AronowAudit.P011.Wave1.CorollaryOne
  MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology

noncomputable section

/-! ## Target -/

/-- **Target (P011-T33).** Exact negation of printed Corollary 3 (p. 2248). -/
def Target : Prop :=
  ¬ ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 → Valid F →
      ∀ (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)),
        (∀ k y, Maximizes (F.model k).R (F.model k).d
          (fun B => V1 B (weighted (F.model k) y)) (A k y)) →
        PrintedConservativeCoverage F (fun k y => V1 (A k y) (weighted (F.model k) y))

/-- The explicit witness to failure of printed conservative coverage. -/
def Witness : Prop :=
  Scaling PF 6 2 (29 / 15) 2 ∧ Valid PF ∧
    (∀ k y, Maximizes (PF.model k).R (PF.model k).d
      (fun B => V1 B (weighted (PF.model k) y)) (oracleChoice k y)) ∧
    ¬ PrintedConservativeCoverage PF oracleV1

/-! ## Consequence of a negative probability limit -/

/-- A statistic converging in probability to a negative constant is
nonnegative with probability tending to zero. -/
def N1 : Prop :=
  ∀ (F : Family) (T : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (a : ℝ), a < 0 →
    InProbability F T (fun _ => a) →
      Tendsto (fun k => probability (F.model k) {y | 0 ≤ T k y}) atTop (𝓝 0)

/-! ## Coverage bounds -/

/-- The printed coverage probability lies between `0` and `P(V ≥ 0)` (its event contains
the definedness clause `0 ≤ V`). -/
theorem printedCoverage_bounds {n : ℕ} (m : Model n) (V : (Fin n → ℝ) → ℝ) (α : ℝ) :
    0 ≤ printedCoverage m V α ∧ printedCoverage m V α ≤ probability m {y | 0 ≤ V y} := by
  have := m.probability
  exact ⟨measureReal_nonneg, measureReal_mono (fun y hy => hy.1)⟩

/-- `V̂₁ ≥ 0` iff `n V̂₁ ≥ 0`, since `n = 3(k+1) > 0`. -/
theorem nonneg_event_eq (k : ℕ) :
    {y | 0 ≤ oracleV1 k y} = {y | 0 ≤ scaledOracle PF k y} := by
  ext y
  have hn : (0 : ℝ) < (PF.size k : ℝ) := by
    show (0 : ℝ) < ((3 * (k + 1) : ℕ) : ℝ); positivity
  show 0 ≤ oracleV1 k y ↔ 0 ≤ (PF.size k : ℝ) * oracleV1 k y
  constructor
  · intro h; exact mul_nonneg hn.le h
  · intro h; exact nonneg_of_mul_nonneg_right (by linarith) hn

/-! ## Refutation from the witness -/

/-- The stated properties imply the explicit witness to coverage failure. -/
theorem assemble_witness (p1 : PropositionOne.N1) (p2 : PropositionOne.N2)
    (p3 : PropositionOne.N3) (p4 : PropositionOne.N4) (p5 : PropositionOne.N5)
    (p6 : PropositionOne.N6) (p7 : PropositionOne.N7) (p8 : PropositionOne.N8)
    (p9 : PropositionOne.N9) (p10 : PropositionOne.N10)
    (q1 : CorollaryOne.N1) (h1 : N1) : Witness := by
  refine ⟨scaling_of p1 p2 p3 p4 p5 p6 p7, valid_of q1, maximizes_of q1, ?_⟩
  have hzero := h1 PF (scaledOracle PF) (-11 / 15) (by norm_num)
    (limit_of p2 p5 p7 p8 p9 p10)
  have hcov : Tendsto (fun k => printedCoverage (PF.model k) (oracleV1 k) (1 / 2)) atTop
      (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
      (fun k => (printedCoverage_bounds _ _ _).1) (fun k => ?_)
    have := (printedCoverage_bounds (PF.model k) (oracleV1 k) (1 / 2)).2
    rwa [nonneg_event_eq k] at this
  intro hpc
  have h := hpc (1 / 2) (by norm_num) (by norm_num)
  rw [hcov.liminf_eq] at h
  norm_num at h

/-- The stated witness properties imply the refutation of printed Corollary 3. -/
theorem assemble (p1 : PropositionOne.N1) (p2 : PropositionOne.N2)
    (p3 : PropositionOne.N3) (p4 : PropositionOne.N4) (p5 : PropositionOne.N5)
    (p6 : PropositionOne.N6) (p7 : PropositionOne.N7) (p8 : PropositionOne.N8)
    (p9 : PropositionOne.N9) (p10 : PropositionOne.N10)
    (q1 : CorollaryOne.N1) (h1 : N1) : Target := by
  intro hall
  obtain ⟨hS, hV, hM, hnot⟩ := assemble_witness p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q1 h1
  exact hnot (hall PF 6 2 (29 / 15) 2 hS hV oracleChoice hM)

end

end AronowAudit.P011.Wave1.CorollaryThree
