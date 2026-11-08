import AronowAudit.P011.Wave1.PropositionOneBlueprint

/-!
# Blueprint: P011-T32, refutation of printed Corollary 1 (and its homoskedastic reading)

Wave 1, group P011-P013. The frozen record `AronowAudit.P011.printed_corollary_one` asserts,
under `Scaling`, `Valid` and an all-data maximizer `A`, that `V̂₁(A)` is `Conservative`, and
(conjoined, p. 2246) that it is conservative under homoskedasticity. `Target` is the exact
negation of that contract.

Witness (mapper P011-T32, accepted by both referees): the T31 path family with the
constant choice `A(k,y) = G_k`. Known edges exhaust the caps, so the compatible set is
`{G_k}` and `A` maximizes for every raw `y`; every marginal variance is one
(homoskedastic); and `P(n Var(β̂) - n V̂₁ > 1) → 1`. `Witness` records all of this; in
particular it refutes the homoskedastic specialization with a genuinely homoskedastic
family, not only the first conjunct.

Writers: prove `theorem nk_proof : Nk` in `AronowAudit/P011/Wave1/CorollaryOne/Nk.lean`.
The path nodes `PropositionOne.N1`–`N11` are proved under `AronowAudit/P011/Wave1/PropositionOne/`.
-/

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.CorollaryOne

open AronowAudit.P011 AronowAudit.P011.Wave1.PropositionOne MeasureTheory ProbabilityTheory
  Filter Finset
open scoped BigOperators Topology

noncomputable section

/-- The constant oracle choice `A(k,y) = G_k`. -/
def oracleChoice : ∀ k, (Fin (PF.size k) → ℝ) → Graph (PF.size k) := fun k _ => (PF.model k).G

/-- The variance estimator `V̂₁(A(k,y))` of the witness. -/
def oracleV1 : ∀ k, (Fin (PF.size k) → ℝ) → ℝ :=
  fun k y => V1 (oracleChoice k y) (weighted (PF.model k) y)

/-! ## Frozen target -/

/-- **Target (P011-T32).** Exact negation of `printed_corollary_one` (Corollary 1, p. 2245;
proof (A.1), p. 2249; homoskedastic sentence, p. 2246). -/
def Target : Prop :=
  ¬ ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 → Valid F →
      ∀ (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)),
        (∀ k y, Maximizes (F.model k).R (F.model k).d
          (fun B => V1 B (weighted (F.model k) y)) (A k y)) →
        Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y)) ∧
          ((∀ k, Homoskedastic (F.model k)) →
            Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y)))

/-- The mapper's explicit witness statement (`printed_corollary_one_refuted` in the map). -/
def Witness : Prop :=
  Scaling PF 6 2 (29 / 15) 2 ∧ Valid PF ∧ (∀ k, Homoskedastic (PF.model k)) ∧
    (∀ k y, Maximizes (PF.model k).R (PF.model k).d
      (fun B => V1 B (weighted (PF.model k) y)) (oracleChoice k y)) ∧
    ¬ (Conservative PF oracleV1 ∧ ((∀ k, Homoskedastic (PF.model k)) → Conservative PF oracleV1))

/-! ## Nodes (plus the shared `PropositionOne.N1`–`N10`) -/

/-- **Node N1** (paper proof T31/T32, "Any compatible graph contains those edges; each cap is
already exhausted ... Thus the compatible set is the singleton {G}"): use
`saturated_graph_singleton` and `StarCompletion.block_degree` (the caps `d` are the actual
block degrees). -/
def N1 : Prop :=
  ∀ (k : ℕ) (B : Graph (PF.size k)), Compatible (PF.model k).R (PF.model k).d B ↔ B = (PF.model k).G

/-- **Node N2** (paper proof T31, "All three marginal variances equal 1, since
(3/5)^2+(4/5)^2=1 ... Thus Homoskedastic holds"): every unit has covariance-diagonal `1`.
Compare `PathFiniteCompletion.path_covariance` (one block, `t = 0`). -/
def N2 : Prop := ∀ k : ℕ, Homoskedastic (PF.model k)

/-- **Node N3** (paper proof T32, "on the event |T+11/15|<=1 one has 29/15-T>=8/3-1=5/3>1 ...
Conservative would require the same sequence to tend to zero at epsilon=1"): generic
one-sided failure. If `n(Var β̂ - V) = c - T` pointwise and `T → a` in probability with
`c - a > 2`, then `V` is not `Conservative`. -/
def N3 : Prop :=
  ∀ (F : Family) (T V : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (c a : ℝ),
    (∀ k y, (F.size k : ℝ) * (var (F.model k) (betaHat (F.model k)) - V k y) = c - T k y) →
    InProbability F T (fun _ => a) → 2 < c - a → ¬ Conservative F V

/-! ## Glue (proved here; reused by T33 and T35) -/

/-- `Valid` for the witness, from N1. -/
theorem valid_of (h1 : N1) : Valid PF := fun k => (h1 k _).mpr rfl

/-- The constant oracle choice maximizes `V̂₁` over the compatible set for every raw `y`. -/
theorem maximizes_of (h1 : N1) :
    ∀ k y, Maximizes (PF.model k).R (PF.model k).d
      (fun B => V1 B (weighted (PF.model k) y)) (oracleChoice k y) := by
  intro k y
  refine ⟨(h1 k _).mpr rfl, fun B hB => ?_⟩
  have hBG := (h1 k B).mp hB
  subst hBG
  exact le_rfl

/-- `V̂₁(G)` is not conservative for the witness (one-sided failure at `ε = 1`). -/
theorem not_conservative_of (p2 : PropositionOne.N2) (p5 : PropositionOne.N5)
    (p7 : PropositionOne.N7) (p8 : PropositionOne.N8) (p9 : PropositionOne.N9)
    (p10 : PropositionOne.N10) (h3 : N3) : ¬ Conservative PF oracleV1 := by
  refine h3 PF (scaledOracle PF) oracleV1 (29 / 15) (-11 / 15) (fun k y => ?_)
    (limit_of p2 p5 p7 p8 p9 p10) (by norm_num)
  have hT := scaledTrue_eq p2 p5 p7 k
  unfold scaledTrue at hT
  rw [mul_sub, hT]
  rfl

/-! ## Assembly (fully proved) -/

/-- **Assembly of the explicit witness.** -/
theorem assemble_witness (p1 : PropositionOne.N1) (p2 : PropositionOne.N2)
    (p3 : PropositionOne.N3) (p4 : PropositionOne.N4) (p5 : PropositionOne.N5)
    (p6 : PropositionOne.N6) (p7 : PropositionOne.N7) (p8 : PropositionOne.N8)
    (p9 : PropositionOne.N9) (p10 : PropositionOne.N10)
    (h1 : N1) (h2 : N2) (h3 : N3) : Witness :=
  ⟨scaling_of p1 p2 p3 p4 p5 p6 p7, valid_of h1, h2, maximizes_of h1,
    fun hc => not_conservative_of p2 p5 p7 p8 p9 p10 h3 hc.1⟩

/-- **Assembly.** The nodes suffice for the refutation. (`PropositionOne.N11` is not needed
here.) -/
theorem assemble (p1 : PropositionOne.N1) (p2 : PropositionOne.N2)
    (p3 : PropositionOne.N3) (p4 : PropositionOne.N4) (p5 : PropositionOne.N5)
    (p6 : PropositionOne.N6) (p7 : PropositionOne.N7) (p8 : PropositionOne.N8)
    (p9 : PropositionOne.N9) (p10 : PropositionOne.N10)
    (h1 : N1) (h2 : N2) (h3 : N3) : Target := by
  intro hall
  obtain ⟨hS, hV, -, hM, hnot⟩ := assemble_witness p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 h1 h2 h3
  exact hnot (hall PF 6 2 (29 / 15) 2 hS hV oracleChoice hM)

/-- Fidelity check: `Target` is literally the negation of the frozen statement
`AronowAudit.P011.printed_corollary_one` (only its type is read; its unproved draft proof is never used). -/
example : Target = ¬ type_of% @AronowAudit.P011.printed_corollary_one := rfl

end

end AronowAudit.P011.Wave1.CorollaryOne
