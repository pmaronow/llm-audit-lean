import AronowAudit.P044.Wave1.Checks.Fid2P044Contracts

/-!
Compile-time binding for the credited P044-T13 endpoint (fidelity correction, 23 October 2026).

The printed baseline-law description concerns the chapter's two supplied networks (a small-world network and a DCBM, N = 1000).
Its negation is credited at every nonempty supplied graph, with the graph fixed outside the negation. The empty graph is excluded
because the description holds vacuously there (`Fid2P044Contracts.printedContractAt_zero`).
-/

namespace AronowAudit.P044.Wave1.Fid3P044Contracts

open AronowAudit.P044.Wave1.Fid2P044Contracts

/-- The negation of the printed baseline-law description at every nonempty supplied graph. -/
abbrev TargetPos : Prop :=
  ∀ (N : ℕ) (A : AronowAudit.P044.Adjacency N) (hdiag : ∀ i, A i i = false),
    0 < N → ¬ printedContractAt N A hdiag

example : TargetPos := AronowAudit.P044.Wave1.baseline_description_refuted_at_every_graph_of_pos

example : TargetPos ↔
    ∀ (N : ℕ) (A : AronowAudit.P044.Adjacency N) (hdiag : ∀ i, A i i = false),
      0 < N → ¬ printedContractAt N A hdiag := Iff.rfl

end AronowAudit.P044.Wave1.Fid3P044Contracts
