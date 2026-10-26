import AronowAudit.P044.Wave1.Gap.FidP044

namespace AronowAudit.P044.Wave1.Fid2P044Contracts

/-- P044-T13's baseline-law component at one supplied graph: every vertex's
baseline has the absolute-standard-normal law, as described on printed
p. 216 (PDF p. 8). The paper uses two networks, each with `N = 1000`.
The graph parameters are fixed outside this proposition's vertex quantifier; this definition does not assert a law for all graphs.

Boolean adjacency entries encode 0/1, the diagonal is zero, and `Fin N`
relabels the units. If `k` is row degree and `q` counts distinct other endpoints
reachable by two-edge walks (possibly also first neighbors), `degreeScale`
is `k + q + k*q`. Conditional on this fixed graph, `baselineLaw` is the law
of `(k + q + k*q)*|G| + E`, where `G ~ N(0,1)` and `E ~ N(1,1/16)` are
independent and the second Gaussian parameter is variance. `halfNormalLaw`
is the law of `|G|`; equality is equality of full real Borel measures.
No cross-unit independence, symmetry, no-isolates, or degree condition is added.
This definition concerns only the baseline law, excluding the multiplier
identities and unspecified degree-correlation description.

For `N = 0`, the vertex quantifier is empty, so this proposition is true.
Consequently its negation cannot hold at every natural-number graph size. -/
def printedContractAt
    (N : ℕ) (A : AronowAudit.P044.Adjacency N)
    (_hdiag : ∀ i, A i i = false) : Prop :=
  ∀ i : Fin N,
    AronowAudit.P044.baselineLaw (AronowAudit.P044.degreeScale A i : ℝ) =
      AronowAudit.P044.halfNormalLaw


end AronowAudit.P044.Wave1.Fid2P044Contracts

namespace AronowAudit.P044.Wave1

/-- The baseline-law assertion is false for every nonempty supplied graph.
The hypothesis `0 < N` is necessary: at `N = 0` the vertex quantifier is empty. -/
theorem baseline_description_refuted_at_every_graph_of_pos :
    ∀ (N : ℕ) (A : AronowAudit.P044.Adjacency N)
      (hdiag : ∀ i, A i i = false),
      0 < N → ¬ Fid2P044Contracts.printedContractAt N A hdiag := by
  intro N A hdiag hN h
  exact baseline_description_refuted_for_every_graph N A hdiag ⟨0, hN⟩
    (h ⟨0, hN⟩)

end AronowAudit.P044.Wave1

namespace AronowAudit.P044.Wave1.Fid2P044Contracts


end AronowAudit.P044.Wave1.Fid2P044Contracts
