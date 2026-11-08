import AronowAudit.P044.Wave1.Gap.FidP044

namespace AronowAudit.P044.Wave1.Fid2P044Contracts

/-- P044-T13's baseline-law component at one supplied graph: every vertex's
baseline has the absolute-standard-normal law. The description is on printed
p. 216 (PDF p. 8), `runs/P044/staged/main.txt:347–353`, and the calls using
`adj_matrix_sw` and `adj_matrix_dcbm` are at `:356–367`. The paper fixes those
two networks, each with `N = 1000`, at `:229–261`, with construction at
`:270–305`. The graph parameters here are fixed outside this proposition's
vertex quantifier; this definition does not assert a law for all graphs.

Conventions are the fixed-graph ideal Gaussian generator model of the approved
certificate `baseline_description_refuted_for_every_graph`. Boolean adjacency
entries encode 0/1, the diagonal is zero, and `Fin N` relabels the units. If
`k` is row degree and `q` counts distinct other endpoints reachable by two-edge
walks (possibly also first neighbors), `degreeScale` is `k + q + k*q`.
Conditional on this fixed graph, `baselineLaw` is the law of
`(k + q + k*q)*|G| + E`, where `G ~ N(0,1)` and `E ~ N(1,1/16)` are
independent and the second Gaussian parameter is variance. `halfNormalLaw`
is the law of `|G|`; equality is equality of full real Borel measures.
No cross-unit independence, symmetry, no-isolates, or degree condition is
added. Identification with the staged generator under ideal Gaussian draws
is external applicability evidence, not a historical-build or seeded-value
claim. This definition isolates the permitted baseline-law component from
the multiplier identities and unspecified degree-correlation prose.

For `N = 0`, the vertex quantifier is empty, so this proposition is true.
Consequently its negation cannot hold at every natural-number graph size. -/
def printedContractAt
    (N : ℕ) (A : AronowAudit.P044.Adjacency N)
    (_hdiag : ∀ i, A i i = false) : Prop :=
  ∀ i : Fin N,
    AronowAudit.P044.baselineLaw (AronowAudit.P044.degreeScale A i : ℝ) =
      AronowAudit.P044.halfNormalLaw

/-- The exact fixed-graph contract holds vacuously at every empty graph. -/
theorem printedContractAt_zero
    (A : AronowAudit.P044.Adjacency 0) (hdiag : ∀ i, A i i = false) :
    printedContractAt 0 A hdiag := by
  intro i
  exact Fin.elim0 i

end AronowAudit.P044.Wave1.Fid2P044Contracts

namespace AronowAudit.P044.Wave1

/-- The graph-fixed negation for every nonempty supplied graph, directly from
the approved pointwise certificate. The explicit extra hypothesis `0 < N`
is necessary: `printedContractAt_zero` refutes the version without it. -/
theorem baseline_description_refuted_at_every_graph_of_pos :
    ∀ (N : ℕ) (A : AronowAudit.P044.Adjacency N)
      (hdiag : ∀ i, A i i = false),
      0 < N → ¬ Fid2P044Contracts.printedContractAt N A hdiag := by
  intro N A hdiag hN h
  exact baseline_description_refuted_for_every_graph N A hdiag ⟨0, hN⟩
    (h ⟨0, hN⟩)

#print axioms baseline_description_refuted_for_every_graph
#print axioms baseline_description_refuted_at_every_graph_of_pos

end AronowAudit.P044.Wave1

namespace AronowAudit.P044.Wave1.Fid2P044Contracts

/-- The endpoint requested in the brief, preserved exactly. It is false
because its graph-size quantifier includes the empty graph. -/
abbrev Target : Prop :=
  ∀ (N : ℕ) (A : AronowAudit.P044.Adjacency N)
    (hdiag : ∀ i, A i i = false), ¬ printedContractAt N A hdiag

example : Target ↔
    ∀ (N : ℕ) (A : AronowAudit.P044.Adjacency N)
      (hdiag : ∀ i, A i i = false), ¬ printedContractAt N A hdiag := Iff.rfl

/-- A formal counterexample to the requested universal endpoint. Thus no
positive `example : Target` or theorem of that type is supplied. -/
theorem target_is_false : ¬ Target := by
  intro h
  let A : AronowAudit.P044.Adjacency 0 := fun _ _ => false
  have hdiag : ∀ i, A i i = false := by
    intro i
    rfl
  exact h 0 A hdiag (printedContractAt_zero A hdiag)

example : ¬ Target := target_is_false

/-- The separately stated result applies to either supplied chapter matrix,
without choosing a different graph as a witness. -/
example (A : AronowAudit.P044.Adjacency 1000)
    (hdiag : ∀ i, A i i = false) : ¬ printedContractAt 1000 A hdiag :=
  AronowAudit.P044.Wave1.baseline_description_refuted_at_every_graph_of_pos
    1000 A hdiag (by decide)

#print axioms printedContractAt_zero
#print axioms target_is_false

end AronowAudit.P044.Wave1.Fid2P044Contracts
