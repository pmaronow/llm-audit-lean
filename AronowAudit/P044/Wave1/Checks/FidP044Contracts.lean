import AronowAudit.P044.Wave1.Gap.FidP044

namespace AronowAudit.P044.Wave1.FidP044Contracts

/-- P044-T13, independently copied from `map-fid-P044/map.json`, record 0,
`proposed_statement_lean`. Both `ref1-fid-P044/referee.json` and
`ref2-fid-P044/referee.json` accept it with `fixes: []`; no statement fix applies. -/
def approvedContract_P044_T13 : Prop :=
  ∀ (N : ℕ) (A : AronowAudit.P044.Adjacency N)
    (_hdiag : ∀ i, A i i = false) (i : Fin N),
    AronowAudit.P044.baselineLaw (AronowAudit.P044.degreeScale A i : ℝ) ≠
      AronowAudit.P044.halfNormalLaw

example : approvedContract_P044_T13 :=
  @AronowAudit.P044.Wave1.baseline_description_refuted_for_every_graph

/-- P044-T13: full universal closure of the baseline-law component on printed
p. 216 (PDF p. 8), `runs/P044/staged/main.txt:347–353`, with the calls on
pp. 216–217 (`:356–367`); see `runs/P044/lean/targets.json`, P044-T13, and
`map-fid-P044/map.json`, record 0, accepted by both referees.

Conventions: the free fixed-graph inputs of the marginal-law assertion are
universally closed below. Boolean entries encode 0/1 and zero diagonal is the
p. 210 graph convention; `Fin N` relabels the paper's units. The empty `N = 0`
fiber has no unit. No symmetry, no-isolates, or degree restriction is imposed.
For each supplied graph, `baselineLaw` is the law of `(k + q + k*q)*|G| + E`,
where `k` counts row neighbors and `q` counts distinct other vertices reachable
by two-edge walks (possibly also first neighbors). Conditional on the graph,
`G ~ N(0,1)` and `E ~ N(1,1/16)` are independent; the second parameter is
variance. `halfNormalLaw` is the law of `|G|`. Equality means equality of the
full real Borel measures; cross-unit independence is unnecessary.

This is the closed graphwise law component, not an attribution of an all-graphs
theorem to the chapter's two `N = 1000` examples. The uniform approved check
above retains coverage at every graph and unit, including both chapter inputs.
The target and referees permit refuting this necessary component separately
from the correct multipliers and the unspecified degree-correlation prose.
Identifying the printed calls with the staged generator under ideal normal-draw
semantics is external applicability evidence; no historical build or seeded
realization is asserted. -/
def printedContract_P044_T13 : Prop :=
  ∀ (N : ℕ) (A : AronowAudit.P044.Adjacency N)
    (_hdiag : ∀ i, A i i = false) (i : Fin N),
    AronowAudit.P044.baselineLaw (AronowAudit.P044.degreeScale A i : ℝ) =
      AronowAudit.P044.halfNormalLaw

end AronowAudit.P044.Wave1.FidP044Contracts

namespace AronowAudit.P044.Wave1

/-- P044-T13: the graphwise certificate refutes the entire universally closed
printed baseline-law component. The complete graph used to discharge this
closed negation is not identified with either realized chapter network. -/
theorem baseline_description_refuted_for_every_graph_printed_negation :
    ¬ FidP044Contracts.printedContract_P044_T13 := by
  intro h
  let A : AronowAudit.P044.Adjacency 1000 := fun i j => decide (i ≠ j)
  have hdiag : ∀ i, A i i = false := by
    intro i
    simp [A]
  exact baseline_description_refuted_for_every_graph 1000 A hdiag 0
    (h 1000 A hdiag 0)

#print axioms baseline_description_refuted_for_every_graph_printed_negation
#print axioms baseline_description_refuted_for_every_graph

end AronowAudit.P044.Wave1

namespace AronowAudit.P044.Wave1.FidP044Contracts

/-- P044-T13's exact negation endpoint, distinct from the uniform certificate. -/
abbrev Target_P044_T13 : Prop := ¬ printedContract_P044_T13

example : Target_P044_T13 :=
  AronowAudit.P044.Wave1.baseline_description_refuted_for_every_graph_printed_negation

example : Target_P044_T13 ↔ ¬ printedContract_P044_T13 := Iff.rfl

end AronowAudit.P044.Wave1.FidP044Contracts
