# P012a package

The current package has **11 whole, 1 restricted, 0 refuted, 0 omitted** targets, with 12 proved Solution theorems and no open glue tasks. Only P012-T1 through P012-T12 are included. Canonical counterexample targets remain whole statements of the recorded refutations, rather than refuted positive claims.

## Restrictions

**P012-T5** retains the exact symbolic attained lower limit, its quotient formula, the lower bound on every defined compatible value, and both uniform bounds under the published totals. It omits the assertion about which recruitment-edge count triples the published paper reports and their recoverability from the paper. This is the only remaining restricted target. No target is omitted.

The supplied whole-statement modules already present at the start of this round cover T1, T2, T3, T6, T7, T9, T10 and T11. Their theorem statements and proofs are preserved. T4, T5, T8 and T12 keep their existing statements and proofs as well. This round adds no proofs or mathematical hypotheses.

## Definitions and bridges

The shared-definition route uses `Defs/Part1.lean` through `Defs/Part4.lean` and the supplied `Defs/WholeW1.lean` and `Defs/WholeW2.lean`. Their external imports are Mathlib. Both Challenge and Solution use these same compiled definitions. The model represents finite graphs, sampled data, binary traits and distinct recruitment order; it uses guarded Option values for the two functionals.

`Bridge/Part1.lean` repacks the SAP data and graph structures into the project's structures and back. The inverse maps and primitive-function correspondences are definitional equalities. Universal and existential graph quantifiers are transported with the inverse maps; graph operations agree by reflexivity.

`Bridge/Part2.lean` transports compatible-value-set witnesses and rewrites the full-region predicates. Concrete data and graph witnesses agree by reflexivity. `Bridge/Part3.lean` maps replacement, graph-proposal and trait-proposal constructors in both directions, splitting the repair flag where necessary. This is structural transport of execution relations, without an output compatibility test. `Bridge/Part4.lean` and `Bridge/Part5.lean` transport project theorems through these correspondences.

The existing Solution combines the transported facts and supplied whole-statement proofs. Its remaining glue rewrites the exported phi formula as a quotient, checks the corresponding denominators by arithmetic, extracts a value from a guarded Option equality, and evaluates explicit finite examples. The supplied `WH/W1/` and `WH/W2/` proof modules are unchanged in this round.

The narrower `uniform_integer_leaf_bound` row is used only for its universal inequality; `table_numeric_gaps` supplies the two attainment evaluations. The manifest records cross-target uses of existing declarations and the supplied whole-statement proofs. This round also removes stale entries that appeared in both `rows_used` and `rows_not_used` after the supplied whole versions were integrated.

## Declaration review round 1

Both reported findings are accepted after checking their entries in the review reports, the canonical text in `work.json`, and the corresponding Lean definitions.

- **SAP.P012a.T7 / P012-T7:** The previous sentence suggested that one graph/trait pair attains two potentially different endpoints. The formal statement instead includes `exact_p_regionClaim`, which assigns `pLower` to `leafCompletion D true` and `pUpper` to `leafCompletion D false`; the Boolean selects same-trait versus opposite-trait unsampled leaves. The canonical claim likewise specifies these two assignments. Both the Challenge docstring and `T7WholeStatement` docstring now say: “Same-trait private degree-one neighbours attain p_min, and opposite-trait private degree-one neighbours attain p_max.” The formal proposition and whole decision remain unchanged. Sources: [T7 finding](fw/round1/T7/r3g2/findings.json), [review report](fw/round1/T7/r3g2/REPORT.md), [endpoint statement](SAP/P012a/Defs/Part3.lean), [shared statement](SAP/P012a/Defs/WholeW1.lean).
- **SAP.P012a.T10 / P012-T10:** The previous phrase incorrectly described the selected sampled vertices as neighbours. `T10WholeStatement` assumes time order, no recruitment edge between the vertices and positive spare degrees; it does not assume adjacency. `R1WholeGeometry` explicitly states that the edge is absent from the first constructed graph and present in the second. Both the Challenge and shared-statement docstrings now begin: “Two time-ordered sampled vertices not joined by a recruitment edge, each with positive spare degree, give two distinct compatible augmented graphs and two distinct compatible sampled induced graphs.” The formal proposition and whole decision remain unchanged. Sources: [T10 finding](fw/round1/T10/r3g2/findings.json), [review report](fw/round1/T10/r3g2/REPORT.md), [hypotheses and geometry](SAP/P012a/Defs/WholeW1.lean).

The only Lean-source edits are these four docstrings in `Challenge/Part1.lean` and `Defs/WholeW1.lean`. Removing comments gives byte-for-byte identical Lean text before and after the edits. No shared definition body, theorem type, theorem name or proof changed. The shared module was recompiled, but its mathematical declarations were not revised. The checksums and documentation-only checks are in `scratch/P012aRound1Changes.json`.

The manifest records each finding and its resolution; both targets retain `whole` and `proved`. The Comparator configuration was revalidated and rewritten with the same module names, 12 theorem names, empty explicit definition list, permitted foundational dependencies and external-kernel commands.

## Domain and validation checks

Homophily and preferential recruitment enter their compatible-value sets only as defined Option values. T5 retains its canonical domain condition; T6 requires positive sampled degree totals in both trait groups; T7 requires a nonempty recruitment history and positive event denominators. Admissibility guards natural spare-degree subtraction. Least/greatest attainable values describe the smallest containing interval, rather than identifying the finite value set with every point of a real interval.

All 45 SAP modules compiled successfully with `sap-lean` in topological import order, with one Lean process at a time. The build includes every Defs, Bridge, supplied WH proof, Challenge and Solution module. `scratch/P012aRound1Axioms.lean` reran `#print axioms` on all twelve Solution theorems; each reported exactly `propext`, `Classical.choice` and `Quot.sound`. Final results are recorded in `scratch/P012aRound1Build.log` and `scratch/P012aRound1Axioms.log`. JSON parsing, theorem-name agreement, implicit-variable options, import separation and forbidden-token checks all passed. Existing deprecation and linter warnings remain in the unchanged supplied proofs.

The pre-round certificate in [verification/comparator-result.json](SAP/P012a/verification/comparator-result.json) records all 12 theorems accepted, including con-ron, nanoda and Lean's default kernel. Its source and manifest hashes describe the pre-round snapshot. That certificate is preserved as historical evidence; this round does not claim a newly issued external-kernel certificate for the edited documentation and metadata.

The supplied source already contained six files above the brief's 300-line limit: `Defs/WholeW1.lean`, `WH/W1/Leaves.lean`, `WH/W1/P/T7_L3.lean`, `WH/W1/P/T7_L2.lean`, `WH/W1/P/T10_L1.lean` and `WH/W1/P/T1_L3.lean`. Their module boundaries and mathematical text are preserved during this documentation correction; no claim is made that this pre-existing file-size limitation has been resolved.
