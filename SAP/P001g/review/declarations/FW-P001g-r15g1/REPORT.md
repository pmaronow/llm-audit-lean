# Review of T115–T119

All five declarations are faithful to their recorded scopes.

| Declaration | Recorded decision | Verdict | Severity |
|---|---|---|---|
| SAP.P001g.T115 | whole | faithful | none |
| SAP.P001g.T116 | whole | faithful | none |
| SAP.P001g.T117 | whole | faithful | none |
| SAP.P001g.T118 | refuted | faithful | none |
| SAP.P001g.T119 | restricted | faithful | none |

T115 includes population identification, every decomposition link, and both
empirical arm means and their plug-in difference. T116 includes discrete
identification, conditional identification and all three propensity-score
conclusions, with an independent moment-free score domain. T117 includes
both IPW and double robustness with the correct alternatives; requiring
integrability of the complete augmented score matches the usual conditions.

T118 contradicts both actual printed assertions. A constant differentiable
functional defeats the required positive-variance limit. Tiny probability
moved to a remote point defeats mean-functional Hadamard differentiability
at a finite-variance law. Both witnesses satisfy measurability and moment
conditions; no totalized junk value supplies the contradiction.

T119 accurately discloses failure of the integrated squared-risk
interpretation. Its recorded `restricted` decision and docstring expressly
preserve the distinction from the undefined regional-consistency assertion.
The literal `ContDiff ℝ ⊤` premise is analyticity in this Mathlib version;
the zero CEF satisfies it. A measurable Gaussian/uniform counterexample
meets all conditions. Eventual full rank also prevents arbitrary
nonmeasurable fit selections from creating an artificial asymptotic failure.

The blind reading was saved before claims were read, and `claim-stage.json`
was saved before the record was read. No step-2 comparison was revised:
T119 remains `different` as a bare comparison to the canonical assertion,
and is faithful as the explicitly disclosed restricted item.

`scratch/Inspect.lean`, `scratch/Nonvacuity.lean`,
`scratch/RefutationChecks.lean`, and `scratch/SieveDomain.lean` all compiled
with `sap-lean`. Nonvacuity checks use definitions without invoking the
Challenge theorems. The full mathematical witness checks are in
`claim-analysis.md`; they were not all re-proved in Lean. The five output
fingerprints were copied from `closure.json` and the JSON files were parsed
and checked for exactly one entry per target. Unit sources were unchanged.
