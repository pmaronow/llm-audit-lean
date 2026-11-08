# Declaration review

All five current declarations are **faithful, severity none**. Their statements,
dependency definitions, and docstrings agree with the canonical claims and the
recorded decisions: T27 and T29 are refutations of implementation contracts;
T30, T31, and T32 are whole claims. No step-2 conclusion changed after reading
`record.json`.

| Declaration | Assessment |
|---|---|
| T27 | Negates precisely the documented all-control equivalence for the coded closed-neighborhood indicator. A two-vertex mixed neighborhood is a valid witness. |
| T29 | Refutes the coded sampler's contract with its singleton-number behavior and actual retry traces. On the four-vertex path, the normalized terminal law assigns probability 5/6 to three-nets. |
| T30 | Contains both exact-probability HT unbiasedness conclusions, with the required positive marginals and correctly specified observed outcomes. Empty realized exposure cells contribute zero without being discarded. |
| T31 | States both household contagion decompositions and the zero pointwise contribution when a household's mediator is unchanged. All differences are inside their population means. |
| T32 | Contains the complete specified 65-of-66 clique counterexample: counts, exact and simulated moments, both sampling regimes, both strict comparisons, all fixed tables, graph relabelings, and the real-estimator shortfall. |

The refutation readings, their conditions, and the witness checks are recorded
in `refutation-checks.md`. T29's retry series converges, so its counterexample
does not rely on Mathlib's zero value for a nonsummable real `tsum`. T32's
canonical statement expressly specifies sampling without replacement; its
distinct simulation rows satisfy that setting. Its docstring correctly limits
the counterexample to the stronger finite-simulation extension.

The sole earlier issue, T29's ambiguous phrase “the documented sampler,” is
fixed at `SAP/P045b/Challenge/Part2.lean:21`: the current text says “the package's
cluster sampler as coded.” Line 23 explicitly distinguishes the intended
uniform-unmarked algorithm. This judgment is recorded in the T29 `resolved`
entry; there is no remaining issue.

`reading.md` was saved before opening the canonical claims, record, or prior
review material. Every closure member was read, including all six generated
numeral-support proofs. `claim-stage.json` preserves the comparison against the
claims. Lean scratch instances use only Defs and do not invoke the Challenge
stubs. Independent exact-fraction checks reproduce all T32 reported moments
and all 66 fixed-table/relabeling cases. `findings.json` contains exactly the
five requested entries, with fingerprints copied from `closure.json`.

Validation passed: `sap-lean` compiled `scratch/Blind.lean`,
`scratch/Instances.lean`, `scratch/Sampler.lean`, and `scratch/Clique.lean`;
the independent Python checks passed; and Python parsed both output JSON
files and checked target completeness, fingerprints, and verdict consistency.
