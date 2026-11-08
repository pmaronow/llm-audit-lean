# Declaration review

All five current declarations are faithful, with severity **none**. The five
`whole` decisions in `record.json` are correct; no restriction or correction is
needed. Both earlier wording findings are fixed.

| Declaration | Verdict | Severity |
|---|---|---|
| SAP.P012a.T6 | faithful | none |
| SAP.P012a.T7 | faithful | none |
| SAP.P012a.T8 | faithful | none |
| SAP.P012a.T9 | faithful | none |
| SAP.P012a.T10 | faithful | none |

The blind reading was saved in `reading.md` before claims, prior reviews or the
record were opened. `claim-stage.json` was saved after the canonical comparison
and before opening the prior reviews and record. No step-2 conclusion changed.
Every closure entry was read, including generated matchers, recursive helpers,
constructors, numeric instances and the default algorithm cell.

T6 includes each edge-count and homophily formula, the canonical positivity
hypotheses, sharp bounds, private-leaf attainment, the smallest containing
interval and a concrete one-pass scan. Natural spare subtraction cannot truncate
under admissibility; the scan explicitly recovers the same budgets. Its 26 final
arithmetic operations can be counted directly in `w2Finish` under the stated
unit-cost model.

T7 includes obligatory susceptible children, the extra-neighbour decomposition,
both fraction bounds, sharp global bounds and endpoint constructions, and a
chronological streaming algorithm. Least/greatest elements of the guarded value
set give the smallest containing interval; they do not assert that the finite
attainable values fill it. A chronological input exists for every admissible
datum. Positive event denominators and existing parent cells are conclusions
for every prefix, so default cells and zero division cannot drive the result.
The corrected docstrings assign the two endpoints to their respective trait
assignments; the earlier simultaneous-attainment wording is gone.

For T8, the printed reading is: **any compatible starting graph satisfying the
selected vertices' conditions and containing their shared unsampled neighbour
can undergo the displayed replacement to produce a second compatible augmented
graph and a distinct sampled induced graph.** Its conditions and witness checks
are:

- Admissible recruitment history and time order: 1→2→3, one seed, times 1,2,3.
- Selected sampled vertices 1 and 3: no recruitment edge between them and both
  have spare degree 2.
- Simple augmented compatible start, sampled degrees (3,2,3), traits (0,0,1),
  and a shared unsampled trait-0 vertex: all hold for edges {12,23,13,14,34}.
- The printed hypotheses do not require edge 13 to be absent. Its presence
  makes the output {12,23,13} incompatible, with unchanged induced edges.

For T9, the printed reading is: **any compatible pair with the selected
opposite-trait sampled vertices, positive spare degrees, and the specified
unsampled neighbours admits the displayed compatible edge swap.** Its conditions
and witness checks are:

- The same admissible data give the required positive spares and sampled traits
  0 and 1.
- Distinct unsampled vertices 4 and 5 have traits 0 and 1, and edges 14 and 35;
  the complete starting graph {12,23,14,35,15,34} is simple and compatible.
- Absence of the cross edges is not a printed hypothesis. Insertion cannot
  duplicate them, so the output loses two edges and violates sampled degrees.
  Its positive denominator 15/8 differs from the starting denominator 35/12.

These are direct counterexamples to the canonical printed proof steps. Neither
declaration refutes Result 1 or Result 2. Recording each as a whole canonical
counterexample is appropriate; the docstrings specify the failed step.

T10 states every part of the repaired Result 1 construction: one shared vertex,
the exact private leaves, arbitrary extending binary traits, the prescribed
replacement, both compatibility notions and induced edge sets, and distinction
under unsampled renaming. Its new wording correctly avoids assuming that the
selected vertices are neighbours.

`scratch/ClosureChecks.lean`, `scratch/Nonvacuity.lean` and
`scratch/Algorithms.lean` compiled successfully with `sap-lean`, with at most two
Lean processes active. The concrete checks use definitions and finite
calculations, without invoking the audited theorem stubs. They establish all
domains jointly on concrete data, both genuine failed proof-step witnesses,
and algorithm outputs (-5/7,23/35) for homophily and (0,1/3) for preferential
recruitment. The remaining geometry of the concrete T10 witness is checked
directly in `findings.json`. No source declaration was edited.
