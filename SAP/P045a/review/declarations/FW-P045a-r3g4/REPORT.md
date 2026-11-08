`SAP.P045a.T16`: **faithful**, severity **none**, as an accurately disclosed
restriction of canonical claim P045-T16.

The blind reading and full dependency inspection were saved in `reading.md`
before opening `claims.json`. The comparison was then saved in `claim-stage.json`
before opening `record.json`. The record's `restricted` decision agrees with that
independent comparison; no step-2 conclusion changed.

The matrix, uniform design on 45 distinct treatment pairs, outcome table,
exposure probabilities, and HT definitions match the canonical claim and its
standing assumptions. The [paper's exposure and HT definitions](https://arxiv.org/pdf/2001.05444)
in sections 4.1–4.2 agree with this interpretation. Lean's zero-based vertices
(5,8) are the paper's treated units 6 and 9. The estimator retains the original
design's inclusion probabilities when its averaging support is restricted.

`SAP/P045a/Defs/Part6.lean:60–78` contains all four probability formulas and
positivity, the printed assignment's exposure-cell and HT calculations, support
sizes 20 and 19, and all five means. Both the docstring at
`SAP/P045a/Challenge/Part1.lean:174–182` and the record accurately disclose the
omitted separate population totals and true-effect equality, the adjacency
equivalence, and identification of the exceptional adjacent pair. These
omissions are permitted by the task's correctness rule. The theorem supports the
canonical witness assertion; it is not labelled as refuting that assertion.

`scratch/BlindPrint.lean` compiled successfully and exposes all generated closure
auxiliaries. `scratch/BlindChecks.lean` compiled from Defs alone, checking a
normalized, nonempty design, its concrete assignment, graph properties, realized
cells, and restricted-support sizes. Independent exact rational enumeration in
`scratch/enumerate_t16.py` verified every numerical conjunct, including the means
20, 45, 1, 651/200, and 1227/380. There are no hypotheses to make inconsistent;
all relevant inclusion probabilities and averaging denominators are positive.
The empty exposure cell supplies an ordinary empty sum. No junk-value convention
affects the asserted quantities. No issue or correction was found.
