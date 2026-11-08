# Statement audit

All 17 targets have a theorem and an entry in `findings.json`.

| Verdict | Count |
| --- | ---: |
| correct_whole | 6 |
| correct_restricted | 11 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity counts: **none 17, minor 0, major 0**.

There are no items outside `correct_whole`, `correct_restricted`, and
`omission_ok` requiring an adverse finding.

The six whole entries comprise T24, T31, T33, T34 and the two valid refutations
T26 and T27. T26 certifies a legal deterministic missingness example with
defined endpoints and coverage `297/380 < 1-109/500`. T27 refutes the printed
binary-search assertion on the lawful input `k1=1,k2=2,r=2,f=false`.
These two entries uphold the record's `refuted` decisions.

All eleven `restricted` decisions are accurate. Their restrictions appear in
the corresponding theorem docstrings and agree with `record.json`. The
disclosures account for the omitted canonical content, the corrected search
and full-j-loop procedures, and the stipulated arithmetic cost models. No
omission decisions were present. No step-2 verdict was changed after reading
the record: its two `different` entries identify the explicit refutations of
the positive printed assertions and are adjudicated accordingly here.

## Evidence

`reading.md` was saved before opening `claims.json` or `record.json`; its
SHA-256 is
`d3e95f254976ae47480d308ff497179caa28e705aa9ead19b22e9feeb7011f82`.
`claim-stage.json` was saved and parsed before opening `record.json`.
The audit used the supplied statements and canonical transcriptions, together
with the permitted Mathlib sources. No Solution or Comparator source was read.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with exit code 0.
It imports only `SAP.P003b.Defs` and checks admissible parameter values,
accepted-set nonemptiness, nonempty finite random spaces, the numerical lattice
example, the literal search failure, and exact Wald arithmetic. Natural
subtractions are exact on the domains where the statements use them as
ordinary differences. Positive arms and sample sizes prevent probability
denominators from vanishing. Nonempty finite accepted sets justify all uses
of their extrema; T26 explicitly establishes this for every completion in
its counterexample. The finite pool budgets prevent modulo batch reuse in
the probabilistic assertions, and the factorial seed construction implements
the stated reuse probabilities exactly.

`python3 scratch/audit.py` completed with exit code 0 and saved
`scratch/audit-results.json`. Its independent calculations include:

* 155 observed tables with every positive allocation for `2 <= n <= 6`,
  checking count-law normalization and candidate lattices, and 2,539 checks
  that every possible vector is reached from the minimum of its reuse line.
* 162 balanced observed-table/level cases for `2 <= n <= 8`, and ten cases
  at `n=16` comparing the corrected searches with exhaustive exact endpoints.
* All ten states of the T26 missingness counterexample, including both
  nonempty extremal accepted sets and the exact coverage fraction.
* T6's exact intervals, A/B/D paths, both exact probability inequalities,
  and precisely the rational Chebyshev product in its aggregate bound.
* Three exact one-step reuse transition kernels, both Wald coverage
  fractions, and explicit positive-probability draws for the `n=16` shuffle
  lower-bound witness.

The instance checks support the mathematical review; they are not a claim of
exhaustive verification of the universal statements. Both requested JSON
artifacts parse with Python, contain exactly one entry per canonical target,
and satisfy the requested field and verdict constraints.
