# P007 statement referee report

All 17 targets were assessed. There are 16 Challenge theorems and one justified
omission. No statement defect was found.

| Verdict | Count |
| --- | ---: |
| correct_whole | 14 |
| correct_restricted | 2 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |
| **Total** | **17** |

Severity counts: none 17; minor 0; major 0. There are no items outside
`correct_whole`, `correct_restricted`, and `omission_ok` to list as adverse
findings. No changes to the supplied Lean files or docstrings are needed.

## Restrictions and omission

- **P007-T2 — correct_restricted.** The theorem retains all exact count,
  mask-removal, corrected-average and four-variable population assertions,
  together with the comparisons of the three supplied estimates at k=4,5,6.
  It drops the corrected sentence's assertion for every k>6. Both the
  Challenge docstring and record describe that restriction accurately.
- **P007-T10 — correct_restricted.** The final coincidence assertion is
  qualified by 0<q<1. This qualification is necessary: at q=0, both bounds
  equal one for every positive n,k, including n=2. The docstring and record
  explicitly disclose the qualification and correctly say that the other
  expectation bounds and identities retain q=0.
- **P007-T13 — omission_ok.** `claims.json` marks this target `no_lean=true`
  and explicitly permits non-applicability if no statement beyond T1, T2 and
  T12 can be supplied. The named empirical array is unavailable, while its
  log-derived conditional refutation and corrections are covered by those
  targets. The record's omission is justified on the supplied evidence.

The record's `whole` decisions are correct for T1, T3–T9, T11–T12 and
T14–T17. In particular, the group theorems legitimately use one common
indicator per nonempty group, as the canonical claims expressly allow.
The pair type `Fin n × Fin 2` supplies the two-element-group counting witness
in T6. No step-2 verdict was changed after opening the record.

## Reading and verification

`reading.md` was saved before opening `claims.json`. It expands every theorem
and all SAP definitions, including quantifier order, each conjunct, row versus
cell independence, observation versus missingness probabilities, and the
distinction between expected deleted fraction and all-deletion probability.
`claim-stage.json` was saved before opening `record.json`.

The definitions are faithful to the finite indicator laws and fixed-array
subsampling experiments in the supplied claims. Finite joint laws lose no
distributional generality for finitely many binary indicators. Full row
independence is expressed through arbitrary row events; identical row laws and
within-row independence are not silently assumed. The explicitly repaired
coefficient at a null prefix is confined to the repaired product formula.
The null-prefix counterexamples instead use zero prefix probabilities and the
relation 0=v*0, so they expose the printed gap without relying on division by
zero. Positive dimensions and threshold domains protect the relevant averages,
roots, logarithms and rounding operations. The asymptotic n=0 extension and
the exceptional logarithmic terms at n=0,1 do not affect the limits.

The following checks were completed using only the supplied definitions and
permitted Mathlib sources:

- `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` compiled successfully.
  It constructs normalized point laws, proves their row independence, proves
  the all-missing observation assumptions for arbitrary admissible q, proves
  normalization of the product weights for arbitrary dimensions, and supplies
  the full asymptotic-hypothesis instance k(n)=n²+1. Its printed axiom checks
  contain only `propext`, `Classical.choice`, and `Quot.sound`.
- `python3 scratch/numerical_checks.py` passed. Its exact output is saved in
  `scratch/checks.json`. It checks all 1206 supporting-line inequalities,
  every main certificate fraction, the log tolerance and integer uniqueness,
  count/average and percentage-point arithmetic, and the three simulation
  comparisons. Integer interval arithmetic at scale 10^80 certifies both
  large-power 50% crossings and both advertised rounding intervals.
- The same script exactly enumerates the small specified laws, checking
  nonnegative normalized weights, independence by row-atom factorization,
  prefix probabilities, observation bounds, expected deleted fractions and
  all-deletion probabilities. The all-missing examples exercise the zero
  endpoint; positive product laws exercise nontrivial survival probabilities.
- An explicit feasible count array has 947 rows with 405 observed entries
  and 7633 rows with 406. Appending 19 wholly missing columns realizes all
  logged-count application hypotheses. This verifies satisfiability and
  does not claim to reconstruct the authors' empirical data.

These checks support statement fidelity and truth; the supplied theorem stubs
and the architect's credited proof names were not used as proof evidence.
