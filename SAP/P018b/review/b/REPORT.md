Audited all 14 targets in `claims.json`. The blind reading was saved in
`reading.md` before opening the claims; `claim-stage.json` was saved and
parsed before opening `record.json`. No step-2 classification was changed
after reading the record.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 6 |
| `correct_restricted` | 8 |
| `restriction_inaccurate` | 0 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 0 |
| `omission_questionable` | 0 |

All 14 targets have theorem stubs; there are no omitted targets. No target
has a non-`correct_*` verdict, and no fixes are requested.

The architect's decisions are accepted: whole for T15, T16 and T23;
restricted for T17–T22, T24 and T27; and refuted for T25, T26 and T28.
The three successful refutations receive `correct_whole` because they
refute the corresponding printed universal claim. They do not endorse
the false printed statements or assert that every conjunct fails.

The phase-2 `broader` labels for T15, T16 and T23 remain unchanged:
their true extra cases include zero-dimensional vectors, zero record
counts or general finite simple graphs. All canonical conclusions and
positive-dimensional/nonempty cases are covered, which warrants the
final `correct_whole` coverage verdict.

| Target | Declared restriction checked against the actual statement |
| --- | --- |
| T17 | Retains the full-rank negative-diagonal OLS sample and finite-population certificate; omits (a), (b), (e) and the listed classifications, support/determinant values and distributional interpretation. |
| T18 | Omits the non-PSD OLS witness and restricts the rarity limit to a fixed positive target; retains the structural, domain, contraction and probability assertions. |
| T19 | Retains an existential model with the specified moment failures and limits; omits the named law/construction, population projection, detailed formulas/events, full-estimator moment consequences and directed reformulation. The abstract record model itself does not impose a common symmetric pair formula. |
| T20 | Retains only the abstract weak-limit/UI-squares moment implication with explicit L2 assumptions; omits the listed OLS identities, target-subtraction consequence and other parts. |
| T21 | Retains only the diagonal-plus-neighbor/sparse conditional sum identity under Standing and N>=2; omits all stated counts and statistical corrections. |
| T22 | Retains the independent normal inputs, error laws, covariances and conditional zero means; omits response-regression specification. |
| T24 | Retains exact table arithmetic and rounding bounds; restricts the significance clauses to the three disclosed simultaneous two-sided intervals. |
| T27 | Adds exactly eventual almost-sure sample rank, with one deterministic N0, beyond the population-rank and fitted-moment hypotheses. |

All eight restriction strings in the record occur verbatim in the Challenge
docstrings after whitespace normalization. The declared omissions and
added premises account for the narrower phase-2 readings.

Independent exact rational checks passed for the six-dyad arithmetic,
OLS negative covariance, finite-population Gram/projection matrices and
positive-probability event, every table ratio and rounding extremum, and
the N=3 cross-role covariance obstruction. The script also checked the
fair-sign fitted-moment formulas by exhaustive enumeration for N=3,...,7.
See `scratch/audit_exact.py` and `scratch/exact-results.json`.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully.
It imports only Defs and checks an inhabited dyad instance, its size and
injectivity assumptions, the fair-sign population probability/Gram,
Standing and SampleRank, and nonempty significance intervals. No
Challenge theorem is used. Only one Lean process ran at a time; no
`lake` command was run.

The general fair-sign moment identities and the continuous T26
counterexample are written out in `scratch/nonvacuity.md`, along with
witnesses for every other target. The deeper T19 existence/limit argument
was checked mathematically against the supplied construction, without
reproving that existential theorem in Lean; its confidence is accordingly
reported as medium-high. All other confidence ratings are high.

The convention checks found no reliance on an undefined statistical
quantity: the relevant covariance integrals are integrable, T19 uses
extended integrals to state divergence, inverse matrices have the
needed rank where used statistically (eventually for asymptotic
statements), rounding/significance denominators are positive, and
the population intercept/rank premises have positive-dimensional
nonvacuity witnesses. The initial N=0,1 totalized values do not affect
limits. Mathematical paper content was taken from the canonical text
and standing assumptions supplied in `claims.json`; no Solution or
Comparator sources were read.
