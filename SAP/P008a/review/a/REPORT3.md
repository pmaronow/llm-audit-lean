# Round 3 statement review

All 14 targets were checked against their canonical `statement`,
`definitions_needed` and standing assumptions, with the revised decisions in
`record3.json`. Audit notes and `finite_lemmas` were not used to remove clauses.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 5 |
| `correct_restricted` | 8 |
| `restriction_inaccurate` | 1 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 0 |
| `omission_questionable` | 0 |

Severity: **13 none, 1 minor, 0 major**. All four earlier adverse findings are
**fixed**; none is partly fixed or unfixed. One further disclosure issue remains
in T8. No mathematical proposition was found false or vacuous.

## Earlier findings

| Earlier finding | Status | Evidence in revision 3 |
| --- | --- | --- |
| Round 1, T6: separation incorrectly restricted the matrix representation | Fixed, remains fixed | In Defs/Part6.lean, the representation precedes the nested zero-diagonal and separation hypotheses. The current docstring describes that scope accurately. |
| Round 2, T5: unqualified printed-falsity opening | Fixed | The decision is `whole`; the docstring explicitly identifies the outcome-effect-range sufficiency reading and distinguishes it from the printed contribution-dependence instruction. |
| Round 2, T7: spatial refutation claimed without a spatial realization | Fixed | The decision is `restricted`. The opening calls these the counting components, and the paragraph explicitly omits the planar realization, geometric circle identification and centre outcomes. |
| Round 2, T9: archived-code result attributed too broadly to the article | Fixed | The decision is `restricted`; both the docstring and record scope the failure to the transcribed archived-code correctness reading and do not attribute the printed intervals to that model. |

T7's spatial realization remains unproved by the retained theorem. Restoring
the limited claim, rather than claiming that missing realization, fixes the
earlier issue.

## T8 — restriction_inaccurate, minor

The canonical statement begins with corrected text asserting that the
sharp-null percentiles for the application's unscaled sum are **−0.0304 and
0.0336**, and that its **observed sum is −0.0321**. These assertions are inside
`statement`, so they cannot be removed by the target's historical note.

The retained theorem establishes generic normalization, mixture bounds,
rescaling and exact arithmetic on those constants. In particular,
[Defs/Part7.lean:78](/home/ubuntu/sap/tasks/CHFID-P008a-a/SAP/P008a/Defs/Part7.lean:78)
gives the sorted-sample scaling law, and
[the numerical conjunct](/home/ubuntu/sap/tasks/CHFID-P008a-a/SAP/P008a/Defs/Part7.lean:82)
divides the three rational constants by four and compares the results. It does
not identify an application's observed statistic or empirical distribution
with those constants.

The current [restriction paragraph](/home/ubuntu/sap/tasks/CHFID-P008a-a/SAP/P008a/Challenge/Part1.lean:92)
and `record3.json` accurately disclose the spatial, finite-extremum,
order-statistic and sampling-space limitations. They do not disclose this
additional omission of the empirical output identifications. Saying that the
three reported values are divided by four describes the arithmetic retained;
it does not state that the corrected-text assertions about what those values
are have been dropped.

The smallest repair is to keep the current paragraph and append, in both the
docstring and record:

> The numerical clauses treat −0.0304, −0.0321 and 0.0336 as supplied reported
> constants. They do not certify that −0.0304 and 0.0336 are the empirical
> sharp-null percentiles, that −0.0321 is the observed sum on the application
> grid, or that the divided values are reconstructed empirical outputs; only
> their exact division and comparison are established.

The proposition itself needs no change for this restricted claim. This is a
further issue identified under the clarified claim rule, not a claim that the
unchanged normalization or rescaling theorem became false.

## Label and scope checks

No target is now labelled `refuted`. That is appropriate: the six canonical
counterexample targets already assert the relevant examples or reading
failures. Establishing those assertions agrees with the canonical claims.

| Target | Revision 3 assessment |
| --- | --- |
| T1 | `correct_restricted`: the fixed labelled observation and both directions of the finite-law discrepancy are retained; the arbitrary-observation/relabeling limitation is disclosed. The docstring names the identification reading. |
| T2 | `correct_restricted`: finite calibration, conditioning, Bernoulli count uniformity and cumulative sharp-null imputability retain the disclosed spatial, integrability and conditional-support domain. Documentary/empirical conclusions are explicitly omitted. |
| T3 | `correct_whole`: all clauses of the prescribed spatial counterexample remain present, including the sharp null, enumeration, circle means, quantiles, rejecting assignments and 1/3 probabilities. |
| T4 | `correct_restricted`: the general bounds, calibration and IID rank statement remain; the observed reconstruction and exact observed p-value omissions are explicit. |
| T5 | `correct_whole`: the finite pair and replication construction covers the canonical outcome-range counterexample. The limiting consequence is optional in the canonical statement itself, so no historical note is needed to exclude it. |
| T6 | `correct_restricted`: the general representation is restored; geometric-domain restrictions and numerical omissions remain accurately disclosed. |
| T7 | `correct_restricted`: the counting models and arithmetic are retained with the complete spatial-realization omissions disclosed. |
| T8 | `restriction_inaccurate`: the further empirical-output omission above must be disclosed. |
| T9 | `correct_restricted`: the spatial archived-code example and sixth-row incompatibility remain, with intermediate-vector/mask omissions and attribution limits stated. |
| T10 | `correct_restricted`: physical-cutoff invariance and all-pairs identities remain; omitted residual strict positivity is disclosed. |
| T11 | `correct_restricted`: the arithmetic and rounding envelope remain, while the actual 7.99649/8.00 identification and empirical percentile outputs are now explicitly omitted. |
| T12 | `correct_whole`: the entire canonical grid/output incompatibility remains established. |
| T13 | `correct_whole`: all exact corrected-grid clauses remain present. |
| T14 | `correct_whole`: the corrected mean identity, real-product characterization and numerical witness remain present. |

My earlier `whole` assessment of T11 was too narrow: its canonical
`[Corrected]` text asserts the actual display **8.00** and gives the unrounded
reconstruction **7.99649**, beyond arithmetic clauses (a)–(c). The present
`restricted` decision is correct. This can be checked directly: decreasing
each of the five printed estimates by 1/2000 satisfies all rounding premises
and yields 7.9935, below the 7.995 boundary for rounding to 8.00. The revised
disclosure now states exactly why the retained envelope does not establish
the actual corrected display.

## Delta, junk values and nonvacuity

SHA-256 comparison with the round-two source hashes found **only
`SAP/P008a/Challenge/Part1.lean` changed**. All eight Defs parts and both import
roots are byte-identical. All 14 theorem signatures remain their corresponding
`TnStatement`. Thus no mathematical proposition or underlying definition has
changed since round two. Relative to the original `reading.md`, the only
mathematical change remains the already checked T6 separation-scope repair.

The retained nonvacuity evidence remains applicable:

* T2 and T8 admit the compiled two-distinct-node model, field R², radius one,
  Dirac mass at the midpoint, binary constant outcomes and a positive
  conditional two-arm event. Its circle masses are one and the required
  schedules are integrable.
* T6 admits both the diagonal regime and the independently compiled
  off-diagonal example z=0011, M=(0,2,4,6), D_ij=|2i−2j|, c=12/5. Both arms
  have size two, X'X has a genuine inverse, separation fails, and the sandwich
  entry and score HAC both equal 1/2.
* T3's and T9's actual circle measures have positive finite masses at their
  evaluated radii. Their fixed designs/observations have both arms present.
* T5's full Bernoulli support is used for linearization scores, without
  evaluating a Hájek ratio at an empty arm. Positive replication counts
  provide genuine finite populations.
* T7's thresholds are 400/1000 before treatment and 79/679 after treatment;
  natural subtraction does not truncate. Every labelled mean divides by
  40000, and the reported observation has positive design probability.
* Normalized mixture weights exclude an empty radius type; quantile samples
  are nonempty and rescaling divisors are positive. T12's empty selected range
  is the intended grid defect, not a vacuous premise.

No new Lean compilation was needed for this documentation-only delta. The
successful independent checks in `scratch/Check.lean`,
`scratch/DeltaCheck.lean` and `scratch/check_finite.py` apply to the identical
definitions; their round-two success records were checked. A fresh exact
rational calculation checked the T11 lower-envelope witness above.

`findings3.json` was parsed with Python, with exact target coverage, theorem
correspondence, allowed verdicts/severities, required fields and counts checked.
Source hashes and prior-check reuse are recorded in
`scratch/validation3.json`. No `lake` command or external project proof source
was used. The Solution/Comparator status is separate from this statement
review.
