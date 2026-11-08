# Delta statement review

**13 targets: 11 correct_whole, 1 correct_restricted, 1 omission_ok.**
There are zero restriction_inaccurate, not_faithful, vacuous, false or
omission_questionable verdicts. All thirteen severities are none. The eleven
correct_whole verdicts include T18's correctly labelled full refutation.

## Earlier findings

| Target | Earlier finding | Delta status | Current verdict |
| --- | --- | --- | --- |
| P013-T24 | The disclosure incorrectly called the inter-set containment a hypothesis. | **Fixed.** The docstring and record now explicitly omit it and list the actual premises. | correct_restricted |
| P013-T20 | The stated reason for excluding the strong-law results overlooked the canonical IID instruction. | **Fixed as an omission-justification finding.** The revised account supplies the separate binding row-usability and glue constraints; the theorem remains omitted. | omission_ok |

### T24: the corrected disclosure matches the statement

`SAP/P013b/Challenge/Part1.lean:49-55` now specifies the two inclusions
`item ⊆ S` and `survey ⊆ S`, the three cardinalities, positive weights,
and retention of every nonzero score in both retained sets. It expressly
says that `item ⊆ survey` is neither assumed nor established, and that
the corresponding containment of survey nonrespondents within item
nonrespondents is omitted. `record2.json:253` agrees.

The remaining disclosed omissions are also accurate: verification of the
reconstruction's counts and zero coding, linkage to the released orange
indicator, reproduction of the twelve rounded Table 2 estimates, and a
separate assertion that the sufficient loss condition is strictly stronger
than the necessary and sufficient one. The loss identities, unbiasedness,
identification equivalences, sufficient condition, exclusion formulas,
unequal Hajek factors, arithmetic and conditional HT scaling remain intact.

The mathematical theorem agrees with the six-conjunct reading saved in
`reading.md`. The repair uses precisely the docstring correction proposed
in round 1 and introduces no mathematical hypothesis.

### T20: omission accepted under the clarified reuse constraint

The supplied `claims.json` note still explicitly requests an infinite
sequence of independent replicates distributed as the design. I retain that
observation and the IID mathematical reading from round 1. The revised
account does not remove that sentence from the supplied claim.

The additional information in `architect-report.md:158-166` is decisive
for the omission decision: the two limit rows have **final** `wrong_credit`
status and are excluded even from an IID-restricted Challenge; constructing
a new strong-law argument is outside the authorized glue. `record2.json:159`
now distinguishes these source-use constraints from the finite identities
that remain available. Those identities, and a lemma transforming an
already assumed scalar limit, do not supply either almost-sure limit.

This is sufficient justification for omission on the visible account of
the architect's permitted source rows. It resolves the earlier suggestion
to reuse the IID rows: that suggested route is expressly unavailable under
the stated final row-usability rule. The mathematical availability of
Mathlib's strong law alone does not establish that an architect operating
under those glue restrictions may write a new proof.

The report also quotes a precedence rule treating notes as diagnostic
history. Acceptance of the omission here rests on the independently stated
reuse prohibition, without needing to delete or reinterpret the canonical
note's IID sentence. The external architect brief, work file and original
Lean signatures linked by the report lie outside the permitted workspace
and were not inspected. Accordingly this conclusion accepts their account
of the source-use restriction; it does not certify the original credit
adjudication. T20 remains unformalized in this package.

## Statement and label comparison

I reread all ten current Defs parts, both aggregators and the Challenge,
and compared their mathematical content with `reading.md`. All twelve
included statements retain the same objects, quantifier order, hypotheses
and conclusions. No mathematical statement change was identified. The
Challenge change is T24's disclosure. Comparing `record.json` with
`record2.json` shows changes only to the restriction strings for T20 and
T24; theorem names, decisions and row lists remain unchanged.

| Target | Decision | Clause and label check |
| --- | --- | --- |
| T15 | whole | All four covariance/variance clauses, with their correct directions and locally scoped cross-joint hypotheses, remain present. |
| T16 | whole | All explicitly selected finite clauses (a1), (b1), (b2) remain present, including the residual identity and prescribed zero-count ratio. |
| T17 | whole | Total and contrast expectations use the randomization outcomes and the exposure-appropriate weights. |
| T18 | refuted | The theorem negates the entire printed coverage assertion with nestedness, positivity and Conditions 3, printed 5 and 6 intact. |
| T19 | whole | The full convergence-in-probability statement retains the uniform bounds and the vanishing normalized pair-dependence count. |
| T20 | omitted | Accepted under the clarified final source-row and glue restrictions described above. |
| T21 | whole | Every specified three-unit baseline, shift, translation-error, moment, residual and repair clause remains present. |
| T22 | whole | All six canonical parts remain covered, including exact change and iff formulas, joint and fixed translations, expectations, and calibration showing nonnecessity. |
| T23 | whole | All three worlds, identical records, targets, losses, moments, nonidentification and respondent comparisons remain present. |
| T24 | restricted | Every retained mathematical clause is correct, and all dropped empirical/strictness assertions and the absent containment are now disclosed accurately. |
| T25 | whole | The complete support witness, school population, moments, both signs of wrong-joint bias and correct-joint equality remain present. |
| T26 | whole | Counts, strict support inclusion, marginals, joint laws, differences and all specified student-exposure preservation and nonhosting clauses remain present. |
| T27 | whole | The exact five-exposure mapping, consistent binary outcomes, all four proportion contrasts and HT unbiasedness remain present. |

T21, T23 and T25 are correctly labelled whole because their canonical
targets themselves specify the counterexamples. T23's refutation remains
limited to the additional zero-scoring interpretation; T25 continues to
leave the printed block-randomization sentence correct. T18 is correctly
labelled refuted because its canonical target is the positive printed
assertion. The unchanged nested common-exposure example in the first report
still supplies a genuine counterexample: bounded telescoping treated
potentials give N times the true variance equal to 1, yet coverage is at
most 1/2 under printed Condition 5, violating level alpha=1/4.

## Junk values and nonvacuity

For T24's revised disclosure, the earlier separating instance still
satisfies every premise:

    S      = {0,...,2049},
    item   = {0,...,1707},
    survey = {1,...,1899},
    w_i = 2, D_i = i mod 2, G_i = 1 exactly when i=1.

Both retained sets contain the nonzero score, but `item ⊆ survey` fails.
The full, item and survey HT contrasts are respectively 1/1025, 1/854
and 2/1899. Multiplication by the stated factors 854/1025 and 1899/2050
gives the full contrast exactly. These calculations were rechecked in
`scratch/delta-checks.log`.

All three numerical sample-size denominators are strictly positive. The
generic HT clauses require positive population size and positive exposure
probabilities. In the conditional Hajek clause, positivity of the retained
denominator, positive weights and subset inclusion imply positivity of the
full denominator. The fixed natural-number subtractions have smaller
subtrahends, so truncation does not change them. The hypothetical sets are
inhabited and the score is nonzero; no empty index set or division by zero
supplies this result.

The finite-law, probability, Gaussian quantile and coverage definitions
agree with the earlier reading. Marginal positivity protects reciprocal
bounds; finite support and normalized positive weights give ordinary
expectations and probabilities; coverage stays in [0,1], and the Wald event
explicitly excludes negative estimated variances. T16 continues to use the
specific zero-denominator convention prescribed by its canonical target.
No new junk-value issue was introduced.

The earlier concrete covariance, misspecification and five-exposure
hypothesis checks were recompiled against the refreshed Defs with
`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`; they passed with an
empty `scratch/lean-check2.log`. The previous nonvacuity arguments apply to
the unchanged statements. The final `findings2.json` contains exactly one
object for each of the thirteen canonical targets and was parsed and
schema-checked with Python.
