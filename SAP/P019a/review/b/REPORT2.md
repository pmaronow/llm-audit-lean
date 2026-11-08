# P019a delta statement review

| Verdict | Count |
| --- | ---: |
| correct_whole | 2 |
| correct_restricted | 9 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |
| **Total targets** | **11** |

All severities are `none`. No adverse finding remains, and no new adverse
finding was identified. The revised decisions are 2 whole, 9 restricted,
0 refuted and 0 omitted.

## Earlier findings and the revision

My earlier `findings.json` contained no adverse issues or requested fixes.
Consequently there are no earlier adverse findings to classify as partly
fixed or not fixed. Each previous acceptance was rechecked as follows.

| Target | Earlier verdict | Current verdict | Recheck and disposition |
| --- | --- | --- | --- |
| P019-T1 | correct_restricted | correct_restricted | Upheld; integrated mixture and absence of joint-law identification remain accurately disclosed. |
| P019-T2 | correct_restricted | correct_restricted | Upheld; the approximate-power and joint-law-identification omissions remain explicit. |
| P019-T3 | correct_restricted | correct_restricted | Other referee's disclosure finding **fixed**: the retained population mean 5/6 is now expressly acknowledged. The mathematical assertion is unchanged. |
| P019-T4 | correct_restricted | correct_restricted | Upheld; n>=2 conditional block, omitted count identity and n+2 covariance sequence remain correctly described. |
| P019-T5 | correct_restricted | correct_restricted | Upheld; three point probabilities at zero, with the fuller laws and numerical details expressly omitted. |
| P019-T6 | correct_whole | correct_whole | Upheld; every canonical formal distributional equality and its conditioning hypotheses are retained. |
| P019-T7 | correct_restricted | correct_restricted | Upheld; the first diagnosis counterexample remains, with the second example and listed ancillary details omitted. |
| P019-T8 | correct_whole | correct_whole | Upheld; decomposition, balance, beta=1, general diagnosis and specialized diagnosis are all retained. |
| P019-T9 | correct_restricted | correct_restricted | Upheld; explicit joint statistic/Fisher limits and unequal-law conclusion remain, with listed additional clauses omitted. |
| P019-T10 | correct_restricted | correct_restricted | Upheld; full joint assignment premise and inference remain, with the empirical result omitted. |
| P019-T11 | correct_restricted | correct_restricted | Upheld; the four mathematical blocks, estimator completions and quantile guards remain accurately disclosed. |

My first review missed the imprecision in T3's former disclosure. Although
the blind reading explicitly recorded `m_10=5/6`, I accepted wording that
said the numerical population-cell means were omitted. The other referee
correctly identified that mismatch. The revised docstring now says:

> Retains the treated negative-cell population mean E[V | Z=1,Y=0]=5/6,
> but omits the other numerical population-cell means

This agrees with `SAP/P019a/Defs/Part5.lean:59`. The remaining omissions in
the T3 docstring are still accurate: population probabilities and variances,
other means, the observable-law table, individual singleton and n=4 moments,
the general conditional-count/missing-mass assertions and the separate
variance equality are not separately stated. The four displayed missing-mass
values remain arithmetic expressions, not new conditioned-count assertions.
The same corrected disclosure appears in `record2.json` and
`architect-report.md`; the documentation issue is fully fixed.

## Changed statements and labels

I compared every revised Defs and Challenge statement with the saved expanded
mathematics in `reading.md`. No mathematical change was found in any of the
eleven propositions or their supporting definitions. The change relevant to
this audit is T3's corrected disclosure in
`SAP/P019a/Challenge/Part1.lean:25`. Comparing `record.json` with
`record2.json` likewise finds only T3's `restriction` field changed.

The two whole labels cover all canonical **formal** clauses. T6 asserts the
control and treated-minus-one laws, their common baseline law for every real
point, and the equivalent treated `t+1` identity. Its positive-cell premises
match the canonical formal hypotheses. T8 states all three canonical formal
parts, including both consequences of beta departing from one. The claims
file explicitly excludes the informal test-permission language in T6 and
the sample-evidence sentence in T8 from the formal content; these are not
undisclosed omissions.

Each of the nine restricted labels still accurately discloses the omitted
or added content. In particular, T1 and T2 do not identify their deterministic
mixture with a joint population's observable conditional means; T4's count
block still loses the n=0,1 sample-size endpoints; T9 does not add a separate
exact variance formula; T10 does not assert the empirical statistic or
p-value; and T11 explicitly adds the quantile-set guards and fixed
completions. Normalizing whitespace, every recorded restriction matches its
Challenge docstring exactly. Their mathematical content was checked as well.

No revised decision uses `refuted`. This is appropriate: the canonical T1,
T3, T5, T7 and T9 targets already ask for counterexamples, and the restricted
labels describe which parts of those canonical counterexamples are retained.
The retained counterexamples still address their printed readings: the
mechanism discrepancy, zero-completed unconditional covariance and exact
product formula, incorrect distributional shift, exhaustive two-cause
diagnosis, and Fisher reference-law implication, respectively. No assertion
of the observed survey result or a numerical power guarantee is inferred.

## Junk values and nonvacuity

The documentation edit adds no hypotheses, divisions, integrals, infima or
sample-size cases. The revised T3 has the same positive-probability cells
and occupied event as before. A new direct Lean check proves both
`P(Z=1,Y=0)>0` and the retained mean `5/6` from the current Defs, without
importing a Challenge or Solution theorem.

The earlier nonvacuity instances remain valid. The Defs-only Lean proof of
`finiteSampleWitness.standing` and the eight-atom standing/positive-cell
instance was recompiled successfully against the refreshed package. These
give actual models for T4, T6, T8 and T11. The unchanged 128-atom shared-latent
model gives T10's full joint assignment premise; the unchanged sequential
population gives T9's positive influence variances. Earlier exact rational
checks remain applicable because these population definitions and
statistics agree with the saved reading.

Positive conditioning probabilities, occupied-cell guards, fixed empty-cell
completions, real subtraction, integrable Gaussian tests and T9's explicit
first/second-moment integrability are unchanged. T11 still requires a
nonempty, lower-bounded normal quantile set; these premises have concrete
instances and are automatic for its alpha range. No changed or newly exposed
assertion relies on a junk value or vacuous antecedent.

Validation: both `scratch/DeltaT3.lean` and `scratch/Nonvacuity.lean` compiled
successfully with the supplied `sap-lean` wrapper. At most two Lean processes
ran concurrently. The record/docstring comparison is saved in
`scratch/delta-validation.json`. `findings2.json` was parsed and checked for
one correctly named entry per canonical target and the required schema.
No assessment of external proof certification is inferred from the
architect's report; this remains a statement audit.
