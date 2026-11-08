Audited 13 targets and 11 theorem stubs: **6 correct_whole, 5
correct_restricted, 2 omission_ok**. There are **0 restriction_inaccurate,
0 not_faithful, 0 vacuous, 0 false, and 0 omission_questionable** findings.
All severities are `none`.

The six `correct_whole` targets are T1, T4, T5, T6, T8 and T13. T13 is an
accepted refutation of the printed baseline-law assertion, counted under
`correct_whole` because the requested verdict vocabulary has no separate
successful-refutation value. Its Gaussian generator identification is an
external premise in the canonical definitions, not a conclusion of Lean.
Refuting the baseline-law conjunct suffices; it does not purport to refute
the multiplier identities.

The five restrictions are accurate and disclosed in both `record.json`
and the Challenge docstrings:

| Target | Exact restriction checked |
| --- | --- |
| T2 | Retains the full exact-input surplus identity and conservativeness and the two concrete finite-bank failures. Drops the quoted R=10000 assertion, broader seed-reuse claims, probability-approximation-error-control claims and Hajek/numerical commentary. See `SAP/P044/Challenge/Part1.lean:12`. |
| T3 | Omits six explicit exposure vectors and makes the weighted means/biases conditional on positivity of actually observed terms. It does not separately assert that positivity. The condition is true and nonvacuous. See `SAP/P044/Challenge/Part1.lean:20`. |
| T7 | Omits the base exposure vector, four individual joint counts, individual returned entries 1/9 and 1/8, and the explicit exact-joint row identity. See `SAP/P044/Challenge/Part1.lean:48`. |
| T9 | Omits the diagnosis of the printed row-times-row matrix product. This is an actual canonical clause, regardless of the audit note saying it need not be formalized. See `SAP/P044/Challenge/Part1.lean:63`. |
| T10 | Assumes zero crossing marginals or explicit no-isolate/no-crossing graph conditions. It does not construct the generator/rejection law or derive those hypotheses from the source-code premise. The finite-law restriction, including hypotheses at all states in its last block, is visible in the type. See `SAP/P044/Challenge/Part1.lean:70`. |

The two omissions are justified on the visible mathematical content.
For **T11**, T1 establishes failure of an exact expected-variance-dominance
reading for its specific R=65 laws, including an included observation.
It does not establish failure for the chapter's R=10000 recipe, give an
error bound for an approximation, or address Hajek variance. The printed
approximation assertion has no specified tolerance or finite-sample
quantification. A negation of a stronger universal assertion is therefore
not a direct refutation of this canonical assertion. T1's docstring correctly
names the narrower reading it refutes, and T2 states the exact-input result.

For **T12**, S7's positive-marginal-input domain is part of the standing
assumptions. The star's zero-support terms fall outside that domain. Dropping
them defines an extension; its bias alone cannot refute exact-positive-input
unbiasedness. The star's nonidentification argument and T4's corrected theorem
are both valid, as are T7/T8's separate results about smoothed inputs.
The quoted Hajek/WLS consistency and efficiency assertions have no specified
asymptotic regime or quantitative comparison to formalize here. These
observations support omission without endorsing an unrestricted reading of
the prose or relying on an unavailable credited proof row.

No step-2 relation was changed after reading the record. `reading.md` was
saved before opening `claims.json`; `claim-stage.json` was saved before
opening `record.json`. The latter contains one object for each of the eleven
stubs. In particular, T13 remains classified there as a negation of the
positive printed assertion; recognizing it as a valid refutation is not a
change in that reading. Canonical statements, definitions and standing
assumptions determined coverage. Audit-history `note` and `finite_lemmas`
fields were not used to add or delete canonical clauses.

Definitions were followed into the installed Mathlib sources. In particular,
the Gaussian parameter 1/16 is a variance, two-walk degree counts reachable
vertices rather than paths or shortest-distance-two neighbors, graph edges
are unordered, and the bias numerator uses real subtraction. N>0 and the
support/nonempty-set conditions protect the relevant denominators. The
Gaussian maps are measurable; L2 and integrability assertions prevent
nonintegrable-integral or infinite-variance conversion conventions from
doing the work. The nonnormalization of smoothed exposure values is the
subject of the counterexample, not an assumed probability law.

`scratch/Nonvacuity.lean` compiled with
`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean` (exit 0), importing
only `SAP.P044.Defs`. It checks a real two-state probability design with
both contrasted marginals positive, a nonempty nonisolated loopless Boolean
network, and a singleton graph law satisfying T10's positive-degree and
zero-crossing hypotheses. `scratch/Check.lean` also compiled (exit 0),
including a direct finite-sum proof of the exact additional positivity
premise in T3 and positivity of every smoothed marginal weight. An event
actually observed at one of six uniform atoms has probability at least 1/6.

`python3 scratch/finite_checks.py` passed using independent exact rational
arithmetic. It checked all 66 omitted-bank tables and both joint observation
laws, every T1 numerical moment and fixed-table shortfall, the star's observed
support and biases, all cycle weighted means and joint-row values, 168
complete-randomization degree cases, 93 binomial-bank cases including R=0,
and a signed structural-zero example with surplus 25. The detailed numbers
are in `scratch/finite-results.json`. These computations supplement the
statement audit; they do not claim to re-certify the absent Solution or
Comparator.

The relevant original prose was also checked against the
[chapter PDF](https://cyrussamii.com/wp-content/uploads/2025/11/BK-EEP-Chp16.pdf),
printed pp. 211–212 and 216–217. This confirms the context of the exposure,
unbiasedness, baseline-law and variance-approximation assertions; it does not
independently verify the external R source-code premises.
