# P019a statement audit

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

All severities are `none`. There are no adverse items requiring a fix.

T6 and T8 cover the canonical formal claims. T1, T2, T3, T4, T5, T7, T9,
T10 and T11 correctly state their disclosed restricted content. All targets
have a theorem; the record contains no omitted targets.

The blind reading was saved in `reading.md` before opening `claims.json`.
The independent classifications and reasons were saved in `claim-stage.json`
before opening `record.json`. Reading the record caused no classification
changes. Each recorded decision agrees with that assessment, and its
restriction is reproduced accurately in the corresponding Challenge docstring.
This assessment does not rely on the source-proof names listed in the record.

The restrictions preserve the distinctions that matter here: the ceiling
results are integrated mixture calculations without a joint-law identification;
T3's four missing-mass expressions are arithmetic identities rather than a
general conditioned-count theorem; T4 omits the n=0,1 count endpoints and uses
n+2 for its occupied-event covariance sequence; the sign and diagnosis
counterexamples omit their declared ancillary details; and the five-list
counterexample asserts failure of the Fisher reference-law implication, not a
claim about the observed survey data. T10 uses the full joint assignment
premise from the canonical sufficient-condition claim. T11 explicitly guards
the normal quantile and defines its incomplete finite-sample estimators.

Finite probability vectors faithfully represent the bounded count outcomes in
this setting. Conditional expectations use positive-probability events, or
explicit nonzero guards; occupied-cell statements have positive probability
when their sample-size hypotheses apply. Real subtraction avoids count
truncation. The Gaussian laws are probability measures, their bounded
continuous test functions are integrable, and T9 explicitly requires the
moments used in its continuous variance. No retained result depends on an
empty index type, undefined ratio, unbounded limsup, or a nonintegrable
integral convention. The standard-normal quantile premises in T11 are
automatic for the specified alpha range, although still explicitly disclosed.

Validation used a Defs-only Lean scratch file, compiled successfully with
`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean`, and independent exact
rational enumeration in `scratch/exact_checks.py` (all checks passed; results
in `scratch/exact-results.json`). The Lean checks establish concrete standing
instances and affirmative-cell positivity. The rational checks cover the
ceiling contrasts, finite counterexamples, n=4 occupied-sample discrepancy,
sequential influence matrix, and a concrete model of T10's full joint premise.
The asymptotic assertions were also checked mathematically through the
conditional-variance/count expansion and multivariate influence-function
arguments; the scratch checks do not constitute new formal proofs of every
asymptotic theorem. Challenge/Solution proofs were not used as substitutes
for the statement audit.
