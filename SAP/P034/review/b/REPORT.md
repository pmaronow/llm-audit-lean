# P034 statement audit

| Verdict | Count |
|---|---:|
| correct_whole | 5 |
| correct_restricted | 0 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |
| **Total targets** | **5** |

Severity counts: none 5; minor 0; major 0. No adverse findings or omissions.

The blind expansion was saved in [reading.md](reading.md) before opening
`claims.json`. The claim comparison was saved and parsed in
[claim-stage.json](claim-stage.json) before opening `record.json`. The record
declares all five targets whole, with no restrictions or omissions; all five
coverage decisions are supported. No step-2 reading was changed after reading
the record. Claims were assessed from their canonical statements and
`definitions_needed`, with the standing assumptions; audit-history notes and
provenance rows were not used to add or remove mathematical clauses.

T4 is classified as `broader` at step 2 solely because its two unaveraged
identities quantify over real factor values as well as the required binary
values. These are true extensions of the same polynomial identities and cover
all canonical cases, so its final coverage verdict is `correct_whole`. The
counterexample docstrings for T1 and T3 describe the relevant complete-case and
averaged-effect interpretations without declaring the printed empirical claims
false.

## Checks and mathematical assessment

[scratch/Check.lean](scratch/Check.lean) imports `SAP.P034.Defs`, not the
sorry-bearing Challenge. It compiled successfully, with exit code 0 and no
diagnostics, using:

```text
/home/ubuntu/sap/tools/sap-lean scratch/Check.lean
```

The scratch file checks `WorldANumericalFacts`, `SampleNumericalFacts`,
`WorldBFacts`, `EqualCompletionFailure`, and `T5Statement` by `native_decide`.
It also proves all T2 hypotheses simultaneously for a uniform Boolean treatment,
one constant covariate, full response, and potential outcomes 0 and 1.
Independent Python exact-rational calculations verified both finite probability
laws, all 12 observed-cell equalities, the actual World A moments and determinant,
and all 39 percentages and count totals. No `lake` command was run.

For T1, strict positivity makes every conditioning event used in the witness
non-null; all Pearson expected counts are 100. The nonsingular computed Gram
matrix and its sample scaling give the two stated unique real solutions. The
chi-square p-value at statistic zero is one because the defining squared-normal
event is the entire real line. No division-by-zero convention supplies any result.

For T2, the variables are measurable and L². Realized outcomes are therefore
integrable, and the Gram/RHS products are integrable by the L² product bound;
event restrictions preserve integrability. H1 and H2 factor the joint law in
each arm into its treatment, response, and outcome/covariate factors. This gives
positive arm response, the arm means, and the unchanged covariate laws. Under
the respondent distribution, E(T−p)=0, E((T−p)X)=0,
E((T−p)T)=p(1−p), and E((T−p)Y)=p(1−p)τ. Multiplying any normal equations
by the row (−p,1,0,…,0) gives β_T=τ since 0<p<1, including when G is singular.
Nonsingularity separately guarantees unique existence. Thus neither
nonintegrable Bochner integrals nor an assumption of the desired coefficient
is doing the work. An additional nondegenerate instance with independent fair
T,X,R0,R1 and Y0=X,Y1=X+1 has genuine attrition and det G=1/16; details are in
[findings.json](findings.json).

T3 uses the actual four-cell saturated witness, for which no covariates are
required. T4 follows by polynomial cancellation at fixed covariates and ordinary
real-field cancellation for its equality conditions. T5 uses the exact supplied
table and its stated half-open rounding rule, with positive fixed denominators.
None uses an empty treatment or observation index, truncated subtraction, or an
unbounded limit convention. No repair is required.
