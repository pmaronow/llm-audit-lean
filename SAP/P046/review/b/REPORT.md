# P046 statement audit

Ten targets were audited. The architect's decisions are supported on the
available evidence.

| Verdict | Count |
| --- | ---: |
| correct_whole | 3 |
| correct_restricted | 7 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity counts: none 10, minor 0, major 0. There are no adverse findings or
omitted targets.

`SAP.P046.T6`, `T7` and `T10` receive `correct_whole`. For T6 this certifies
the complete, valid refutation of the canonical printed population-tail
assertion. The record's `refuted` label and its docstring are justified. The
remaining seven targets receive `correct_restricted`; their declared scope
reductions and added integrability conditions are accurate.

## Procedure and evidence

The blind reading was saved in `reading.md` before `claims.json` was opened.
The per-theorem comparisons were saved and parsed in `claim-stage.json`
before `record.json` was opened. No step-2 mathematical reading was changed
after reading the record. T6's step-2 `different` entry records its deliberate
negation of the canonical positive assertion; its final acceptance concerns
the correctness of that refutation.

All SAP definitions were expanded, including the conditional sigma algebras,
opposite-fold dependence, finite product sampling, uniformity quantifiers,
and Gaussian-limit convention. Mathlib's real integral, variance, conditional
expectation, measure pushforward and probability conversions were checked at
their definitions. The relevant integrals are finite under the theorem
hypotheses. In particular, T5 and T9 explicitly exclude finite-sample fitted
functions with infinite L2 norm, so their convergence premises do not exploit
Mathlib's zero value for a nonintegrable Bochner integral. Positive sample
sizes and the positivity assumptions rule out division-by-zero artifacts in
the asserted bounds. Zero-dimensional parameter spaces and the `n=0` values
of sequences do not supply the conclusions.

The distinctions between population and conditional centres, random and
deterministic radii, and strict and non-strict noncoverage events are preserved.
The common positivity constant in T7 is prescribed by canonical
`definitions_needed`. T10 quantifies over the unrestricted class in the
canonical claim. The stronger common-positivity impossibility construction in
`finite_lemmas` adds no target clause. Neither audit notes nor finite lemmas
were used to remove or add claim requirements.

Independent numerical checks in `scratch/audit_checks.py` use exact integers
and fractions. A logarithm enclosure was proved by the positive atanh series
and an explicit geometric remainder. All 5,151 T1 count states lie strictly
outside that enclosure; the minimum separation exceeds 0.0087. The integer
classifier agrees with the logarithmic exclusion test in every state, exactly
1,946 states fail, the full multinomial mass sums to one, and the stated
noncoverage numerator is exact. The resulting probability is
`1.1979291069795625472576722625601454579... × 10^(-7)`, greater than
`119/10^9`, which is greater than `10^(-7)`.

An independent exact enumeration of the T4 `(L,Z,X)` states gives means
`1/20`, second moments `1/5` and `17/40`, variances `79/400` and `169/400`,
and risks `3/20` and `3/8`. Thus the counterexample has the stated efficiency
reversal. The bounded iid summands support both normal limits.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully
(exit 0, with two stylistic linter warnings). It checked that the uniform
covariate measure is a probability and atomless, that constant-zero
opposite-fold fits satisfy the L1/L2 and convergence predicates, and that
Lean's integer classifier has exactly 1,946 failing states and the stated
huge numerator. These scratch proofs import only `SAP.P046.Defs`; they do not
use the Challenge stubs. No `lake` command was run, and at most one Lean
process was active. Machine-readable independent results are in
`scratch/check-results.json`.

## Nonvacuity

Each target has its instance or argument in `findings.json`. A common
nondegenerate instance for the general results is independent
`W ~ Uniform[0,1]`, `X ~ Bernoulli(1/2)` and `B ~ Bernoulli(1/2)`, with
`Y0=0`, `Y1=B`, `pi=m=1/2`, and `delta=1/4`. It satisfies probability,
atomlessness, measurability, both separate conditional independences, both
conditional-mean requirements and strict positivity. Its mean is `1/2` and
its HT summand variance is `3/4`.

For T5 use the singleton-zero working family, constant-zero fits and
deterministic folds of sizes `floor(n/2)` and `ceil(n/2)`. Every empirical
and population minimization premise holds, both convergence errors vanish,
and both limiting variances are `3/4`. For T9(b) the same fits suffice; for
T9(d), constant-`1/2` fits give zero prediction error and Hahn variance
`1/2`. T8 admits the same integrable fits for every positive sample size.
These are mathematical nonvacuity arguments; the scratch file separately
certifies the uniform measure and zero-fit predicates, rather than claiming a
Lean proof of every field of the full product study.

For T10 there is a direct verification over the canonical unrestricted class.
At each `n>=1`, take independent uniform W and Bernoulli treatment with
`p_n=1/(n+1)^2`, and compare constant treated potential outcomes zero and one,
with untreated potential outcome zero. Both laws are valid with
`delta=p_n/2`. Their observed laws agree on the no-treatment event of mass at
least `3/4`. At every common observed sample, errors of at most `1/4` for
both population means are impossible. Therefore at least one law has error
greater than `1/4` with probability at least `3/8`. This supplies the required
positive constants and arbitrarily late sample sizes without any empty-class
or unbounded-limsup convention.
