Audited all 11 targets: **2 correct_whole, 8 correct_restricted,
1 restriction_inaccurate**. Severity: **10 none, 1 minor, 0 major**.
There are no false, vacuous, not_faithful, or omitted targets.

| Verdict | Count | Targets |
| --- | ---: | --- |
| correct_whole | 2 | T6, T8 |
| correct_restricted | 8 | T1, T2, T4, T5, T7, T9, T10, T11 |
| restriction_inaccurate | 1 | T3 |
| not_faithful | 0 | — |
| vacuous | 0 | — |
| false | 0 | — |
| omission_ok | 0 | — |
| omission_questionable | 0 | — |

**P019-T3 / SAP.P019a.T3 — restriction_inaccurate, minor.**
The restriction in `Challenge/Part1.lean:25` and the corresponding record
says that the numerical population-cell means are omitted.
`Defs/Part5.lean:59` explicitly asserts `S.listMean true false = 5/6`,
which is the numerical population-cell mean E[V | Z=1,Y=0]. The theorem
is mathematically sound, but this description of its omissions is inaccurate.
Replace the first restriction sentence with:

> Retains the treated negative-cell population mean E[V | Z=1,Y=0]=5/6,
> but omits the other numerical population-cell means, all numerical
> population-cell probabilities and variances, marginal variances, mu and
> truth-rate values, and the nine-atom observable-law table.

Keep the remaining restriction text. The full replacement is in `findings.json`.

The remaining architect decisions are justified. T1 and T2 disclose their
deterministic-mixture scope; T4 discloses its sample-size endpoints and omitted
count identity; T5 and T7 retain sufficient genuine counterexamples while
listing the omitted detail; T9 retains both the joint limit and an unequal-law
conclusion, with its omissions disclosed. T6 and T8 state their whole formal
claims. T10 covers the whole formal sufficient-premise theorem; its record's
conservative `restricted` label accurately describes the omitted empirical
numbers and explicit completions, so it is accepted as `correct_restricted`.
T11's completions and quantile-set premises are accurately disclosed. There
are no omitted targets to assess.

The blind reading was saved before reading the claims, and the initial
claim-stage file was saved before reading the record. There was one subsequent
source-version correction: I initially questioned T11's division by n after
consulting an earlier manuscript. The published page 49 instead defines
n times the estimated variance as the plug-in bracket, exactly agreeing with
the Lean definition. This was confirmed visually in the published PDF;
`claim-stage.json` records the cited correction and the initial stage file is
preserved in `scratch/claim-stage-before-source-correction.json`.
[Published paper, p. 49](https://alexandercoppock.com/aronow_etal_2015.pdf#page=7).
No claim-stage judgment was changed merely to agree with `record.json`.

Independent exact rational checks in `scratch/exact_audit.py` passed for the
ceiling formulas, all three finite witnesses, the n=4 occupied-sample moments,
the five sequential studies and influence matrix, and a shared-outcome model
satisfying T10's full joint premise. The actual n=4 conditional variance is
141205/404496; the printed product expression is 75809/202248; their
difference is −1157/44944. Results are saved in
`scratch/exact_audit_results.json`.

`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean` passed. This scratch
file imports only Defs and proves the eight-atom study's standing assumptions
and positive affirmative-cell masses, and checks the completed variance on
a sample with every cell occupied twice. No Solution or Comparator was read,
and no `lake` command was run.

The remaining truth checks used the ordinary finite conditional-variance
decomposition and bounded-variable central limit arguments. Conditional on
the entire label pattern, occupied subgroup means have constant expectations,
variances σ²/N, and zero cross covariance. This gives T4's exact discrepancy;
the multinomial count expansion gives its n⁻² coefficient. T9's Gaussian
limit has the verified influence covariance matrix; conditioning on its
shared normal coordinate gives a strictly positive extra Fisher variance.
T10's stronger joint premise cancels the cross-influence terms and gives a
diagonal, positive limiting covariance. T11 uses a positive consistent
variance estimate and standard normal quantiles.

The finite-law representation preserves the full joint law of the paper's
bounded counts and binary variables. Population and occupied-sample
conditioning probabilities are positive wherever their moments are used.
All named universal premises have explicit satisfying instances in
`findings.json`; none assumes its conclusion. There is no unbounded limsup,
empty-type argument, effective truncated subtraction, or nonintegrable
integral used to obtain a conclusion. In particular, the limiting variance in
T9 has explicit first- and second-moment integrability, and normal p-values
at finite statistics are strictly positive, so the totalized real logarithm
at zero plays no role.
