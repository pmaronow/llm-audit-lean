# Referee report: P025a

All 11 supplied targets are accounted for. No statement error, undisclosed restriction, invalid refutation, or vacuity was found.

| Final verdict | Count |
|---|---:|
| correct_whole | 4 |
| correct_restricted | 7 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

There are no non-`correct_*`/`omission_ok` items to report. All severities are `none`.

## Scope and decisions

The architect's decisions are appropriate: seven restrictions are accurate and disclosed in the Challenge docstrings; two whole corrected statements match the canonical claims; and two printed propositions are correctly refuted. The permitted final verdict vocabulary has no `correct_refutation` label, so `correct_whole` includes the two faithful `refuted` decisions. This does not mean that the paper's printed propositions are true.

| Target | Final verdict | Assessment of the exported scope |
|---|---|---|
| P025-T1 | correct_restricted | The numerical counterexample, exact range, finite design and general zero-cut/nonoptimality conclusions are retained. Both numerical residual decompositions, the general sample-mean residual identity, the exact coordinate-change formula and an explicit independence assertion are omitted as disclosed. |
| P025-T2 | correct_restricted | The numerical weighted counterexample and Assumption 2 are retained. Population/design/class-weight construction, replication, upper-cut identification, residual decompositions and the general weighted diagnosis are omitted as disclosed. |
| P025-T3 | correct_restricted | Both cuts, prescribed feasible optimizers, attained endpoints, full range, segment attainment, increments and lower residual certificate are retained. A separate continuity assertion is omitted as disclosed. “Separation” here denotes the asserted prefix/tail inequalities about the lower endpoint, not an added Assumption 2. |
| P025-T4 | correct_restricted | Both first cuts and their attained global extremal values are retained. The last-cut inequalities, increments and explicit original-scale threshold-vector assertions are omitted as disclosed. |
| P025-T5 | correct_restricted | Both numerical witnesses, rounded variants, rounding arithmetic, interval memberships and seven individual uniform quota laws are retained. The joint independent design and its population/count/estimator linkage are omitted as disclosed. |
| P025-T6 | correct_whole | The overlap threshold, exact numerical odds ratios, odds transformation, product equivalence and common-cap consequence match the canonical corrected claim. |
| P025-T7 | correct_whole | A faithful refutation of the printed sample optimizer/range assertion, together with the valid upper first-cut endpoint result. |
| P025-T8 | correct_whole | A faithful refutation of the printed class optimizer/formula assertion, together with the valid upper first-cut endpoint result. No separate sharpness claim is made. |
| P025-T9 | correct_whole | The corrected partition and minimum formulas, exact duplicated-class discrepancy and undefined-index cases match the canonical claim. |
| P025-T10 | correct_restricted | The finite design and numerical counterexample are retained. The all-weight residual equality and equality/uniqueness characterization are omitted as disclosed. |
| P025-T11 | correct_restricted | The normalized proof identities and boundary/strict two-coordinate conclusions are retained. The original-scale, endpoint, first-index/global-maximum and finite-population calibration assertions are omitted as disclosed. |

## Checks and limits

The blind mathematical reading was saved in `reading.md` before opening `claims.json`. The independent claim comparison was then saved in `claim-stage.json` before opening `record.json`. No claim-stage relation was changed after reading the record. In particular T7 and T8 remain `different` there: their theorems refute rather than affirm the canonical printed propositions. The final assessment accepts the architect's explicitly declared refutation decisions.

Definitions were unfolded through the supplied SAP files to the relevant Mathlib operations. Cut indices count a prefix and range over the indices where the next outcome is defined. The printed lower tail is represented by `Option`: cuts 0 and 1 have no value. Guarded subtraction at the valid cuts has the correct two duplicated classes. No invalid tail is converted into a numeric value through truncated subtraction.

For the general sample/class optimization statements the index sets are nonempty, masses are positive, and 0<alpha<=beta<=1. The feasible box contains the constant vector 1/beta. Every weighted denominator is positive, and every objective is between the smallest and largest outcomes. Thus the attainable set is nonempty and bounded, and the real infimum/supremum operations have their ordinary meaning. `IsLeast` and `IsGreatest` include actual membership, not only a bound. The binary intervals use interior proportions and gamma>=1; their denominators and odds ratios are positive. In the two-coordinate argument, positive a,p,q and nonnegative c2 keep every denominator positive, including a=b. No hypothesis assumes the optimization conclusion.

`scratch/Check.lean` imports only the Defs and uses no Challenge theorem or `sorry`. It compiles successfully with:

```text
/home/ubuntu/sap/tools/sap-lean scratch/Check.lean
```

The checks establish nonconstant sorted sample data, strictly ordered positive and separated class data, original-scale box feasibility and denominator positivity, concrete attained counterexample values, the two-unit sampling distribution and marginals, nonemptiness of all seven quota spaces without powerset enumeration, the four-class feasible optimizer value, and satisfiable boundary and strict branches. They independently prove both printed assertions false using their wrong optimizer values. The class refutation uses a realizable two-unit population and does not rely on the optional printed expression being undefined. Fine square-root brackets and the four numerical reweighting witnesses were also checked with exact rational arithmetic.

This is a statement audit, not a replacement proof or Comparator certification. Nonvacuity checks import no Solution and the refutations do not use the Challenge stubs. The comparison uses the canonical transcriptions and standing assumptions supplied in `claims.json`. A paper-only search identified the [journal article](https://academic.oup.com/biomet/article-abstract/100/1/235/193266), but its final PDF was inaccessible; no independent page-image verification of the supplied transcription is claimed.

The per-target evidence and confidence are in `findings.json`. Both output JSON files were parsed and checked against all 11 target identifiers.
