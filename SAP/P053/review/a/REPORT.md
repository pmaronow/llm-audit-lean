# P053 statement audit

Eight canonical targets and eight Challenge theorems were audited. Counts:

| Verdict | Count |
|---|---:|
| correct_whole | 6 |
| correct_restricted | 2 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity counts: none 8, minor 0, major 0. There are no adverse findings and no omitted targets.

`reading.md` was saved before opening `claims.json`. `claim-stage.json` was saved and parsed before opening `record.json`; it independently classified T1, T3, T4, T5, T7 and T8 as whole, and T2 and T6 as narrower. The record required no change to any step-2 verdict.

The architect's six `whole` decisions match the canonical statements and their `definitions_needed`, with the standing assumptions included. In particular, T1 includes the factor uniform over fixed-total outcome vectors, both sample-symmetry directions and the exact fiber criterion; T3 includes all finite inferences and the real-outcome monotonicity clause; T5 and T7 retain every stipulated expansion and probability limit; and T8 retains the complete explicit witness and full regularity certificate. Audit-history `note` and `finite_lemmas` fields were not used to add requirements or excuse missing ones.

The two restrictions are accurate and fully disclosed:

* **P053-T2 — correct_restricted.** `Defs/Part4.lean:90` includes both finite statistics, both nonfactorization assertions, every positive repeated block size, size divergence, allocation/success-fraction limits and a raw fourth-moment bound. It does not assert a complete S5 certificate with all potential-outcome/effect variance and average-effect limits for that family. `Challenge/Part1.lean:12` and the record describe exactly that loss of stated scope. The docstring correctly identifies the unrestricted label/covariate reading as the reading refuted and explicitly distinguishes the corrected table-statistic assertion. The record uses `restricted`, not `refuted`, as required. The missing limits actually hold for the displayed family; no impossible regularity premise makes the examples vacuous.
* **P053-T6 — correct_restricted.** `Defs/Part5.lean:52` adds `PositiveOLS` only to the variance-ratio and sharp-null studentized implications. It means eventual strict positivity for every supported assignment, not merely positivity with probability tending to one. Neither the local unstudentized difference nor either constant-effect approximation receives that premise. The theorem also omits the printed local equivalence of FRT and Wald tests, including the conditional FRT distribution/quantile/p-value/rejection-rule comparisons. `Challenge/Part1.lean:36` and the record disclose both limitations. The positive-limit hypotheses themselves are already canonical. A nondegenerate family satisfying every strengthened premise is exhibited below, and a different S5 family shows that the assignment-wide positivity restriction is real.

The definitions render complete randomization as uniform counting over all assignments of the prescribed size. All finite examples have nonempty supports and positive divisors. Table coordinates use integer subtraction. The only relevant natural subtraction, the control success count in the canonical binary sample, is protected by containment. The asymptotic `Regularity` premise is exactly the stated moment/allocation regularity with harmless eventual arm-size bounds; it contains no estimator-consistency or central-limit conclusion. Early zero-divisor conventions cannot affect its limits. Studentization has the disclosed positivity restriction; Gaussian probabilities are finite, and the normal quantile is used only for 0<alpha<1. No empty type, nonintegrable integral, or unbounded limsup supplies a conclusion.

Nonvacuity is substantive. With r=k+1, use N=4r, n1=n0=2r and common potential outcomes consisting of r ones and 3r zeros. Then p=1/2, v1=v0=3/16, vt=tauInf=0, the raw fourth-moment average is 1/2, and every supported OLS variance is at least 1/[2(4r−2)]>0. This realizes all strengthened T6 sharp-null hypotheses. Adding 1 to treatment potential outcomes realizes nonlocal constant effects and the tauInf=1 case of T5. By contrast, balanced half-one/half-zero sharp-null populations satisfy S5 with positive variance but admit zero-residual assignments, so S5 alone does not imply `PositiveOLS`. T8's heterogeneous family separately supplies p=1/5, variances 4,1,1, and the three distinct coefficients 81/4,10,85/4.

Verification used `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`, which exited successfully. This scratch file imports only the definitions and proves a `Regularity` instance; the displayed axiom list has no `sorryAx`. Independent exact arithmetic in `scratch/check_finite.py` passed all assertions: 21,336 binary assignment/vector cases for T1; both T2 statistics at four repeated block sizes; every stated T3 count and p-value; 225 T4 sign/identity cases; all assignments of the T8 witnesses for N=10 and 20; and all assignments of the positive T6 witnesses for N=4,8,12. It also checked the exact Fisher-minus-OLS and actual randomization-variance identities on those populations. The general asymptotic conclusions were checked mathematically against sample-moment consistency, the exact variance identities and the finite-population central limit condition; finite enumeration is not presented as their proof. Details are in `scratch/nonvacuity.md` and results in `scratch/check-results.json`.

The original [paper at the publisher](https://projecteuclid.org/journals/statistical-science/volume-32/issue-3/Understanding-Dings-Apparent-Paradox/10.1214/16-STS582.pdf) and the indexed IMS PDF were sought using only the paper DOI. A readable original PDF could not be retrieved, so the paper-text comparison relies on the canonical transcriptions supplied in `claims.json`; no independent comparison with the original page images is claimed. No Solution, Comparator, or underlying audit formalization was read.
