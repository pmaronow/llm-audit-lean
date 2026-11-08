# Statement referee report

Audited all 17 targets, P009-T18 through P009-T34.

| Verdict | Count |
| --- | ---: |
| correct_whole | 7 |
| correct_restricted | 9 |
| restriction_inaccurate | 0 |
| not_faithful | 1 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity counts: none 16, minor 0, major 1. There is one faithfulness failure, in T25, and no omitted target.

The blind mathematical expansion was saved in `reading.md` before opening `claims.json` or `record.json`. The independent comparison was saved in `claim-stage.json` before opening the record. The original versions are preserved in `scratch/reading-blind.md` and `scratch/claim-stage-before-record.json`. A later R=2 Lean check exposed one misreading of summation scope in T25. That is the sole change to a step-2 verdict, and its source and compiled evidence are cited below and in both corrected files.

## P009-T25 — not_faithful, major

At `SAP/P009b/Defs/Part2.lean:82`, the definition

```lean
(∑ r, estimates r-1)/(R:ℝ)
```

elaborates as `((∑ r, estimates r)-1)/(R:ℝ)`. The subtraction occurs after the sum. With notation disabled, Lean prints `HDiv.hDiv (HSub.hSub (Finset.univ.sum fun r => estimates r) 1) ↑R`. The canonical target defines the signed mean error about 1, `(∑ r, (estimates r-1))/(R:ℝ)`, followed by its absolute value.

For R=2 and two estimates equal to 1, the canonical reported statistic is zero, while the package's `reportedBias` is 1/2. At the actual simulation replication count R=50000, estimates all equal to 1 give package `reportedBias=49999/50000`, again with canonical value zero. `scratch/Parse.lean` proves the parsing equality by `rfl`, the numerical values and the discrepancy; it imports only Defs and compiles successfully.

The theorem's caption conjunct is true of the incorrectly defined statistic. Its R=1 sign-loss example passes because the formulas coincide at R=1. Its population-bias clauses are correct. The theorem therefore fails to state the canonical caption claim, and the record's `whole` decision is wrong. The positive-R hypothesis is satisfied by both counterexamples.

Fix the definition with explicit summand parentheses:

```lean
def empiricalBias (R : ℕ) (estimates : Fin R → ℝ) : ℝ :=
  (∑ r, (estimates r - 1)) / (R : ℝ)
```

`reportedBias` can remain its absolute value. The package source was left intact for this audit.

## Decisions and restrictions

Sixteen record decisions agree with the corrected assessment; T25's `whole` decision fails for the reason above. All nine restriction texts occur verbatim in their theorem docstrings. Their substance also matches the actual definitions and quantifiers, as follows.

| Target | Verdict | Assessment |
| --- | --- | --- |
| T18 | correct_whole | Both corrected count laws, zero case, exact ratio, scalar bounds and supported-vector bound are present. The masked n-vector with its own coordinate fixed to false faithfully represents the deleted-coordinate vector. |
| T19 | correct_whole | The schedules realize exactly the six-unit counterexample, with indicator one and witness count three, including the detailed interference certificates. |
| T20 | correct_restricted | The two pointwise inequalities and final lemma remain. The intermediate aggregate chain and supplied-array formulation are expressly omitted. |
| T21 | correct_restricted | Every aggregate numerical quantity and discrepancy remains. The six pairwise covariance calculations are expressly omitted; convergence is not challenged. |
| T22 | correct_restricted | Aggregate finite formulas, the centre correction and corrected-centre convergence remain. Individual covariances, printed-centre convergence and the three regimes are expressly omitted. Common regularity and q>=4 are expressly required for convergence. |
| T23 | correct_restricted | The twelve sampling integrals and complete-design ratio remain. Integrability is expressly added; universal fixed-baseline clauses, support identities and ratio divergence are expressly omitted. The variance being integrated is design variance at fixed baselines. |
| T24 | correct_restricted | The exact complete-interference exception remains for both designs and both estimators. The blanket empirical assertion about other settings and numerical Monte Carlo certification are expressly omitted. |
| T25 | not_faithful | The empiricalBias definition subtracts one after summing, giving a different statistic for R>1. The claimed whole treatment of the caption is incorrect. |
| T26 | correct_restricted | Pairwise and external coefficients and the exponent-one limit remain. Potential boundedness, selection of the maximal exponent and the two separately stated specializations are expressly omitted. |
| T27 | correct_restricted | Atom bounds, finite approximation, supplied-minimizer error and limits remain. Existence of a minimizing sequence, a separate exponential-limit clause and the heavy-atom example are expressly omitted. |
| T28 | correct_whole | The mean identity, finite centering criterion and eventual CDF identities, including failure of the reversed inequality, match the canonical formal content. |
| T29 | correct_restricted | The natural-power restriction is explicit. On that domain every numerical link remains, and the absolute-covariance form validly strengthens the signed bound. |
| T30 | correct_whole | MAX/SR are the specified multiples, with exactly the equality-or-zero alternatives for the erroneous AVG identities. The Rayleigh maximum represents the largest eigenvalue of the symmetric nonnegative dependence matrix. |
| T31 | correct_whole | Both the corrected CDF and its mass-limit implication include every threshold, including all three jumps. |
| T32 | correct_whole | Unweighted balance updates, change by two, integer multiplier crossings and simultaneous-flip membership cases are all present. |
| T33 | correct_whole | Every corrected distinct-unit spillover clause, reciprocal product, source weighted mean and B1 formula is present. |
| T34 | correct_restricted | The half-difference identity, endpoint and two-arm bounds, k>=2 and Lemma A17 remain. Both first-moment links and the weighted proof-chain equalities are expressly omitted. |

There is no target-level omission to justify. Unused helper rows in the record do not constitute omitted claims; the stated conclusions were assessed directly from the Challenge and Defs rather than inferred from those row names.

## Definition and truth checks

All marginal or conditional denominators used substantively are positive under their local hypotheses. In T18, incoming includes self, the count restriction gives `r=incoming-1<=min(m,n-m)-1`, and every count probability in a ratio is positive on the quantified range. The zero-count case is separate. The natural subtractions in the hypergeometric laws therefore have their intended integer values.

The Hajek zero-arm convention is irrelevant on the supported assignments used here: balanced complete and paired designs with positive even n have both arms nonempty. The real suprema used for mixing and graph quantities have nonempty bounded domains. Three-point variables can be represented by their finite distributions without losing the probability identities being audited. T23's integrability premise rules out reliance on the Bochner integral's default value for nonintegrable functions.

The supplied-minimizer premise in T27 is a genuine finite optimization condition, not the desired mass limit as a hypothesis. Its explicit nonvacuity instance has zero error. For T22 the fair one-source model and uniform regularity bound control baseline sizes; conditional on the source bit, the remaining contributions to BER are independent. After the stated normalization, the source fluctuation is bounded by a constant times `h/[n+h(h-1)]`, and the residual variance by a constant times `n/[n+h(h-1)]^2`. Both vanish as n grows, uniformly over 1<=h<=n.

For T23, the complete-design variance integrated over independent baselines is `4 Var(X_i+u_i)/n=58/(3n)`. In the paired design, each adjacent uniform-[0,3] order-statistic gap has squared expectation `18/[(n+1)(n+2)]`; independent noise differences have variance `49/6`. Substitution into `4/n^2` times the sum of squared within-pair baseline differences gives the stated `49/(3n)+36/[n(n+1)(n+2)]`.

## Verification evidence

* `scratch/Check.lean` imports only the Defs and compiled successfully with `/home/ubuntu/sap/tools/sap-lean`. It constructs an actual two-unit probability law, complete and paired designs, positive marginals, regularity, incoming-count hypotheses, a mean-zero three-point law and actual empiricalBias examples. It contains no admissions and does not import Challenge stubs.
* `scratch/Parse.lean` compiles the T25 parsing equality and counterexamples. It also checks the scope of the other suspect sums with explicit binders; `scratch/Parse.log` records elaborated definitions. The raw subtraction after a sum occurs only in empiricalBias among the affected definitions, and its uses in the audited package are confined to T25.
* `scratch/check_finite.py` independently enumerates finite assignments with rational arithmetic. Results are in `scratch/finite-results.json`: T18 count/vector ratios through n=10; T19's six-unit fixture; all 4096 four-unit indicator arrays for T20; T21's exact aggregates; 42 finite one-source instances for T22/T33; balanced support/bias/MSE identities at n=2,4,6,8; and all four-unit balance-flip cases for T32. Finite enumeration supports the audit and is not claimed as a general proof.
* Every target has an explicit instance or construction in `findings.json`, including the study, integrability and supplied-minimizer hypotheses.
* Both requested JSON files were parsed with Python, and their target/theorem coverage was checked against all 17 entries of `claims.json`.
