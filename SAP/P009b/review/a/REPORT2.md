# Delta statement review

The earlier major T25 finding is **fixed**. All three linked issues are fixed; none is partly fixed or unfixed. No new adverse finding was identified in the revised statements, restrictions or decision labels.

| Finding verdict | Count |
| --- | ---: |
| correct_whole | 8 |
| correct_restricted | 9 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

All 17 severities are `none`. The architect's revised decision counts are independently accepted: **7 whole, 7 restricted, 3 refuted, 0 omitted**.

`findings2.json` uses the same verdict schema as `findings.json`, which has no `correct_refuted` value. Its `correct_whole`/`correct_restricted` verdicts describe coverage of the **canonical target**, including a canonical counterexample target. Thus T19 has `correct_whole` because its full canonical counterexample is present; T21 and T23 have `correct_restricted` because their counterexamples retain disclosed exclusions. Their accepted architect decision is `refuted` in all three cases. This does not relabel any printed assertion as a whole positive theorem.

## Earlier finding: P009-T25

| Earlier issue | Status | Revised evidence |
| --- | --- | --- |
| The definition subtracted one after summation. | Fixed | `SAP/P009b/Defs/Part2.lean:82` now reads `(∑ r, (estimates r - 1)) / (R : ℝ)`. The parentheses put subtraction inside the summand. |
| R=2 and R=50000 constant-one samples gave nonzero reported bias. | Fixed | Both signed and reported bias are now zero at both replication counts. Fresh Lean checks prove these exact values. |
| The `whole` decision and docstring claimed the canonical statistic despite the different definition. | Fixed | The definition now represents the canonical statistic for every positive R, and the docstring explicitly displays the sum of estimate-minus-one. The population clauses and sign-loss example remain correct. |

The revised definition expands to

`empiricalBias(R, estimates) = R⁻¹ Σr (estimates_r − 1)`.

For every positive R it also equals `(Σr estimates_r)/R − 1`. This general identity is compiled in `scratch/DeltaBias.lean`, so the repair covers arbitrary samples and replication counts. Constant-zero and constant-two samples have errors −1 and +1 with identical reported magnitudes for every positive R. The heterogeneous sample `(0,2)` has signed and reported bias zero.

The positive-R hypothesis makes the denominator nonzero. All sums are finite real sums. The population clause still has the same balanced complete-or-paired full-interference hypotheses and the same concrete nonempty two-unit instance. The architect's account of the original defect and its repair agrees with the revised source.

## Comparison with the saved reading

I reread every revised Defs and Challenge part and compared their expanded mathematics with `reading.md`, including its postblind T25 correction. T25's empirical statistic is the sole mathematical change found. The remaining expanded theorem statements match that reading. T19, T21 and T23 additionally have changed decision labels and refutation prefixes; T25's docstring displays the repaired statistic. The round-1 reading and findings were preserved.

| Target | Revised decision | Finding verdict | Delta assessment |
| --- | --- | --- | --- |
| T18 | whole | correct_whole | Unchanged. Includes both hypergeometric laws, zero case, exact ratio, scalar chain and supported-vector bound. |
| T19 | refuted | correct_whole | Mathematics unchanged; refutation label accepted. The complete six-unit counterexample and all interference/witness details are present. |
| T20 | restricted | correct_restricted | Unchanged. Pointwise inequalities and endpoint retained; all omitted aggregate-chain links and indicator-array presentation are disclosed. |
| T21 | refuted | correct_restricted | Mathematics unchanged; refutation label accepted. Exact aggregate discrepancies remain, with pairwise enumeration omitted and convergence expressly excluded. |
| T22 | restricted | correct_restricted | Unchanged. Aggregate formulas and corrected-centre convergence retained; individual covariances, printed-centre convergence and regimes omitted as disclosed. Common regularity with q≥4 remains explicit. |
| T23 | refuted | correct_restricted | Mathematics unchanged; refutation label accepted. Sampling-integral counterexample retains explicit integrability and all previous exclusions. See the printed-reading check below. |
| T24 | restricted | correct_restricted | Unchanged. Exact finite full-interference exception retained for both estimators/designs; blanket empirical assertion and Monte Carlo certification excluded. |
| T25 | whole | correct_whole | Definition repaired. Every formal caption and population-bias clause is now faithful; the general replication-count domain is preserved. |
| T26 | restricted | correct_restricted | Unchanged. Supplied-exponent coefficient and normalized limit retained; boundedness, maximal-order selection and separate specializations omitted as disclosed. |
| T27 | restricted | correct_restricted | Unchanged. Atom/approximation statements and supplied-minimizer conclusions retained; minimizer existence, separate exponential limit and heavy-atom example excluded. |
| T28 | whole | correct_whole | Unchanged. Mean identity, finite centering criterion, eventual distance/CDF clauses and failure of the reversed inequality are all present. |
| T29 | restricted | correct_restricted | Unchanged. Natural powers only, with every moment-chain link and endpoint; non-natural orders are expressly omitted. |
| T30 | whole | correct_whole | Unchanged. Both corrected estimator identities and exact equality-or-zero characterizations are present. |
| T31 | whole | correct_whole | Unchanged. Finite CDF and mass-limit implication hold at every threshold, including the atoms. |
| T32 | whole | correct_whole | Unchanged. Updates, change by two, integer multiplier crossings and simultaneous-flip membership cases are all present. |
| T33 | whole | correct_whole | Unchanged. Corrected distinct-unit spillovers, reciprocal products, source weighted mean and B1 formula are all present. |
| T34 | restricted | correct_restricted | Unchanged. Half-difference, endpoint, two-arm and final bias bounds retained; both first-moment links and weighted proof-chain equalities omitted as disclosed. |

All nine non-null restriction texts occur verbatim in the revised Challenge docstrings, including the exclusions attached to the two partial refutations. Their content accurately describes the actual clauses and hypotheses. All seven `whole` decisions cover the canonical formal content; no canonical counterexample is labelled `whole` in `record2.json`.

## Refutation labels and the printed readings

**T19.** The printed equality identifies an existence indicator with a witness count. The fixed experiment gives `e_01=1` and witness count 3. The diagonal convention, off-diagonal interference schedule and symmetric fixed-point-free pairing match the canonical example after shifting unit indices by one. These combinatorial quantities are independent of the assignment law, so using the fair law does not evade the paired-design setting. The equality is refuted; the lemma's inequality remains valid.

**T21.** The stated fair one-source experiment gives `B2=1/3`, whereas the printed exact expression gives `2/3`. Its exact normalized expected variance gap is `−1/6`, whereas the printed exact centre is `−1/2`. These are the exact evaluations singled out by the canonical counterexample. The retained restriction explicitly disclaims refuting convergence, so the new introductory refutation prefix does not overstate the conclusion. Its denominators are positive: arm marginals 1/2, distinct-unit conditioning probabilities 1/4 and `n*dAVG=18`.

**T23.** The printed sentence says bias is negligible relative to variance for the simulation settings and sample sizes. Under the retained independent uniform baselines and balanced designs, the theorem supplies sampling-averaged signed bias −1 and the exact integrated design variances. At the printed sample size n=100, complete randomization has variance `58/300=29/150`, giving squared bias divided by variance `150/29>1`. This finite comparison already contradicts the printed negligibility summary; a separately asserted divergence limit is unnecessary for that counterexample.

The joint-distribution reading is also respected for a concrete instance of this model: balance and marginals 1/2 give design estimator mean zero at every fixed baseline, and EATE is one. Total variance therefore equates joint sampling-and-assignment variance with the integrated design variance in that instance. These are consequences of the supplied model; the T23 conclusion still omits a separately formalized joint-space identification, universal fixed-baseline clauses and divergence limit, exactly as disclosed. I do not count those omitted conclusions as present.

Nonvacuity holds at n=100 as well as at n=2. Take the uniform balanced complete law, sort covariates with index-based tie-breaking, pair adjacent ranks and use independent fair within-pair assignments. This gives a measurable paired-law family satisfying rank adjacency. On the compact sampling box, the twelve integrands are bounded piecewise polynomials and hence integrable. Thus the refutation does not depend on impossible ranking/integrability hypotheses or the default value of a nonintegrable integral.

## Fresh verification

* `scratch/DeltaBias.lean` imports only Defs. It checks the revised summand by definitional equality, proves the arbitrary-positive-R mean-error identity, checks both former counterexamples, demonstrates sign loss for every positive R, checks a heterogeneous sample, and constructs a positive-R caption instance. It also verifies the exact refutation comparisons, including the n=100 ratio.
* `scratch/DeltaNonvacuity.lean` recompiles the prior explicit two-unit law, complete and paired design certificates, positive marginals, regularity, incoming-count hypotheses and mean-zero three-point instance against the revised Defs. Its empirical-bias check uses the corrected value.
* Both files compile with `/home/ubuntu/sap/tools/sap-lean` and contain no admissions or Challenge imports. Their logs are `scratch/DeltaBias.log` and `scratch/DeltaNonvacuity.log`.
* Every target retains an explicit nonvacuity construction in `findings2.json`. The earlier finite counterexample calculations concern unchanged schedules and quantities.
* `findings2.json` was parsed with Python; its schema, all 17 target/theorem mappings, verdict counts and changed verdict were checked against `claims.json`, `findings.json` and `record2.json`.
