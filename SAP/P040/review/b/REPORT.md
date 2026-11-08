Five targets audited: **4 correct_whole, 1 correct_restricted, 0 adverse findings**. All severities are `none`.

| Verdict | Count |
|---|---:|
| correct_whole | 4 |
| correct_restricted | 1 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

There are no items outside `correct_*` or `omission_ok` requiring correction. No target is omitted.

| Target | Theorem | Verdict |
|---|---|---|
| P040-T1 | SAP.P040.T1 | correct_restricted |
| P040-T3 | SAP.P040.T3 | correct_whole |
| P040-T2 | SAP.P040.T2 | correct_whole |
| P040-T4 | SAP.P040.T4 | correct_whole |
| P040-T5 | SAP.P040.T5 | correct_whole |

The blind reading was saved in [reading.md](reading.md) before opening `claims.json`. The comparisons in [claim-stage.json](claim-stage.json) were saved before opening `record.json`. The record agrees with every independent assessment; no step-2 verdict was changed. The canonical `statement`, `definitions_needed`, and standing assumptions determined the claim scope; historical notes and the record supplied no additional clauses.

T1's restriction is accurate and complete. The assertion omitted from canonical A4 is that the actual standard-normal .975 quantile belongs to [1.9599,1.9601]. The theorem retains the universal multiplier result throughout that range, both coverage calculations, the lower-bound failure probability, both arbitrary-rule obstructions, and the reconstructed endpoint arithmetic. Substitution of z=49/25 recovers A3. [The Challenge docstring](SAP/P040/Challenge/Part1.lean#L6) explicitly discloses this omission and identifies the result as a calibration counterexample under the added binomial model. It makes no claim to refute the printed nominal approximate-confidence interpretation. No docstring repair is needed.

T3 states the canonical passage's retained P1/P2 arithmetic. Its canonical statement expressly declines to attribute uniform exact finite-sample coverage to the article. Omitting the historical exact-coverage proposition, or its negation, therefore loses no asserted T3 clause. T4 directly witnesses the mismatch between the named normal reference and the reported numbers; T5 correctly treats Student-t as a computational reference without asserting an exact null distribution. The quoted interval, reference description, reported values, and significance threshold agree with the corresponding passages on pages 3–5 of the [paper](https://springerplus.springeropen.com/counter/pdf/10.1186/s40064-016-2303-5).

Independent verification is reproducible in [scratch/audit_checks.py](scratch/audit_checks.py), with results in [scratch/check-results.json](scratch/check-results.json). It compares every fixed data entry with canonical S6(d), recomputes all eight OLS/HC1 statistics using exact rational arithmetic, checks all reported rounding, and bounds the normal and Student reference integrals using alternating series, rational bounds for pi from Machin's formula, and integer square-root enclosures. The computed Gram determinants are 224 and 323086400; all eight actual HC1 variances are positive. The original ten-column adjusted design is used for its rank, while OLS inverts the full-rank nine-column design. Thus a singular inverse or division by zero contributes no result. The recorded degrees of freedom are 28 and 21, so natural subtraction does not truncate. The sales rows were checked against the supplied canonical data; the deposited archive itself was not accessed.

The same checks reproduce the mass at count 14, all Wald coverage/failure fractions, and all exact endpoint brackets and rounding. Checking the count classifications at both positive multiplier endpoints suffices for every multiplier between them because each Wald radius increases with the multiplier. The count set has 16 elements, and all its masses are strictly positive at p=4/5. At the boundary parameters p=0 and p=1, both replacement rules cover with probability one. The actual endpoint roots lie strictly between zero and one; rounded numbers are used only as reported approximations.

The uniform-coverage conclusion in T2 also has the correct general argument. At any fixed p in [0,1], nonnegative binomial masses sum to one. The counts with upper tail below alpha form an upper set; if nonempty its probability equals the upper tail at its least count and is below alpha. The counts with lower tail below alpha form a lower set with the analogous bound at its greatest count. A union bound with alpha=1/40 gives equal-tailed coverage at least 19/20; the single upper-tail rejection with alpha=1/20 gives the one-sided guarantee. This uses no assumed monotonicity in the unknown parameter. At the observed count, the derivative 210 p^13(1-p)>0 on (0,1), continuity, and the endpoint values supply root existence, uniqueness, and the stated interval identities.

[scratch/Check.lean](scratch/Check.lean) imports only the supplied Defs and checks concrete nonvacuity witnesses, positivity and normalization of the binomial masses at p=4/5, positivity of the stated variance/statistic constants, and interval integrability of both reference integrands. There are no circular or contradictory hypotheses in the Challenge statements: all five theorems assert closed conjunctions, and the internal conditional antecedents have explicit witnesses. Their definitions were traced to the Mathlib sources recorded in the blind reading. JSON validation covers both required JSON outputs and their complete one-to-one target/theorem mapping.
