Revision 2 delta review: all 19 targets remain represented by the same theorem names. The current judgments are **7 correct_whole and 12 correct_restricted**, with no outstanding adverse verdicts.

| Verdict | Count |
| --- | ---: |
| correct_whole | 7 |
| correct_restricted | 12 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |
| Total | 19 |

All current severities are `none`.

The two earlier adverse findings were rechecked individually:

| Earlier finding | Revision status | Current judgment |
| --- | --- | --- |
| T62: undisclosed global Borel measurability of every statistic | **Fixed.** The record now says `restricted`, and the Challenge docstring states the extra premise and retained clauses. | correct_restricted |
| T65: allegedly inaccurate disclosure of added Gram invertibility | **Not fixed as requested; earlier finding withdrawn after correcting my claim reading.** The architect retained the statement, label and disclosure. | correct_restricted |

For **T62**, the mathematical theorem is unchanged. `Defs/Part2.lean:16` still requires `∀ n, Measurable (@T n)`. The new restriction in `record2.json` and `Challenge/Part1.lean` explicitly distinguishes global Borel measurability on all data vectors from measurability of the observed and resampled statistics. It accurately retains the square-tail equivalence, standard-error implication, exact sample-mean formula and consistency, and the all-size median case with a local density and positive moment. No new assumption or missing clause was introduced by this documentation change.

For **T65**, my first review relied on the sentence in `canonical_claim.note` saying Theorem 4.1.5 inherits invertibility. Re-reading the actual `canonical_claim.statement` and `definitions_needed` corrects that comparison: the statement separately quotes Theorem 4.1.5 with an OLS coefficient estimator and the three residual identities, without a rank premise; Definition 4.1.2 defines OLS by least-squares minimization. Gram invertibility belongs to the separately quoted inverse-formula theorem, 4.1.4. It is unnecessary for those residual identities. Consequently, placing invertibility before both conclusions genuinely restricts the quoted residual theorem, exactly as the existing disclosure says.

This distinction has a concrete witness, compiled in `scratch/Delta.lean`: use three design rows `(1,1)`, response `(-1,0,1)`, and coefficient vector `(0,0)`. The Gram determinant is zero, while

`RSS(c) = 2 + 3(c₀+c₁)²`.

Thus `(0,0)` is a least-squares minimizer; its residuals have mean zero, zero sample cross-products with both columns, and zero sample covariance with both columns. These valid cases of the quoted residual theorem are excluded by the Lean premise. The prior recommendation to relabel T65 `whole` is withdrawn. This correction cites the canonical theorem quotation and argmin definition; the original blind mathematical reading of the Lean theorem remains accurate. The architect's reference to a separate precedence rule is not stated in this workspace's `brief.md` and is not needed for this judgment.

I re-read all four revised Defs parts, both Challenge parts and their root imports against `reading.md`. **No mathematical definition, theorem type, hypothesis, conclusion, quantifier or theorem name changed.** Comparing `record.json` with `record2.json` finds only T62's decision and restriction changed. Its added Challenge restriction paragraph is the only change to the earlier theorem readings. The earlier artifacts are preserved as the review history.

The seven `whole` targets remain **T59, T60, T63, T67, T71, T72 and T75**. Their complete canonical mathematical content remains present: density/CDF properties, both kernel identities, the cluster mean formulas and WLLN, population homoskedastic moment and sandwich identities, the lasso properties, the positive-scale normal density and mean with explicit exclusion of the totalized zero scale, and the fixed two-point conditional-PMF mean calculation. CDF-domain applicability in T59 and the conditional-PMF mean calculation in T75 are the corresponding mathematical domain and defining expectation facts.

The twelve `restricted` targets are **T58, T61, T62, T64, T65, T66, T68, T69, T70, T73, T74 and T76**. Every restriction text matches its Challenge docstring and accurately describes the added hypotheses or omitted conclusions. The unchanged omissions enumerated in the first review remain disclosed. In particular, the regular-functional weak bootstrap conclusion remains dropped in T61, the normalized covariance-estimator identities remain dropped in T66, and full-rank uniqueness and the explicit coefficient formula remain dropped in T76.

There are **0 `refuted` labels and 0 omitted targets**. T58, T61 and T73 remain restricted versions of canonical counterexample claims. Their retained negative integrated density, bootstrap variance obstruction and failure of the independence product equation still address the specified printed readings; no positive canonical assertion has been relabelled `refuted` without a counterexample.

No new junk-value or nonvacuity issue arose. T62 uses positive sample sizes, a bounded-probability limsup and genuine finite resampling averages. T65's retained inverse is protected by nonzero Gram determinant. The previous checks of normalized kernels, the four-atom model, Gaussian scale, median convention and the full IID heavy-law hypotheses continue to apply to the unchanged definitions. Per-target concrete instances are retained in `findings2.json`, with the singular-design boundary witness added for T65.

Validation: both `scratch/Delta.lean` and the earlier `scratch/Check.lean` were compiled against the revised Defs using `/home/ubuntu/sap/tools/sap-lean`, importing no Challenge theorem. Their logs are `scratch/Delta.log` and `scratch/Check2.log`. Python parsed `findings2.json` and verified its schema, unique and complete coverage of the 19 canonical targets, theorem-name agreement, verdict/severity values and counts. It also checked all 19 revised record/docstring scope entries. No Solutions or external project files were consulted.
