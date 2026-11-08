# P001e delta referee report

All 19 targets pass the statement review. The one earlier actionable finding
is **fixed**; none is partly fixed or not fixed. No new issue was found.

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

All severities are `none`. There are no omitted targets. As in the first
report, a complete, successful refutation receives `correct_whole` in the
findings schema, which has no `refuted` verdict. Thus these counts correspond
to the architect's **4 whole, 12 restricted, 3 refuted** decisions.

## Earlier finding: P001-T91 — fixed

The earlier finding was an incomplete disclosure of an added hypothesis:
`hind` assumes conditional independence of the entire real-indexed
potential-outcome process, whereas the canonical claim assumes independence
only of the process on supported doses. Independence of unsupported
coordinates does not follow from all-dose integrability.

The revised
[Challenge docstring](/home/ubuntu/sap/tasks/CHFID-P001e-a/SAP/P001e/Challenge/Part1.lean:73)
and `record2.json` now explicitly disclose:

* measurability and integrability of every real-dose coordinate;
* conditional independence of the whole real-indexed process, including
  coordinates outside `Supp[D]`, and its strengthening of the canonical premise;
* separate measurability and integrability of the observed diagonal `Y(D)`;
* countable measurable covariate cells and the retained positive-mass formulas
  and two-dose contrast;
* omission of continuous-dose clause (b), its observed-CEF bridge and continuity
  argument, and the intermediate conditional mean given both X and D.

The new restriction string exactly matches the replacement proposed in the
earlier `findings.json`, after removing its `Restriction:` prefix. The docstring
and `record2.json` agree. The unchanged theorem is appropriately labeled
`restricted`, and its disclosure is now accurate and complete.

The architect's account of this finding is correct. Its discussion of replacing
unsupported coordinates by zeros does not silently equate the supplied process
with that replacement. No further statement change was needed to repair this
disclosure defect.

## Comparison with the saved blind reading

I read all six revised Defs parts, both Challenge files, `record2.json`, and
`architect-report.md`, and compared every expanded theorem with its section of
`reading.md`. No mathematical change was found in any of the 19 theorem types,
their hypotheses or conclusions, or their shared definitions. T91's restriction
paragraph is the only statement-description change found. Comparing the two
records confirms that only T91's restriction field changed; all decisions,
theorem names and row selections remain the same.

The following table records the label checks for every target, including
unchanged statements.

| Target | Revised decision | Assessment against canonical claim |
| --- | --- | --- |
| T77 | restricted | Function-space domain and finite nonnegative codomain retained; Gaussian evaluation and above-one example explicitly omitted. |
| T78 | restricted | Joint maximum and fitted scale retained; intercept residual centering and centered variance formula explicitly omitted. |
| T79 | restricted | Fitted probability law and corrected lower-orthant formula retained; population identity, PMF/PDF realizations, common ML parameter and functional construction explicitly omitted. |
| T80 | restricted | Bounds, interval attainability and both six-unit values retained; pointwise support strengthening and omitted conditional-mean endpoint formulas disclosed. |
| T81 | whole | All eight distances, both nearest donors, second-nearest comparison and gap, completed vector and mean are present. |
| T82 | whole | Bounded propensity version, conditional probability/mean equality, impossible-range equivalence and the erroneous-threshold tautology are all present. |
| T83 | restricted | Correct MAR reweighting identity retained; pointwise binarity and positivity strengthening disclosed. |
| T84 | refuted | Fixed logistic sample has the required unique ML fit, fitted probability 7/12, unequal IPW and plug-in estimates 3/7 and 5/12, and difference 1/84. |
| T85 | restricted | Grouped difference, necessary-and-sufficient saturation criterion and stabilized equality retained; omitted per-unit grouping and unit-outcome formulation disclosed. |
| T86 | restricted | One-unit conditional and unconditional mean-one facts and reciprocal bound/equality case retained; pointwise premises and omitted sample/asymptotic material disclosed. |
| T87 | restricted | Stable-outcome branches and MAR identification retained for a supplied respondent version; positivity, version integrability and omitted construction/numerical fit disclosed. |
| T88 | whole | Both endpoint formulas, sharpness, inclusion, width, finite-sample unbiasedness and convergence in probability are present under the stated IID and almost-sure support assumptions. |
| T89 | restricted | Randomization, zero effect, positive cells, repeated mass, conditional means and adjusted contrast retained; omitted full PMF and separate probability witnesses disclosed. |
| T90 | refuted | Uniform-dose zero and spike processes have equal observable laws and unequal effects at both specified dose pairs. |
| T91 | restricted | Unchanged positive-mass identification statement; all-real-process and diagonal premises now explicitly disclosed, together with the omitted clauses. |
| T92 | refuted | Actual full-rank OLS fit uses the data-table covariate 10; evaluating the printed tables at 9 yields the stated unequal estimates and nonzero difference. |
| T93 | restricted | Both imputation identities under residual normal equations and the corrected six-unit fit retained; omitted general OLS derivation and population identification disclosed. |
| T94 | restricted | Both binary population means and estimator formulas retained under supplied integrated conditional means; pointwise overlap, integrability and omitted density-to-mean derivation disclosed. |
| T95 | whole | All opposite-arm donors, second-nearest comparison and gap, completed columns, their means and contrast 7/6 are present. |

The three refutations address the printed readings. T84 concerns arbitrary
finite-support samples with a fitted binary-choice propensity, so it need not
refute the saturated-cell equality. T90 concerns continuous-dose identification
without continuity; its deterministic processes satisfy independence and all
moment conditions, and positive uniform density does not identify a value at a
null singleton. T92 concerns the literal inconsistent tables; it does not
refute the corrected normal-equation identity. Each refutation retains the
explicit opening sentence that the printed claim is false.

All twelve restriction strings in `record2.json` were also checked mechanically
against their Challenge docstrings. The four `whole` labels retain every clause
of their canonical mathematical claims. There is no new omission or mislabeled
refutation.

## Junk values, nonvacuity and verification

The description change introduces no new mathematical hypothesis or default
value. The nonvacuity witnesses from the first review continue to apply to all
19 unchanged statements and are recorded individually in `findings2.json`.

For the newly explicit T91 scope, take the fair Bernoulli probability measure
on Bool, constant X, treatment D equal to the true indicator, and
`Y(t,omega)=t` for every real t. The entire process is deterministic, every
coordinate is measurable and integrable, and the observed diagonal equals the
bounded measurable D. Query doses 0 and 1; both cells have mass 1/2. Hence even
the full real-indexed premises have a nondegenerate instance.

The selected-dose cell denominators are positive in every positive-mass
covariate cell. Zero-mass covariate cells are explicitly guarded out of the
standardization. Countability and integrability of the selected potential
outcomes justify the real sums: the sum of absolute weighted conditional means
is bounded by the corresponding absolute first moment. Integrability of the
observed diagonal also makes its cell integrals legitimate. The conditional
expectations in the independence premise have a subordinate conditioning
sigma-algebra, finite trimmed measure and bounded measurable indicators. No
zero-division, nonintegrable-integral or nonsummable-sum convention supplies the
retained identification conclusion.

The other previously checked safeguards are unchanged: positive sample sizes,
positive normal residual sum and scale, normalized fitted laws, positive grouped
cell denominators, the stabilized denominator-one conclusion, positive
post-treatment conditioning cells, nonsingular concrete OLS design, and finite
inner model integrals where evaluated.

I reran
`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean` against the refreshed
Defs. It exited successfully, with only linter/deprecation warnings; output is
in `scratch/lean-check2.log`. This includes the T91 nonvacuity components and
the earlier supported-process versus full-process counterexample. It imports
only the Defs and uses no Challenge stub. Existing exact arithmetic evidence in
`scratch/arithmetic-results.json` applies to the unchanged numerical data.

`findings2.json` parses with Python and contains exactly one object per target,
with the same schema as the first findings file. The original reading and
first-round outputs were preserved. No Solution, Comparator, or source outside
the permitted audit inputs was inspected for this delta review; the architect's
external proof-certification account was not used as evidence of statement
faithfulness. No `lake` command was run, and only one Lean process ran at a time.
