# Palomar statement referee report: P001e

Audited all 19 targets and all 19 Challenge theorem stubs.

| Verdict | Count |
| --- | ---: |
| correct_whole | 7 |
| correct_restricted | 11 |
| restriction_inaccurate | 1 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity: 18 none, 1 minor, 0 major. No target is omitted. The three successful
counterexamples (T84, T90, T92) count as `correct_whole`; their printed claims
are refuted, while the Challenge propositions themselves appear true.

## P001-T91 — restriction_inaccurate, minor

The retained positive-mass identification theorem appears mathematically true
and has nondegenerate instances. Its restriction is incompletely disclosed in
both `record.json` and the Challenge docstring.

The canonical claim assumes independence of the potential-outcome process
indexed by doses in `Supp[D]`. In
[Defs/Part5.lean](/home/ubuntu/sap/tasks/CHFID-P001e-a/SAP/P001e/Defs/Part5.lean:63),
`hind` instead passes the entire function `t -> Y t omega`, with domain all real
numbers, to `CondIndependent`. The product measurable space has a measurable
evaluation coordinate at every real dose, including unsupported doses. The
restriction text discloses integrability at every real dose but does not
disclose independence of these additional coordinates.

These assumptions are different even with all the stated moment assumptions.
Take constant X and a fair Bernoulli treatment D with support {0,1}. Set
Y(0)=Y(1)=0, set Y(2)=D, and set every other potential outcome to zero. Then:

* The supported potential process is identically zero and independent of D.
* Every real-dose potential outcome is measurable and integrable; the observed
  outcome Y(D) is zero. Both queried doses 0 and 1 have probability 1/2.
* The full real-indexed process reveals D through its dose-2 coordinate. The
  dose-2 cylinder event and {D=1} each have probability 1/2, and their
  intersection has probability 1/2 rather than 1/4. Thus the stronger `hind`
  fails.

The relevant facts, including failure of `CondIndependent` for the full
process, compile in
[scratch/Nonvacuity.lean](/home/ubuntu/sap/tasks/CHFID-P001e-a/scratch/Nonvacuity.lean:89).
This is a scope/disclosure issue; it is not a counterexample to the retained
identification formula. The architect's `restricted` decision is appropriate,
but the declaration needs this additional strengthening. Its omission of the
continuous-dose clause is disclosed; the canonical scope note itself warns
that the evaluation-ready contract is stronger than bare process independence.

Replace the restriction paragraph in the Challenge docstring and record with:

> Restriction: Retains positive-mass identification and the two-dose contrast
> for countable measurable covariate cells. Requires a potential-outcome family
> indexed by all real doses: every coordinate is measurable and integrable, and
> the entire real-indexed process is conditionally independent of treatment
> given X, including coordinates at doses outside Supp[D]. This strengthens the
> canonical independence assumption, which concerns only supported doses. The
> observed diagonal Y(D) is also required to be measurable and integrable.
> Omits continuous-dose clause (b), its almost-everywhere observed-CEF bridge
> and continuity-based uniqueness, and the intermediate conditional mean of an
> unobserved potential outcome given both X and D.

## Audit and validation

The blind mathematical reading was saved in `reading.md` before opening either
JSON input. `claim-stage.json` was saved before opening `record.json`. No
step-2 relation was changed after reading the record. It records seven `whole`
relations and twelve `narrower` relations. The other eleven declared
restrictions accurately describe the retained conclusions, omitted content,
and substantive added assumptions.

The audit followed the SAP definitions into Mathlib's real-valued measure
conversion, Bochner integrals, conditional expectation, independence,
identical-distribution, infinite-sum and matrix-inverse definitions. No
retained conclusion was found to depend on an empty index type, infinite mass
converted to zero, division by zero, a nonsummable real sum, or an integral
silently evaluating a nonintegrable function to zero. Conditional-mean and
residual-normal-equation premises constrain the appropriate observed means and
residuals; they do not assume the potential-mean or imputation conclusions.

Nonvacuity witnesses are recorded for every target in `findings.json`.
`scratch/Nonvacuity.lean` imports only the Defs and compiles using
`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean`, with exit status zero
and only linter/deprecation warnings. It proves a nondegenerate Bernoulli
propensity model, positive queried dose masses, conditional independence of
deterministic processes, a positive-residual least-squares instance, a nonempty
saturated cell system, nontrivial residual-normal-equation data, positivity of
the four post-treatment conditioning cells, and the T91 scope distinction.
The infinite IID product witness for T88 and the genuine conditional-density
witness for T94 are given mathematically; their full hypotheses were not
compiled. No Challenge `sorry` was used in these checks.

Independent Python `Fraction` arithmetic reproduced the full-rank OLS fit
(determinant 7311), both printed-table estimates and their difference, both
corrected estimates, the hot-deck and matching donor choices and estimates,
the IPW and plug-in discrepancy, and the post-treatment conditional means and
contrast. Results are saved in `scratch/arithmetic-results.json`. The logistic
maximum is also supported by its zero score at (log(7/5),0) and strictly
negative definite Hessian for this full-rank design. Both output JSON files
were parsed and checked for one object per target and the required fields.

Only the supplied Defs, Challenge, claims and record, the permitted Mathlib
sources, and scratch checks were used as mathematical evidence. No Solution,
Comparator, or other formalization was read. No `lake` command was run; Lean
checks were run sequentially.
