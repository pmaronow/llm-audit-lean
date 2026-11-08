# P005-T8 omission review

Verdict: **omission_ok**. Severity: **none**.

The architect's reason accurately describes the available formal evidence.
`claims.json` has `no_lean: false` and one proved row, marked `ok`:
`AronowAudit.P005.Wave1.corrected_interacted_expansion_max_conditional`
(`CondP005T8T9Proofs.lean:711`). The architect acknowledges this row rather than
claiming that no proved row exists.

The row's statement, defined in `Literature/CondP002P005P006.lean:110`, has the form

```text
Tropp2011RowSampling →
  ∀ d m P, standingAssumptions d m P →
    eventual interactedRegular →
    (κ log(max(d,2)) → 0) →
    interacted remainder = O_p(sqrt(κ d/n)).
```

The additional premise is a universally quantified matrix row-sampling inequality,
independent of the population sequence. It is not a canonical or standing
assumption of T8. Its definition states a proposition; it does not prove it.
The proof genuinely uses this premise through `CondT8T9_tropp_finite`.
Lean inspection confirms that the credited implication depends only on the
standard axioms `propext`, `Classical.choice`, and `Quot.sound`; this does not
discharge its explicit premise. The row's `ok` status and the metadata about an
independently checked source likewise do not supply a Lean term proving that
premise.

No faithful restricted expansion follows by the allowed glue. Specializing the
population sequence or dimension leaves the independent premise in place.
Copying the conditional theorem into Mathlib-only definitions would still add
an unlisted universal sampling assumption, rather than retain an established
case or component of the canonical claim. Establishing that sampling result
would require a further proof. The logarithm equivalences already stated in T9
do not qualify as a distinct restricted T8 result under the task's exclusion of
restating another target. The audit's `finite_lemmas` add no claim components.

The corrected condition, estimator, and rate are accurately described by the
reason. No correction or additional Challenge statement is proposed.

Validation: `sap-lean scratch/Check.lean` succeeded for declaration, statement,
and axiom inspection. No new theorem was proved and no project source was
modified. `findings.json` was parsed and checked with Python 3 against the target
and fingerprint in `closure.json`.
