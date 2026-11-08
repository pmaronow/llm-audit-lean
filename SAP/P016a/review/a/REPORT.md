Audited 11 targets and 10 theorem stubs, in the requested blind / claim / record
order. The record did not change any saved claim-stage verdict.

| Verdict | Count |
| --- | ---: |
| correct_whole | 8 |
| correct_restricted | 2 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 1 |

Severity: 10 none, 1 minor, 0 major.

**P016-T5: omission_questionable, minor.** There is no associated theorem.
The record rejects an unused row because fixed empirical-margin invariance does
not refute a distribution-level information comparison. The canonical target,
however, explicitly asks for a refutation under its specified reading: an
asserted basic-SSR dependence on cross-group information beyond the two empirical
group margins. Rejecting one unseen row does not explain dropping that target.
The general margin-invariance clause already present in
[T2Statement](/home/ubuntu/sap/tasks/CHFID-P016a-a/SAP/P016a/Defs/Part3.lean:59), together with its design-dependence
identities and T1's two reference-distribution witnesses, supplies relevant
evidence. The original paper uses informal information-comparison prose; the
interpretation to be audited here is the explicit one in `claims.json`.
[Paper, p. 397](https://www.jakebowers.org/PAPERS/BowersFredricksonAronow2016PowerfulTestStatistic.pdf#page=3).

The proposed correction is to state and refute that interpretation explicitly:
there do not exist positive treatment/control groups and two outcome/assignment
pairs with equal group multisets but different basic RSS. This follows from T2's
universal margin-invariance conjunct. The docstring should distinguish this
assertion from an assertion that RSS is determined by the scalar KS value, and
retain T1/T2's evidence that both reference distributions incorporate assignment
design. This finding questions the omission rationale; it does not certify the
unseen rejected row, require a proof of the false printed claim, or claim that
the printed prose has a unique mathematical interpretation. Detailed proposed
statement and docstring text are in `findings.json`.

T4 and T6 are correctly marked restricted. T4 discloses its additional
common-bank-count and two-positive-SD hypotheses and the omitted application
procedure identifications. Its raw identity's bank-count condition is an added
theorem hypothesis, rather than a mathematical necessity for the raw identity
alone. T6 specifies across-unit sample variance with divisor n-1 and omits
identification with the actual application, regression/testing procedure and
empirical rates. Its claim is algebraic model consistency for the specified
class of g, without an assertion that g is the released exposure algorithm.

Verification artifacts:

- `reading.md`: expanded blind readings, including every SAP definition and
  the relevant Mathlib meanings and totalization conventions.
- `claim-stage.json`: ten verdicts saved before opening `record.json`.
- `scratch/Check.lean`: successfully compiled using
  `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`; imports only Defs,
  uses no `sorry`, and checks nonempty positive-group domains, bank support,
  nonempty positive-SD model instances with nonzero coefficients, raw-distance
  standardization on a two-assignment design, a normalized nonuniform law,
  and nonempty bounded-below least-squares ranges. No `lake` command was run.
- `scratch/check_witnesses.py` and `scratch/witness-checks.json`: 277 passing
  exact-rational checks, including regression minima certified by orthogonal
  residuals, both determinants and all seventy-assignment KS probabilities.

The four-unit matched bank contains some zero-SD assignments, so the positive-SD
assumption cannot be silently removed. The Lean nonvacuity check uses the
explicit nonempty design `{complete4(1)}`, where the sample variance is 1/48.
No empty index, zero denominator or unbounded-extremum convention establishes
any audited conclusion. These checks audit statement meaning and mathematical
plausibility; they do not replace the Solution/Comparator proof certification.
