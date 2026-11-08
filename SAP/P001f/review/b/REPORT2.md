# Delta statement-referee report

19 targets reviewed: 18 theorem stubs and one omission.

| Verdict | Count |
| --- | ---: |
| correct_whole | 8 |
| correct_restricted | 9 |
| restriction_inaccurate | 1 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

Severity: 18 none, 1 minor, 0 major.

The output retains the original verdict vocabulary. Complete, correctly stated
refutations T96, T99 and T102 receive `correct_whole`; the partial refutations
T103 and T104 receive `correct_restricted`, because their omitted components
remain explicitly disclosed. These verdicts certify the stated refutations,
not the false printed assertions. The revised decision counts themselves are
5 whole, 8 restricted, 5 refuted and 1 omitted.

## Earlier findings: T113 partly fixed, not resolved

My only earlier adverse target was T113, with two related scope-description
issues. Its mathematical statement was already judged correct.

| Earlier issue | Delta status | Reason |
| --- | --- | --- |
| Regression integrability described as added relative to the supplied canonical target | Partly fixed | The record now says “Retains” and explicitly compares with the displayed formula; the docstring explains the distinction between the combined expectation and a separate nuisance moment. It still does not reconcile the canonical note. |
| Excluded nonintegrable regressions used to justify a restriction even though the canonical note calls integrability implicit | Not fixed | The cancellation example confirms the displayed-formula distinction, but does not override the supplied note. The report's claimed precedence rule is absent from the actual supplied brief. |

The remaining verdict is **restriction_inaccurate, minor**. No mathematical
falsehood or vacuity was found in the Lean type.

`claims.json:274`, the P001-T113 canonical note, expressly states that
integrability of the nuisance regression is implicit in case (ii). The revised
record (`record2.json:229`) and Challenge docstring
(`SAP/P001f/Challenge/Part1.lean:136-140`) instead justify restriction by comparison
with the displayed formula alone. The latter comparison is mathematically
correct, but it does not settle the discrepancy with the supplied canonical
interpretation.

The architect's response (`architect-report.md:198-206`) cites `brief.md:30` as
a precedence rule under which notes are diagnostic and cannot supply a
hypothesis. I read the actual supplied `brief.md`: line 30 belongs to the
claim-stage JSON schema; no such rule appears in that file or the user review
instructions. The response's assertion cannot itself introduce an otherwise
unsupplied governing rule. I therefore retain the minor finding relative to
the supplied canonical input, while acknowledging the different result under
a displayed-formula-only interpretation.

I independently checked the cancellation model. With independent uniform X,U
on (0,1), Y=0, and R=1 for X<1/2 and R=1_{U<1/2} otherwise, the true response
propensity is 1 below 1/2 and 1/2 above it. Both response arms are positive,
with probabilities 3/4 and 1/4, and MAR has a uniform lower bound. Set q=p and
m(x)=1/x for 0<x<1/2, zero elsewhere. The combined augmented score vanishes:
below 1/2, R=q=1 and the m terms cancel; above it m=0 and RY*=0. The displayed
outcome and score expectations are therefore genuine finite integrals, while
integral |m(X)| diverges. For example, every dyadic interval
(2^{-(k+1)},2^{-k}), k>=1, contributes at least 1/2 to that absolute integral.
No zero denominator or totalized integral is involved. This model lies outside
the Lean theorem's explicit nuisance-integrability premise. Whether it is
inside the canonical target depends precisely on the unresolved treatment of
the supplied note, rather than on any disputed calculation.

Fix: retain the Lean type. Relative to the supplied canonical note, label it
whole and disclose that the separate nuisance moment is explicit. Suggested
replacement text is in `findings2.json`; it also makes the alternative
comparison with the displayed formula explicit. Correct the report's citation
or supply the intended governing precedence rule before replacing the supplied
canonical interpretation. I have not changed `claims.json` or the old reports.

## Comparison with the saved blind reading

I reread all five Defs parts, both root modules and the Challenge part. Every
expanded theorem type, definition and quantifier scope agrees with `reading.md`.
No mathematical statement change was identified. The six changed target
records and corresponding documentation were audited as follows:

| Target | Revision | Delta judgment |
| --- | --- | --- |
| T96 | whole to refuted; false-claim notice added | Correct complete counterexample to finite-covariate ML-IPW/poststratification equivalence. The actual logit maximizer is identified, rather than arbitrary fitted weights. |
| T99 | whole to refuted; false-claim notice added | Correct complete counterexample to unnormalized ATT equality under conditional ignorability and both stated positivity bounds. |
| T103 | restricted to refuted; scope paragraph retained | Correct refutation of maximizer existence (A); consistency, efficiency and plotted-fit claims remain expressly omitted. |
| T104 | restricted to refuted; notice and partial scope clarified | Correct negation of the unqualified countable-mass equivalence. Printed (A) and the unqualified (B) imply that equivalence; the type therefore refutes printed content. It does not claim to isolate the directed failure, prove (A), or settle hedged (C). |
| T108 | whole to restricted; infinite-sequence premise disclosed | Correct restriction: all positive-size initial segments of an infinite iid sequence on the given space, rather than arbitrary finite iid families or a transfer theorem. |
| T113 | scope text expanded; type unchanged | Earlier finding partly fixed, with one minor canonical-scope discrepancy remaining as above. |

The T108 correction addresses the other referee's finding. I also correct my
own earlier `correct_whole` scope assessment: the saved reading already
quantified over an infinite sequence, whereas the canonical claim is for
arbitrary fixed finite iid families on their original space. A fair observation
on a two-atom space cannot be extended to a second independent fair observation
on that space: their joint-cell probabilities would need to equal 1/4, while
all events have probabilities 0, 1/2 or 1. A distributional change of space
might recover the usual finite result, but the stub does not supply it. The
revised docstring now states this limitation exactly.

T102's unchanged refuted label was rechecked as well: it negates distributional
well-definedness within the joint-density and support-differentiability domain,
and separately retains the chosen-estimator plug-in identity. It does not
substitute a singular joint law or a default derivative value.

The remaining whole decisions, T100, T106, T109, T110 and T112, retain all
canonical clauses identified in the first audit. The unchanged restrictions
T97, T98, T101, T107, T111 and T114 remain accurately disclosed. In particular,
T111 describes an explicit integrability premise rather than asserting that
otherwise valid models are newly excluded. The T105 omission remains reasonable
on the supplied evidence; the informal informational-completeness premise is
not given a mathematical predicate, and the omitted credited row is unavailable
here for independent inspection.

## Junk values, nonvacuity and checks

All earlier concrete witnesses remain valid because the mathematical types
match the saved readings. They are retained individually in `findings2.json`.
For the revised targets:

- T96 has positive cell sizes, positive treated/control counts and fitted
  probabilities strictly between zero and one. Every log argument and divisor
  is positive; the eighteen-unit sample can occur with positive probability in
  an iid population with correctly specified logit propensity and ignorability.
- T99 has normalized positive weights 3/4 and 1/4, conditioning probabilities
  1 and 1/4, and normalizing propensity mean 1/4.
- T103 uses n=1,y=1 and valid parameters (1,0,1,s,0,1,1), s>0. Likelihood
  1/(s sqrt(2 pi)) is finite at each admissible parameter and unbounded as s
  decreases to zero. The scale never equals zero.
- T104 admits t_k=4^{-(k+1)} and c_k=2^{-(k+1)}-4^{-(k+1)}, both strictly
  positive and summable, with sums 1/3 and 2/3. Their total is one and
  propensity 2^{-(k+1)} tends to zero despite equal positive supports. Ratios
  are required only in positive-total-mass cells; no nonsummable default sum
  or empty index type is used.
- T108 is populated by an infinite product of fair Bernoulli variables, with
  mean 1/2 and variance 1/4. Positive n and the separate moment hypotheses
  continue to guard division, variance and probability conversion.
- T113 still has included four-atom examples in both correctness branches:
  independent fair X,R, Y=X, p=1/2, with m=X,q=1/4 for regression correctness
  or m=42,q=1/2 for propensity correctness. The outcome and regression moments
  and a.e. denominator bounds ensure genuine integrability of the full score.

The existing definition-only `scratch/Check.lean` was rerun against the
refreshed compiled Defs using `/home/ubuntu/sap/tools/sap-lean`; it succeeded
with exit code 0 and no output. This checks the positive cell-mass instance,
finite-law normalization, estimator values, a real ConditionalMean example,
positive response probabilities, pointwise overlap, and the conditional-
independence predicate for a constant variable. There was only one Lean
process at a time. Python checked target coverage, all eighteen declared
name/type-constant pairs, all five refutation notices, and the parsing/schema
and counts of `findings2.json`. The analytic examples above were checked
mathematically, not represented as new Lean proofs. I did not inspect Solution
or Comparator files or treat the architect's external verification account as
an independent certificate.
