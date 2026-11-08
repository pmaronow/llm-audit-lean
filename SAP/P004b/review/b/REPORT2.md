# P004b delta review

All earlier findings are fixed. No changed mathematical statement or new
statement problem was found when the revised Defs and Challenge were compared
with `reading.md`. Only the scope descriptions for T26 and T27 changed.

| Verdict | Count |
| --- | ---: |
| correct_whole | 1 |
| correct_restricted | 14 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity: 15 none, 0 minor, 0 major. There are no outstanding adverse items.
The architect's labels are 1 whole, 14 restricted, 0 refuted, 0 omitted;
these labels are appropriate for the canonical targets.

## Disposition of every earlier finding

The two flagged targets contained three specific disclosure issues. All three
are fixed, rather than partly fixed or left open.

| Target and earlier issue | Status | Revised evidence |
| --- | --- | --- |
| T26: canonical uniform quadratic spacing described as additional | Fixed | The restriction now calls C_b(1+s²) the canonical spacing bound. The canonical corrected T26 claim and `QuadraticSpacing` require the same uniform quantifier order. |
| T26: inherited metric setup described as additional | Fixed | The restriction now identifies the metric-distance setup as inherited from Appendix C, in agreement with standing assumption S8. |
| T27: omitted all-distance NED clause not disclosed | Fixed | The retained property now says “NED only at the analyzed distance d=1,” and the omitted clauses explicitly include W1's additional NED assertion at every other distance. |

The fixes appear both in `record2.json` and in the Challenge docstrings at
[Part1.lean:69](/home/ubuntu/sap/tasks/CHFID-P004b-b/SAP/P004b/Challenge/Part1.lean:69)
and
[Part1.lean:75](/home/ubuntu/sap/tasks/CHFID-P004b-b/SAP/P004b/Challenge/Part1.lean:75).
The architect-report account agrees with these changes. No mathematical
assertion was added to resolve either finding. Consequently T26 and T27
move from `restriction_inaccurate` to `correct_restricted`; the other
thirteen verdicts remain unchanged.

## Statement and label comparison

I reread all eight Defs parts, the Defs root, the Challenge part and root,
and compared their mathematical content with the saved blind reading.
The objects, hypotheses, quantifier order, guards and conclusions still
match that reading for every target. Comparing the two decision records
finds changes only to T26's and T27's restriction text. All fourteen revised
restriction strings match their current Challenge docstrings verbatim.

| Target | Decision and scope check |
| --- | --- |
| T16 | Restricted. The zero-distance rectangle witness, arbitrary-separation existence, and complete crowding count remain; the omitted positive-distance witness and subsidiary formulas remain disclosed. |
| T17 | Whole. The compact-node cutoff, point specialization D=0, C3 implication including the diagonal, failure without a diameter bound, polygon area/diameter count, and area-only crowding failure cover all canonical clauses. The count implies the stated uniform C4 consequence when the area and diameter bounds are fixed. |
| T18 | Restricted. Both corrected rates retain the disclosed zero extension on empty-arm assignments; the printed-formula witness remains omitted. |
| T19 | Restricted. Witness 1 has variance one and a genuine nonnormal standardized law. The cancelling-pair witness remains expressly omitted. |
| T20 | Restricted. The general bounded-degree CLT remains; its normalized version and estimator applications remain expressly omitted. |
| T21 | Restricted. The compact corrected node variance and finite SAH bound remain; the two numerical counterexamples remain omitted. |
| T22 | Restricted. The augmented variance and homophily consequence for deterministic fits remain. The grouped expression, omitted separate displays and witness, and lack of a fitted-IPW asymptotic assertion are disclosed. |
| T23 | Restricted. Corrected observational weights and the treatment sandwich entry remain; omitted quantile, event, label and homophily assertions are disclosed. |
| T24 | Restricted. The projection, leverage and sandwich identities remain; the degrees-of-freedom correction and other omitted clauses are disclosed. |
| T25 | Restricted. Corrected means, sum identity and shifted printed mean remain; conditional-expectation, numerical and separately written specialization clauses remain omitted. |
| T26 | Restricted. Its mathematical exterior-tail convergence statement is unchanged. The revised text now distinguishes inherited assumptions from added requirements accurately. |
| T27 | Restricted. The sparse witness is unchanged and still asserts NED only at d=1. The revised text now discloses the omitted all-distance clause accurately. |
| T28 | Restricted. The three guarded errors, bias bound and conditional guarded coverage remain. Invalid intervals still count as successes; the docstring discloses that weakening. |
| T29 | Restricted. The far-pair bound and corrected finite identities remain. The stronger spacing setup and omitted independent five-term V1 correspondence are disclosed. |
| T30 | Restricted. Positive support cardinalities, forced-coordinate marginalization and corrected class identities remain. The additional guards and omitted subsidiary assertions are disclosed. |

No target is labelled `refuted` in `record2.json`. T16, T19 and T27 already
have counterexample/refutation canonical claims, and each theorem retains
only part of that canonical claim, so `restricted` is appropriate. Their
refutations retain the same readings as in round 1: T16 concerns the offered
polygon sufficient conditions, T19 the printed CLT without the variance
condition, and T27 coverage under the explicitly identified nonvacuous
C_b(1+s²) reading of Appendix C spacing. They do not establish a false
positive canonical claim. No omission decision needs review.

## Junk values and nonvacuity

There are no changed mathematical statements requiring a new kind of
nonvacuity instance. Every prior instance remains applicable and is retained
in the corresponding `findings2.json` entry. I also rechecked the definitions
behind the revised scope descriptions:

* T26 still assumes positive finite region mass and integrability through
  `WellDefined`, interior p and positive bandwidths. Its exterior envelope
  uses a maximum of finitely many finite sums at every N>0; the N=0 prefix
  does not affect its limit. The earlier nonhomogeneous instance still
  works: singleton nodes at 0, 1, 6, 9, … on a line, counting measure,
  effects (1,−1,0,…), p=1/2, zero-distance averages, the uniform kernel,
  bandwidth N+1 and φ=1 on [0,1], zero elsewhere. This gives genuine
  positive average denominators and eventually zero exterior tails for
  every diverging radius sequence.
* T27 still establishes a positive-variance valid interval on `SparseGood`,
  whose probability tends to one. For N=10, the assignment with the first
  five nodes treated and its complement both have arm counts five. The
  HAC variances are respectively 4/125 and 1/500, both strictly positive;
  their squared studentized statistics are 125/256 and 125/16. Thus the
  first covers at ±2 and the second does not. The refutation does not
  depend on empty arms, division by zero or nonpositive interval variance.
* The other existing guards remain intact: T18/T28 zero the tested errors
  outside nonempty arms; T28 explicitly uses an implication event and
  guarded real quantiles; matrix assertions require positive arm counts;
  T30 has positive support counts and admissible natural subtractions.
  The positive-variance population example for T28's coverage branch
  remains in `findings2.json`, so that branch has satisfiable premises.

The existing Defs-only `scratch/Check.lean` was compiled again against the
refreshed package with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`.
It exited successfully; `scratch/check2.log` records only the existing unused
binder warning. This checks genuine arms, local neighborhoods, positive
conditional supports, a positive linearized variance and a positive-variance
valid interval. The unchanged finite-enumeration results from round 1 remain
applicable. One Lean process was used; `lake` was not run.

`findings2.json` has exactly one object per canonical target and uses the same
schema as `findings.json`. JSON parsing, target coverage, decision/theorem
names, docstring correspondence and verdict counts were checked with Python.
