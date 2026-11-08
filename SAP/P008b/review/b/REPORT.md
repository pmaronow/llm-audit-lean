# Palomar statement referee report

14 targets; 13 theorem stubs.

| Verdict | Count |
|---|---:|
| correct_whole | 2 |
| correct_restricted | 10 |
| restriction_inaccurate | 1 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

Severity counts: none 13; minor 1; major 0.

## P008-T17 — inaccurate width wording, minor

The docstring at [Challenge/Part1.lean:16](/home/ubuntu/sap/tasks/CHFID-P008b-b/SAP/P008b/Challenge/Part1.lean:16)
says that circle tolerance gives the **clipped** radial band “of width twice
the tolerance.” This omits the condition `k <= d`. With `d=1,k=2`, the clipped
radial interval is `[0,3]`, of width 3, whereas `2k=4`. That calculation was
independently compiled in [scratch/Check.lean](/home/ubuntu/sap/tasks/CHFID-P008b-b/scratch/Check.lean).

The Lean statement itself is correct: [Defs/Part6.lean:31](/home/ubuntu/sap/tasks/CHFID-P008b-b/SAP/P008b/Defs/Part6.lean:31)
uses the clipped lower endpoint `max 0 (d-k)` and conditions the width conclusion
on `k <= d`, exactly as canonical T17(a) does. The architect's restricted
decision and its declared omissions of the polygon zero-buffer and archived
disk-branch identifications are sound. The issue is the docstring's overstated
description of the retained conclusion, not a false theorem.

Replace the summary sentence with:

> Circle tolerance gives the clipped radial band, whose radial width is twice
> the tolerance when k <= d; adjacent-buffer differences average the added
> cells up to the outer radius.

Keep the existing Restriction sentence. No theorem change is needed.

## Other record decisions

T16 and T19 correctly receive `whole`: both supply the canonical concrete
counterexamples with nonempty averages and treatment arms. T16 uses a different
rectangle realization of the same distance/outcome data, which the canonical
note expressly identifies as the data used by the example. The geometry and
all contrasts were checked independently with exact arithmetic.

The restrictions for T15, T18, T20–T23 and T25–T28 are accurate and disclosed.
In particular, T21 and T22 retain only printed numerical comparisons; neither
claims a calibrated statistical test. T23 retains only the population covariance
identity. T28 retains the audit's explicit sufficient consistency theorem,
including collection independence, without asserting the cited normality or
spatial-HAC error-control results. T26's cancelling witness concerns every
nonempty finite circle and makes no claim at empty circles.

T24's omission is justified on the material supplied. Its empirical forest-loss
event is undefined and the stated percentiles and statistic are not reconstructed.
An unrelated numerical sum outside `[-1,1]` cannot refute the interpretation of
these three reported numbers, which all lie inside that interval. This accepts
the omission, without endorsing the probability interpretation or the universal
identification of unnormalized AMR sums with probability changes.

## Procedure and checks

[reading.md](/home/ubuntu/sap/tasks/CHFID-P008b-b/reading.md) was saved before `claims.json` was opened.
[claim-stage.json](/home/ubuntu/sap/tasks/CHFID-P008b-b/claim-stage.json) was saved before `record.json` was opened.
No step-2 classification was changed after reading the record: two `whole`,
eleven `narrower`. The T17 finding concerns its prose disclosure, not a changed
reading of its proposition.

Definitions were followed into the permitted Mathlib sources. The paper check
used only its [public manuscript](https://arxiv.org/pdf/2106.15081), whose
pagination differs from the journal version. Its definitions of marginalization
over other nodes and its default Euclidean geometry agree with the supplied
claim text. `claims.json` remains the canonical comparison standard.

The final run of `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` succeeded
with no diagnostics. `python3 scratch/check_finite.py` succeeded with exact
rational results. Nonvacuity instances include positive-mass radius-1 circles,
a band with an actual separated second node, nonzero additive effects,
positive variance with omitted zero covariances, and a full consistency sequence
with nonzero target AMR. Details and the distinction between compiled checks
and mathematical reasoning are in [scratch/checks.md](/home/ubuntu/sap/tasks/CHFID-P008b-b/scratch/checks.md).

The general theorem statements were assessed mathematically, not reproved in
full. No Solution, Comparator or external audit proof was read. No `lake`
command was run, and Lean checks ran one at a time. Python validation confirmed
that both JSON outputs parse and that findings cover each target exactly once.
