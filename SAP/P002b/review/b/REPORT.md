# Palomar statement audit: P002b

15 targets were audited. There are 13 Challenge theorem stubs and two omissions.

| Verdict | Count | Targets |
| --- | ---: | --- |
| correct_whole | 10 | T16, T17, T18, T19, T23, T24, T25, T27, T29, T30 |
| correct_restricted | 2 | T20, T22 |
| restriction_inaccurate | 1 | T26 |
| omission_ok | 1 | T21 |
| omission_questionable | 1 | T28 |
| not_faithful | 0 | |
| vacuous | 0 | |
| false | 0 | |

There is one major issue and one minor issue. T26's mathematical statement is
correct and covers its canonical target; its restriction classification needs
correction. T29 and T30 are counted as correct complete **refutations**, as the
record declares. They do not certify the positive printed coverage assertions.

## T28: omission_questionable — major

The record's reason for omission contradicts the specified target. It rejects
`AronowAudit.P002.Wave1.algorithm_correctness_paper` because the row concerns
corrected interval-index pairs, while the quoted algorithms have shifted Step 5
indices. But `claims.json`, P002-T28, `canonical_claim.note`, explicitly says:

> formalize Algorithm 2 with the pairs as Step 4 records them, in the corrected form of P002-T22

Thus the target already uses `([e_{k-1}, e_k], m_k)`. The printed indexing slip
does not justify rejecting a theorem about those corrected pairs. The available
files do not expose the cited supporting row, so its full sufficiency cannot be
certified here; its stated rejection reason is nevertheless wrong.

No Challenge theorem exports T28, including its no-intersection branch and both
covariate settings. T22 and T23 require a nonempty crossing list, so those stubs
do not supply the empty-list branch. That branch has admitted instances: with
one simulation equal to the observed assignment, the observed and simulated
curves coincide, their denominator may be everywhere positive, and the returned
Monte Carlo confidence set is all of R.

**Fix:** reassess the cited row against the corrected target and export the full
T28 algorithm-correctness statement, including the empty-crossing case. If some
part remains unavailable, identify that actual limitation and disclose it
precisely. Do not cite the already corrected indexing slip as the reason.

## T26: restriction_inaccurate — minor

The record and Challenge docstring label this theorem restricted because it
omits the introductory description that the confidence set is generally a
finite union of intervals. However, `claims.json`, P002-T26,
`canonical_claim.note`, explicitly says:

> The first sentence of Remark 4 (the set is 'generally a finite union of intervals') is descriptive and not part of the target.

The theorem retains all the target's algebraic assertions (a)-(c). Its nonzero
receipt-contrast guard on the IV product identity creates no further restriction:
full-rank arm designs give a full-rank instrument design, and invertibility of
the IV cross matrix forces the first-stage coefficient, equal to the adjusted
receipt contrast, to be nonzero. Thus the correct classification relative to the
specified target is **whole**.

**Fix:** change the T26 record to `decision: "whole"`, `restriction: null`, and
replace the restriction paragraph with a description of assertions (a)-(c).
The descriptive finite-union sentence can be identified as outside the target.
The exact replacement docstring is in `findings.json`; no theorem change is needed.

## Accepted restrictions and omission

T20 accurately discloses positive oracle design variance at every sequence index
and invertible control Grams for every assignment in every design support. These
conditions are stronger than the unrestricted remainder target, and they are
jointly satisfiable. For example, use sample sizes n=4(j+1), a centered equally
spaced scalar covariate in [-1,1], all compliers, outcomes x_i^2 in both receipt
states, and half the units assigned treatment. Constants
(delta,e,A,B,r)=(0,1/4,1,4,1/4) work. Every control subset contains at least two
distinct covariate values, and the population residual x_i^2-mean(x^2) is
nonconstant, giving strictly positive oracle design variance.

T22 accurately discloses existence of a completed finite run and correctness of
every completed finite run, without asserting termination of every prescribed
policy. Its nonempty-crossing assumption already belongs to this canonical
corrected target.

T21's omission is justified on the visible evidence: a theorem about an inner
limsup does not establish existence of the ordinary inner limit required by the
canonical claim. No substitute asymptotic theorem is silently credited as T21.

## Nonvacuity and refutation checks

Both scratch files import only `SAP.P002b.Defs`, use no Challenge theorem, and
contain no `sorry` or added axiom. They compiled successfully with:

```
/home/ubuntu/sap/tools/sap-lean scratch/Checks.lean
/home/ubuntu/sap/tools/sap-lean scratch/Algorithms.lean
```

`Checks.lean` establishes a real one-covariate, four-unit valid design with two
full-rank arms, a full-rank population Gram, centered covariates, and compliers.
It also verifies concrete members of Theta with A=1/2 and Xi with B=1/2. Thus the
small-moment model classes used below are not empty.

`Algorithms.lean` verifies joint data generation, both ARRegular conditions, and
the complete nonempty crossing list J=[-4] for an eight-unit example. Its curves
are g_0(beta)=(8/5)(beta+4)^2 and g_1(beta)=0. Their denominator polynomials are
5/128 and ((beta+4)^2+5)/128. At alpha=1/2 the zero curve supplies valid indices
for both algorithm gaps. The same example gives a crossing-free half-line and
a genuine finite-endpoint tie for T27. The concrete witnesses for every target
are recorded in `findings.json`.

For T29, fix (delta,r,A)=(0,1/4,1/2). The power-mean inequality gives

```
fourthNorm(centered w) >= sqrt((n-1)/n) * sqrt(popVar(w)).
```

For n>=2 the coefficient on the right exceeds 1/2, so both adjusted potential
arrays must be constant. Their constants coincide at the LATE; the observed
studentized statistic is zero and coverage is 1. For every real LATE and every
n>=2 there are all-complier constant-effect models with these constants and
n1=floor(n/2). Consequently the nested infimum is 1, which refutes the printed
universal equality to 1-alpha without using empty infima.

For T30, fix (k,delta,e,A,B,r)=(1,0,1/4,4,1/2,1/4). The same inequality and the
OLS intercept normal equation force both population residual arrays to vanish.
The covariate second moment is at least 1/4 and its fourth moment is at most 4.
Finite-population variance bounds imply, uniformly over this class, that either
arm's mean differs from zero by a fixed threshold or its second moment differs
from the population second moment by a fixed threshold with probability O(1/n).
For instance, an arm mean of absolute value below 1/4 and an arm second moment
at least 1/8 give a strictly positive arm Gram determinant. Hence the probability
of either arm being singular is O(1/n). On every full-rank assignment, the
observed arm regressions recover the population affine functions exactly, their
intercepts coincide at the LATE, and the observed adjusted AR statistic is zero.
Coverage is therefore at least 1-O(1/n). Centered equally spaced covariates,
all compliers, and constant additive outcomes give nonempty classes for every
LATE and every sufficiently large n. The nested infimum tends to 1. This refutes
the printed nominal limit without relying on undefined regressions or empty
classes.

## Audit order and validation

`reading.md` was saved before opening `claims.json`; its SHA-256 at that point was
`8cf6f9aef750d8716e61c75f892fd548225c92ae4a6885640d6228facaedb486`.
`claim-stage.json` was saved before opening `record.json`; its SHA-256 was
`cfc000c50ae1d8cb95e40d62e249c208c59c9404ccc08d4216ebed89fa544e31`.
Neither file was changed during the record stage. In particular, the step-2
“different” classifications for T29/T30 record their negative polarity relative
to the positive printed claims. The final judgments accept those exact
negations through the record's explicit refutation route, without revising the
step-2 readings.

The final JSON files were parsed with Python. Target coverage, theorem names,
required fields, verdict values, severities, and counts were checked against
`claims.json` and the Challenge declarations. No `lake` command was run; at most
two Lean checks ran concurrently. Original Defs, Challenge, claims and record
files were left unchanged.
