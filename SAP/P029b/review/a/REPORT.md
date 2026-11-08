# Statement referee report

13 targets; 12 Challenge theorems. No false, vacuous, unfaithful, or inaccurately
disclosed theorem statement was found.

| Verdict | Count | Targets |
| --- | ---: | --- |
| `correct_whole` | 3 | T20, T23, T25 |
| `correct_restricted` | 9 | T14, T15, T16, T17, T18, T19, T21, T26, T27 |
| `omission_ok` | 1 | T22 |
| `restriction_inaccurate` | 0 | |
| `not_faithful` | 0 | |
| `vacuous` | 0 | |
| `false` | 0 | |
| `omission_questionable` | 0 | |

Severity: 13 none, 0 minor, 0 major. There are no items requiring a correction.

## Comparison with the record

The restricted decisions agree with the independent claim-stage reading. In
particular, T14 drops the entire maximum-likelihood characterization, T17 drops
the general additive-factor formulas, and T19 retains the pointwise simulation
algebra while dropping the probability laws. The corresponding docstrings state
these limits. T15 and T18 also disclose their omitted conventions and generality.

T16, T26 and T27 explicitly add almost sure eventual definedness of sample ratios.
This is an additional assumption: convergence of score errors in probability
does not by itself give eventual definedness along almost every draw sequence.
The docstrings disclose this assumption, along with the stronger score consistency
and other regularity conditions. T21's refutations match the printed joint
implications; its restricted true constant-effect component and the use of marginal
complier-indicator independence are also disclosed.

T20 and T23 faithfully refute the printed claims identified by their canonical
targets. T23 concerns the package's exact observation-weight fitting contract;
its statement does not purport to refute the article's bootstrap recommendation
or predict a numerical solver's output. T25 covers its full canonical formal
claim.

T22's omission is acceptable on the visible evidence. The record describes only
an arbitrary-array expansion of RMSE with a supplied benchmark of 5; that helper
does not establish the homogeneous design's target or connect the historical
estimators to the scoring rule. The canonical claim expressly excludes asserting
the printed Monte Carlo numbers, and the historical arrays are unavailable here.
The homogeneous-effect and scoring-rule content is formalizable, but no such
substantive connection is present in the reported available row. The omission
does not claim that the target is intrinsically unformalizable.

No claim-stage verdict was changed after reading the record.

## Definedness and nonvacuity checks

The finite laws used in the examples are genuine nonnegative normalized laws.
The binomial arm sizes are positive, and the count indices ensure that `n-k`
does not use unintended truncated subtraction. No empty observation or parameter
domain is needed for the likelihood result.

Positive profile mass, positive compliance, and randomized assignment make all
received-treatment events in the ignorability refutations have positive mass.
In T16's finite covariate sum, null profiles have zero outer weight; at positive
profiles overlap ensures positive complier mass. The convention for a conditional
mean at a null profile therefore does not supply a substantive conclusion.

For T27(a), overlap is unnecessary. The score versions imply nonnegative scores
almost everywhere, and the density clips only irrelevant exceptional values.
Moreover, writing `p=P(C)>0`,

`integral |m| dnu_C = E[c(X)|m(X)|]/p <= E[1_C |tau|]/p < infinity`.

Thus its LATE integral does not exploit Mathlib's zero value for a nonintegrable
Bochner integral. In the overlap components, bounded inverse scores and integrable
potential outcomes likewise keep all weighted population integrals integrable.
Measurability ensures the comap sigma algebra is a subalgebra and the pushforwards
have their ordinary meaning.

A concrete common witness for the infinite-sample hypotheses is an infinite
sequence of independent fair assignments, with constant covariate, all units
compliers, potential outcomes `(0,1)`, oracle scores and estimates equal to 1,
and cutoff 1. Both assignment values appear eventually almost surely, and then
every relevant first stage is exactly 1. This satisfies the additional ratio
hypotheses as well as independence, overlap, version, and quantile conditions.
This infinite-product witness is justified mathematically; a full Lean instance
of `ICSWConditions` was not compiled.

Both scratch files compiled successfully through the required wrapper:

- `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`
- `/home/ubuntu/sap/tools/sap-lean scratch/PopulationCheck.lean`

They import only `SAP.P029b.Defs`. The first checks the finite-law IV models,
conditional-mean counterexamples, a strictly positive binomial bias, an interior
receipt parameter vector, a defined nonempty sample, and a type-7 quantile
instance. The second checks a probability-measure IV instance and the conditional
score/effect versions. Exact rational finite-law countermodels for the two T21
implications, and a corroborating evaluation of the T23 objectives, are saved in
`scratch/finite-evidence.json`; check metadata is in `scratch/validation.json`.

The restrictions do not assume their conclusions. Their nonvacuity witnesses and
target-by-target judgments are in `findings.json`. These checks assess statements
and examples; they do not inspect Solution or Comparator proofs.

The required order was maintained: `reading.md` was saved before opening the
canonical claims, and `claim-stage.json` was saved before opening `record.json`.
