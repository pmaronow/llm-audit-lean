# Declaration review

Both declarations are faithful to their recorded scopes. T7 covers the whole
corrected conditional claim; T8 is an accurately disclosed restriction.

The review followed the requested order. `reading.md` was saved after reading
both declarations, all closure source declarations, and the generated proof
declarations, before opening the claims or review history. `claim-stage.json`
records the independent claim comparison. The earlier findings and architect
report were then read before `record.json`. No step-2 conclusion changed.

## T7

`SAP/P024/Defs/WholeW1.lean:113` includes the exact positive event probability
for every K≥2 and 0<p<1, and connects the normalized conditional masses to the
actual independent Bernoulli parent. Its included `T7Statement`
(`SAP/P024/Defs/Part6.lean:30`) gives equal-size conditional unbiasedness for
arbitrary fixed individual outcomes, the allocationwise cluster-mean formula,
and the unequal-size witness. The final conjunct realizes that witness with
individual outcomes, not merely stipulated cluster averages. Every empty-arm
extension is allowed, and the conditional domain excludes those allocations.

This matches every clause of the canonical corrected component, including its
individual-level estimand. The canonical scope expressly excludes consistency
and the blocking recommendation; the historical complete-randomization note
adds no requirement. The counterexample supports the canonical assertion that
bias is possible. The whole label and current docstrings are accurate.

## T8

`SAP/P024/Defs/WholeW3.lean:15` uses actual design propensities and observed
outcomes in the Horvitz–Thompson estimator. The raw block means use the observed
arm counts through `clusterDIM`, and the weights are the randomized population
shares. `T8WholeStatement_W3` at line 38 proves the allocationwise identity
and both unbiasedness conclusions under fixed interior quotas and actual common
block marginals. It assumes neither uniform joint assignment masses nor
independence across blocks.

These design conditions narrow the canonical statement and definitions; the
historical note cannot make them canonical assumptions. The current record
correctly labels this restricted (`record.json:21`) and states the precise
restriction at line 23. Both the Challenge docstring at line 82 and the statement
docstring at line 25 now identify these as additional assumptions. Both earlier
T8 issues are fixed; no earlier issue was supplied for T7. The old W1 T8
counterexample declaration is outside this target's statement closure and is
not the proposition being reviewed.

## Definitions, boundaries, and checks

All statistical quantities are finite real sums. Positive cluster sizes,
proper nonempty allocations, positive conditioning mass, and T8's interior
quotas and actual marginals exclude division-by-zero conventions where means
or inverse-probability terms are used. No infinite integral, extended-real
conversion, or empty-extremum convention contributes to either statement.

Two scratch files compiled successfully with `sap-lean`:

- `scratch/PrintClosure.lean` prints every generated proof declaration in the
  closure; these supply only validity certificates and small typeclass facts.
- `scratch/Check.lean` constructs all equal-size T7 hypotheses at p=1/3 with
  nonconstant individual outcomes and independently checks the conditioning
  masses and conditional unbiasedness for every extension. It also computes
  the unequal-size witness's effect 2/3, estimates 0 and 1, and conditional
  mean 1/2 from the individual population. Its T8 instance has two four-unit
  blocks with quotas 1 and 3, actual propensities 1/4 and 3/4, dependent
  assignments across blocks, varying individual outcomes, and effect 2; it
  verifies all hypotheses together, the identity, and the HT expectation.

The scratch checks use definitions and elementary calculations, without
invoking T7 or T8 as proof steps. The supplied Comparator certification is the
basis for theorem proof validity; this review concerns statement fidelity.
`findings.json` contains exactly the two requested declarations, with the
fingerprints copied from `closure.json`, empty current-issue lists, and the
two earlier T8 issues recorded as resolved.
