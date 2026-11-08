# Round 4 statement review

All **14** targets were checked against the canonical `statement`,
`definitions_needed`, standing assumptions, and `record4.json`. Audit notes and
`finite_lemmas` were not used to add or remove clauses.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 5 |
| `correct_restricted` | 9 |
| `restriction_inaccurate` | 0 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 0 |
| `omission_questionable` | 0 |

Severity: **14 none, 0 minor, 0 major**. All five earlier adverse findings are
**fixed**; none is partly fixed or unfixed. No new adverse findings remain.

## Earlier findings

| Finding | Status | Current evidence |
| --- | --- | --- |
| Round 1, T6: separation scoped over the general matrix representation | Fixed, remains fixed | The representation requires only a nonnegative cutoff and both arms. Zero diagonal and separation are nested inside the HC0 specialization. The disclosure agrees. |
| Round 2, T5: unqualified printed-falsity claim | Fixed, remains fixed | The `whole` theorem and docstring identify the outcome-effect-range sufficiency reading; they do not claim to contradict the printed contribution-dependence guidance. |
| Round 2, T7: spatial refutation claimed without a spatial realization | Fixed, remains fixed | The decision is `restricted`, and all planar-realization omissions remain explicit. The theorem claims only the retained counting components. |
| Round 2, T9: archived-code result attributed too broadly to the article | Fixed, remains fixed | The decision is `restricted`; the disclosure identifies the transcribed archived-code correctness reading without attributing the printed intervals to that model. |
| Round 3, T8: empirical-output identifications omitted without disclosure | Fixed | The docstring and record explicitly omit the actual observed sum, actual percentiles, empirical comparison, application grid/unit weights, actual normalized estimate/target identification and reconstructed permutation outputs. |

The T8 repair retains the previous accurate geometric, integrability, finite
extremum, order-statistic and sampling-space limitations. In
[the extended disclosure](/home/ubuntu/sap/tasks/CHFID-P008a-a/SAP/P008a/Challenge/Part1.lean:101),
the three reported numbers are explicitly supplied rational constants. Thus
the theorem no longer appears to certify the empirical assertions in the
canonical corrected text. The docstring and `record4.json` agree.

## Changed theorem: T8

Source-hash comparison with round 3 identifies changes only in
`Defs/Part7.lean` and `Challenge/Part1.lean`. The sole mathematical change is
the added, unconditional numerical conclusion

    (-321 / 10000 : ℝ) < -19 / 625

in [T8's numerical block](/home/ubuntu/sap/tasks/CHFID-P008a-a/SAP/P008a/Defs/Part7.lean:82).
It states **−0.0321 < −0.0304**, restoring the explicit unscaled comparison
from canonical clause (c). The existing three division equalities and scaled
comparison remain unchanged. The new inequality is true: the right-hand side
minus the left-hand side is exactly 17/10000.

All other T8 conjuncts retain their saved reading: binary fixed-radius spatial
risk bounds and the AMR identity under the stated domain assumptions;
nonnegative normalized mixtures and common effect bounds; equal-weight and
constant-effect algebra; order and absolute-tail comparisons under positive
rescaling; sorted type-7 quantile rescaling; and the labelled companion sum
−4. No quantifier or hypothesis changed. Removing just the added comparison
reproduces the round-three Part7 source hash, so T7 and T9 in the same file
are unchanged as well. The exact source delta is in
`scratch/delta4-source.diff`.

The numerical comparison does not identify an empirical observed statistic or
permutation quantile; that limitation is now explicit. T8 therefore remains
`correct_restricted`.

Relative to the original `reading.md`, the mathematical changes are the T6
scope repair already reviewed and this added T8 comparison. The other saved
readings remain applicable.

## Labels and scope

The five `whole` targets remain T3, T5, T12, T13 and T14. They retain the
complete required spatial percentile counterexample, finite outcome-range
counterexample and replications, printed-grid incompatibility, corrected-grid
identities, and corrected AMR/product identities respectively. T5's asymptotic
consequence is explicitly optional in the canonical statement itself.

The nine `restricted` targets remain T1, T2, T4, T6, T7, T8, T9, T10 and T11.
Their declared limitations match the retained assertions, including T7's
missing spatial realization, T10's missing strict-positivity assertion and
T11's omitted actual 7.99649/8.00 identification and empirical percentiles.
The repaired T8 empirical omissions now receive equally explicit treatment.

There are no `refuted` decisions. This is appropriate under the clarified
rule: these theorems establish all or disclosed parts of their canonical
counterexample/correction assertions; they do not contradict those assertions.
Docstrings naming a reading failure do not say “The printed claim is false.”

## Junk values, nonvacuity and checks

The added T8 conclusion uses ordinary real division by positive integer
constants. It adds no premise, empty type, integral, ratio domain or
totalization convention. The spatial and probability definitions and all
previous domain guards are unchanged.

The compiled T8 nonvacuity witness still has two distinct nodes, field R²,
radius one, Dirac measure at their midpoint, binary constant outcomes and
circle masses one, with integrability of every required override. Normalized
weights exist on four radii; normalization excludes an empty radius type.
The sorted sample (−2,−1,0,0,1,2), level 1/40 and positive divisor four give
a nontrivial quantile-rescaling instance. The −4 companion remains an actual
binary labelled counting model, with its spatial-realization limitation
disclosed. Full target-by-target instances remain in `findings4.json`.

Validation completed:

* `sap-lean scratch/Delta4Check.lean` — passed. Independently proves the entire
  revised five-part numerical block and both positive comparison margins. A
  separate projection verifies that the new comparison is a conclusion of
  T8 rather than an added hypothesis.
* `sap-lean scratch/Check.lean` — passed against the refreshed imports. This
  rechecks the spatial, conditional-design, integrability, binary-outcome and
  IID nonvacuity instances.
* Source hashes identify the complete delta. All other Defs parts and import
  roots are unchanged. All 14 theorem names and `TnStatement` signatures are
  retained; all record decisions remain unchanged.
* Python parsing and validation check `findings4.json`, its required fields,
  exact target coverage, theorem correspondence, allowed verdicts/severities,
  agreement of record/docstring restrictions and report counts. Results are
  recorded in `scratch/validation4.json`.

At most two Lean processes ran concurrently. No `lake` command, Solution,
Bridge or external project proof source was used. Statement review does not
replace renewed Solution/Comparator certification after the T8 type change.
