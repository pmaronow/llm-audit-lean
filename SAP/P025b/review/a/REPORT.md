# P025b statement-referee report

All 10 targets are accounted for. There are **5 correct whole statements and 5 correct restricted statements**, with **0 findings requiring a correction**.

| Verdict | Count |
|---|---:|
| correct_whole | 5 |
| correct_restricted | 5 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity counts: none 10, minor 0, major 0. No target is omitted. There are no non-`correct_*` items to report.

## Order and evidence

The blind mathematical expansion was saved in [reading.md](reading.md) before opening `claims.json`. The independent comparison was then saved in [claim-stage.json](claim-stage.json) before opening `record.json`. Reading the record caused **no changes** to those verdicts. The final per-target results and nonvacuity witnesses are in [findings.json](findings.json).

Only the supplied definitions, Challenge stubs, claims, record, relevant Mathlib sources, and referee-created scratch files were used. The Challenge's `sorry` proofs were not used as evidence of truth.

## Decisions and disclosed restrictions

| Target | Final verdict | Scope assessment |
|---|---|---|
| P025-T12 | correct_restricted | Retains the genuine census proof-step counterexample. The singleton feasible-box statement, optimization endpoint equalities with the mean, and separate explicit Proposition 1 formula evaluation are absent as disclosed. |
| P025-T13 | correct_whole | Gives the unconditional almost-sure convergence and its separated consequence, including eventual domain nonemptiness. The finite lemmas in the claim metadata are supporting proof ingredients, not extra conclusions of the two stated propositions. |
| P025-T14 | correct_restricted | Retains the actual random design, failed separation, limiting extrema, and exact positive-replication pooled endpoints and limits on every path. Omits the displayed polynomial certificates, named optimizer evaluations, and explicit pooled weight-sum/onto assertions as disclosed. |
| P025-T15 | correct_restricted | Retains shares-only sharpness as infimum/supremum, rational realizability and attainment, and retained-total/known-size calibration. Omits the nonsharpness assertion for richer information and the two parenthetical compatibility characterizations as disclosed. Its compatible-population existence hypothesis is already present in the canonical claim. |
| P025-T16 | correct_restricted | Retains both exact integer-compatible mean sets, all four continuous-box extrema, the realizable first design and separation, and the endpoint gaps. Omits the named endpoint weight evaluations and explicit second population/probability/sampling construction as disclosed. |
| P025-T17 | correct_whole | Includes the three unique counts, all 42 cells, six corrections, rounded-input reconstruction, and every gallery/exchange grid comparison. |
| P025-T18 | correct_whole | Includes equality of the full attainable sets, normalized-box representation, both extrema, and the singleton box and sample mean at ratio one. |
| P025-T19 | correct_restricted | Retains equality of both physical first-cut weights for all tied pairs using the corrected lower rule. Omits the separately stated no-cut formulation and Supplement steps (i)-(iv) as disclosed. The additional singleton-sample case is a true harmless extension. |
| P025-T20 | correct_whole | Gives the entire binary attainable interval and both endpoints, including all stated degenerate cases. |
| P025-T21 | correct_whole | Gives the sufficient-condition almost-sure convergence with precisely the valid finite separation range. |

Each record restriction is reproduced exactly in its theorem's Challenge docstring. No unlisted extra hypothesis or additional dropped part was identified. The record's unused rows describe supporting results, not omitted targets.

## Definition, truth, and nonvacuity checks

For nonempty samples, all feasible weights are positive, every ratio denominator is positive, and the attainable set is a nonempty compact image of a compact box. It is bounded between the smallest and largest outcome, so `sInf` and `sSup` represent the ordinary attained extrema. For the pooled statements, the initial empty-sample value is harmless: eventual nonemptiness is explicitly part of the conclusion. Positive inclusion probabilities and iid replication ensure it almost surely.

The PMF construction preserves each nonnegative design probability. Its measures have mass one, so `Measure.infinitePi` uses its probability-product branch, not its zero-measure fallback. Finiteness and measurable singletons make the outcome sigma-algebra discrete. Restricting to a finite design outcome type loses no subset-valued sampling law on a finite population. Surjectivity and strictly increasing class outcomes represent exactly the distinct inhabited outcome classes. Separation tests precisely indices 0 through J-1, including the zero cut.

For T13 and T21, iid bounded class counts converge to their positive class totals by the strong law. Aggregating unit weights within each outcome class preserves exactly the attainable ratios. The ratio objectives converge uniformly over the compact positive weight box, so both extrema converge without separation. In particular T21's additional separation hypothesis is sufficient and is not circular.

For T15, positive integer class sizes and the absolute-total inequalities are equivalent to a choice of admissible per-unit inclusion probabilities; class-constant probabilities already suffice. Arbitrary such marginals can be realized by independent Bernoulli sampling, so the compatibility predicates omit no joint-design feasibility condition. The proportion inequalities force every coordinate to be positive. When the ratio exceeds one, the region has relative interior in the simplex and rational points are dense; when the ratio is one, the region is the singleton q and the stated compatibility hypothesis forces q rational. These facts support the claimed GLB/LUB and rational-attainment readings. No conclusion is assumed as a hypothesis.

For T19, a first cut exists because the last valid index qualifies: a positive weighted mean is at most the largest outcome. Thus the cut predicates introduce no hidden existence restriction. At a putative cut through two equal outcomes, the first-cut strict inequality at the preceding index persists through the threshold update, contradicting the stopping test. The same argument works for both orientations. Equal-probability weights are constant.

The concrete refutations concern the printed readings identified in `claims.json`: T12 refutes the proof steps at equal bounds; T14 refutes necessity of separation; and T16 refutes sharpness when absolute totals or known size are retained. They do not rely on an empty feasible set. The subtraction `1000-k` in T16 is used only for k<=750, so natural-number truncation does not alter it. The binary formulas have positive denominators throughout their stated domains.

## Checks performed

The following completed successfully:

* `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` — exit 0. [The scratch file](scratch/Check.lean) imports only the supplied Defs and proves concrete convergence/separation hypotheses, shares compatibility, a ratio-greater-than-one instance with a genuine tied pair and both least cuts, equal-ratio hypotheses, binary outcomes, and retained-total compatibility witnesses. It uses no `sorry` and no Challenge theorem.
* `python3 scratch/exact_checks.py` — exit 0. [The rational-arithmetic check](scratch/exact_checks.py) verifies all 42 exact-input and all 42 rounded-input cells without rounding ties, precisely six corrections, unique integer counts, the complete comparison grid, the box-vertex extrema, both exact integer compatibility sets and their gaps, and 2,632 first-cut cases. The finite search is supporting adversarial evidence, not a proof of the general theorem.
* Python JSON parsing, target coverage, theorem-name matching, verdict/severity validation, and exact matching of each declared restriction to its docstring.

No `lake` command was run; Lean checks ran sequentially, with at most one Lean process active.
