# P024 statement referee report

Eight targets were assessed. There is one minor error in the description of
T8's scope; no mathematical falsehood or vacuous theorem was found.

| Verdict | Count |
| --- | ---: |
| correct_whole | 3 |
| correct_restricted | 3 |
| restriction_inaccurate | 1 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |
| **Total** | **8** |

Severity counts: **none 7, minor 1, major 0**.

## P024-T8: inaccurate restriction description (minor)

The statement is mathematically sound and covers the complete mandatory
fixed-count formal claim. The scope comparison in its docstring and record
needs correction.

[The docstring](SAP/P024/Challenge/Part1.lean#L51) describes fixed nonempty
counts and actual marginal probabilities m_b/N_b as restrictions, and
`record.json` calls these additions. However, in `claims.json`, target
P024-T8, `canonical_claim.note`, the mandatory formal reading already
specifies uniform assignment of m_b units within each block, with
1≤m_b≤N_b−1 and π_b=m_b/N_b. Variable counts and unequal within-block
propensities therefore are not cases dropped from that formal claim.
The pooled-bias example is explicitly optional.

[T8Statement](SAP/P024/Defs/Part4.lean#L60) retains the pointwise equality
between the overall HT statistic and the population-share weighted actual
block means, together with unbiasedness of both. Its count and common-marginal
assumptions permit additional balanced nonuniform assignments. For example,
in one block of four units, treat either {0,1} or {2,3}, each with probability
1/2. Exactly two units are treated and every unit's marginal is 1/2, although
the distribution is not uniform on the six two-element subsets. The count,
marginal, and six-subset cardinality checks are compiled in
[scratch/Check.lean](scratch/Check.lean#L114).

This is a minor documentation/coverage error: the theorem includes the
canonical fixed-count case and a valid extension. It does not threaten the
HT identity or its unbiasedness. The architect's decision should describe
whole coverage of the mandatory formal component and the extension to
balanced nonuniform laws. The docstring may separately explain that it does
not address arbitrary variable-count or unequal-propensity readings of the
paper's informal sentence.

Suggested replacement for the restriction paragraph:

> This covers the entire mandatory fixed-count formal component of P024-T8.
> In each nonempty block require 0<m_b<N_b, exactly m_b treated units on every
> assignment, and actual marginal probability m_b/N_b for every unit. The
> canonical uniform m_b-of-N_b design satisfies these conditions; the theorem
> also allows balanced nonuniform laws with the same fixed counts and
> marginals. Independence across blocks is not required. The optional
> pooled-difference bias example is not included.

No change to the Lean statement is needed.

## Architect decisions

| Target | Record decision | Assessment |
| --- | --- | --- |
| T1 | whole | Agreed: all numerical and inferential witness clauses are present. |
| T2 | whole | Agreed: overlap estimation, inclusive uniform null ranks, and actual before-after bias are retained. |
| T3 | omitted | Justified: explicitly marked no_lean; the unmodeled design-strength and robustness prose has no separate precise theorem here. |
| T4 | whole | Agreed: both designs, arbitrary empty-arm extensions, limits, conditional mean, shares, and six-cluster checks are retained. |
| T5 | restricted | Accurate and disclosed: the appreciable-bias prose and the cross-reference to failure without no dominance are omitted; the full consistency conclusion and weight equivalence remain. |
| T6 | restricted | Accurate and disclosed: fixed pointwise counts and true equal marginals; random-count conditional Bernoulli unbiasedness is omitted. |
| T7 | restricted | Accurate and disclosed: the general closed conditioning-probability formula is replaced by positivity; normalization, equal-size conditional claims, arbitrary extensions, and the unequal-size witness remain. |
| T8 | restricted | Inaccurate comparison with the canonical fixed-count formal component; see above. |

T3's omission does not endorse the printed necessity assertion. T1 refutes
its audited reading and T2 supplies the corrected mathematical content.
The record appropriately gives T3 no separate credit for an application-level
comparison or robustness claim.

## Reading order and checks

`reading.md` was saved after reading all Defs and Challenge files and the
relevant Mathlib endpoints, before opening `claims.json` or `record.json`.
`claim-stage.json` was saved before opening `record.json`. Neither file was
revised after the record was opened; no step-2 verdict was changed. T8's
step-2 classification was already `broader` relative to its explicit
canonical formal reading.

The comparison uses the canonical transcriptions and standing assumptions
provided in `claims.json`. A paper-only web lookup reached the
[paper's institutional listing](https://isps.yale.edu/resource/field-experimental-designs-for-the-study-of-media-effects);
the linked publisher full-article endpoint refused access with HTTP 403.
No additional paper passage is asserted to have been independently read.
No Solution, Comparator, or external formalization source was inspected.
The names of credited proof rows in `record.json` were not used as evidence
that a statement is faithful or true.

The final [scratch/Check.lean](scratch/Check.lean) imports only the Defs and
contains no `sorry`. It compiled successfully with:

```text
/home/ubuntu/sap/tools/sap-lean scratch/Check.lean
```

The compiled checks include nonempty calendar overlap, positive conditional
event probability, simultaneous fixed-count/common-marginal instances,
dependent assignments across two nonempty blocks, and an entire sequence
satisfying T5's substantive hypotheses. For the latter sequence, K=k+2,
all cluster sizes are 1, Y0=0, Y1=1, p=1/2, B=1, η=1/4, and the maximum
population share is 1/K→0. Thus T5 is not made vacuous by its asymptotic
antecedent. The four-unit nonuniform example additionally verifies T8's
scope extension.

[scratch/audit_checks.py](scratch/audit_checks.py) passed independent exact
rational calculations, saved in
[scratch/audit_checks.json](scratch/audit_checks.json). These include all
T1 numerical clauses; a nonuniform T2 overlap example; 1,092 small uniform
rank examples with ties; exhaustive T4 allocations for K=2 through 10;
all five treatment counts in the canonical six-unit T6 example; 18 equal-size
conditional T7 cases and its unequal-size witness; and all 16 allocations
in the canonical T8 example. There, both weighted and HT expectations are
3, while the pooled expectation is 35/4. Finite checks are evidence for
the numerical clauses and nonvacuity, not proofs of the general theorems.

The general identities have the expected finite-sum arguments. Inclusive
rank counting gives null-test superuniformity. Equal-size conditional
Bernoulli assignment is uniform conditional on each treated count, yielding
T7's conditional unbiasedness. For T5, bounded potential outcomes bound the
variances of normalized treatment/control totals by constants times
Σj w_j²; this tends to zero since Σj w_j²≤max_j w_j. A positive lower bound
on p and 1−p then controls both ratios off an event of vanishing probability,
including every empty-arm allocation regardless of its extension value.
The converse weight implication follows from (max_j w_j)²≤Σj w_j².

No active instance relies on division by zero, natural-number truncated
subtraction, a nonintegrable integral, an unbounded supremum/limsup, an empty
allocation subtype, or a hypothesis assuming the desired estimator equality.
All maxima are over nonempty finite cluster sets. No `lake` command was
run, and Lean checks were run sequentially. The supplied Lean source files
were not edited.
