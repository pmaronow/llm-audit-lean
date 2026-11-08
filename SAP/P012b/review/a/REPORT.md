Audited 12 targets and 10 Challenge theorems: **4 correct_whole,
6 correct_restricted, 2 omission_ok**. All other verdict counts are zero;
all severities are none. There are no adverse findings requiring a fix.

| Verdict | Count |
| --- | ---: |
| correct_whole | 4 |
| correct_restricted | 6 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 2 |
| omission_questionable | 0 |

The blind reading was saved in `reading.md` before opening `claims.json`.
`claim-stage.json` was saved before opening `record.json` and has not been
revised: two theorems state the whole canonical correction, six are narrower,
and two have deliberately different polarity because they refute printed
claims. The architect's decisions agree with that assessment. No Solution or
external formalization source was consulted.

`correct_whole` applies to T13 and T16 and to the **explicitly labeled
refutations** T19 and T20. It does not mean the printed assertions refuted by
T19/T20 are true. The permitted refutation treatment reconciles the final
verdicts with the preserved step-2 `different` classifications.

The six restricted decisions are accurate and completely disclosed in their
Challenge docstrings; each disclosure also matches the record verbatim:

| Target | Disclosed omissions or specialization |
| --- | --- |
| T14 | Uniqueness in A/C; raw B/C fractions; complete D classification and trait-count formula; explicit failure of whole-space intervals in A/D. All four concrete families and all eight D assignments remain. |
| T15 | Endpoint existence/attainment and possible emptiness of the h-defined-only region. The retained endpoint equivalences alone do not establish existence. Individual and whole-space domain criteria are retained separately for h and p. |
| T17 | The two-seed common-neighbor example, comparison graph and degree calculations. General induced compatibility and its exact-degree criterion remain. |
| T18 | Specialization to two admissible compatible histories, and omission of the contrasting dependence of p on recruitment history/times. Homophily equality includes undefined cases. |
| T22 | The illustrative two-vertex classification, numerical values and intervals. All four general identification clauses, the private-leaf witness and on-vertex trait uniqueness remain. |
| T23 | Nonuniqueness of extremizing graphs. All four attained marginal extrema and the containing rectangle remain. |

T21's omission is justified: `claims.json` marks it `no_lean`, and no formal
class of closed-form expressions is specified for the denial. The record
does not claim to establish that denial, optimization speed, or a global
optimization guarantee. This audit gives no credit to general endpoint
formulas outside the supplied Challenge.

T24's omission is justified on the visible evidence. Its canonical target is
convergence of the printed process; that proposal can leave the stated state
space, and its first temperature is undefined. Convergence for repaired
proposals concerns a different process. The record excludes that credit and
does not substitute supporting objective/depth facts for the probability
limit. This conclusion does not require examining the excluded proof.

The definitions faithfully represent the finite simple augmented graph model,
with no unsampled-unsampled edges, the observed recruitment forest, binary
traits, and susceptible neighbors immediately before each recruitment. Natural
times preserve every order comparison needed here. Traits outside the vertex
set and names of unsampled vertices do not affect any exported functional.
The journal's homophily and preferential-recruitment definitions were also
cross-checked against the [published article](https://pmc.ncbi.nlm.nih.gov/articles/PMC5860647/).
The 2015 arXiv draft uses an earlier homophily definition and was not used to
override the canonical journal claim.

Real division is totalized in the raw auxiliary functions, but the partial
`Option` values exclude zero edge counts, zero homophily denominators, empty
recruitment averages and zero susceptible denominators as appropriate. The
admissibility and recruitment hypotheses imply positive susceptible counts
where raw p appears in T13/T22. Natural subtraction in spare degrees is exact
under admissibility. No exported result depends on an empty compatible set,
an unbounded order operation, or an assumed identification conclusion.

Verification used `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` and exited
successfully. This scratch file imports only Defs and kernel-checks concrete
admissible and compatible examples, positive-domain instances, a private-leaf
p difference, the mixed dyad's h, feasible cooling/depth parameters, and an
explicit literal-proposal counterexample. No Challenge stub is used to prove
these checks. At most one Lean process was running at a time; `lake` was never
run directly.

`python3 scratch/audit_checks.py` independently verifies the rational domain
examples, a two-child flip difference, the table bound, and all Figure 1
extrema. Its 762 representatives cover all h,p values: splitting an unsampled
vertex into private leaves with the same trait preserves edge counts, trait
degree sums, edge trait types and each recruiter's susceptible counts. The
resulting sampled internal graphs and leaf-trait counts are enumerated
exhaustively. Explicit extremizers are in `scratch/audit_checks.json`.

For T19, two sampled degree-zero seeds form admissible compatible data; an
unchanged graph proposal followed by the printed isolate cleanup deletes both
seeds. The resulting incompatible output and the allowed proposal are checked
in Lean. For T20, the counts imply 521 recruitment edges and 3,445 spare degree
incidences. The opposite-trait private-leaf completion has 3,966 edges. Writing
c for its number of cross-trait edges and D0,D1 for its trait degree totals,

    h = 1 - 2mc/(D0 D1) <= 1 - 2c/m
      <= 1 - 2*3445/3966 = -1462/1983.

The positive cross-trait count makes the denominator nonzero. This bound is
below all three printed lower endpoints even at the rounding tolerance's lower
edge. A chain forest with six seeds and sampled degrees 9 at the first 271
vertices and 8 at the remaining 256 supplies admissible inputs with exactly
these totals, so the count assumptions themselves are consistent. The
refutation grants no correctness or incorrectness claim about individual
upper endpoints, p intervals, or point estimates.

Both requested JSON files parse with Python; `findings.json` has exactly one
entry for each target in `claims.json`, and `claim-stage.json` has exactly one
entry for each Challenge theorem.
