# Palomar statement audit: P012a

All 12 targets are accounted for: **3 correct whole statements and 9 correct,
accurately disclosed restrictions**. There are no adverse findings, no vacuous
statements, and no omitted targets. All severities are `none`.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 3 |
| `correct_restricted` | 9 |
| `restriction_inaccurate` | 0 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 0 |
| `omission_questionable` | 0 |

The required order was observed. `reading.md` was saved before opening
`claims.json`. `claim-stage.json` was saved before opening `record.json`.
No step-two verdict was changed after the record was read. All twelve theorem
mappings agree with the record, and all nine restriction descriptions appear
verbatim in the corresponding Challenge docstrings. Source statements and
definitions were left unchanged.

| Target | Decision upheld | Scope assessment |
| --- | --- | --- |
| P012-T1 | Restricted | All four concrete obstructions remain. The disclosed omissions cover exhaustive execution/Bernoulli assertions, separate output and failed/preserved-condition characterizations, and uniqueness in the empty-unsampled example. |
| P012-T2 | Restricted | Every represented execution of either corrected mechanism preserves compatibility. Intermediate branch descriptions, exact cleanup criteria, and the second-pool explanation are disclosed omissions. |
| P012-T3 | Restricted | The compatible counterexample, counts, quotient, both uniform bounds, endpoint evaluations, strict comparisons and gaps remain. Explicit denominator positivity, the polynomial certificate, and separate vertexwise leaf-degree assertions are disclosed omissions. |
| P012-T4 | Whole | Both bounds, all three gap bounds, and the degree-discrepancy converse are present. The rounding tolerance strengthens the exact-endpoint implication. |
| P012-T5 | Restricted | Exact attained minimum, quotient and numerical specialization remain on precisely the claimed domain. The assertion about count triples being unavailable from the paper is explicitly excluded. |
| P012-T6 | Restricted | The full mathematical homophily interval, including denominator positivity and attainment, remains. One-pass computation and operation counts are explicitly excluded. |
| P012-T7 | Restricted | The full mathematical preferential interval, count decomposition, fraction bounds, definedness and simultaneous attainment remain. One-pass computation and operation counts are explicitly excluded. |
| P012-T8 | Whole | The concrete incompatible proof-step output, its degree vector, and equality of sampled induced graphs match the canonical counterexample. |
| P012-T9 | Restricted | The concrete swap failure, full degree vectors, vertices and edge counts remain. The final assertion about the common denominator in (A1) is explicitly excluded. |
| P012-T10 | Restricted | Both augmented and induced nonidentification witnesses and their connecting move remain. The full private-leaf construction, deletion of the shared neighbor, and arbitrary-trait construction assertion are explicitly excluded. |
| P012-T11 | Restricted | General nonidentification, arbitrary other unsampled traits on the private-leaf graph, swap invariants, denominator formulas, (A1), and the numerical instance remain. The separate supporting degree-sum inequalities are explicitly excluded. |
| P012-T12 | Whole | Both full preferential values and the failures of both printed single-recruit expressions are present. |

There are no items requiring a corrected statement or docstring.

The graph and functional definitions match the standing assumptions. Edges are
sets of two distinct vertices, and edge collections have no multiplicities.
Every compatible edge has a sampled endpoint, every unsampled vertex has a
sampled neighbor, and reported sampled degrees are exact. Natural-number
recruitment times faithfully encode the finite strict order used by these
targets; actual durations never enter the functionals. Unused labels and trait
values outside a state's vertex set do not affect the values. Although states
are labeled rather than quotiented by unsampled renaming, the graph witnesses
in T10 differ on a sampled edge and all functional conclusions are invariant
under such renaming.

Truncated natural subtraction does no work: admissibility gives recruitment
degree at most reported degree at every sampled vertex. Undefined real
quotients do no work either: `some` values require their explicit domain
predicates, and the unguarded bounds occur on domains with positive relevant
denominators. T5 deliberately minimizes over defined homophily values and
allows other compatible states to have undefined homophily. T6 has exactly
the two positive sampled-trait degree sums required in its canonical claim.
T7 requires at least one recruitment; its susceptible sets include the current
recruit, as required by the left-continuous convention. T12 needs only defined
preferential recruitment: undefined homophily at its all-true starting state
does not invalidate this refutation of (A2).

Minimum and maximum assertions include membership in the attainable value set,
so they cannot succeed through an empty compatible family. `FullHomophilyRegion`
and `FullPreferentialRegion` give the smallest containing intervals of
Definition 4; they make no unsupported claim that every interior real value is
attainable. T4's GLB hypothesis names the infimum being discussed rather than
assuming its advertised numerical bound. Its converse does **not** also assume
that the alternative reported degree vector totals 4487.

For the proposal relation, existing replacement pools are taken from the original
state, fresh vertices are absent from the pending vertex set, and the second
fresh choice therefore differs from the first. The corrected unsampled-deletion
branch adds only the replacement edge at the sampled vertex. Corrected cleanup
keeps sampled isolated vertices, and the corrected trait branch is a no-op on
an empty unsampled set. The printed relation used by T1 instead retains the
unconditional additional edge responsible for its counterexamples. The theorem
about preservation quantifies over executions and makes no unsupported claim
that every compatible starting state offers a graph choice.

Nonvacuity was checked concretely. `scratch/Check.lean` imports only Defs and
successfully compiles with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`
(exit 0; only tactic-style warnings). It checks an admissible compatible
starting state, an actual corrected trait proposal, positive-spare and
positive-trait-degree premises, a nonempty recruitment set, the full T10 and
T11 selected-pair premises, and admissibility, definedness and exact preferential
values for T12. No `lake` command was run; at most one Lean process ran at a time.

`scratch/audit_checks.py` supplies independent exact rational calculations,
with successful results in `scratch/audit_checks.json`. It checks the fixed
counterexamples and numerical swap, exhausts all **136,503** nonnegative
integer triples summing to 521, and finds exactly the advertised maximum
`-178409/241987` at `(260,261,0)` and `(261,260,0)`. A separate exhaustive
small-graph calculation covers **1,048** admissible data sets with one to three
sampled vertices and total spare degree at most three, and **7,160** compatible
states up to unsampled renaming. It checks the lower homophily endpoint on
1,016 applicable data sets, both homophily endpoints on 608, and both
preferential endpoints on 840. These finite checks support, rather than replace,
the mathematical review of the general edge-budget, fraction-bound and
attainment arguments.

The published-total premises have an explicit fixture: samples `0..526`, seeds
`0..5`, and 521 recruits of seed 0; give seed 0 reported degree 3966, each
recruit degree 1, and the other seeds degree 0. The degree sum is 4487 and the
spare sum is 3445. With all sampled traits false, the opposite-trait completion
is compatible and has `h=-3445/4487` with positive denominator. Its larger
number of unsampled vertices is allowed by the canonical compatibility notion.

The rounded-limit converse also has consistent premises. Use 260 true-trait
recruits of a true seed, 261 false-trait recruits of a false seed, and four
isolated seeds. Add 2984 spare degrees at the true seed. The reported total is
4026, and the attained lower endpoint is `-539551/767814`, within
`40511/3839070000 < 1/20000` of `-0.7027`. This endpoint is a GLB by the
edge-count bounds and monotonicity of the homophily formula. A nomination state
using 3445 private leaves instead has sampled-degree total 4487. Thus the
converse is not an implication with contradictory rounding premises. Each
target's `nonvacuity` field gives its own instance or explanation.

The independently retrieved published PDF text confirms the Table 1 values,
network counts, and the relevant Result 1–3 proof passages in the
[published paper](https://doi.org/10.1093/aje/kwx208). The supplement images
could not be retrieved independently; the proposal listing was checked against
its complete canonical transcription in `claims.json`. The older arXiv text
was not substituted for the specified journal version. No solution files or
external audit artifacts were read.
