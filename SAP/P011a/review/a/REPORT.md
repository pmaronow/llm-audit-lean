# Palomar statement audit: P011a

Fourteen targets were read blind, compared with their canonical claims, and then checked against the architect's record. Eight targets have an undisclosed additional hypothesis concerning the observed dependency graphs. No false or vacuous statement was found.

| Verdict | Count |
| --- | ---: |
| correct_whole | 3 |
| correct_restricted | 3 |
| restriction_inaccurate | 3 |
| not_faithful | 5 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity: 8 major, 0 minor, 6 none. There are no omitted targets. The accepted whole targets are T1, T11 and T14; the accurately disclosed restrictions are T2, T10 and T13.

The shared issue is in [Defs/Part1.lean](/home/ubuntu/sap/tasks/CHFID-P011a-a/SAP/P011a/Defs/Part1.lean:119). `Scaling` includes `Nested F`: the observed sample sizes are nondecreasing and, at every step, an injection preserves both edges and nonedges of the observed graph. This is an induced-subgraph requirement. In the supplied canonical standing assumptions, S2 distinguishes the full graph G from its observed induced graph G_S, and S5 nests the full graphs G. No condition requires the observed subsets to be nested. Consequently, nesting of the full graphs alone does not imply the Lean premise.

A concrete separating sequence uses full graphs consisting of the first n disjoint edges of a fixed infinite matching. These full graphs are nested even as induced subgraphs. At odd n, observe one endpoint of each of n edges, giving an edgeless observed graph. At even n, observe both endpoints of one edge and one endpoint from each of n-2 other edges, giving exactly one observed edge. Use independent Rademacher outcomes on every full vertex, weights one, empty recruitment graph and the true full degrees d_i=1. All dependency and scaling bounds hold with c1=c2=c3=1, c4=2: beta=0, |Y_i|=1, observed degrees at most one and n Var(bHat)=1. At every even-to-odd transition an edge would have to embed into an edgeless graph, which is impossible. The finite obstruction is compiled independently in [scratch/Check.lean](/home/ubuntu/sap/tasks/CHFID-P011a-a/scratch/Check.lean:53). This is an excluded model sequence, not a counterexample to the formulas under the stronger Lean hypotheses.

Each affected target has the following result:

- **P011-T3 / SAP.P011a.T3 — not_faithful, major.** The oracle limit, expectation bound, sample-variance limit and mean criteria are universally quantified only under the stronger `Scaling` premise. The architect marks the target whole. Its finite clique characterization is correctly represented, but it does not remove the scope loss in the general assertions.
- **P011-T4 / SAP.P011a.T4 — restriction_inaccurate, major.** The exact expectations, deterministic expansion, variance bound and PSD sufficiency use the stronger `Scaling`. The restriction correctly drops the covariance-trace alternative and support observation, but omits the added observed-graph hypothesis.
- **P011-T5 / SAP.P011a.T5 — not_faithful, major.** The finite correction and optimization statements agree with the claim. The general conservativeness and norm assertions use the additional observed-graph nesting premise, which is absent from the whole decision and docstring.
- **P011-T6 / SAP.P011a.T6 — not_faithful, major.** The finite positive-part statements and concrete cycle certificates agree. The general conservativeness assertion is narrowed by `Scaling`, with no disclosed restriction.
- **P011-T7 / SAP.P011a.T7 — restriction_inaccurate, major.** Both finite comparison bounds and the unbounded-cap example agree. The degree-only conservativeness theorem requires the extra nesting premise. The declared omissions of the two-clique characterization and interval consequence are accurate, but incomplete as a description of the restriction.
- **P011-T8 / SAP.P011a.T8 — not_faithful, major.** The estimator classes, validity and mean-bias conditions and clipped coverage are faithfully encoded. The general variance and coverage guarantees nevertheless require induced nesting of the observed graphs; the whole decision does not disclose it.
- **P011-T9 / SAP.P011a.T9 — restriction_inaccurate, major.** The root-n route, prediction-error route and misspecified-model route all carry the additional nesting premise. The stated omissions from the unstable OLS example and explicit coefficient-map measurability are accurately described, but do not disclose this further hypothesis.
- **P011-T12 / SAP.P011a.T12 — not_faithful, major.** The complete finite moment and gap chain, tail constant and one-sided limit agree under the Lean hypotheses. Those hypotheses include observed induced nesting, so the whole decision overstates the covered class.

A concrete repair that preserves every existing Lean theorem is to mark T3, T5, T6, T8 and T12 restricted and add the exact observed-graph restriction text supplied in findings.json to all eight docstrings and record entries. An alternative mathematical repair is to remove the across-size observed-graph embedding condition from the generic scaling premise and prove the stronger general statements; the estimates themselves do not require that embedding. Explicit example nesting can remain a separate asserted fact.

No step-2 verdict was changed after reading record.json. All fourteen targets have theorem entries, so no omission decision requires assessment. The restrictions for T2, T10 and T13 accurately describe the conclusions not explicitly restated; they do not inherit the extra-hypothesis issue because their `Scaling` facts concern specified example families rather than assumptions restricting a universal class.

Validation used only the permitted Defs/Challenge files, supplied JSON, Mathlib sources and independent scratch files. [scratch/Check.lean](/home/ubuntu/sap/tasks/CHFID-P011a-a/scratch/Check.lean) imports only SAP.P011a.Defs and establishes finite maximizer existence, compatible positive-size instances, exact negative quadratic values, the edge-to-empty embedding obstruction and the six-unit integer witness. It was checked using the required sap-lean wrapper, with at most one Lean process at a time. [scratch/exact_checks.py](/home/ubuntu/sap/tasks/CHFID-P011a-a/scratch/exact_checks.py) passed 78 independent exact checks, recorded in [scratch/exact-results.json](/home/ubuntu/sap/tasks/CHFID-P011a-a/scratch/exact-results.json). These are finite audit checks, not proofs of all asymptotic conclusions. Each target's nonvacuity instance is given in findings.json.

The totalized definitions do not create a further defect in the audited statements: sample sizes used in denominators are positive; weighted coordinates are measurable and essentially bounded under Scaling, hence integrable with all finite moments at each size; residual expectations are covered by mean-model integrability or finite-support examples; meanBias is bounded by (1+c2)c1², so its real liminf is meaningful; coverage probabilities lie in [0,1]; and the normal quantile has a nonempty, bounded-below defining set for alpha in (0,1). Zero-degree correction is an explicit canonical convention, residual natural subtraction is protected by the forced-degree feasibility test, and the displayed OLS designs have nonsingular Gram matrices. Arbitrary argmax selections give measurable maximum values over finite graph sets. No conclusion is smuggled in as a hypothesis.
