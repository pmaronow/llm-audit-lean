# P023 delta statement review

**12 targets: 8 correct_whole, 4 correct_restricted; no outstanding issues.** All severities are `none`. No target is false, vacuous, or omitted. The two architect decisions labeled `refuted` are accepted as complete, faithful refutations and therefore receive `correct_whole` in the findings schema.

## Earlier finding: fully fixed

The sole adverse finding in my first review concerned **P023-T10**: its polynomial localization refutation could be proved using degree zero, which supplies no vote-share control. Its status is **fixed**, with **0 partly fixed and 0 not fixed** findings.

The revised definition in `SAP/P023/Defs/Part4.lean:194` now reads, in relevant part:

```lean
¬ (∀ (n J : ℕ) (x d : Fin n → ℝ) (k : ℝ),
  1 ≤ J → 0 < k → k < 1 → TwoParty x d → Condition1 k x →
  FullRank (polynomialDesign J x d) →
  (∃ c : Fin (J + 2) → ℝ, ∀ i,
    0 < predict (polynomialDesign J x d) c i ∧
    predict (polynomialDesign J x d) c i < 1) →
  Localized k x (polynomialOLS J x d))
```

The new `1 ≤ J` premise is **inside** the universal proposition being negated. It strengthens the refutation by requiring a counterexample with a genuine positive-degree margin control. The docstring expressly says “positive-degree polynomial vote-share controls” and correctly states the positive close-count domain of the accompanying coarsened comparison. `record2.json` retains the appropriate `refuted` decision, replaces the old broader refutation row with the degree-one witness, and explains why the broader row is unused. This agrees with the architect's account of the finding.

## Changed-statement and nonvacuity checks

I read every revised Defs and Challenge source and compared its mathematical content with the saved `reading.md`. The only substantive statement change is the degree premise in T10; its Challenge description is correspondingly revised. The shared estimator definitions, other component propositions, and all twelve outer theorem signatures match the earlier reading. The only record-entry change is T10's supporting-row selection and explanation. There are no newly dropped clauses or added restrictions elsewhere.

The revised T10 has a concrete qualifying counterexample:

| Quantity | Instance |
| --- | --- |
| Observations and degree | Six elections, J=1 |
| Margins and party indicator | `linearX`, `linearD` |
| Bandwidth | 1/200 |
| Close observations | Indices 2 and 3 |
| Close winner and loser counts | 1 and 1 |
| Polynomial design rank | 3 |
| Exact baseline coefficients | (1/2, 1/10, 1/20) |
| Outcome perturbation | Add 1/100 only at index 5, margin 3/4 |
| Baseline party coefficient | 1/10 |
| Perturbed party coefficient | 1371721/13920200 |
| Difference | −20299/13920200, nonzero |

The baseline equals its fitted linear model and all fitted values lie strictly between zero and one. The outcomes agree at every close observation. This is the canonical correctly specified linear-control counterexample, so the revised theorem refutes the selected printed data-dependence assertion. The valid coarsened-localization conjunct preserves the paper's existential “may” statement.

`scratch/DeltaT10.lean` independently proves the **entire revised polynomial refutation** using this J=1 example. It imports only `SAP.P023.Defs`, checks the sign assumptions, Condition 1, rank, exact fit, bounded fitted values, close counts, normal equations and distinct OLS values, and applies the revised universal proposition at degree one. Compilation with `/home/ubuntu/sap/tools/sap-lean scratch/DeltaT10.lean` succeeds. Its axiom output is:

```text
'DeltaT10.positive_degree_refutation' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

Full rank and explicitly verified normal-equation solutions make the chosen OLS coefficients unique. Both RD denominators equal one. The six-element index type is inhabited, the bandwidth is positive, and the fitted-value existence premise is explicitly satisfied. No integral, supremum, infimum, or limit is introduced by the revision. The change therefore introduces no junk-value or vacuity problem. The old degree-zero scratch proof remains historical evidence for the first review and is not used to validate the revision.

## Labels and retained coverage

| Targets | Revised architect label | Review |
| --- | --- | --- |
| T1, T2 | whole | Retain all concrete witness clauses, including ranks, models, weights, perturbations, close windows and coarsened estimates. |
| T6 | whole | Retains the amplification rate and norm, one fixed continuous witness, increasing-degree divergence, RD limit and failure of a Lipschitz bound. |
| T7 | whole | Retains all population bias identities, bounds and criteria, the finite residual/conditional formulas, and uniform constants. |
| T9 | whole | Retains the pair-indexed partition, demeaning, positive denominator and localized ratio. |
| T11 | whole | Retains Proposition 1 for every solution of the printed coarsened normal equations, including designs with empty nuisance bins. |
| T10 | refuted | Now refutes localization for positive-degree polynomial controls and preserves valid coarsened localization. |
| T12 | refuted | Retains the selected fixed-law, all-sufficiently-large-fixed-degrees reading and its refutation. Its bounded continuous uniform-law counterexample defeats the population tolerance without relying on degenerate sample branches. |

The four restrictions remain accurate and complete, with their record text appearing verbatim in the relevant Challenge docstrings:

| Target | Disclosed restriction retained |
| --- | --- |
| T3 | Omits the separate fixed-tolerance probability inequality; adds positive close winner/loser counts to nonlocality; adds the stated probability-law, positive-degree, positive-bandwidth and sample-admissibility premises to shared consistency. |
| T4 | Adds degree-one/degree-seven OLS admissibility and RD admissibility to sampling; restricts predictor comparisons to measurable predictors with integrable squared error. |
| T5 | Restricts predictor comparisons to measurable predictors with integrable squared error. |
| T8 | Adds RD admissibility and OLS admissibility for every fixed positive degree and every growing schedule satisfying the stated rate; retains every population and sampling conclusion, including existence of degree schedules. |

The original nonvacuity instances remain applicable to these unchanged components and are carried forward per target in `findings2.json`. There are no target omissions. No additional statement repair is required.

Both findings JSON files and `record2.json` were parsed with Python. The revised findings were checked for the required schema, unique coverage of the twelve canonical target IDs, theorem-name agreement, valid verdicts, severities and confidence values, and the counts above. The source files, original blind reading and first-round findings were preserved. No `lake` command was run, and only one Lean process was used at a time.
