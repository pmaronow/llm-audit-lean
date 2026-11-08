# Palomar statement review: P004b

All 15 targets have Challenge theorem stubs. The final counts are:

| Verdict | Count |
| --- | ---: |
| correct_whole | 1 |
| correct_restricted | 12 |
| restriction_inaccurate | 2 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity: 13 none, 2 minor, 0 major. T17 is the whole claim. T16,
T18–T25, and T28–T30 have accurate restrictions. The two remaining
restrictions need wording corrections; their retained mathematical
statements appear correct.

## P004-T26 — restriction_inaccurate, minor

The record and Challenge docstring say the statement “additionally requires
… uniform quadratic spacing.” The **canonical corrected claim already
requires** a single positive constant C_b such that, for all sufficiently
large N, every node and every radius s≥0 satisfy
|B_N(i;s)| ≤ C_b(1+s²). This is precisely `QuadraticSpacing` in
[Defs/Part4.lean](/home/ubuntu/sap/tasks/CHFID-P004b-b/SAP/P004b/Defs/Part4.lean:59).
It is an inherited hypothesis, not an added restriction. Likewise, the
metric-distance assumption is already part of the Appendix C setup in
standing assumption S8. Making it explicit is appropriate, but describing
it as additional overstates the restriction.

The architect's decision to retain a restricted statement is appropriate;
the description of what was added is inaccurate. This does not make the
theorem false or vacuous.

Replace the restriction text with:

> States convergence to zero under the corrected exterior-tail condition,
> the canonical uniform quadratic spacing bound C_b(1+s²), and the
> metric-distance setup of Appendix C. Explicitly assumes an interior
> Bernoulli probability 0<p<1 and requires well-defined averages and
> positive bandwidths for every sample size. Omits separate liminf/C6
> conclusions, the explicit diverging auxiliary radius and its cubic rate,
> and all assertions in the remark about the printed inside-ball condition
> and heterogeneity.

A nonhomogeneous instance satisfies these hypotheses: use counting measure
on singleton nodes at 0, 1, 6, 9, … on a line, with effects +1 and −1 on the
first two nodes and zero elsewhere, p=1/2, zero-distance averages, uniform
kernel, bandwidth N+1, and envelope φ(s)=1 on [0,1] and zero elsewhere.
Every diverging exterior-tail sum is eventually zero, and all average
denominators are positive. No supremum or integral default supplies the
result.

## P004-T27 — restriction_inaccurate, minor

The canonical witness's W1 verifies the NED condition at **every distance**:
it gives the coefficient ψ_d(s)=1{s≤d} at other distances as well as the
own-coordinate argument at d=1. The theorem asserts only
`NEDConditions sparsePopulation (1/2) 1` in
[Defs/Part7.lean](/home/ubuntu/sap/tasks/CHFID-P004b-b/SAP/P004b/Defs/Part7.lean:16).
The record and docstring say that the witness's NED properties are retained,
but their list of omissions does not disclose this loss of the all-distance
part of W1.

The restricted decision is appropriate. Amend the retained-property phrase
to **“NED at the analyzed distance d=1”**, and add **“verification of NED at
the other distances in W1”** to the omitted clauses. The full replacement
restriction text is in `findings.json`.

The retained counterexample remains substantive. On its balanced-count
event, both arms and the HAC variance are strictly positive, the event has
probability tending to one, and coverage at critical values ±2 is equivalent
to the first node being treated. Thus its coverage tends to 1/2, whereas the
stated nominal coverage is at least 3/4. The unconditional coverage limit is
an elementary consequence of the retained facts, although it is not a
separate theorem conjunct. Direct inspection of the population also supports
the omitted all-distance NED fact; the defect is its incomplete disclosure.

This counterexample concerns the canonical nonvacuous reading of C4,
C_b(1+s²). The literal printed C_b s² condition at radius zero has no
positive-size population, as `claims.json` itself explains.

## Checks and review order

`reading.md` was saved before opening `claims.json`; `claim-stage.json` was
saved before opening `record.json`. Step 2 classified T17 as whole and the
other fourteen statements as narrower. No step-2 verdict changed after the
record was read. All fourteen restriction strings in the record match their
Challenge docstrings verbatim. There are no omitted-target decisions.

The SAP definitions were followed through to their finite probability sums,
spatial integrals, distances, matrix operations, conditional expectations,
and asymptotic predicates. The relevant Mathlib boundary definitions are
listed in `reading.md`. Positive finite masses and integrability protect the
spatial averages where used; interior probabilities protect conditional
probability denominators; nonempty arms protect the matrix inverses.
Finite maxima and epsilon/eventual lower bounds avoid unbounded real
supremum/liminf conventions. The empty-arm and invalid-interval guards in
T18 and T28 are explicitly disclosed restrictions.

The nonvacuity examples in `findings.json` include a population satisfying
T28's **additional variance lower bound**: singleton nodes (i,0), counting
measure, deterministic alternating outcomes c_i=(−1)^i, d=0, p=1/2, uniform
kernel, and positive bandwidth (N+1)^(1/12). Its NED coefficient is zero,
its homophily is zero, and N Var(linearHajek)=4(1−c̄_N²)≥3 for N≥2.
Thus the coverage branch's hypotheses are jointly satisfiable.

[scratch/Check.lean](/home/ubuntu/sap/tasks/CHFID-P004b-b/scratch/Check.lean)
compiled successfully with `/home/ubuntu/sap/tools/sap-lean`; its log is
`scratch/check.log`. It imports only the supplied Defs and checks positive
arm counts, genuine singleton interference neighborhoods, positive
complete-randomization supports, a positive linearized-estimator variance,
and a positive-variance valid interval. There are no proof holes in this
scratch file. The compiler reports one unused-binder warning.

[scratch/check_finite.py](/home/ubuntu/sap/tasks/CHFID-P004b-b/scratch/check_finite.py)
passed exact rational enumeration of the retained node/augmented variance
and centering formulas, observational weights and inverse-Gram row, all
nontrivial complete-randomization support configurations for N=2 through 6,
the sparse variance for N=3 through 12, and every balanced sparse-witness
assignment for N=10, 11, 12. Results are in `scratch/finite-results.json`.
These finite checks supplement the mathematical statement review; they do
not replace the asymptotic arguments.

T16 refutes the proposed sufficient conditions for polygon nodes, rather
than C3/C4 assumed directly. T19 refutes the printed CLT without a variance
condition using a sum of variance one. T27's undercoverage occurs on valid
intervals with probability tending to one. None of these refutations relies
on undefined normalization.
