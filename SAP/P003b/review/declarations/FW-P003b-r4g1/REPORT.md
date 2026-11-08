# Declaration review

All five declarations are faithful to their recorded scope. No defective
definition, unsatisfiable hypothesis, concealed restriction, or use of a junk
value was found.

| Theorem | Claim-stage reading | Record decision | Verdict | Severity |
| --- | --- | --- | --- | --- |
| `SAP.P003b.T24` | whole | whole | faithful | none |
| `SAP.P003b.T25` | whole | whole | faithful | none |
| `SAP.P003b.T8` | narrower | restricted | faithful | none |
| `SAP.P003b.T19` | whole | whole | faithful | none |
| `SAP.P003b.T20` | whole | whole | faithful | none |

T24 includes the corrected complementary sum, actual weighted design mean, and
every reflected point mass. T25 includes every canonical set identity and
counterexample calculation, with possibility and the lattice intersections in
the right places. Its unbalanced interval uses the permitted empty-hull
convention; its endpoint assertions use genuine nonempty finite extrema.

T8 discloses its critical-value enclosure, wider-range omissions, use of explicit
two-type formulas, and median certification scope. It retains both exact
coverage fractions and design medians, the deterministic reported-pair
incompatibility, the sharper finite-run median bound, and the stated HC0 checks.
It does not claim to identify or enclose the normal quantile itself. The
restriction and docstring describe the same scope.

T19 counts the actual image of labeled tables with fixed covariates, establishes
both independent stratum restrictions, and includes all exact counts and order
bounds. T20 includes every corrected symbol/formula, the feasible-minimum signs
and p-value comparison, and the distinction between equality of distributions
and equality at a fixed assignment. Neither T25 nor T20 labels its illustrative
printed-formula failures as refutations of the corrected canonical claim.

The blind reading was saved before opening the claims. All 99 distinct closure
entries, including generated declarations, were inspected. The claim-stage
assessment was saved before opening the record; the record required no changes
to that assessment.

Both `scratch/Check.lean` and `scratch/WaldCheck.lean` compiled successfully using
the supplied `sap-lean` command. Their examples establish nonvacuity for every
target, including T20's nested rejection antecedent. The independent checks in
`scratch/audit_checks.py` also passed: 4,368 labeled populations for T24, the T25
example and possible maxima, both Wald benchmarks, the T19 enumeration, and the
T20 examples. Detailed instances and fingerprints are in `findings.json`;
expanded statements and boundary analysis are in `reading.md`.
