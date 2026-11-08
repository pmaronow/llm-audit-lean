# Declaration review

All five declarations are faithful to their currently declared scope.

| Theorem | Record decision | Verdict | Severity |
| --- | --- | --- | --- |
| SAP.P011c.T29 | whole | faithful | none |
| SAP.P011c.T30 | restricted | faithful | none |
| SAP.P011c.T31 | refuted | faithful | none |
| SAP.P011c.T32 | refuted | faithful | none |
| SAP.P011c.T33 | restricted | faithful | none |

T29 covers the OLS representation, unbiasedness and general variance identity.
Its integrability and moment requirements are the usual measure-theoretic
conditions. A general compiled Dirac-model construction also checks that grouping
the representation under the mean-model premise does not restrict that clause.
T30 correctly retains the knapsack optimization encoding, with the other
computational assertions expressly omitted in both the docstring and record.

For T31 and T32, an independent family of disjoint paths with outcomes
(1,-2+Z,1), using independent fair signs at distinct centers, satisfies every
printed hypothesis. Its true scaled variance is 1/3, whereas its oracle estimate
is uniformly at most -7/33 after scaling. Requiring all true edges and capping
degrees at their true values makes the maximizing graph unique. Thus both error
and underestimation probabilities equal one at epsilon=1/2. Stronger observed
graph nesting is satisfied by the witness and does not weaken either refutation.
T32 accurately negates the combined contract without claiming a separate
homoskedastic counterexample.

The earlier T33 issue is fixed in scope and attribution. Its statement still
refutes only the extension that treats negative-estimate intervals as misses.
It does not provide undercoverage for the printed interval on its real-square-root
domain. The current `restricted` decision and docstring explicitly say this,
consistent with the task's allowance for accurately labeled interpretation-level
results. Acceptance of this restriction does not certify the remaining printed
coverage guarantee. The step-2 classification `different` remains unchanged.

`reading.md` was saved before opening the claims or review history. Every closure
entry was inspected, including constructors, projections and generated numeral
and measure-instance proofs. `claim-stage.json` was saved before reading the
record. The earlier issue and architect response were read between the blind
reading and record comparison. No step-2 conclusion changed at the record stage.

Successful Lean checks are `scratch/BlindCheck.lean`, `scratch/FiniteChecks.lean`,
`scratch/WitnessChecks.lean`, and `scratch/API.lean`. T29 and T30 have compiled
instances satisfying all their premises. For the asymptotic items, the checks
compile the genuine block law, moments, estimator values, uniform algebraic
bounds, and general saturated-constraint maximization. The complete product-law
families and all printed-condition checks are given analytically in
`scratch/Witnesses.md`; no compiled full `Scaling` instance is claimed. No `lake`
command was used, and at most two Lean processes ran concurrently. All relevant
totalization cases are excluded or, for T33's extension, expressly disclosed.
