# P047 declaration audit

All three declarations are **faithful**, with severity **none**. The record's
`whole` decisions are correct; no restrictions or docstring corrections are
needed. No claim-stage conclusion changed after reading the record.

The blind mathematical expansions and totalization audit were saved in
`reading.md` before opening `claims.json`. Every entry in each supplied closure
was inspected, including the generated auxiliary declarations printed in
`scratch/BlindPrint.lean`. The independent comparisons were then saved in
`claim-stage.json` before opening `record.json`.

**SAP.P047.T1.** `SAP/P047/Defs/Part2.lean:15` includes all canonical items
(i)–(vi): conditional and unconditional ATE means, bounded contributions,
the exact finite-sample tail inequality, coverage at every permitted level,
and the deterministic root-n width identity. The separate treated-mean branch
uses exactly its weaker outcome and one-arm positivity bounds, with the
required tail and interval constants. Armwise ignorability is not strengthened
to joint ignorability. Estimators use observed outcomes and the supplied
propensity. The docstring at `SAP/P047/Challenge/Part1.lean:11` accurately
describes the result.

**SAP.P047.T2.** `SAP/P047/Defs/Part2.lean:58` includes simultaneous uniformity
over all positive sample sizes and all laws with common B and epsilon, the
exact exponential bound, and the fixed-law centered normal limit with the
specified variance bound. `knownRootRisk` uses a strict tail for tightness;
the explicit inequality uses the canonical weak tail. Degenerate variance
gives an actual point mass at zero. Each estimator uses its law's known
propensity. No uniform normal approximation is claimed. Audit-history
`finite_lemmas` were not treated as additional clauses. The docstring at
`SAP/P047/Challenge/Part1.lean:18` is accurate.

**SAP.P047.T3.** `SAP/P047/Defs/WholeW1.lean:95` includes both estimation
obstructions, the specified full baseline population, the fixed-baseline
interval-width lower bound, failure of uniform width shrinkage, and every
containing model with an existing mean effect. `UnknownModel` at
`SAP/P047/Defs/Part3.lean:35` imposes exactly the hard model's uniform
covariate, binary outcomes, joint ignorability and common overlap. Procedures
receive precisely n observed triples and an independent seed. The coverage
antecedent is asymptotically uniform. Extended-real endpoints handle ordinary,
unbounded and empty intervals through the finite-shift width event. No
separate claim of testability or sufficiency is asserted, consistently with
canonical clause (c). The docstring at `SAP/P047/Challenge/Part1.lean:24` is
accurate. None of these declarations is labelled or presented as a refutation.

The definitions contain no placeholders or estimator conclusions. Almost-sure
overlap bounds remove relevant division defaults; boundedness gives genuine
integrals and finite variance. Conditional expectations use a legitimate
covariate sub-sigma-algebra and finite measures. Probability-valued extrema
and their asymptotic sequences lie in [0,1], excluding empty/unbounded-real
supremum and limit defaults. The additional integrability hypothesis in T3
is an authorized usual measure-theoretic condition.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully.
The checks construct the full baseline independently from Mathlib product
and Bernoulli measures, prove both forms of ignorability, identify it with
`baselineLaw`, compute effect 1/2, and satisfy both T1 model hypotheses and
T2's bounded-overlap hypothesis. They also prove integrability throughout
T3's nonempty hard model and instantiate its estimator, seed, endpoint and
honesty hypotheses. Full intervals have coverage and width-event probability
one; the zero estimator has baseline error probability one at tolerance 1/12.
The named witness proofs' `#print axioms` outputs contain only `propext`,
`Classical.choice` and `Quot.sound`, with no dependency on the audited theorem
stubs or `sorryAx`. Compiler evidence is in `scratch/check.log`.

`findings.json` and `claim-stage.json` were parsed with Python and checked
against the target names and fingerprints in `closure.json`.
