# Declaration review

All five declarations are **faithful**, severity **none**. The record's five
`whole` decisions are correct. No current issue remains.

The blind reading was saved in [reading.md](reading.md) before the claims and
review history were opened. It unfolds every mathematical definition in the
five closures and records all relevant total-value conventions. Generated
recursors, matchers, and auxiliary proofs were inspected through
[ClosurePrint.lean](scratch/ClosurePrint.lean). The independent claim comparison
was saved in [claim-stage.json](claim-stage.json) before opening the earlier
review, architect report, and decision record. Step 3 required no change to
those assessments.

| Declaration | Assessment |
|---|---|
| `SAP.P003a.T29` | Exact finite randomization coverage for every positive allocation and interior real level. |
| `SAP.P003a.T1` | Every clause of the canonical twenty-unit counterexample is present, including labeled realizations, actual tails, constrained maximizers, all ten groups, and the coverage deficit. |
| `SAP.P003a.T2` | Arbitrary joint missingness under balance, completion inclusion, and every asserted plus-coupling identity and inequality are present. |
| `SAP.P003a.T3` | Both arbitrary-allocation coverages, deterministic inclusions, the count of distinct count completions, and the numerical repair are present. |
| `SAP.P003a.T4` | Both abstract counterexamples and the complete legal balanced experiment are present, including queries, cardinalities, estimator atoms, and the additional call-domain failures. |

The finite state weights are products of binomial coefficients, exactly the
numbers of labeled assignments in their fibers. Count compression therefore
preserves the statistical quantities used here. An arbitrary labeled joint law
of randomization and missingness aggregates to `IsMissingLaw`; it adds no
independence assumption. The completion lists enumerate all possible observed
count tables of binary completions. Their length is not misidentified as the
number of labeled completions. Definitions compute the stated statistical
objects without assuming coverage or encoding the desired conclusions.

Positive-arm hypotheses prevent zero statistical denominators. Valid masks and
state bounds prevent harmful natural-number truncation. Empty accepted sets
give empty existential hulls, as the canonical claims require. Imputation
endpoints are guarded; the coupling's accepted possible table ensures its
unguarded upper endpoint is genuine. The search uses integer division by 2;
its logarithm is evaluated at 2. Fuel exhaustion is explicit, and the failure
assertion quantifies over every fuel.

For T1, the printed reading asserts imputation coverage for arbitrary positive
allocation and arbitrary assignment-dependent missingness, together with the
stated completion inclusion and tail inequality. Its conditions and witness
checks are:

* Fixed binary potential outcomes: the explicit population has counts
  `(11,0,3,6)` and effect `−3/20`.
* Positive arms and interior level: `n=20`, `m=3`, `alpha=109/500`.
* Uniform design: all 1140 size-three assignments have equal probability.
* Permitted missingness: only unit 0 is hidden, only on treatment set
  `{11,12,13}`; this deterministic dependence is expressly allowed.
* Defined quantities and the D.7 setting: both accepted sets are nonempty, the
  true table is possible for the original completion, and its effect exceeds
  the favorable endpoint and estimate. Both actual tails equal `83/380`.

The imputation coverage `297/380` is below `1-alpha` by `1/2375`, so the witness
contradicts the printed assertions themselves.

For T4, the printed reading says the sequential B.1 search returns the threshold
and terminates within its evaluation bound for every positive ordered domain
and allowed threshold predicate. Both witnesses use `0<1<2`, Boolean predicates
on that domain, and permitted thresholds (`r=2` for constant acceptance;
`r=0` for constant rejection). Step 2 executes before the adjacency test and
the first return ends execution, as the canonical reading specifies. The first
returns the wrong value; the second reaches a self-loop. The balanced example
also satisfies the algorithm's legal domain and interior level. The three
additional invalid domains are expressly failures of Algorithm 4.3's calls,
rather than alleged legal-domain counterexamples to B.1. T1 and T4 correctly
receive `whole`: their canonical claims already ask for these counterexamples.

Both earlier T1 issues are fixed. The Challenge docstring at
`SAP/P003a/Challenge/Part1.lean:19` and repeated definition docstring at
`SAP/P003a/Defs/WholeW1/Part3.lean:145` now restrict the maximum-p-value assertion
to possible upper-completion tables with effect at least `−3/20`, matching the
formal bound. Each issue has its own `resolved` entry in
[findings.json](findings.json).

Validation: `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with
exit code 0 and no diagnostics. [Check.lean](scratch/Check.lean) imports only
definitions and independently constructs nonvacuity data for every quantified
component, including dependent missingness and a coupling with `d=1` and
p-value `1/3`. It also checks the counterexample observations, rational
intervals, coverage fractions, and search outputs. Both output JSON files
parse, and the five finding identities and fingerprints match `closure.json`.
