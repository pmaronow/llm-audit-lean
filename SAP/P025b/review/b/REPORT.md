# Statement audit of P025b

All 10 targets are acceptable: 5 whole statements and 5 correctly disclosed
restrictions. No false, vacuous, unfaithful or inaccurately restricted statement
was found. There are no omitted targets.

| Verdict | Count | Targets |
| --- | ---: | --- |
| correct_whole | 5 | T13, T17, T18, T20, T21 |
| correct_restricted | 5 | T12, T14, T15, T16, T19 |
| restriction_inaccurate | 0 | |
| not_faithful | 0 | |
| vacuous | 0 | |
| false | 0 | |
| omission_ok | 0 | |
| omission_questionable | 0 | |

Severity counts: none 10; minor 0; major 0. There are no adverse items requiring
a corrected statement or docstring.

## Blind stage and comparison order

`reading.md` was saved before opening `claims.json`. It expands all ten theorem
propositions through every relevant SAP definition, including the actual pooled
unit-weight optimizations and the countable product sampling law, and traces the
order and probability notions to Mathlib. `claim-stage.json` was then saved and
parsed before opening `record.json`. No step-2 classification changed after the
record was read. The five recorded whole decisions and five restricted decisions
all agree with the independent claim-stage classifications.

The `finite_lemmas` fields for T13 and T21 describe derivations supporting the
canonical convergence propositions. They were not counted as independent
conclusions of those propositions. The Lean statements quantify the actual
random pooled endpoints, rather than assuming the deterministic convergence
which the derivations establish.

Comparison used the canonical claim text and standing assumptions supplied in
`claims.json`. A paper-only web search located the publication; direct full-text
retrieval was unavailable and supplied no additional evidence. No Solution,
Comparator, or external formalization source was read.

## Restriction review

Each restriction in `record.json` is reproduced verbatim in its Challenge
docstring. Each also accurately and completely describes the substantive
subclaims left out of the proposition:

| Target | Retained mathematical content | Disclosed omissions |
| --- | --- | --- |
| T12 | Genuine census counterexample to the Appendix implication, distinct least indices, and both Supplement strict-improvement equivalences | Singleton feasible box; sample/population mean endpoint identities for (2),(3),(6),(7); explicit Proposition 1 formula evaluation |
| T14 | Explicit six-unit random design, failed separation, attained limiting extrema, and exact actual pooled endpoints on every positive-length path | Polynomial certificates; evaluations at the three named optimizer vectors; pooled class-weight-sum formula and onto-box assertion |
| T15 | Shares-only infimum/supremum sharpness, weight certificate, proportional region, rational realizability and endpoint attainment, and absolute-total/known-size calibration | Assertion that richer-information sharpness can fail; automatic compatibility for gamma>1; rational-share characterization of compatibility at gamma=1 |
| T16 | Realizable first design and separation; both exact compatible mean sets and count characterizations; four global continuous-box extrema and strict gaps | Specified endpoint weight evaluations; explicit known-size example population and its per-unit probabilities; uniform fixed-quota construction |
| T19 | Equal physical upper and corrected lower first-cut weights for every tied pair | Separate gamma>1 no-cut formulation and Supplement steps (i)-(iv) |

The restricted counterexamples still refute exactly the printed readings named
in their canonical targets. T12 attacks the proof steps at gamma=1. T14 attacks
necessity of separation. T16 attacks sharpness when absolute class totals, and
in the second example population size, are retained. Its conclusion is correctly
scoped to that information.

## Definition and truth checks

The bounds always satisfy 0<alpha<=beta<=1. For the ordinary sample statements,
n>0 makes the denominator of every feasible weighted mean positive. For class
statements, positive shares, positive compatible sizes, or surjectivity together
with positive inclusion probabilities give positive total class mass. Feasible
boxes are nonempty and compact; the positive-denominator objective is continuous
and bounded between the minimum and maximum outcomes. Thus the real `sInf` and
`sSup` operations have their ordinary extremum meaning in these uses.

An initially empty pooled sample gives the harmless totalized value zero. Both
convergence statements explicitly conclude eventual nonemptiness. The PMF and
its infinite product have total mass one. Finite measurable outcome types cover
every law of subset-valued sampling from a finite population, and no independence
of indicators within a replicate is imposed. Class-count strong laws and uniform
continuity of the box objective explain both endpoint limits, including without
separation. Separation is only over valid indices 0,...,J-1.

The compatibility predicates require positive integer class sizes and, for shares,
a positive free scale. Their inequalities are exactly the conditions for bounded
unit inclusion probabilities: within a class choose every marginal equal to its
total divided by its size. Such finite marginal vectors have sampling-law
realizations, for example by independent Bernoulli selection. The continuous
proportional region has positive coordinates; its rational vectors are exactly
the finite-population proportions. For gamma>1 they are dense, yielding sharp
infima and suprema; for gamma=1 the canonical existence hypothesis ensures the
single proportional vector is rational. This validates the scope and attainment
distinctions of T15. No conclusion is hidden in a hypothesis.

The only natural subtraction relevant to the numerical examples is 1000-k under
500<=k<=750, so truncation does not affect its intended integer value. The binary
formula denominators are positive for p in [0,1] and gamma>=1. There is no
non-integrable integral, unbounded limsup, empty-index argument, or undefined
sentinel outcome doing mathematical work.

## Independent validation and nonvacuity

The command

```text
/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean
```

completed with exit code 0, with one stylistic linter warning. It imports only
`SAP.P025b.Defs`, never the Challenge stubs, and contains no `sorry` or extra
axioms. It checks:

- A two-class design whose sample is empty or the complete two-unit population,
  each with probability 1/2. With strict bounds alpha=1/4,beta=3/4 it satisfies
  all T13/T21 hypotheses, including separation and a joint law of mass one.
- Shares-only compatibility with two positive classes at gamma>1 and at gamma=1.
- Valid corrected lower and upper first cuts for the genuinely tied sample
  (0,0,1), at gamma=2.
- Explicit positive feasible physical weights giving distinct binary means 1/3
  and 2/3.

The closed T12, T14, T16 and T17 examples have no premises to make inconsistent;
their concrete probability designs or rational data give positive finite
instances. Every target's `nonvacuity` field records its instance and the relevant
domain checks.

`python3 scratch/ExactAudit.py` passed all independent exact rational checks.
Its results are saved in `scratch/exact-audit.json`: all 42 table roundings and
the six one-tenth corrections, the three unique count-inference windows, all
specified grid comparisons, all four T16 continuous-box extrema, the T14
extrema, the two compatible-count examples including all 251 known-size means,
and 332 small sorted sample/ratio cases checking tied first-cut weights.
These numerical checks support the mathematical statement review; they are not
presented as proofs of the universal Lean stubs.

`claim-stage.json`, `findings.json`, and the exact-audit result were parsed with
Python. Target coverage, theorem identities, verdict counts, required fields,
and all five record/docstring restriction matches were checked programmatically.
