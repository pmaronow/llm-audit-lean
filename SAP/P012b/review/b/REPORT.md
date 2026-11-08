# P012b statement audit

Twelve targets: **4 correct_whole, 6 correct_restricted, 2 omission_ok**.
There are **0 minor issues and 0 major issues**; no target is false,
vacuous, not faithful, inaccurately restricted, or questionably omitted.

| Target | Theorem | Verdict |
| --- | --- | --- |
| P012-T13 | SAP.P012b.T13 | correct_whole |
| P012-T14 | SAP.P012b.T14 | correct_restricted |
| P012-T15 | SAP.P012b.T15 | correct_restricted |
| P012-T16 | SAP.P012b.T16 | correct_whole |
| P012-T17 | SAP.P012b.T17 | correct_restricted |
| P012-T18 | SAP.P012b.T18 | correct_restricted |
| P012-T19 | SAP.P012b.T19 | correct_whole (refutation) |
| P012-T20 | SAP.P012b.T20 | correct_whole (refutation) |
| P012-T21 | none | omission_ok |
| P012-T22 | SAP.P012b.T22 | correct_restricted |
| P012-T23 | SAP.P012b.T23 | correct_restricted |
| P012-T24 | none | omission_ok |

No items require correction. For T19 and T20, `correct_whole` certifies
the recorded refutation of the printed claim, not the printed claim's
truth. Their step-2 classifications remain `different`, because each
theorem negates the literal canonical assertion. Reading the record did
not change any step-2 classification.

## Assessment of the record

The two `whole` decisions retain the complete corrected claims. T13
includes the existential construction, calculation at any private-leaf
start, signed sum over every recruit of the recruiter, sharp bound and
sole-child equality criterion. T16 includes the two printed schedule
defects, repaired schedule and divergent depth series, with the natural
index shifted by one from paper time.

Each of the six `restricted` decisions has an accurate matching Challenge
docstring:

* T14 retains the four counterexample families while omitting their
  uniqueness/classification, selected raw calculations, and explicit
  no-interval conclusions, exactly as listed.
* T15 retains the denominator and exact domain criteria. Its endpoint
  predicate equivalences do not prove endpoint existence or attainment.
  That omission and the omitted empty defined-only-set example are
  disclosed. The two parameter domains are treated separately.
* T17 retains the general induced-compatibility theorem and exact-degree
  equivalence while omitting the stated two-seed illustration.
* T18 retains history independence of partial homophily on two compatible
  admissible histories while omitting the contrasting dependence of p.
  The specialization is explicit.
* T22 retains clauses (i)-(iv), including the graph and on-vertex-trait
  uniqueness, both joint-identification equivalences, private-leaf
  witness, and recruiter-only p criterion. Its omitted numerical example
  is precisely identified.
* T23 retains all four attained extrema and the containing rectangle.
  Its omission of extremizer nonuniqueness is explicit.

The `refuted` decisions are supported independently. For T19, the literal
line-22 execution replaces sampled-to-unsampled edge {1,a} with {1,b}
and {a,b}; the latter has two unsampled endpoints. The output violates
the augmented-graph definition. The compiled source state has both h
and p defined, so repairing only the parameter domains would not avoid
this counterexample. The Lean proposal relation accurately follows the
printed branch indentation and original-state replacement pools.

For T20, there are 527-6=521 recruitment edges and
4487-2(521)=3445 spare stubs. Attach one opposite-trait private leaf
per spare stub. This compatible completion has m=3966 edges and at
least c=3445 mixed edges. Its positive trait-degree totals satisfy
D0+D1=2m and D0*D1<=m^2; consequently

    h = 1 - 2mc/(D0*D1) <= 1 - 2c/m <= -1462/1983.

This is below -0.71795, the lowest of the three lower-endpoint rounding
windows, and hence below each window. A defined compatible value
therefore lies below every proposed minimum. The argument refutes the
printed full-space intervals and also their defined-only interpretation;
it needs no individual study records. The count and shared-data
hypotheses have a concrete admissible instance given in `findings.json`.

Both omissions are justified. T21 is explicitly marked `no_lean` in the
claims, and the informal denial of closed forms provides no specified
class of formulas to quantify over. The record claims no theorem or
optimization guarantee for it. T24 concerns convergence for the printed
process, which has both a defective initial temperature and proposals
that leave the designated state space. Corrected cooling arithmetic or
an objective bound does not establish that convergence conclusion.
Substituting a materially repaired process would change the target.
The record's individual source-row labels cannot be independently
verified from the permitted statement files; this audit makes no claim
to have inspected those source declarations.

## Definitions, nonvacuity and verification

`reading.md` was saved before reading `claims.json`; `claim-stage.json`
was saved before reading `record.json`. The blind reading expands every
SAP predicate used by each theorem and records the relevant Mathlib
semantics. No Solution or Comparator sources were read.

The graph representation matches the standing assumptions: finite
simple undirected graphs, no edges between unsampled vertices,
preserved recruitment edges and sampled traits, exact sampled degrees,
and no isolated unsampled vertices. Natural recruitment times encode
their distinct finite order; the statistics only use that order. The
infinite supply of ambient labels permits all finite completions, and
unobserved total-function values do not affect the statistics. Being
unsampled means absence from the sampled set, including unused labels
from either summand. Thus labels do not impose a hidden population bound.

Raw real division is totalized in Mathlib, but Option-valued h and p
enforce their genuine domains. Under admissibility, natural spare-degree
subtraction never truncates a negative sampled quantity. A recruited
vertex is in its own recruitment event's susceptible set, so those
denominators are positive. A compatible completion exists for every
admissible datum by adding private leaves; the universal domain criteria
therefore do not hide an empty compatible class. `PointIdentified`
requires a nonempty singleton. `FullRegion` uses least/greatest elements
and hence actual attainment; it does not claim every intermediate value
occurs. There are no integrals, limsups, or empty auxiliary index types.

The following checks passed:

* `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` imports only Defs.
  It compiles concrete admissibility and compatibility examples,
  simultaneous spare-recruiter and mixed-trait domain hypotheses,
  Figure 1 admissibility and degree totals, raw dyad denominator
  calculations, and a literal bad proposal with both source parameters
  defined. It uses no Challenge theorem or `sorry`.
* `python3 scratch/audit_checks.py` uses exact rational arithmetic.
  It checks all eight D assignments, the four Figure 1 extrema and
  attained witnesses, and the Table 1 rounding obstruction. It checks
  762 private-leaf representatives, giving 377 distinct (h,p) pairs.
  Splitting any shared unsampled neighbor into private leaves with its
  original trait preserves all edge-type counts and every recruitment
  event's susceptible cardinality and same-trait susceptible cardinality.
  Therefore it preserves h and p, and these representatives cover all
  attainable statistic pairs. Results are in `scratch/exact-checks.json`.
* Python JSON parsing and schema/target-coverage checks pass for the
  two audit JSON files and the scratch exact-check output.

No `lake` command was run. Lean checks were run one process at a time.
