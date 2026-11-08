# Review of P009-T40 through P009-T44

All five declarations are faithful to their declared scope. T40 is correctly
classified as restricted; T41–T44 state their whole canonical claims. There are
no current issues, including documentation defects.

`reading.md` was saved before opening the claims, earlier findings, architect
report, or record. It unfolds all five statement closures, including generated
fields and the auxiliary declaration about 2. `claim-stage.json` was saved
before opening `record.json`. The record required no change to that comparison.

| Declaration | Comparison with canonical claim | Record judgment | Verdict |
| --- | --- | --- | --- |
| T40 | Narrower Hájek conclusion | Accurate restriction | faithful / none |
| T41 | Whole | Correct | faithful / none |
| T42 | Whole | Correct | faithful / none |
| T43 | Whole | Correct | faithful / none |
| T44 | Whole | Correct | faithful / none |

T40 preserves sizes, designs, replacement regularity, the positive density
limsup, and unconditional HT inconsistency. Its Hájek conclusion additionally
requires every supported assignment to have both weighted arms eventually.
`Challenge/Part1.lean:38` and the record disclose exactly that loss of scope.
Interior individual marginals alone do not imply this guard. The quantified
replacement precedes the universal extension, so one replacement works for all
extensions under the guard.

T41 and T43 cover every real Hájek extension. Under uniformly interior
Bernoulli assignment, the probability of an empty arm is at most
`2*(1-1/k)^n`, which vanishes. Arbitrary real values on those events therefore
preserve the stated asymptotic conclusions. Complete and paired randomization
give nonzero weighted denominators on their support, so the explicit zero
extension in T42 and T44 does not change their claims. All printed consistency
conclusions and rate terms are present.

The finite probability laws, unconditional EATE, full-cube structural
interference (including its diagonal), outgoing C1 counts, paired dependence,
and convergence predicates render the canonical notions correctly. Positive
sizes and marginals remove inverse-weight junk values; dependence has a
positive diagonal, so all stochastic rates are positive. The real-power bases
and square-root arguments are in their ordinary domains. T40 uses explicit
finite-limsup bounds on sequences in [0,1]. No conclusion is encoded in a
definition or assumed as a hypothesis. The paper's definitions and five
results were also cross-checked against its [archived manuscript, sections 4
and 5.1–5.2](https://pmc.ncbi.nlm.nih.gov/articles/PMC8372033/).

Both earlier issues are fixed. The shared `hajek` docstring at
`SAP/P009c/Defs/Part1.lean:80` now describes the zero extension, limits its
support guarantee to complete and paired randomization, and distinguishes
statements allowing arbitrary extension values. It no longer makes the false
package-wide support assertion identified separately for T42 and T44. Each
resolution is recorded in `findings.json`.

The independent checks in `scratch/Nonvacuity.lean` import only Defs and use no
Challenge stubs or additional axioms:

- T41/T43: `fairStudy`, with n=t+2, independent fair bits, zero outcomes,
  k=2, q=2, s=1 and d_AVG=1. A real extension exists, and the eventual support
  guard fails.
- T42: `completeStudy`, with n=2(t+1), p=1/2, m=t+1 and zero outcomes.
  The binomial support count, all regularity hypotheses, restricted
  interference, and C1/sqrt(n)→0 are checked; d_AVG=C1=1.
- T44: `pairedStudy`, with n=2(t+1), an explicit fixed-point-free involution,
  the full uniform paired law and zero outcomes. All hypotheses hold jointly;
  d_AVG=e_AVG=1 and R_SUM=0.
- T40: `denseStudy` satisfies the outer hypotheses with independent fair
  bits and density 1. The explicit replacement `badStudy` has
  y_i(z)=1[z_0=true]*(1/2 if z_i=true, otherwise -1/2). It has the same
  designs, sizes and density, satisfies regularity, has EATE=1/2 and HT=z_0,
  and has absolute HT error 1/2 everywhere. The file checks failure of
  convergence in probability. The guarded Hájek branch is also nonvacuous:
  use fair paired assignment and the same replacement formula on even growing
  sizes. Each arm has n/2 units, so Hájek=HT=z_0 on support; marginals are
  1/2, EATE remains 1/2, and full-cube dependence density remains 1.

Validation command: `/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean`.
`findings.json` and `claim-stage.json` were parsed and checked with Python,
including exact target coverage and fingerprints from `closure.json`.
