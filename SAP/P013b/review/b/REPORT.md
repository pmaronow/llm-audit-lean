# Statement referee report

Thirteen targets were audited: **11 correct_whole, 0 correct_restricted,
1 restriction_inaccurate, 1 omission_questionable**. All other verdict counts
are zero. The two issues have severities **1 major, 1 minor**; the other
eleven targets have severity none. No theorem was found false or vacuous.

`reading.md` was saved before opening `claims.json`. `claim-stage.json` was
saved before opening `record.json`. No claim-stage relation was revised
after reading the record. The record's `refuted` decision for T18 is accepted
as a correct full refutation; the claim-stage value `different` continues to
record that its statement is the logical negation of the printed universal
coverage claim, rather than that positive assertion.

## P013-T20 — omission_questionable, major

There is no Challenge theorem for Proposition 3.1. The omission rationale
in `record.json:159`, repeated for both excluded strong-law rows at lines
176 and 196, says that mutual independence of the infinite sequence is
absent from the canonical sampling hypotheses. But `claims.json:102`
explicitly says:

> Formalize with an infinite sequence of independent replicates, each
> distributed as the design

That same note ends by confirming independent whole-design replicate
draws. Thus the record's reason for excluding the only listed rows that
prove the limits contradicts the supplied target. Finite expectation
identities alone do not establish almost-sure limits, but that correct
observation does not repair the erroneous exclusion rationale.

Reassess the two strong-law rows against the requested independent-draw
reading and include the two almost-sure matrix limits, with diagonal-only
smoothing in the same-exposure matrix. If some other obstruction exists,
name it accurately. Their actual signatures and proofs are outside the
permitted files, so this report does not certify their reuse. The available
Mathlib supplies `ProbabilityTheory.strong_law_ae_real` in
`Mathlib/Probability/StrongLaw.lean:597`, sufficient for the bounded
Bernoulli entry variables once their independence and distribution are
provided. A fixed finite matrix needs only a finite intersection of the
entrywise probability-one events.

The intended hypotheses are satisfiable: one unit with fair binary
exposure and independent replicate draws on the infinite fair-coin product
space already gives a nontrivial same-exposure limit of 1/2. This target
is marked questionable because its whole omission rests on a misreading,
not because finite identities were mistaken for limit theorems.

## P013-T24 — restriction_inaccurate, minor

The mathematical loss, identification, exclusion and conditional scaling
formulas are correct. Most of the restriction is accurately disclosed.
The defect is the specific assertion in
`SAP/P013b/Challenge/Part1.lean:49-51`, repeated in `record.json:253`, that
the item and survey nonrespondents' **containment** is a hypothesis of the
scaling clause.

The canonical containment is

    survey nonrespondents ⊆ item nonrespondents,

equivalently, for the retained respondent sets,

    item ⊆ survey.

The clause at `SAP/P013b/Defs/Part8.lean:116-122` only assumes
`item ⊆ S`, `survey ⊆ S`, their cardinalities, positive weights and
retention of every nonzero score in both sets. It has no `item ⊆ survey`
hypothesis or conclusion. Thus this canonical relation is omitted entirely,
not moved into the premises.

A nonzero-score separating instance is

    S      = {0,...,2049},
    item   = {0,...,1707},
    survey = {1,...,1899},
    w_i = 2, D_i = i mod 2, G_i = 1 if i=1, otherwise 0.

All numerical hypotheses hold, but unit 0 is a survey nonrespondent and
an item respondent. The missing containment therefore does not follow
from the existing assumptions. This instance was checked directly.

Replace the restriction text with the following, or add the intended
containment as an explicit hypothesis:

> Restricted: the numerical scaling clause assumes item and survey are
> subsets of S, with |S|=2050, |item|=1708 and |survey|=1899, positive
> weights, and zero outcomes outside either retained set. It does not
> assume or establish item ⊆ survey, equivalently containment of survey
> nonrespondents within item nonrespondents. The reconstruction data
> facts, the link to the released orange-wristband indicator, and
> reproduction of the twelve rounded Table 2 estimates are not verified.
> Strictness of the comparison between the sufficient and necessary loss
> conditions is not separately asserted.

No change to the estimator or scaling formulas is needed.

## Verification and scope

`scratch/Check.lean` imports only `SAP.P013b.Defs` and compiled successfully
with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`. It checks concrete
positive, nonzero no-effect covariance hypotheses, genuine exposure
misspecification, a two-student instance in which all five exposure
probabilities are positive, and the diagonal-only witness for the exact
printed dependency predicate. `scratch/lean-check.log` is empty on the
successful run. No Challenge stub was used as a proof.

`scratch/audit_checks.py` independently checked 120 finite rational
designs, including signed outcomes, zero joint probabilities and 176
empty-exposure ratio cases. It also checked the exact location and
reporting tables, the school counts and variance biases, and the T24
separating instance. Results are in `scratch/audit-checks.log`. These
finite checks were not used to infer asymptotic theorems.

T18 has a separate mathematical witness: use a common fair exposure Z at
each size N and nested treated potentials sqrt(i+1)−sqrt(i), with zero
control potentials. Their total is sqrt(N), so N times the true effect
variance is 1. Printed Condition 5 admits diagonal-only h with row bound
1. On the assignment Z=0 the variance estimate is zero and the estimation
error is nonzero; coverage is at most 1/2 at every N. Alpha=1/4 therefore
refutes the printed lower bound 3/4. Every probability is bounded, and no
zero population size, negative-variance square root, or unbounded liminf
is doing the work.

The paper was consulted only to check application-specific network
semantics: Section 10 describes an undirected graph built from within-school
peer nominations, consistent with T27's symmetric within-school neighbor
sets. [Paper, Section 10](https://arxiv.org/pdf/1305.6156#page=25).
The released scripts, data and underlying formalization were not inspected;
no statement here certifies their empirical provenance or the twelve
published estimates.
