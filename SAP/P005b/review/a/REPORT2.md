# P005b delta review

All **3 earlier findings are fixed**: 3 fixed, 0 partly fixed, 0 not
fixed. No new issue was found.

The 13 findings are **10 correct_whole** and **3 correct_restricted**;
all have severity none. All other verdict counts are zero.
The 10 correct_whole findings include the two faithful refutations.
The corresponding record2.json decisions are **8 whole, 3 restricted,
2 refuted, 0 omitted**.

## Earlier findings

| Target | Resolution | Verified correction |
| --- | --- | --- |
| P005-T25 | Fixed | [The revised docstring](/home/ubuntu/sap/tasks/CHFID-P005b-a/SAP/P005b/Challenge/Part1.lean:63) identifies positive dimension as canonical. record2.json now says whole and has restriction null. The complete stochastic expansion is retained. |
| P005-T26 | Fixed | [The revised docstring](/home/ubuntu/sap/tasks/CHFID-P005b-a/SAP/P005b/Challenge/Part1.lean:69) removes the alleged added dimension hypothesis and lists both actual omissions. record2.json agrees. |
| P005-T27 | Fixed | [The revised docstring](/home/ubuntu/sap/tasks/CHFID-P005b-a/SAP/P005b/Challenge/Part1.lean:77) removes the alleged added dimension hypothesis and identifies exactly the omitted remainder bound without leverage decay. record2.json agrees. |

For each target, claims.json's canonical order-symbol definitions
explicitly require 1<=d_n<=n. The architect's explanation of the earlier
mistake and these corrections agrees with the supplied canonical text
and the revised files. No earlier finding is only partly resolved.

## Statement and label comparison

I reread all seven Defs parts, both root imports, and the Challenge
against the saved [blind reading](/home/ubuntu/sap/tasks/CHFID-P005b-a/reading.md).
I found no change to any mathematical definition, hypothesis, quantifier,
or conclusion described there. The observed revisions concern the
T25–T27 docstrings and their classification/disclosure metadata.
All 13 theorem names still assert their corresponding Statement
definitions. No new mathematical assertion needs a new reading.

| Target | Revised decision | Finding | Coverage check |
| --- | --- | --- | --- |
| T15 | whole | correct_whole | Both corrected coefficients, the intermediate treatment fraction, and their combined covariance expression remain. |
| T16 | whole | correct_whole | Corrected finite sums, inclusion moments, coefficient identities, both third moments, and the complement relation remain. |
| T17 | whole | correct_whole | Corrected contraction assertions and both deterministic orders remain. The surrounding variance inequality is excluded by the canonical target itself. |
| T18 | whole | correct_whole | The bracketed vectors, normal equation, and identification with the actual common-residual term remain. |
| T19 | refuted | correct_whole | The negated universal conjunction has exactly the printed uncentered domain. |
| T20 | refuted | correct_whole | The valid exact part and both independent refutations remain. |
| T21 | restricted | correct_restricted | The additional arm-size guards apply only to the disclosed proof-step clauses. |
| T22 | whole | correct_whole | Both unbiasedness results, inverse-free identity, armwise expectations, and weaker centered-covariate assertions remain. |
| T23 | whole | correct_whole | Both decompositions, both bias formulas, covariance interpretation, and both vanishing implications remain. |
| T24 | whole | correct_whole | Both slopes, the bias expression, separate first-component moments, and their difference remain. |
| T25 | whole | correct_whole | The entire canonical expansion under d_n/n -> 0 is present. |
| T26 | restricted | correct_restricted | The leverage-decay little-o expansion remains; both missing stronger conclusions are disclosed. |
| T27 | restricted | correct_restricted | The arm-specific leverage-decay little-o expansion remains; the missing bound without decay is disclosed. |

T25 still quantifies all dimension, allocation, and population sequences
satisfying the canonical standing assumptions, eventual noninteracted
regularity, and d_n/n -> 0. Its conclusion is the common-residual
expansion with remainder O_p(sqrt(kappa_n*d_n/n)). It adds no
leverage-decay premise and drops no clause of the canonical statement.
The whole label is now correct.

T26 retains the common-residual o_p(n^(-1/2)) expansion under
kappa_n -> 0. It does not state the O_p(sqrt(kappa_n/n)) bound without
leverage decay or the exact identification of the remainder with term
(*) on p.1516. Its docstring and revised record disclose both omissions
and accurately identify dimension positivity as canonical.

T27 retains the o_p(n^(-1/2)) expansion with separate population arm
slopes under kappa_n -> 0. The sole disclosed missing conclusion is
O_p(sqrt(kappa_n/n)) without that decay condition. Its restricted label
and revised disclosure are accurate.

T21's unchanged disclosure remains accurate: n>=3 and nonempty arms
suffice for its main clauses, together with standardization and the
specified regularity. Only the listed expectations of (11) and (12),
the equivalent coefficient formula, and coefficient collection acquire
both-arm-size-at-least-two hypotheses.

## Junk values and nonvacuity

The revised labels introduce no new domain convention. In the sequence
statements, every sufficiently large n is positive, both arms are
nonempty, and their design has positive cardinality. Relevant inverses
are protected by the same eventual all-assignment determinant
conditions as before. The real supremum defining kappa is over a finite
nonempty population. Eventual standardization and d_n>=1 imply
kappa_n>=d_n/n>0, so the stochastic rates are positive eventually.
Exceptional initial sizes do not affect the limits.

A single positive-dimensional construction realizes all hypotheses of
T25–T27. For n>=3, i=0,...,n-1, take

\[
 d_n=1,\qquad m_n=\lfloor n/2\rfloor,\qquad
 x_{ni}=\sqrt{\frac{12}{n^2-1}}\left(i-\frac{n-1}{2}\right),
 \qquad y_{T,ni}=x_{ni}^2,\quad y_{C,ni}=0.
\]

Fill the finite prefix arbitrarily. These distinct covariates have
population mean zero and second moment one. Their squared maximum is
3(n-1)/(n+1)<3, so the outcome and covariate second moments have a common
bound K=3. Treatment proportions lie strictly between 1/4 and 3/4.
The pooled matrix is positive for every assignment for n>=3, and both
arm matrices are positive for every assignment for n>=4. Moreover,

\[
 d_n/n\longrightarrow0,\qquad
 \kappa_n=\frac{3(n-1)}{n(n+1)}>0,\qquad \kappa_n\longrightarrow0.
\]

Thus none of the three corrected labels relies on an empty dimension,
an empty design, a zero rate, or a singular inverse convention.
The additional T21 denominators remain guarded by arm sizes at least
two, and its unrestricted main domain retains the singleton-arm
instances checked in the first review.

## Refutations and verification

T19 still refutes the printed reading: n=7,m=6,
a=(10,1,1,1,1,1,1), b=(1/10,1,1,1,1,1,1) yields variance
243/1568 greater than the printed bound 31853/226800. The expectation
clause is true in that witness; the theorem does not separately deny it.

T20 still refutes the printed third-component signs under nonsingular
standardized hypotheses. For n=5,d=1,m=2,
x=(-3/2,-1/2,0,1/2,3/2), yT=x^2,yC=0, the actual component is
21/320 and the printed value is -21/320. Its additional literal-logarithm
refutation retains the d=1, distinct-covariate sequence established in
[the earlier independent checks](/home/ubuntu/sap/tasks/CHFID-P005b-a/scratch/checks.md),
where kappa*log(d)=0 and the remainder grows linearly despite eventual
all-assignment nonsingularity.

I reran /home/ubuntu/sap/tools/sap-lean scratch/Check.lean against the
refreshed definitions; it completed with exit code 0. This independent
scratch file imports only SAP.P005b.Defs and verifies standardization,
nonempty design, both regularity conditions, the leverage covariance
21/20, and the actual third-component moment 21/320. The successful
compiler output is empty, as recorded in
[delta-lean-check.log](/home/ubuntu/sap/tasks/CHFID-P005b-a/scratch/delta-lean-check.log).
The earlier exact-rational enumeration and analytic nonvacuity arguments
remain applicable to the unchanged mathematical statements.

The review does not rely on the architect's proof or Comparator
certification claims. No Solution, Bridge, original project source, or
other referee's files were opened, and lake was not run.
[findings2.json](/home/ubuntu/sap/tasks/CHFID-P005b-a/findings2.json)
contains exactly one result per canonical target with the original
schema. No repair remains to recommend.
