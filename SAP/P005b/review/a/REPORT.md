# Palomar statement audit: P005b

All 13 targets have a theorem. There are **9 correct_whole**,
**1 correct_restricted**, and **3 restriction_inaccurate** verdicts.
The three issues have minor severity. There are no false, vacuous,
not_faithful, omitted, or major-severity targets.

| Verdict | Count |
| --- | ---: |
| correct_whole | 9 |
| correct_restricted | 1 |
| restriction_inaccurate | 3 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

The blind mathematical reading was saved in [reading.md](/home/ubuntu/sap/tasks/CHFID-P005b-a/reading.md)
before opening claims.json. The independent comparison was saved in
[claim-stage.json](/home/ubuntu/sap/tasks/CHFID-P005b-a/claim-stage.json) before opening record.json.
No stage-2 reading or relation-to-claim verdict was changed after
opening the record. Full per-target results, proposed repairs and
nonvacuity instances are in [findings.json](/home/ubuntu/sap/tasks/CHFID-P005b-a/findings.json).

## P005-T25 — restriction_inaccurate, minor

The theorem states the complete canonical stochastic expansion.
Its docstring at
[Challenge/Part1.lean:63](/home/ubuntu/sap/tasks/CHFID-P005b-a/SAP/P005b/Challenge/Part1.lean:63)
and its record entry say that positive dimension is an added hypothesis
and that the canonical claim imposes only d_n<=n.

However, this target's canonical_claim.definitions_needed in claims.json,
under "[Reading of the order symbols]", explicitly specifies
"1 <= d_n <= n". The sequence paragraph of the canonical statement
mentions just d_n<=n, but the accompanying explicit definition of the
sequence already supplies positivity. The claimed additional
restriction therefore is not a restriction relative to the supplied
canonical package. This is a documentation and decision-classification
defect; I found no false mathematical assertion in the Lean statement.

Repair the docstring to say:

> The dimension convention 1 <= d_n <= n agrees with the canonical
> order-symbol definitions. No conclusion is omitted.

The record decision should be whole, with restriction null.

## P005-T26 — restriction_inaccurate, minor

The docstring at
[Challenge/Part1.lean:69](/home/ubuntu/sap/tasks/CHFID-P005b-a/SAP/P005b/Challenge/Part1.lean:69)
and the record likewise describe 1<=d_n as added.
This target's own canonical order-symbol definitions already require
1<=d_n<=n. That description is inaccurate.

The actual omissions are correctly disclosed: the
O_p(sqrt(kappa_n/n)) remainder bound without leverage decay, and the exact
identification of the remainder with the printed term (*) on p.1516.
The retained little-o expansion has the correct leading term,
hypotheses and probability quantifiers.

Keep the restricted decision, but replace its restriction text and the
docstring restriction with:

> Retains the o_p(n^(-1/2)) expansion under kappa_n -> 0. Omits the
> O_p(sqrt(kappa_n/n)) remainder bound without leverage decay and the
> exact identification of the remainder with term (*) on p. 1516.
> Positive dimension is already part of the canonical order-symbol
> definitions.

## P005-T27 — restriction_inaccurate, minor

The docstring at
[Challenge/Part1.lean:76](/home/ubuntu/sap/tasks/CHFID-P005b-a/SAP/P005b/Challenge/Part1.lean:76)
and the record make the same inaccurate claim of an added
positive-dimension hypothesis. The target's canonical order-symbol
definitions explicitly already require 1<=d_n<=n.

The omission of O_p(sqrt(kappa_n/n)) without leverage decay is accurately
disclosed. The retained arm-specific little-o expansion matches the
canonical formula.

Keep the restricted decision, with this replacement restriction text:

> Retains the interacted o_p(n^(-1/2)) expansion under kappa_n -> 0.
> Omits the O_p(sqrt(kappa_n/n)) remainder bound without that decay
> condition. Positive dimension is already part of the canonical
> order-symbol definitions.

## Other decisions and verification

The whole decisions for T15–T18 and T22–T24 are justified.
T21's restricted decision is accurate and completely disclosed: its main
unbiasedness and inverse-free clauses retain the full nonempty-arm
domain, and only the listed proof-step clauses require both arm
sizes to be at least two. No target is omitted.

T19 and T20 are correct faithful refutations, as the record declares.
Their correct_whole verdicts mean that the refutations address the
printed claims; they do not mean that the positive printed claims are
true. The stage-2 relation "different" records their negative polarity
and has not been changed.

For T19, a seven-unit, six-treated design with
a=(10,1,1,1,1,1,1), b=(1/10,1,1,1,1,1,1)
has covariance variance 243/1568, exceeding the printed bound
31853/226800. Its expectation identity is still true.
For T20, a standardized five-unit, one-covariate population with
x=(-3/2,-1/2,0,1/2,3/2), yT=x^2, yC=0 and m=2
has actual third-bias component 21/320 against printed -21/320,
with all arm matrices nonsingular. The literal-logarithm refutation
also has a positive-dimensional sequence with distinct covariates,
bounded second moments and all-assignment nonsingularity; its remainder
grows linearly although d=1 makes kappa*log(d) identically zero.
The construction and analytic argument are in
[scratch/checks.md](/home/ubuntu/sap/tasks/CHFID-P005b-a/scratch/checks.md).

Nonvacuity is not inferred from empty dimensions. A distinct centered,
variance-normalized linear grid with d_n=1, m_n=floor(n/2) and bounded
quadratic outcomes satisfies all the positive sequence hypotheses.
Its maximum leverage is 3(n-1)/(n(n+1))->0, and both arm matrices
are nonsingular for every assignment once n>=4.

Independent exact-rational enumeration in
[scratch/audit.py](/home/ubuntu/sap/tasks/CHFID-P005b-a/scratch/audit.py) checked 92 regression allocations,
492 third-moment allocations, both finite refutation witnesses,
and 1266 allocations of the logarithm counterexample.
Results are saved in
[scratch/audit-results.json](/home/ubuntu/sap/tasks/CHFID-P005b-a/scratch/audit-results.json).
The scratch Lean file [scratch/Check.lean](/home/ubuntu/sap/tasks/CHFID-P005b-a/scratch/Check.lean) imports
only SAP.P005b.Defs and successfully checks the concrete standardized
population, nonempty design, both forms of all-assignment regularity,
leverage covariance 21/20, and the actual third-bias component 21/320.
The command /home/ubuntu/sap/tools/sap-lean scratch/Check.lean completed
with exit code 0. No Solution, Comparator, or original
formalization was read; lake was never run.
