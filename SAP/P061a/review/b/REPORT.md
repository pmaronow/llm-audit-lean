# P061a statement audit

Eleven targets audited: ten retained theorems and one omission. No statement
or disclosure defect was found.

| Verdict | Count | Targets |
| --- | ---: | --- |
| `correct_whole` | 7 | T1, T2, T3, T6, T8, T9, T11 |
| `correct_restricted` | 3 | T4, T5, T7 |
| `omission_ok` | 1 | T10 |
| `restriction_inaccurate` | 0 | |
| `not_faithful` | 0 | |
| `vacuous` | 0 | |
| `false` | 0 | |
| `omission_questionable` | 0 | |

Severity: none 11; minor 0; major 0. There are no items outside
`correct_*`/`omission_ok` requiring a correction.

## Order and scope

The definitions and Challenge were read first, including the referenced
Mathlib conventions for infinite sums, extension functions, finite product
indexing, square roots and bounded continuous tests. The mathematical
reading was saved in `reading.md` before `claims.json` was opened.
`claim-stage.json` was then saved before `record.json` was opened. No
step-2 classification was changed after reading the record.

The paper comparison uses the canonical statements, definitions and quoted
standing assumptions supplied in `claims.json`. Audit-history notes and
unused-row explanations supply no additional clauses or exceptions. The
record's referenced formalization was not inspected, and theorem proofs
were not part of this statement audit.

## Record decisions and disclosures

T1 and T2 certify the canonical counterexamples to specified readings of the
printed comparison. Their docstrings identify those readings and do not
call the printed assertion itself false. T3 gives both corrected comparisons
with the canonical positivity, targeted moments and joint independence
hypotheses. Extending its exposure-level response schedule to all real
vectors is harmless: arbitrary extension adds no restriction on the
supported hybrid evaluations.

T4's restriction is accurately disclosed: it retains the explicit independent
correlated-pair model, partner-only responses, covariance, exact moments,
positive standard errors, squared standardized-gap divergence and coverage
limits. It does not separately formulate the graph predicates, alternate
variance expression, unsquared divergence or order classifications. The
restriction also correctly explains the finite range m>=2 and limit
reindexing m=n+2. The omitted graph and rate assertions are consequences
of the retained model, rather than counterexamples to it.

T5 accurately discloses separate absolute integrability of each hybrid,
strict positivity of every estimated scale, interval conclusions only for
ADE and positive q at continuity endpoints, the absence of a separate AEED
interval assertion, a finite common alphabet with full assignment space for
the local bound, and omission of the explicit T4 sequence. These are the
differences found independently at step 2.

T6 uses exactly the finite common domain in its canonical claim; it is not
an undisclosed finite-support repair of a general-domain assertion. T8 gives
the general targeted-first-moment repair and both canonical sufficient
conditions. T9 gives the full specified four-unit witness to design
dependence, including support stability under both designs and failure of
global stability.

T7's declared scope matches the statement: it retains the full real-domain
geometric design, support, positivity, ordinary zero-cell mean, exact
alternating response and HT terms, partial sums, and nonsummability of both
sign parts. It does not separately state ordered-sum nonconvergence,
derived AEPO/EED/AEED nonexistence or extended-real infinity identities.
Its retained certificates imply ordinary-mean failure without interpreting
Mathlib's totalized divergent sums as ordinary expectations.

T10's omission is justified on the visible canonical formal content: the
target transcribes three rate conditions with the population index
corrected, without asserting that an arbitrary dependency graph satisfies
them or asserting a theorem relating them. Omitting this definitional
transcription is consistent with the record's reason.

T11 is a correct **refutation**, included in `correct_whole`. Its canonical
claim asserts ordinary-mean existence for arbitrary raw outcomes under
positivity alone. The normalized geometric example satisfies the standing
assumptions and positivity but has divergent positive and negative response
parts. The theorem contradicts that existence assertion itself. Thus the
record's `refuted` decision and the docstring's statement that the printed
claim is false are justified. This does not mean the Lean theorem is false.

## Nonvacuity and verification

`findings.json` gives a concrete witness or satisfiability explanation for
every target. The universal claims have positive-size, distinct-target
instances; the transfer theorem also has an instance with a nondegenerate
limiting law. No impossible hypothesis or conclusion assumed as a hypothesis
was found.

The atomic representation is faithful to the standing discrete design:
nonnegative summable masses of total one give masses at most one, countable
positive support and a countably additive probability on every subset.
All positive denominators and necessary finite absolute moments are present
or follow from finite domains. T3 proves hybrid feasibility on relevant
supported assignments; T5 assumes it explicitly. T2 tests infeasibility
directly without assigning it a numerical response. T7 and T11 certify
nonsummability rather than using the zero default of a divergent `tsum`.
The local-bound extrema in T5 are over finite nonempty function spaces.
Natural subtraction in T2 is guarded by K>0, and the inference limits in
T4 evaluate only m>=2.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with exit code
0. These checks import only the definitions and construct their own designs;
they use no Challenge stubs. They verify normalized positive binary-pair
designs, positive target probabilities, finite targeted moments, coordinate
independence, a stability instance, outcomes varying within an exposure cell,
conditional means, and point-design weak/probability convergence. The only
compiler messages on the successful run were two optional `simpa` style
lints. At most one Lean process ran at a time; `lake` was never run.

Independent exact-rational checks in `scratch/audit_finite.py` passed for
T1 (N=1,2,3,4), T2 (K=1,2,3), T4's single-pair moments and variance polynomial
(m=2,...,40), and both complete T9 supports. Results are in
`scratch/finite-checks.json`. The general T4 variance follows by averaging
independent pair scores; its limiting claims follow from the retained exact
formulas and polynomial bounds. These finite checks support, and do not
replace, the mathematical reading of the quantified statements.

Both requested JSON audit files were parsed and checked with Python. The
findings cover every canonical target exactly once and match the retained
theorem names and the sole omission.
