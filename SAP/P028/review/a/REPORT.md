# P028 statement audit

| Verdict | Count | Targets |
| --- | ---: | --- |
| correct_whole | 3 | T4, T7, T8 |
| correct_restricted | 6 | T1, T2, T5, T6, T9, T10 |
| omission_ok | 1 | T3 |
| restriction_inaccurate | 0 | |
| not_faithful | 0 | |
| vacuous | 0 | |
| false | 0 | |
| omission_questionable | 0 | |

All ten targets have severity `none`. There are no adverse items requiring a fix.

## Scope and order

The blind reading of every stub and its SAP definitions was saved in
`reading.md` before opening `claims.json`. `claim-stage.json` was then saved
before opening `record.json`. No claim-stage verdict changed after the record
was read. Every architect decision agrees with that independent comparison.
The comparisons use each canonical statement, definitions_needed, and standing
assumptions. Audit-history notes do not remove clauses or excuse omissions.

## Accepted restrictions

| Target | Accurately disclosed reduction |
| --- | --- |
| T1 | Exact tables replace completion parameters/formulas and the conditional Bernoulli construction; A/N probabilities are not separately asserted. All N1–N5 content and finite-law nonidentification remain. |
| T2 | Omits the cellwise-versus-arm mean counterexample, source-law endpoint attainment, and consequent sharpness. The formulas, sufficient response assumptions, reweighting, sensitivity inequalities and eight values remain. |
| T5 | Omits E5's entire feasible-set equalities and the specified E6 construction; retains the counterexample, numerical endpoints, and existence of a bounded realization of the input triple. |
| T6 | Omits its own p=1 existence witness, the optional positive-cell probability-times-mean representation, and the separate empty-cell zero-moment assertion. Both compliance branches and all stated bounds remain. |
| T9 | Requires both potentials to be measurable and globally absolutely integrable. Positive observed cells implement ordinary conditional-mean existence; identification and the noncomplier ratio remain. |
| T10 | The universal LATE identities require measurable globally integrable potentials. The full existential nonidentification claim remains. |

The T9/T10 domain reductions are genuine. For example, take independent uniform
S in {A,N,C}, fair Z, and a variable H with
P(H=2^n)=2^(-n-1), n≥0. Set Y0=0, Y1=1 on A and C, and Y1=H on N.
Observed Y=D, every observed cell mean is finite, both complier means and CACE
are finite, all four cells are positive, and random assignment holds.
Nevertheless E|Y1|=∞. Thus finite moments printed in those claims do not imply
the additional CausalModel moment field. Their docstrings identify the loss.

T3 is a printed empirical application passage. Omitting it as a separate theorem
is justified: the conditional population identification is handled by T9,
the missing-response identification reading by T1, and its repairs by T2.
The material supplies no deterministic theorem that its printed empirical
estimates equal exact population quantities. Neither T1 nor the record labels
those printed numerical estimates false. T5 and T7 concern the precise printed
proof steps described in their canonical counterexample claims, rather than
refuting Proposition 1 or positive-cell Corollary 1.

## Checks and limits

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with exit code 0
and no diagnostics. It imports only `SAP.P028.Defs`, constructs a fair
full-compliance model and a six-point mixed-stratum model, proves bounded
outcomes for both, proves p=1 for the former, and proves positivity of all four
treatment-assignment cells for the latter. With R=1 the latter also satisfies
all response-identification premise sets simultaneously. Every hypothesis set
has a concrete instance; none assumes its conclusion.

`python3 scratch/verify.py` passed. Exact rational checks independently rebuilt
both canonical 17-atom Bernoulli laws and matched every atom and weight in the
SAP definitions, verified normalized positive product laws, all observed cells,
positive conditioning events, complier and arm means, both Corollary plug-ins,
and all eight source-table values. It additionally checked interval
nonemptiness, translated endpoints, and endpoint/midpoint realization for 480
compatible triples. Results are in `scratch/exact-results.json`. These finite
checks support the independent algebraic reading; they are not universal Lean
proofs of the Challenge stubs, whose proofs are outside this statement audit.

All real/rational divisions, conditional means, and Bochner integrals were
checked against Mathlib semantics. Positivity guards exclude invalid ordinary
conditional means where used; the full-compliance diagnostic states failed
side conditions rather than exploiting totalized division. The arbitrary
ambient-type quantifiers do not replace concrete existential attainability.
No theorem relies on a truncated subtraction, unbounded limsup, or empty index
type. No changes to the supplied definitions or challenges were needed.

Python parsing and coverage checks passed for `claim-stage.json`,
`findings.json`, and the saved exact-arithmetic results.
