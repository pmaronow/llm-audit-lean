# Delta statement review

18 targets: **6 correct_whole, 12 correct_restricted, 0 outstanding adverse findings, 0 omissions**. The two T14 disclosure issues described in the architect's account of the other referee are **fixed**; none is partly fixed or not fixed.

| Verdict | Count |
| --- | ---: |
| correct_whole | 6 |
| correct_restricted | 12 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

The comparison baseline was the saved [blind reading](/home/ubuntu/sap/tasks/CHFID-P003a-a/reading.md). I reread all current Defs and Challenge files, compared their mathematical content with that reading, reviewed the canonical claims and revised decisions, and checked the architect's account. I found no changed theorem type, packaged mathematical statement, or supporting mathematical definition. The changed scope disclosure is T14's Challenge docstring; the only changed field between `record.json` and `record2.json` is T14's restriction text. All eighteen theorem names and target associations remain correct.

## Earlier findings and the T14 correction

My original `findings.json` reported no adverse issues: all eighteen `issues` lists are empty. Thus there are no earlier adverse findings of mine to classify as fixed, partly fixed, or not fixed. Each previous target verdict has been rechecked below and remains the verdict for the current package.

My earlier endorsement of T14's old disclosure as complete was too generous. The [saved reading, line 105](/home/ubuntu/sap/tasks/CHFID-P003a-a/reading.md:105) already said there was no separate source lattice function in the proposition. Canonical T14(iii) supplies that source law and identifies the constructed integer mass as the law of kX. The old disclosure did not fully account for this omission, and its description of normalization could suggest a transported conclusion. I agree with the other referee's two objections to that old wording. The revised disclosure fixes both, without restoring omitted mathematical clauses.

| Reported T14 issue | Status | Evidence and assessment |
| --- | --- | --- |
| Missing disclosure of the source lattice law, construction g(j)=f(j/k), and identification as the pmf of kX | **Fixed** | The [revised restriction](/home/ubuntu/sap/tasks/CHFID-P003a-a/SAP/P003a/Challenge/Part2.lean:13) explicitly lists all three omissions. The actual [T14Statement](/home/ubuntu/sap/tasks/CHFID-P003a-a/SAP/P003a/Defs/Part9.lean:13) still quantifies only k and g. It is correctly labelled restricted. |
| Normalization is already assumed in IsMass | **Fixed** | The [revised restriction](/home/ubuntu/sap/tasks/CHFID-P003a-a/SAP/P003a/Challenge/Part2.lean:11) expressly retains only normalization already contained in the hypothesis and the coordinate-mean identity. This matches [IsMass](/home/ubuntu/sap/tasks/CHFID-P003a-a/SAP/P003a/Defs/Part4.lean:36), whose third conjunct is total mass one. The introductory sentence now refers to an assumed integer mass. |

T14's revised disclosure is accurate and complete for the retained statement. It also discloses the absolute-first-moment hypothesis on the whole lattice component, even though canonical normalization and reindexing require only a PMF. The impossibility of unrestricted decrease, zero and fair SD examples, fair mean, and fixed printed-rescaling witness remain present. No current statement or docstring fix is requested.

## Target-by-target recheck

“Retained” below means there was no adverse finding in my earlier review and the current scope was checked again. T14 additionally received the correction assessed above.

| Target | Earlier finding / disposition | Revised label | Current verdict | Clause or scope check |
| --- | --- | --- | --- | --- |
| P003-T29 | correct_whole; retained | whole | correct_whole | Every positive finite population, every 0<m<n and interior real level; the weighted count law represents all labeled binary tables and complete randomization. Coverage and the required empty-inversion convention agree with the claim. |
| P003-T1 | correct_restricted; retained | restricted | correct_restricted | The legal missingness witness, exact coverage failure and critical tails still refute the printed assertion. The omitted labeled identities, inclusions, proof inequalities, extrema and numerical tables remain disclosed. |
| P003-T2 | correct_whole; retained | whole | correct_whole | Arbitrary dependent missingness under balance, completion inclusion, and all substantive coupling conclusions (a)-(f) are present, including possibility, shifts, all-assignment deviation bound, p-value comparison and upper endpoint. Completion inclusion also supplies the lower bound. |
| P003-T3 | correct_whole; retained | whole | correct_whole | Both joint-law coverage bounds, both containments, true-data completion, distinct completion count, complete-data coverage and repaired numerical hull/coverage are present. The finite completion enumeration gives the stated bound on inversion calls. |
| P003-T4 | correct_restricted; retained | restricted | correct_restricted | The legal wrong-return and nontermination examples and executed balanced upper-search failure remain genuine printed-reading refutations. The additional traces, budgets, domain calculations and examples remain disclosed omissions. |
| P003-T5 | correct_restricted; retained | restricted | correct_restricted | Threshold correctness and valid, distinct logarithmically bounded traces are retained. The omitted intermediate invariants, arbitrary-decision adjacency/nonexhaustion certificate and application budgets remain accurately disclosed. |
| P003-T11 | correct_restricted; retained | restricted | correct_restricted | The actual all-zero randomization tail has a nonempty real rejecting half-line with no minimum, refuting the printed existence claim. Omission of the universal version remains explicit. |
| P003-T12 | correct_restricted; retained | restricted | correct_restricted | The general finite-support threshold dichotomy and strict rejection bound remain present; the missing experiment-specific inversion steps are explicitly omitted. Positive weights are valid for the support representation. |
| P003-T13 | correct_whole; retained | whole | correct_whole | Both potential-outcome marginal sums, total population size, corrected effect formula and both numerical printed-numerator witnesses are present. |
| P003-T14 | correct_restricted; old disclosure endorsement corrected; both other-referee issues fixed | restricted | correct_restricted | The revised restriction exactly describes the assumed input normalization and coordinate-mean identity, stronger moment premise, retained witnesses, and omitted source-law construction/correspondence. |
| P003-T9 | correct_restricted; retained | restricted | correct_restricted | The common-Boolean law genuinely gives SD marginals and a non-SD sum; the omitted integer-centered second counterexample remains disclosed. |
| P003-T10 | correct_whole; retained | whole | correct_whole | Independent convolution closure, its defining mass formula, half-integer center shift and shape monotonicity, and parity-lattice closure with both duplicated masses are present. Integer indexing represents the scaled laws for arbitrary lattice denominator. |
| P003-T15 | correct_restricted; retained | restricted | correct_restricted | The full positive balanced discordant-population SD lemma remains; the omitted induction facts, case laws and printed-proof-gap witnesses remain disclosed. |
| P003-T16 | correct_restricted; retained | restricted | correct_restricted | The normalized signed sum and all six corrected pair outcomes remain; the remaining-subject formula, printed-expression laws and sampling construction remain disclosed omissions. |
| P003-T17 | correct_restricted; retained | restricted | correct_restricted | The simplified variance, fixed extension, zero condition, nonzero-numerator witness, Monte Carlo rank bound and extension-dependent exact tails remain. The omitted printed-formula derivation and additional examples/counts remain disclosed. |
| P003-T21 | correct_restricted; retained | restricted | correct_restricted | Accepted numerators, interval, estimate exclusion and the negative p-value remain; lattice/table enumerations, maxima and additional certificates remain explicitly omitted. |
| P003-T22 | correct_restricted; retained | restricted | correct_restricted | The minimum-base/reuse representation of every possible table and reduced n=2 witness remain. Omitted executed confidence sets, other-effect lines and labeled realization remain disclosed. |
| P003-T23 | correct_whole; retained | whole | correct_whole | All three arbitrary-decision endpoint/trace implications remain, including all later queries after a rejection and the arbitrary-u consequence. Substitution gives the claimed exact-endpoint application. |

All twelve revised record restriction texts match the corresponding current Challenge docstrings after whitespace normalization. No row is labelled `refuted` or `omitted`. The canonical counterexample targets T1, T4, T9 and T11 remain correctly restricted because they omit declared parts of their canonical packages. Their retained assertions do refute the printed readings; no true printed assertion has been substituted as their conclusion.

## Junk values, nonvacuity and validation

T14 is a disclosure change with unchanged hypotheses and conclusions. Its positive k excludes division by zero. `IsMass` ensures nonnegative normalized summable mass and an absolutely summable first moment, so the mean calculation uses convergent real sums. Repeating normalization from that premise adds no result about a source lattice law; the revised text now says exactly this. The fixed bad-rescaling witness is the arithmetic impossibility 2j=1/2 for integer j and uses no empty domain.

A fresh [DeltaCheck.lean](/home/ubuntu/sap/tasks/CHFID-P003a-a/scratch/DeltaCheck.lean) imports only `SAP.P003a.Defs`. It compiles a nonzero-coordinate witness: g has unit mass at integer index 1, k=2, `IsMass g` holds, and its physical-coordinate mean is 1/2. It also checks the normalization projection directly from `IsMass` and the fixed integer rescaling witness. Command: `/home/ubuntu/sap/tools/sap-lean scratch/DeltaCheck.lean`; exit status 0, with one deprecation warning.

The original [Check.lean](/home/ubuntu/sap/tasks/CHFID-P003a-a/scratch/Check.lean) was freshly compiled against the refreshed Defs; exit status 0, with one tactic-style warning. It checks positive arms, an inhabited assignment type, possible tables, exact rational p-values, an SD mass with an ordinary convergent moment, a normalized missingness law, positive finite weights and the one-point search boundary runs. The per-target nonvacuity instances are recorded in `findings2.json`. The unchanged definitions preserve the previous guards against truncated subtraction, empty inversion endpoints, nonsummable moments, empty probability spaces and inconsistent zero-variance extensions.

The previous independent exact numerical checks remain evidence for the unchanged mathematical statements; they were not rerun as a new exhaustive verification. No Solution, Bridge, project proof export, or path linked outside the permitted workspace was opened. The architect's proof-build account is not used as a substitute for the statement review.

`findings2.json` contains exactly one object per canonical target, with the requested schema. It was parsed and checked with Python 3, including target order, uniqueness, theorem correspondence, allowed verdicts and the reported counts.
