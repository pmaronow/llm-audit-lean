# Statement referee report

18 targets: **6 correct_whole, 12 correct_restricted, 0 adverse findings**. No targets were omitted.

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

`reading.md` was saved before either comparison file was opened. `claim-stage.json` was saved after reading all canonical claims and before `record.json` was opened. The record caused no changes to the independent claim-stage classifications.

Every architect decision is supported. Each of the twelve record restriction texts also matches its Challenge docstring after whitespace normalization. The mathematical comparison, including omitted components, is given for every theorem in `claim-stage.json`; concrete premise instances are in `findings.json`.

| Target | Architect decision | Finding | Scope checked |
| --- | --- | --- | --- |
| P003-T29 | whole | correct_whole | All finite complete-randomization inversion coverage, with the required empty-accepted-set convention. |
| P003-T1 | restricted | correct_restricted | The numerical legal missingness witness is retained; labeled identities, explicit inclusion/proof inequalities, maxima, group table and extra numerical facts are disclosed omissions. |
| P003-T2 | whole | correct_whole | Balanced arbitrary-dependent-missingness coverage, completion inclusion and the full labeled plus coupling. |
| P003-T3 | whole | correct_whole | Both joint-law coverages, both containments, completion enumeration/cardinality, complete-data coverage and repaired numerical example. |
| P003-T4 | restricted | correct_restricted | Wrong return, nontermination and executed balanced example; traces, domain calculations and extra domains are disclosed omissions. |
| P003-T5 | restricted | correct_restricted | Finite-fuel threshold correctness and logarithmic traces, including arbitrary decisions; intermediate invariants, arbitrary-decision nonexhaustion and application budgets are disclosed omissions. |
| P003-T11 | restricted | correct_restricted | The all-zero real-threshold counterexample is retained; the universal no-minimum assertion is disclosed as omitted. |
| P003-T12 | restricted | correct_restricted | The general finite-support repair is retained; the experiment-specific inversion argument is disclosed as omitted. |
| P003-T13 | whole | correct_whole | Corrected effect formula from labeled binary tables, and both numerical refutations of the printed numerator. |
| P003-T14 | restricted | correct_restricted | The entire rescaling clause requires an absolute first moment; this extra hypothesis, including its unnecessary use for normalization/reindexing, is explicitly disclosed. |
| P003-T9 | restricted | correct_restricted | The explicit common-Boolean dependent counterexample A is retained; counterexample B is disclosed as omitted. |
| P003-T10 | whole | correct_whole | Independent smoothing, half-integer-center shape shift, and the parity-lattice convolution including both masses. |
| P003-T15 | restricted | correct_restricted | The full SD sampling-law lemma is retained; induction case facts and proof-gap examples/laws are disclosed omissions. |
| P003-T16 | restricted | correct_restricted | The normalized signed sum and six pair outcomes are retained; the remaining-subject formula, printed laws and sampling construction are disclosed omissions. |
| P003-T17 | restricted | correct_restricted | Simplified variance, fixed extension, rank validity and extension-dependent exact tails are retained; printed-formula derivation and additional examples/counts are disclosed omissions. |
| P003-T21 | restricted | correct_restricted | Accepted effects, interval, estimator exclusion and negative p-value are retained; full enumerations, maxima and additional certificates are disclosed omissions. |
| P003-T22 | restricted | correct_restricted | Every possible table has the minimum-base/reuse representation; reduced witness facts are retained and the omitted executions and labeled realization are disclosed. |
| P003-T23 | whole | correct_whole | All three arbitrary-decision rejection/endpoint/trace implications, permitting specialization to the exact endpoint. |

No item has an adverse verdict, so no statement or docstring fix is requested.

The definition audit checked binomial multiplicities, list support bounds, possibility enumeration, inclusive ties, empty intervals/hulls, guarded missing-data endpoints, integer versus natural subtraction, physical lattice coordinates, absolutely summable first moments, fixed zero-variance extensions, and nonempty normalized probability spaces. Valid experiment hypotheses make the field denominators positive. The general combinatorial and shape clauses do not rely on degenerate conventions. No hypothesis assumes its conclusion.

Validation used `SAP.P003a.Defs`, without importing a Challenge theorem or reading a Solution. `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully: it checks positive arms, a nonempty assignment type, possible tables, exact rational p-values, an SD law with convergent moment, a normalized missingness law, positive finite weights and both one-point search boundary runs. It emitted one tactic-style linter warning and no errors.

`python3 scratch/audit.py` independently enumerates labeled assignments and uses exact rational arithmetic. It confirms the T1/T3 missing and repaired coverages (297/380 and 892/1140), T4 interval [1/2,15/16], T21 effects {0,1/9}, T17 extension-dependent p-values 1 and 2/5, and a nonzero-change T2 coupling premise instance with p=1/3. It also checks 8,349 selected-level inversion coverage instances over all populations and allocations with 2 <= n <= 6, and all 114 balanced discordant SD laws with n=2,4,6. These finite checks supplement the statement/definition analysis; they are not proofs of the universal claims. Results are saved in `scratch/audit-results.json`.

All requested JSON outputs were parsed and their target/theorem coverage checked with Python 3. No paper web lookup was needed because the supplied canonical claims include the relevant text and standing assumptions.
