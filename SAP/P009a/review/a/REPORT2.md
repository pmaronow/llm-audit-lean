All 17 targets are `correct_restricted`. Both earlier adverse findings are **fixed**. There are no partly fixed or unfixed findings and no new adverse findings.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 0 |
| `correct_restricted` | 17 |
| `restriction_inaccurate` | 0 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 0 |
| `omission_questionable` | 0 |

Severity: 17 none, 0 minor, 0 major. Revised architect decisions: 17 restricted, 0 whole, 0 refuted, 0 omitted.

The revised Defs and all 17 theorem types were compared with the objects, hypotheses, quantifier order and conclusions saved in [reading.md](reading.md). Their mathematical readings are unchanged. The changed target documentation is confined to T4 and T6; those are also the only changed entries in `record2.json` compared with `record.json`. Each revised Challenge docstring agrees with its `record2.json` restriction after normalizing line wrapping, and each theorem still refers to the corresponding `SAP.P009a.TkStatement`. The architectural account was checked against these actual statements and disclosures. The original reading, claim-stage judgments and first-round findings were preserved.

| Earlier finding | Resolution | Evidence |
| --- | --- | --- |
| P009-T4: undisclosed full regularity for standalone absolute Lemma A3 | **fixed** | [Challenge/Part1.lean:50](SAP/P009a/Challenge/Part1.lean#L50) explicitly identifies positive n, full `Regularity E k q s` at the same k, and the additional Assumption 1A and 1C premises. `record2.json` says the same. |
| P009-T6: undisclosed original-outcome moments in finite construction | **fixed** | [Challenge/Part1.lean:78](SAP/P009a/Challenge/Part1.lean#L78) explicitly identifies full regularity of the original experiment and both original-outcome moment bounds at the same k, even though the outcomes are replaced. `record2.json` says the same. |

T4 still assumes full regularity in [Defs/Part5.lean:146](SAP/P009a/Defs/Part5.lean#L146), rather than only the canonical observed-moment hypothesis. Its disclosure now states that restriction accurately and retains the earlier finite-space, finite-order and omitted-chain qualifications. T6 still assumes full regularity in [Defs/Part5.lean:170](SAP/P009a/Defs/Part5.lean#L170); its disclosure now identifies the unnecessary original-outcome moment premises while retaining the restriction 0<L≤1 and the omissions of sequence assembly and nonconvergence. Both first-round findings were disclosure defects, so these documentation repairs fully resolve them without weakening or otherwise changing the propositions.

All 17 `restricted` decisions remain appropriate: each statement retains substantive canonical content, and its listed omissions or added hypotheses remain in the actual proposition. No theorem was promoted to `whole`, and none is labeled `refuted`. The nine canonical counterexample targets still contradict their specified printed assertions; their partial clause coverage continues to justify `restricted`. No positive canonical assertion was replaced by an unrelated refutation.

| Target | Comparison with the saved reading and current restriction | Verdict |
| --- | --- | --- |
| P009-T1 | Same sparse family, variance and conservativeness assertions; coverage remains restricted to alpha=1/20. | `correct_restricted` |
| P009-T2 | Same finite coverage bound, asymptotic implications and Bernoulli application; declared general omissions remain. | `correct_restricted` |
| P009-T3 | Same three explicit signed-covariance violations; auxiliary laws and universal moment assertions remain omitted. | `correct_restricted` |
| P009-T4 | Same weighted bounds and moment component; the extra full-regularity premises are now disclosed. | `correct_restricted` |
| P009-T5 | Same cluster density, limit, threshold characterization and gap formulas. | `correct_restricted` |
| P009-T6 | Same finite-limsup lemma and construction; the original-outcome moment premises are now disclosed. | `correct_restricted` |
| P009-T7 | Same first sparse two-atom standardized family and failure of Gaussian convergence. | `correct_restricted` |
| P009-T8 | Same CLT with positive variance at every index; the added finite-prefix restriction remains disclosed. | `correct_restricted` |
| P009-T9 | Same complete-randomization family with selected-pair mixing exactly 1/4. | `correct_restricted` |
| P009-T10 | Same exceptional-set quantifiers and uniform mixing limit; all-index pair-set positivity remains disclosed. | `correct_restricted` |
| P009-T11 | Same square-size star family and B1>0, B2=0 comparison. | `correct_restricted` |
| P009-T12 | Same finite and asymptotic bounds; eventual nonzero B2 for relative domination remains disclosed. | `correct_restricted` |
| P009-T13 | Same three-unit interference example with zero expected spillovers. | `correct_restricted` |
| P009-T14 | Same implications and converse failure; positive-arm domain for zero B1 remains disclosed. | `correct_restricted` |
| P009-T15 | Same maximal-infinite-order identity family and full/off-diagonal sum discrepancy. | `correct_restricted` |
| P009-T16 | Same two all-pairs inequalities; termwise and alternative displays remain omitted. | `correct_restricted` |
| P009-T17 | Same four-unit example and t=0,z=1 probability and likelihood-ratio discrepancies. | `correct_restricted` |

No statement or shared definition introduces a new junk-value or nonvacuity problem. In particular, positive n and regularity exclude zero size and zero arm probabilities in T4 and T6; 0<L≤1 ensures 1≤ceil(sqrt(L)n)≤n in T6. The finite-limsup predicate still requires eventual upper bounds and frequent lower approximations to a finite real L, so unbounded real-supremum conventions do not enter. The retained mixing supremums have nonempty bounded value sets. Existing all-index or eventual positivity guards on T8, T10, T12 and T14 are unchanged. No added hypothesis assumes the conclusion.

Concrete nonvacuity examples for every target are recorded in [findings2.json](findings2.json). For the two corrected disclosures, fair identity outcomes at k=2,q=4,s=1 meet the full retained domain. T6 also has the explicit n=2,L=1/4 construction with HT=Z_0 and EATE=1/2. The previous strictness witnesses remain valid: the one-unit identity experiment has observed fourth moment 1/2≤1 at k=1 but fails full regularity at k=1; the fair one-unit experiment with original outcome 3 satisfies assignment bounds at k=2 but has fourth moment 81>16. These show precisely the additional restrictions now disclosed.

The existing eight Lean examples in [scratch/Check.lean](scratch/Check.lean) were freshly compiled against the revised Defs with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`; the command succeeded without diagnostics, recorded in [scratch/lean-checks-round2.log](scratch/lean-checks-round2.log). The earlier exact-rational finite witnesses remain applicable to the unchanged mathematical definitions and statements. Python parsed and checked `findings2.json`, including its schema, one-to-one target coverage, theorem names and verdict counts.
