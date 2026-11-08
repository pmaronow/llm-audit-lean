P009a packages exactly P009-T1 through P009-T17 from *Average treatment effects in the presence of unknown interference*, DOI 10.1214/20-AOS1973.

| Decision or status | Count |
| --- | ---: |
| whole | 16 |
| restricted | 1 |
| refuted | 0 |
| omitted | 0 |
| proved | 17 |
| open glue | 0 |

The current mathematical statements and proofs are the supplied `TkWholeStatement` and `WH` assemblies. Their names are historical: the name `T11WholeStatement` does not determine its coverage decision. T11 is the sole restricted target. There are no omitted targets or open glue tasks.

**P009-T11 — restricted.** Only the failure of guaranteed eventual largest-in-absolute-value dominance is asserted, for sequences with uniform q>=4 regularity, independent Bernoulli assignment, restricted interference, and d_AVG/C1 tending to infinity. The specified square-size m-block fair-Bernoulli witness and its full outcome schedule are not stated. Omitted witness clauses are: the full-cube [0,2] bounds and regularity at every moment order; the exact interference and dependence graphs, C1=2, d_AVG=m=sqrt(n), the ratio m/2 and its divergence, and Assumption 2 for that family; the expected direct effects all equal to 1, tau_MSQ=1 and tau_MSQ/d_AVG=1/m; the xi and weighted-xi formulas, reciprocal products and B1=2/m^2>0; the arm-independent conditional covariances, their alternating-sum cancellations and B2=0; the comparison 0=B2<B1<=tau_MSQ/d_AVG with equality of the last two terms exactly at m=2; and the extension to every n>=4 with its floor-defined blocks, isolated units, and exact C1, d_AVG, tau_MSQ, B1 and B2 formulas. The printed big-O bounds and Proposition 7 are not refuted.

## Declaration review round 1

The two open-item directories contain the same five-declaration reviewer batch. I checked the relevant entry for each open declaration against its canonical claim, the exact proposition, its definition dependencies, and its supplied proof. Both adverse findings are accepted; no reviewer disagreement remains.

| Declaration | Finding | Action |
| --- | --- | --- |
| SAP.P009a.T11 | not_faithful, major: canonical witness clauses are absent | Decision changed from refuted to restricted; every omitted witness clause is disclosed. |
| SAP.P009a.T11 | The refuted label is relative to the quoted guidance rather than the canonical counterexample | Canonical-relative restricted label replaces refuted. |
| SAP.P009a.T11 | Both docstrings broadly say the printed claim is false | Both now identify only failure of guaranteed eventual largest-in-absolute-value dominance; the printed big-O bounds and Proposition 7 are expressly preserved. |
| SAP.P009a.T13 | label_wrong, minor: the complete canonical cancellation counterexample is proved | Decision changed from refuted to whole, with restriction null; statement, proof and docstring retained. |
| SAP.P009a.T12 | faithful, no open issue | Retained without mathematical changes. |
| SAP.P009a.T14 | faithful, no open issue | Retained without mathematical changes. |
| SAP.P009a.T15 | faithful, no open issue | Retained without mathematical changes. |

**T11 scope.** Its proposition negates a universal eventual-dominance implication over regular product-design sequences with restricted interference and a divergent d_AVG/C1 ratio. Neither the specified square-size block experiment nor its concrete formulas occur as a conclusion. The proof's internal choice of `wholeStarSequence` does not turn its properties into theorem clauses. The minimal repair therefore changes the label and disclosures, without adding a witness theorem or inventing the every-size extension. The manifest and both T11 docstrings now enumerate omitted clauses (a)-(e), the final comparison and equality case, and the extension to every n>=4. The theorem and its supplied proof remain unchanged. Sources: [reviewer T11 finding](fw/round1/T11/r3g3/findings.json), [canonical T11](/home/ubuntu/sap/wt/ARCH-P009a/work.json:888), [T11 statement](SAP/P009a/Defs/WholeW2.lean), [supplied assembly](SAP/P009a/WH/W2/LeavesBase.lean).

**T13 label.** The canonical target already asserts the three-unit cancellation counterexample. Its proposition states the fair law, exact outcomes, full-cube bound, all finite moment orders and the infinite endpoint, the nonzero pointwise spillover, structural interference, and zero expected and weighted spillovers. It thus proves the canonical counterexample in full. The existing docstring correctly identifies the particular printed implication contradicted by that counterexample and is retained; the manifest alone changes its decision to whole. Sources: [reviewer T13 finding](fw/round1/T13/r3g3/findings.json), [canonical T13](/home/ubuntu/sap/wt/ARCH-P009a/work.json:1011), [T13 statement](SAP/P009a/Defs/WholeW2.lean), [T13 proof](SAP/P009a/WH/W2/Proofs/T13.lean).

**Same-rule correction for T5.** Its canonical target is also itself a counterexample, and the supplied statement includes the full graph, density, threshold, parity and asymptotic certificate. Its former refuted label had the same canonical-relative error as T13. I changed it to whole with restriction null, preserving its statement and proof. Sources: [canonical T5](/home/ubuntu/sap/wt/ARCH-P009a/work.json:460), [T5 statement](SAP/P009a/Defs/WholeW2.lean), [T5 proof](SAP/P009a/WH/W2/Proofs/T5.lean).

## Definitions, proof transport and source limits

The package continues to use shared SAP definitions importing only Mathlib and other Defs modules. Challenge and Solution refer to the same compiled `SAP.P009a.TkWholeStatement` constants. The existing Bridge converts normalized finite distributions, experiments and sequences by preserving their fields; its correspondence proofs use reflexivity or elimination of structures. Solution instantiates the supplied `WH.W1` through `WH.W4` theorem assemblies. This revision introduces no mathematical proof, hypothesis, theorem clause or changed definition body.

Three supplied Lean files exceeded 300 lines. I compacted only comments and blank lines in `Defs/WholeW1.lean` and `WH/W3/Leaves.lean`, and split `WH/W2/Leaves.lean` at a public declaration boundary into `LeavesBase.lean` plus the original importing module. Every existing fully qualified declaration name and declaration body is preserved. The retained source token hashes, ignoring comments and whitespace, are recorded in `scratch/p009a_declaration_before.json` and `scratch/p009a_declaration_changes.json`; concatenating the split declaration text gives the same token hash as before. T11's Defs change is documentation only. No shared mathematical definition changed, so no dependent statement was broadened or sent back for review by a changed definition. Every SAP file is now at most 300 lines, including the compact manifest.

The domain safeguards in the supplied statements are retained: finite normalized distributions have ordinary finite means; positive sample sizes and arm probabilities protect the relevant ratios and conditional means; T4's general probability-space variables are square integrable; asymptotic normalizations and exception fractions use their supplied eventual nonzero domains; and infinite-order moment branches avoid default finite orders. The declaration reviewer found no relevant junk-value or vacuity issue in the reviewed T11-T15 closures.

## Verification

All 53 SAP Lean modules were recompiled sequentially in dependency order using `/home/ubuntu/sap/tools/sap-lean`; no `lake` command or parallel Lean process was used. The ordered module list is in `scratch/p009a_declaration_order.json`, and module results are in `scratch/p009a_declaration_build.json`. Challenge compilation produced only the expected stub diagnostics. Some supplied definitions and proofs also emit linter warnings; no compilation errors occurred. `scratch/p009a_declaration_axioms.lean` imports Solution and prints dependencies for all 17 named theorems; `scratch/p009a_declaration_axioms.log` shows exactly `propext`, `Classical.choice`, and `Quot.sound` for each.

The manifest and Comparator JSON files parse and name exactly the same 17 proved theorems. Comparator modules, permitted foundations and external-kernel arguments are retained. The manifest now records 16 whole and one restricted target; its proof-status and source-credit fields are preserved. The validation script checks the theorem statement references, both implicit-variable options in every module, import boundaries, source limits, token restrictions, unchanged mathematical bodies and permitted dependencies. Results are in `scratch/p009a_declaration_validation.json`.

The supplied `verification/comparator-result.json` records an accepted three-kernel certificate for the earlier 20261104T170553Z snapshot. That file is retained as historical evidence; its source and manifest hashes describe the earlier snapshot. This revision does not claim a fresh Comparator run or a fresh certificate. The new validation establishes compilation and permitted dependencies for the present files. Project sources, canonical work records, reviewer artifacts and pilot units were not edited.

The earlier referee responses below concern the original restricted package and are preserved as history. Their old counts and restrictions are superseded by the current manifest and the declaration-review decisions above.

## Earlier referee round 1 — revision 2 (historical)

Both referee reports were checked against `work.json`, the shared SAP statements, and the existing declarations used by the Solution. Referee A identifies two incomplete restriction disclosures; both are accepted and corrected. Referee B reports no adverse findings. All 17 decisions remain `restricted`, and all fully qualified theorem names, propositions, and proofs are preserved. No hypotheses or new mathematical conclusions were added.

The following table records every target finding from both [referee A](referees/round1/a/findings.json) and [referee B](referees/round1/b/findings.json).

| Target | Referee A | Referee B | Action |
| --- | --- | --- | --- |
| P009-T1 | correct_restricted | correct_restricted | Checked; retained without change. |
| P009-T2 | correct_restricted | correct_restricted | Checked; retained without change. |
| P009-T3 | correct_restricted | correct_restricted | Checked; retained without change. |
| P009-T4 | restriction_inaccurate | correct_restricted | Restriction disclosure corrected; theorem preserved. |
| P009-T5 | correct_restricted | correct_restricted | Checked; retained without change. |
| P009-T6 | restriction_inaccurate | correct_restricted | Restriction disclosure corrected; theorem preserved. |
| P009-T7 | correct_restricted | correct_restricted | Checked; retained without change. |
| P009-T8 | correct_restricted | correct_restricted | Checked; retained without change. |
| P009-T9 | correct_restricted | correct_restricted | Checked; retained without change. |
| P009-T10 | correct_restricted | correct_restricted | Checked; retained without change. |
| P009-T11 | correct_restricted | correct_restricted | Checked; retained without change. |
| P009-T12 | correct_restricted | correct_restricted | Checked; retained without change. |
| P009-T13 | correct_restricted | correct_restricted | Checked; retained without change. |
| P009-T14 | correct_restricted | correct_restricted | Checked; retained without change. |
| P009-T15 | correct_restricted | correct_restricted | Checked; retained without change. |
| P009-T16 | correct_restricted | correct_restricted | Checked; retained without change. |
| P009-T17 | correct_restricted | correct_restricted | Checked; retained without change. |

**T4: accepted A's finding.** The canonical absolute Lemma A3 component requires Assumption 1B with q at least 2a, whereas the retained component quantifies over positive n and assumes full `Regularity E k q s`. The definition of Regularity includes Assumption 1A assignment bounds and Assumption 1C potential-response moment bounds using that same k. The fair one-unit identity example illustrates the strictness: its fourth observed moment is 1/2, hence at most 1 at k=1, but full regularity at k=1 would require its treatment probability to be simultaneously at least 1 and at most 0. The Challenge docstring and manifest now explicitly disclose these additional premises, alongside the existing finite-space, finite-order, and omitted-chain restrictions. The theorem remains the previously proved restricted statement. See [the canonical T4 record](/home/ubuntu/sap/wt/ARCH-P009a/work.json:367), [the retained moment-bound component](/home/ubuntu/sap/wt/ARCH-P009a/SAP/P009a/Defs/Part5.lean:146), [Regularity](/home/ubuntu/sap/wt/ARCH-P009a/SAP/P009a/Defs/Part2.lean:22), and [A's finding](/home/ubuntu/sap/wt/ARCH-P009a/referees/round1/a/findings.json:33).

**T6: accepted A's finding.** The canonical finite construction replaces the outcomes and uses the design's marginal probabilities. The retained finite component nevertheless assumes full Regularity of the original experiment, as required by the existing construction declaration. It therefore also assumes observed and potential-response moment bounds for the discarded original outcomes at the same k. For example, fair assignment satisfies the assignment bounds at k=2 even if the original outcome is constantly 3; its fourth observed moment 81 exceeds 2^4=16. The Challenge docstring and manifest now disclose the extra original-outcome moment premises, while preserving all previous omissions and the restriction 0<L<=1. The diagnostic finite-lemmas text was not promoted to an assumption or used to justify a new proof. See [the canonical T6 record](/home/ubuntu/sap/wt/ARCH-P009a/work.json:526), [the retained finite component](/home/ubuntu/sap/wt/ARCH-P009a/SAP/P009a/Defs/Part5.lean:170), [the existing construction declaration](/home/ubuntu/sap/wt/ARCH-P009a/AronowAudit/P009/Wave1/Gap/GP0092B2.lean:736), and [A's finding](/home/ubuntu/sap/wt/ARCH-P009a/referees/round1/a/findings.json:55).

For T4 and T6, I disagree with referee B's assessment that the original restriction disclosures were complete; its `correct_restricted` labels and truth assessments remain consistent with the corrected package. The unchanged hypotheses above show precisely the extra premises that the previous disclosures omitted. See [B's T4 finding](/home/ubuntu/sap/wt/ARCH-P009a/referees/round1/b/findings.json:33) and [B's T6 finding](/home/ubuntu/sap/wt/ARCH-P009a/referees/round1/b/findings.json:53). The other 30 target findings are accepted without changes: their retained clauses, omissions, and nondegenerate domains agree with the existing statements and manifest. No canonical positive assertion requires a new refutation label, and no theorem states the whole canonical conjunction.

Revision validation recompiles every SAP Lean module in dependency order and reruns `#print axioms` for all 17 Solution theorems. Both JSON artifacts are regenerated and parsed; the Comparator configuration retains exactly the same 17 theorem names. File limits, option settings, permitted dependencies, and theorem type references are checked again by `scratch/validate_p009a.py`. External certification remains unrun for the tool-availability reason recorded above.
