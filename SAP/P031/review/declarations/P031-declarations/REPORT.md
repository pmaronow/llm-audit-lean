# Independent P031 full-unit fidelity review

## Binding and order

I reviewed all eleven declarations in the bound task, including every source-line definition in their Lean-computed statement closures. `CERTIFICATION.json` is SHA256 `7e06b5f25887bcf166216e27b15a4ce92a7228f2f9351f505f3857bc9dea9df0`; it points to an accepted Comparator record, SHA256 `461ed712fd86a3a5006900a73fbaa42a502044b42d75310a75f97bcc0895bfd8`, whose `accepted` flag is true, all four required acceptance markers are true, and 11 of 11 listed targets are certified. Its config and manifest hashes are `759666631fd4b49f3420760c6a81d82049e2683beaaa478a6949211102a7d8da` and `9c9d01f7961891522e81c3b8403019b47226656f95b2de6d1cea7a253031ae09`; the Comparator snapshot and certification receipt agree. All eleven bound task source file hashes match `binding.json` and the Comparator snapshot. The task binding SHA256 is `7f26de0a8d88e0c71385ffc7090bf79c9679121152a189f99bc968dea910dda5`, source digest `de558616553385d7f20843f23a433731be12b30a280645852d66e11862f28a26`.

I saved the blind mathematical expansion in `reading.md` (SHA256 `836deccbd5888a2ecd7829a361a2209df33e0bc6b5956ac1a236950f9019d766`) before opening `claims.json`, and saved `claim-stage.json` (SHA256 `4a0797411bd6d612781edbe07a733fff63d627622c56fbd6e5cb67e9a0677d3d`) before opening `record.json`. I used the [author-hosted journal PDF](https://cyrussamii.com/wp-content/uploads/2012/06/samii_aronow_equivalencies_white.pdf), especially printed pp. 366–370, as the primary source. The finite identities, proof misprint, coverage remarks, Section 4 comparison, balanced chain and footnote wording agree with the corresponding passages. The canonical T5/T6 contextual regime is an inference from the paper's cited large-sample context, and I assessed the formal declarations against that explicitly supplied canonical reading.

## Findings

All eleven entries in `findings.json` have verdict `faithful`, severity `none`, and fingerprints copied from `closure.json`. This verdict assesses the accuracy of each theorem **and its declared record scope**; it does not turn restricted decisions into whole-claim certifications.

| Target | Decision checked | Result |
| --- | --- | --- |
| T1 | whole | Exact observed-data HC2=Neyman identity. |
| T2 | whole | Exact expected-HC2 conservative inequality over uniform fixed-size assignments. |
| T3 | whole | Correct finite scaling of OLS and constant-effects imputation variance. |
| T4 | whole | Balanced chain, including the finite scaling. |
| T5 | restricted | Finite bias/equality and cited-regime normality, equivalence and coverage are stated. `D>0` excludes the canonical `D=0` coverage case and is disclosed precisely. |
| T6 | restricted | Both variance-error directions, possible OLS/CE undercoverage, and Neyman/HC2 coverage contrast are stated. `D>0` is the disclosed omission. The normality antecedent in its final coverage clause is redundant under the stated regular fourth-moment and positive-`D` regime, not an independent substantive exclusion. |
| T7 | whole | The four-unit legal witness refutes the printed *untilded* covariance equality, without claiming Theorem 2 is false. |
| T8 | whole | Every corrected Theorem 2 proof-chain link, with tilded covariance and indexed residuals. |
| T9 | whole | Every corrected balanced proof-chain link, with restored CE hat and sample variances. |
| T10 | whole | Full exact shifts, three sign sequences, limits and finite comparisons. Its exact-row formula is also proved for every real `a`, a true strengthening of the three selected cases. |
| T11 | restricted | All mathematical clauses of the corrected footnote, including denominator conditions, moment consistency and shifts. The excluded Freedman-page attribution is expressly disclosed and remains unverified here. |

The `record.json` labels and restrictions are accurate. No statement uses a conclusion-encoding placeholder, impossible conjunction of hypotheses, or junk-valued denominator on its stated domain. `Admissible` and `Population` guard every fixed-population variance denominator; positive `D` and the standardized-normal premise guard asymptotic ratios. `scratch/Check.lean` was compiled in the assigned task tree with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` (exit 0). It constructs an admissible, balanced four-unit assignment with nonconstant outcomes, a legal Population, an unbalanced eight-unit footnote row, and checks every statement name. For the asymptotic families, the explicit two-valued footnote schedules supply bounded moments, interior allocation and positive contrast variance; the existential T6 and T10 assertions are themselves certified. These checks establish satisfiable premises without relying on a theorem stub's `sorry` as a witness.

The existing certificate is a normal isolated-unit certificate using its dependency base. A full A3 source replay is outside this review and remains pending. I made no source or claim-state changes.
