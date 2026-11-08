# P001f omission review: T105

**OMIT.P001-T105: omission_ok / none.** The reason in `record.json:6` is accurate for the credited declaration type supplied in this task and corroborated by the older-RC source inspected below. Confidence is 0.86 because the current remote declaration could not be inspected. This review performs no acceptance or registration.

The separate declaration sequence was completed and its findings/report saved before opening this omission brief or the omission claims, record and binding. All 37 omission inventory entries matched initially and at final verification. The ten omission SAP source files are byte-identical to the ten declaration source files already read. There is no T105 Challenge theorem. The omission target has null theorem/module/line and an empty closure, with fingerprint `511c3c5e7c530e110c7d5699246bb302ebeb63460500cbbf94afff7db65f8041`, consistently copied from closure and checked against binding's `OMIT.P001-T105` entry.

The canonical claim concerns **binary** treatment, two potential vote shares and the implication from the description containing all applicant information available to voters (with no additional applicant information) to conditional independence of treatment and the potential-outcome pair given X. The informational premise is substantive. The claim's note describes a modeling interpretation; it does not replace that premise with an arbitrary structural function.

There is one proved credited row, and `no_lean` is false. Its required final status is `narrower`, so it is usable for exactly its exported assertion. The record does not incorrectly say there are no rows, and it does not discard the row merely because of the adverse earlier credit judgment. I compared the row's type with the canonical claim independently of the earlier-review prose carried inside claims.json.

The inspected row is `AronowAudit.P001.Wave1.printed_complete_description_contract_refuted`, at `AronowAudit/P001/Wave1/CompleteDescription.lean:14–20`. Expanded, it negates a universal assertion over probability spaces, measurable covariates X, **arbitrary real-valued D and U**, and functions m whose two potential responses m(X,0,U), m(X,1,U) are measurable and lie in [0,100] pointwise. The universal assertion's conclusion is conditional independence of that response pair and D given X. It has no premise D∈{0,1}, no positive mass for both treatment values, no declaration that U represents electorate preferences rather than additional applicant information, and no predicate for the recorded leaflet being all applicant information available to voters.

The allowed logical glue can unpack this negation as an existential failure of that larger structural contract. It cannot assume that the resulting witness has binary D, both arms positive, or the printed informational premise. In logical terms, `¬∀z, H(z) → CI(z)` does not entail `¬∀z, H(z) → Binary(z) → Complete(z) → CI(z)`. Restricting the domain of a universal **inside a negation** strengthens the counterexample claim. It is not a specialization rule for the exported negation. Recovering an admissible counterexample through a new transformation or new information model would require additional mathematical work, beyond the brief's rewriting/specialization/arithmetic glue. There is also no valid reverse use of contraposition that supplies the missing premises.

A possible descriptive theorem saying only that an arbitrary latent-U structural rule need not imply conditional independence would reproduce the credited larger-domain assertion. It would not be a faithful restricted form of this canonical binary-treatment/information-completeness implication: it removes precisely the counterexample admissibility conditions and leaves U's informational role unspecified. Merely relabeling it as a restricted refutation would not resolve that mismatch. Other P001f declarations do not supply this target's missing premises, and the brief does not permit replacing T105 by a different target's theorem. No new theorem or proof was written.

The supplied claim metadata mentions a separate `ElectorateWitness` and information-completeness certificate in another source. Neither is a credited row for T105 in this task. A proof body's particular witness is also not an extra conjunct of the exported theorem. The omission task allows each credited row's actual type despite its status; it does not authorize using uncredited positive certificates or importing proof-only witness properties as if already exported. Thus these references do not supply an allowed glue proof. This conclusion concerns what is available under the task's rules, not whether a stronger application counterexample could be proved with additional work.

## Source and execution limits

Authorized SSH access was blocked earlier in this review with `ssh: connect to host ... port 22: Operation not permitted` (exit 255). No denial workaround or credential change was attempted. Consequently I did **not** verify current remote source bytes or run a remote scratch check. The exact scoped current-source read command for the parent in an authorized execution context is:

```sh
ssh -o BatchMode=yes -o StrictHostKeyChecking=yes -o ConnectTimeout=10 dbl-ws 'nl -ba /home/ubuntu/sap/repo2/AronowAudit/P001/Wave1/CompleteDescription.lean'
```

I used only this explicitly permitted **older-RC fallback** source:

```text
/Users/paronow/sap-lean/repo/AronowAudit/P001/Wave1/CompleteDescription.lean
SHA-256 27a2729e7533226c1630d97e99021d636a097d19e6f266fbb16dd44e8a87d4b4
```

Its explicit theorem type at physical lines 14–20 agrees with the type described in the supplied task metadata. It was not assumed current. I did not inspect its proof modules, the separate uncredited electorate certificate, other reviews or campaign files. The present verdict is grounded in the supplied credited-type description plus this independently read fallback; if the current exported type differs, it needs a fresh comparison. Local Lean 4.34.1 exists, but an actual import attempt in the declaration task established that the supplied local search path lacks Mathlib. No successful Lean compilation is claimed.

The paper passage and its necessary definitions were provided in full in claims.json, so no web source was needed. The proofchecking certificate was not taken as evidence of paper fidelity or of omission correctness. Final validation parses the one-object JSON, checks the target/null theorem/fingerprint against closure and binding, and rechecks all inventoried input hashes. Exact findings/report hashes are returned with the completed review.
