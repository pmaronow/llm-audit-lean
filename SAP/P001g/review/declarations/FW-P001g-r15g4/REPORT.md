P001-T120: **omission_ok**, severity **none**.

The omission reason is accurate. [claims.json](/home/ubuntu/sap/tasks/FW-P001g-r15g4/claims.json:31) has `no_lean: false` and one credited row, `AronowAudit.P001.Wave1.printed_fixed_covariate_kl_mle_positive_support_refuted`, with final status `ok`. The architect acknowledges this row and omits the target because its statement lacks a canonical premise.

The canonical [definitions_needed](/home/ubuntu/sap/tasks/FW-P001g-r15g4/claims.json:25) explicitly carries the true-model assumption from Definitions 5.2.1–5.2.2: some single parameter in the model must reproduce the true conditional distribution. The credited [Lean contract](/home/ubuntu/sap/repo2/AronowAudit/P001/Wave1/Gap/RepairT120b.lean:18) imposes normalization, measurability, positive covariate mass, domination, integrability, a unique fixed-covariate KL minimizer, and likelihood maximization, but no true-model assumption.

The [witness definitions](/home/ubuntu/sap/repo2/AronowAudit/P001/Wave1/Gap/RepairT120.lean:65) make this difference substantive. The true Bernoulli success probabilities are 1/4 at covariate 0 and 3/4 at covariate 1; both covariates have probability 1/2. The fitted family uses the same success probability at every covariate. No single parameter reproduces both conditional laws, even allowing equality only almost everywhere.

Accepting the row's recorded `ok` status, its negation therefore does not refute the canonical claim. Logically, failure of a universal consistency assertion without the true-model condition does not imply failure after adding that condition. The row also supplies no positive consistency clause. Extracting its counterexample cannot provide the missing premise, and restricting the domain further cannot repair this by glue. Dropping the true-model assumption would instead refute an extension of the canonical claim. The audit note and coverage judgment cannot remove that assumption under the review rules.

The unused [T120Statement](/home/ubuntu/sap/tasks/FW-P001g-r15g4/SAP/P001g/Defs/Part5.lean:23) similarly negates a contract without the true-model condition; its presence in Defs supplies no faithful Challenge theorem. No restricted statement is proposed, and no change to the omission reason is needed.

Validation: `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully, checking the credited declaration and printing its contract without adding a proof. `findings.json` was parsed and its fields and fingerprint checked with Python.
