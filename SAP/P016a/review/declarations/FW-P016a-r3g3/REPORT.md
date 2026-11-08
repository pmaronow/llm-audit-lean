P016-T5: **omission_ok**, severity **none**.

The omission reason is accurate. `claims.json` has `no_lean: false` and one proved credited row, `AronowAudit.P016.t5_printed_contrast_refuted`, with final status `wrong_credit`. The record acknowledges that row; it does not claim that no proved row exists. I allowed the row for exactly its Lean statement despite its rejected credit.

The operative claim is the canonical statement together with its definitions and standing assumptions: the printed comparison of the information used by KS and simple SSR, including the assertion about correlation entering the distribution of the statistic. The definitions specify group-mean SSR and two-sided KS. The historical note does not replace that claim with a fixed-margin existential.

The [credited declaration](/home/ubuntu/sap/repo2/AronowAudit/P016/P016_Interference.lean:1250) states precisely

```text
not exists n, u, v, z, w,
  2 <= n and groupSize(z,false) > 0 and groupSize(z,true) > 0
  and sameMargins(u,z,v,w) and KS(u,z) = KS(v,w)
  and SSR(u,z) != SSR(v,w).
```

Here `sameMargins` means equality of both full empirical group multisets. The declaration supplies a fixed-margin impossibility, with no assignment law, covariance, or comparison of reference distributions. Equal scalar KS alone does not meet its hypotheses: the existing scalar-KS witness has KS values both equal to 1/2 and SSR values 4 and 5.

A direct glue consequence of the credited row is that identical empirical margins and equal KS force equal SSR. This can use the existing Mathlib-only definitions, but is already implied by the margin-invariance clause of [T2Statement](/home/ubuntu/sap/tasks/FW-P016a-r3g3/SAP/P016a/Defs/Part3.lean:59). It therefore fails the explicit rule excluding statements that merely restate another target's theorem. Specializing to the 256-unit balanced design adds no information or distribution comparison. The row also provides no precision comparison or proof of the weaker assertion about assignment-induced dependence entering the SSR reference distribution. Extracting only the defining SSR formula would abandon the information comparison that constitutes this whole claim.

No faithful, distinct restricted statement of T5 is supported by glue from its sole row. The reason accurately distinguishes the printed claim from the fixed-margin auxiliary result, so no correction or replacement Challenge theorem is proposed.

Validation: [scratch/Check.lean](/home/ubuntu/sap/tasks/FW-P016a-r3g3/scratch/Check.lean) compiled with the authorized `sap-lean` helper. The credited row's reported axioms are only `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx`. No new mathematical proof was written. `findings.json` was parsed and its target, fingerprint, and required fields checked with Python.
