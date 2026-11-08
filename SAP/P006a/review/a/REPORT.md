# Palomar statement audit: P006a

15 targets: **10 correct_whole, 3 correct_restricted, 2 restriction_inaccurate**. All other verdict counts are zero. Severity: 13 none, 2 minor, 0 major. There are no omitted targets and no statement found false or vacuous.

The two adverse findings concern incomplete restriction disclosure. The mathematical assertions actually stated appear correct.

## P006-T2 — restriction_inaccurate (minor)

The canonical ATT paragraph states that its vector conditional-unbiasedness condition holds for a nonrandom true baseline and for independent pointwise-unbiased estimation. The theorem assumes `VectorUnbiased` directly at [Defs/Part5.lean:64](/home/ubuntu/sap/tasks/CHFID-P006a-a/SAP/P006a/Defs/Part5.lean:64); it does not assert either sufficient-implementation implication. The omissions listed in the Challenge docstring and `record.json` do not mention these two parenthetical claims. T6's independent-implementation result concludes treated residual unbiasedness, rather than the vector condition required by T2.

Fix: add both sufficient-implementation assertions to the declared omissions, explicitly saying that vector conditional unbiasedness is assumed directly. The full proposed restriction text is in `findings.json`.

The rest of the declared restriction is accurate: the single-unit conditional-mean identity, standalone formula for `h_n`, and explicit nonmaximal-type example are absent as disclosed. The retained sample-average identities, finite threshold results, population-ratio result and one-unit identities match their stated scope.

## P006-T3 — restriction_inaccurate (minor)

Both an ATT maximizer and a welfare maximizer are hypotheses at [Defs/Part5.lean:114](/home/ubuntu/sap/tasks/CHFID-P006a-a/SAP/P006a/Defs/Part5.lean:114), before **all** conclusions. Consequently even the per-policy identities and the zero-policy equalities require the supplied maximizers. Canonical clauses (i) and (ii) do not have those existence conditions. The record and docstring disclose full estimator integrability and the omitted final numeric comparison, but omit this additional restriction.

The scope difference has substantive instances. In T1's two-unit model, restrict the feasible cube by removing `(1,1)`. Zero remains feasible and the unique ATT maximizer `(17/18,1)` remains feasible. Welfare has no attained maximum, so no `s` can be supplied. The per-policy identities are still valid, but this packaged theorem cannot assert them for that class.

Fix: disclose that both maximizing policies are supplied for the entire conclusion. Alternatively, move the per-policy identities and zero-policy equalities outside the optimizer hypotheses, and make the attained-maximum identity conditional on a supplied welfare maximizer. `findings.json` supplies the documentation-only fix.

## Checks and scope

The blind mathematical reading was saved as `reading.md` before opening the claims. `claim-stage.json` was saved and parsed before opening the record. No step-2 verdict was changed after reading the record. Every architect decision was checked against the statements; the remaining whole/restricted decisions are supported, and the restrictions of T8, T12 and T14 are accurately disclosed. The row names in the record were not treated as evidence of statement faithfulness, and no Solution or external formalization was read.

`scratch/Nonvacuity.lean`, importing only `SAP.P006a.Defs`, compiles with `/home/ubuntu/sap/tools/sap-lean`. It constructs a policy-dependent Bernoulli experiment satisfying the complete `Standing` assumptions, vector and treated unbiasedness, and the independent-estimator implementation. It also proves actual ATT and welfare maxima, weighted-summand integrability, and a nonempty two-agent reference-law instance. Its audited named proofs use only `propext`, `Classical.choice`, and `Quot.sound`; no Challenge stub or `sorryAx` is involved. Explicit finite/probability instances or mathematical constructions for every target are recorded in `findings.json`.

Exact rational checks in `scratch/arithmetic-checks.json` verify T1's displayed numbers and sampled finite enumeration against the reward polynomial and gap, and T9's interval endpoints and worst-case printed-table ratios. The global optimizer in T1 is justified by the displayed nonnegative gap identity, rather than by sampling.

The measure-theoretic checks account for Mathlib's zero value for nonintegrable real integrals and invalid conditional expectations, real suprema requiring bounded nonempty sets, positive denominators, RN-derivative direction and a.e. finiteness, measurable pushforwards, and nonempty indexing. The relevant hypotheses or explicit finite models prevent those conventions from doing the mathematical work. T10's general algebraic integral identity also holds for totalized integrals, but its counterexample uses finite ordinary expectations. No paper search was necessary because the supplied canonical claims include the relevant transcriptions.
