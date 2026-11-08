# Referee report

15 targets reviewed: **10 correct_whole, 3 correct_restricted, 2 restriction_inaccurate**. Both issues are **minor disclosure defects**. No false or vacuous statement was identified. All targets have a theorem; there are no omitted targets in this package.

| Verdict | Count |
| --- | ---: |
| correct_whole | 10 |
| correct_restricted | 3 |
| restriction_inaccurate | 2 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

The accurate restrictions are T8 (global evaluated-estimator integrability and explicitly omitted implementation/supporting results), T12 (omit the treatment-model completion), and T14 (integrable positive parts). The ten whole decisions agree with the architect's record. For T2 and T3, choosing `restricted` is appropriate, but the record and docstrings do not enumerate all restrictions.

## P006-T2 — restriction_inaccurate; minor

The canonical ATT setting states that its full-vector conditional unbiasedness follows from pointwise-unbiased independent estimation. The theorem assumes the full-vector condition but does not export this sufficient implementation. The declared restriction lists three omitted assertions without listing this one. See [the ATT hypothesis](SAP/P006a/Defs/Part5.lean#L64), the corresponding n=1 hypothesis at line 104, and [the restriction docstring](SAP/P006a/Challenge/Part1.lean#L13).

T6 does not supply the missing implication: [its implementation conclusion](SAP/P006a/Defs/Part5.lean#L188) is `TreatedUnbiased`, whereas the average-reward condition is `VectorUnbiased`. These are distinct predicates. This finding concerns completeness of the declared restriction; the retained identities and optimization statements are correct.

**Fix:** append this exact text to both the T2 docstring restriction and the record restriction:

> Also omit the sufficient-implementation assertion that pointwise-unbiased independent estimation implies the full-vector conditional unbiasedness hypothesis. T6 states a sufficient implementation only for the treated-residual moment.

Alternatively, include the independent-estimation-to-vector-unbiasedness implication under appropriate evaluation integrability assumptions.

## P006-T3 — restriction_inaccurate; minor

[The binders for both optimizers](SAP/P006a/Defs/Part5.lean#L114) precede the entire conjunction. As a result, even the per-policy identities and the zero-policy reward/welfare values require supplied ATT and welfare maximizers. Canonical clauses (i)-(ii) assert those identities without optimizer hypotheses; clause (iii)'s best-response nonnegativity requires an ATT optimizer but not a welfare optimizer. [The restriction docstring](SAP/P006a/Challenge/Part1.lean#L19) does not disclose these extra premises and says that all numbered conclusions are included.

The extra conditions are not automatic. In the compiled one-unit experiment with constant effect one, zero estimator and one-point covariate, expected ATT and welfare are both the treatment probability p. The feasible class of constant policies with 0≤p<1 contains zero and satisfies all design and estimator conditions, but has neither maximizer. The canonical per-policy and zero-policy identities remain meaningful in this class. The current T3 implication yields no conclusion for it. This demonstrates the loss of scope of the supporting identities; it does not assert a regret formula with an unattained maximum.

**Fix:** add the following exact disclosure to both restrictions, replacing the unqualified sentence about numbered conclusions:

> All conclusions, including the per-policy identities and the zero-policy reward and welfare identities, additionally assume supplied ATT-reward and welfare maximizers; no conclusion is exported for a feasible class lacking either maximizer. Under these supplied maximizers retain the numbered conclusions and the attained-maximum regret identity.

Alternatively, move the per-policy and zero-policy identities outside the optimizer hypotheses, require an ATT optimizer only for best-response conclusions, and reserve the supplied welfare optimizer for the attained-maximum regret identity.

## Audit and verification

The blind expansion was saved in [reading.md](reading.md) before reading claims.json. The claim comparison was saved in [claim-stage.json](claim-stage.json) before reading record.json. Its 10 whole / 5 narrower classifications were not changed after reading the record. The final verdicts assess the accuracy of the record's disclosure as a separate step.

[scratch/Check.lean](scratch/Check.lean) imports only Defs. It compiles a randomized, nonzero-effect Bernoulli experiment satisfying full Standing for every admissible policy, vector and treated unbiasedness, and an independent estimator implementation. It also checks actual ATT and welfare values, simultaneous attained maximizers on the unrestricted class, nonattainment on the open feasible class, the singleton-private-covariate marginal conditions, finite-support premise nonvacuity, and selected finite counterexample identities. The command `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` exited 0 with no diagnostics; only one Lean process was used at a time. No Solution or Comparator was read and no lake command was run.

The measure-theoretic definitions were followed into Mathlib. The nonempty-sample ratios use positive denominators, sample sizes in Experiments are positive, regret suprema in the applied conclusions are bounded and nonempty, and the singleton-private-covariate supremum is exactly the bounded singleton {0}. The density counterexample uses an actual positive atom, and the corrected density theorem assumes the required absolute-continuity direction. These checks found no reliance on undefined expectations or default supremum values in the audited substantive conclusions. The general algebraic integral identities in T10 use Mathlib's total integral convention but also hold on the finite-moment model class needed for the counterexample.
