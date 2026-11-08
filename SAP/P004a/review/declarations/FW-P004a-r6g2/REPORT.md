# P004a declaration review

All five declarations are **faithful**, with severity **none**, relative to
their accurately disclosed scope. No corrections are required.

| Declaration | Record decision | Review |
|---|---|---|
| `SAP.P004a.T6` | restricted | Retains the integral aggregation, marginalization, effect and range identities, equal-mass mean, and exact positive-scaling invariance. Both omitted negative assertions and the excluded empirical conclusions are accurately disclosed. |
| `SAP.P004a.T7` | restricted | Retains the complete finite reversal and the stated spatial and variance guards. The event is an unconditional guarded coverage event; the exact limit and intermediate certificates are expressly omitted. It does not mislabel a reading of procedural guidance as a false printed theorem. |
| `SAP.P004a.T8` | whole | Includes the actual spectral positive part, capped variance with its fallback, sandwich identities, full ordering and interval inclusion, Student comparison, asymptotic guarantee, and genuine uncapped counterexample. |
| `SAP.P004a.T9` | whole | Contains the entire canonical boundary-MLE counterexample, actual maximization, exact moments, explicit tail bounds, failure of the score expansion, and the correctly stated limits and surviving rates. The tail bounds are not called optimal. |
| `SAP.P004a.T10` | whole | Separates compact-membership consistency and root-N rate from the interior-truth score expansions, with both remainder orders present. |

The order was preserved: [reading.md](reading.md), including every closure
entry, was saved before opening the claims; [claim-stage.json](claim-stage.json)
and [claim-audit.md](claim-audit.md) were saved before opening the record.
Reading the record required no changes to the claim-stage conclusions.
The detailed audit checks every printed condition against each counterexample,
including independence, the actual spatial averages or constrained maximizer,
nondegeneracy, and interval validity.

All relevant totalization conventions were checked. Positive masses and
integrability protect the spatial means; positive-arm and trace guards
protect the interval ratios; valid Student degrees and probability levels
protect the quantiles; eventual information nonsingularity protects the MLE
expansion. No conclusion depends on an undefined mean, infinite-measure
`toReal`, singular inverse, or zero-rate shortcut.

[scratch/Nonvacuity.lean](scratch/Nonvacuity.lean) compiles successfully with
no errors or warnings and without invoking any audited theorem. It constructs
all T6 aggregation hypotheses, checks the T7 finite assignment and positive
product probability, instantiates all T8 finite hypotheses, checks a genuine
T9 tail realization, and constructs every T10 premise including interior
truth and an actual MLE. Full asymptotic premise nonvacuity for T8 follows
from the explicit star construction and uniform spacing/variance bounds in
the detailed audit; those infinite geometric checks are argued there rather
than separately formalized.

[scratch/exact_checks.py](scratch/exact_checks.py) independently verifies the
star spectral decomposition and all finite reversal constants using rational
arithmetic, including positive trace-square parameters. It also checks the
boundary moments and tail bounds for N=1 through 80. The general statements
remain the certified declarations. The paper's [Appendix A.6 and Proposition
4](https://arxiv.org/html/2010.13599v5) corroborate the relevant printed
compact-membership assumption and uniform-kernel coverage setting.

`findings.json` contains exactly the five requested entries with fingerprints
copied from `closure.json`; both output JSON files were parsed and checked.
