All five reviewed declarations are faithful to their recorded scope. T12 is an accurately disclosed restriction; the other four cover their canonical claims. No adverse findings were identified.

| Declaration | Claim coverage | Record decision | Verdict | Severity |
| --- | --- | --- | --- | --- |
| SAP.P004a.T11 | Whole | whole | faithful | none |
| SAP.P004a.T12 | Narrower, disclosed | restricted | faithful | none |
| SAP.P004a.T13 | Whole | whole | faithful | none |
| SAP.P004a.T14 | Whole | whole | faithful | none |
| SAP.P004a.T15 | Whole | whole | faithful | none |

The blind reading was saved in [reading.md](reading.md) before opening claims.json. [claim-stage.json](claim-stage.json) and [the condition audit](scratch/claim-audit.md) were saved before opening record.json. Reading the record required no changes to the claim-stage conclusions. Every source declaration in the five closures was read, including the 44 generated auxiliaries inspected through Lean printing.

T11 includes corrected unbiasedness, the printed expectation, its exact equality criterion, and the constant-outcome validator. Strict overlap prevents conditional-mean and inverse-weight division by zero.

T12 retains the specified eight-node realization and the exact absolute-statistic size calculation. Its docstring and record accurately omit the universal negative-observation rule, signed size and decimal approximations, and the seventeen-node large-P witness. Both retained experiments use product laws over the observation and all resamples. Equal realized resample values have positive probability under that independent law. For Witness B the permitted statistic is absolute HT, so the absolute comparison is exactly the printed rule for that statistic. No claim of failure for every P, or eventually for one fixed design, is made.

T13 states all three correction clauses with the correct joint iid law, weak exceedances including ties, floor bound, and exact correction difference. A fixed assignment statistic is the sharp-null reduction of the paper's outcome-and-assignment statistic.

T14 includes all three canonical witnesses. Its discrete uniform average uses supported radii, and its area circle effect is a conditional-mean version rather than a zero-mass set average. The condition audit writes the printed identity explicitly and checks each witness against its setting. The discrepancies therefore address the canonical assertion itself.

T15 includes general band averaging, signed radial densities and positive atoms, finite decompositions, common weights, arbitrary-function nonidentifiability, and the full-annulus area density including disks. Forced marginals preserve the paper's marginalization at endpoint propensities. Its extra common-kernel equivalence is valid. The explicit measurability and integrability premises are the authorized usual conditions. Positive finite band masses and positive-shell filters exclude relevant junk values.

Validation: [scratch/Check.lean](scratch/Check.lean) compiled successfully using sap-lean, with independent nonvacuity examples and no invocation of any reviewed target theorem. [scratch/ClosureChecks.lean](scratch/ClosureChecks.lean) also compiled. [Exact rational checks](scratch/exact_checks.py) passed, including an independent eight-node size calculation of 0.05549969550171698… > 0.05. No lake command was run, and Lean processes were sequential. This is a statement-fidelity review; it relies on the supplied certification of the target proofs.

Paper context was cross-checked against the [public preprint, Sections 6.2–6.4](https://arxiv.org/pdf/2010.13599). The published canonical statements and their scope were taken from claims.json. The publisher's article endpoint was unavailable through the browser.
