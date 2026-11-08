No defects found in the three declarations as labelled. The complete blind
reading was saved in `reading.md` before opening `claims.json`; the comparison
in `claim-stage.json` was saved before opening `record.json`. No step-2
classification was changed after reading the record.

| Declaration | Record decision | Verdict | Severity |
| --- | --- | --- | --- |
| SAP.P004c.T41 | whole | faithful | none |
| SAP.P004c.T42 | whole | faithful | none |
| SAP.P004c.T44 | restricted | faithful | none |

T41 includes both the HT variance order and the conditional CLT, centred at the
AME and divided by the actual standard deviation. T42 uses the variance of
the corrected Hájek linearization, including the control denominator
`N(1-p)`. Their independent Bernoulli law, marginalized effects, shared-source
interference, and radiuswise eventual C3/C4 assumptions match the canonical
claim. Eventual `WellDefined` expresses genuine spatial averaging. Neither
theorem adds C5 or substitutes a second-moment bound for the variance.

T44 retains finite unbiasedness, HT variance order, the root-N linearization
error bound, and the conditional Hájek CLT. Its definition of NED uses actual
finite conditional expectations and L2 norms on the assignment field. The
record and docstring accurately disclose the replacement of the printed
radiuswise `Cb*s^2` premise by `Cb*(1+s^2)` with one eventual threshold for all
radii. Thus its step-2 comparison remains **different**, while its recorded
**restricted** decision is accurate. The canonical note was not used to amend
the assertion: the literal bound at radius zero is impossible for positive
sample sizes because the ball contains its centre. This is a disclosed change
of hypotheses, with no claimed refutation of the canonical assertion. The
weaker radiuswise *nonvacuous reading* mentioned in the record is not established.

Every SAP declaration in each closure was read, including the generated NED
numeral proof inspected through Lean. No definition encodes a conclusion or
turns these statements into tautologies. Interior coins, eventual genuine
averages, and the conditional positive variance bounds exclude relevant junk
values. Zero means on empty Hájek arms are explicit; their exceptional
probability vanishes.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` compiled successfully. Its
three final examples construct **every hypothesis**, including both CLT
nondegeneracy bounds, using only Defs and Mathlib. The common witness has
balanced fixed outcomes in {-1,0,1}, genuine counting-measure averages, metric
node separation N+1 off the diagonal, exact NED, and uniform quadratic spacing.
Both relevant variances equal `8*floor(N/2)/N^2`, and N times either variance
is at least 1 for N>=2. `scratch/LiteralSpacing.lean` also compiled successfully,
checking the radius-zero obstruction. No `lake` command was run.
