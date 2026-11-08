All three declarations are faithful to their recorded scope. T26 and T27 cover
their complete canonical claims; T28 correctly states the disclosed sufficient
consistency restriction. No defects were found.

| Declaration | Claim coverage | Record and docstring | Verdict |
| --- | --- | --- | --- |
| `SAP.P008b.T26` | Whole | Accurate | faithful / none |
| `SAP.P008b.T27` | Whole | Accurate | faithful / none |
| `SAP.P008b.T28` | Narrower | Accurate restriction | faithful / none |

The blind reading and every dependency in `closure.json` were read and recorded
in [reading.md](/home/ubuntu/sap/tasks/FW-P008b-r8g3/reading.md) before opening
`claims.json`. The independent claim judgments were saved in
[claim-stage.json](/home/ubuntu/sap/tasks/FW-P008b-r8g3/claim-stage.json) before
opening `record.json`. The record required no changes to those judgments.

For T26, the sharp null implies all three vanishing conclusions, uniformly over
finite designs and coordinate metrics. The exact three-point witness has valid
circles at radii 0 and 1, zero AMR at every valid real radius, and a nonzero
point effect. These properties were independently proved in
[SpatialChecks.lean](/home/ubuntu/sap/tasks/FW-P008b-r8g3/scratch/SpatialChecks.lean:39).
The converse witness satisfies the usual measure-theoretic conditions.

For T27, both the additive identities and their homogeneous radial specialization
are present. Allowing arbitrary radius selectors includes every permitted metric.
The arbitrary baseline equals the all-control outcome on the field by the
additive hypothesis. Extending a radial function from nonnegative reals to all
reals changes no metric-distance argument. The compiled
[nonvacuity instance](/home/ubuntu/sap/tasks/FW-P008b-r8g3/scratch/SpatialChecks.lean:142)
has baseline 2, coefficient 3 and a circle of mass 1.

For T28, fixed independent Bernoulli assignment, uniformly bounded outcomes,
independence of collections separated by a graph of bounded degree, and a fixed
empty-arm completion match the sufficient version clause by clause. The record
and docstring accurately disclose the omitted general consistency, standardized
normality and spatial-HAC conservativeness assertions. The compiled
[sequence](/home/ubuntu/sap/tasks/FW-P008b-r8g3/scratch/ProbabilityChecks.lean:75)
has p=1/2, H=1, D=0, outcomes equal to own treatment bits, and AMR 1 for every n.

Positive finite circle mass, integrability and concentration prevent the relevant
averages from depending on totalized junk values. Positive node counts guard all
asserted AMR means; T28 explicitly completes empty arms. Finite marginalization
uses the unconditional law of the other treatments, as required by S3.

Both scratch files compiled successfully with `sap-lean`. Their reported proof
dependencies contain only `propext`, `Classical.choice` and `Quot.sound`;
the checks use neither the audited theorems nor `sorryAx`. The final
[findings.json](/home/ubuntu/sap/tasks/FW-P008b-r8g3/findings.json) was parsed and
checked for exactly one entry per declaration and matching fingerprints.
