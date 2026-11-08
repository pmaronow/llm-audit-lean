Audited 2 targets. Counts:

| Verdict | Count |
| --- | ---: |
| correct_whole | 1 |
| correct_restricted | 1 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

There are no adverse findings or omitted targets. Both severities are `none`.

The blind mathematical reading was saved in [reading.md](reading.md) before
opening `claims.json`. The independent comparisons were saved in
[claim-stage.json](claim-stage.json) before opening `record.json`. Reading the
record required no change to either step-2 comparison.

`SAP.P021.T1` is `correct_whole`. Its conditional quantities are the elementary
conditional moments and probabilities on positive-mass strata. It states the
identification formula and every printed Bayes and cancellation equality,
together with the support and nonzero consequences in the canonical reading.
The support convention is already a standing assumption in `claims.json`.
No independence or separate sign assumption is imposed. Finite positive degrees
and bounded measurable outcomes make all relevant integrals genuine integrals;
positivity on the nonempty supported degree set justifies every conditional
denominator used. The inverse-profile denominator is c/sampleFraction, which
is nonzero even when c and the supported profile values are negative.

`SAP.P021.T2` is `correct_restricted`. The additional assumptions at
`Defs/Part2.lean:74` and `Defs/Part2.lean:84` require samples to be nonempty
almost surely at every random stage and at every deterministic stage.
`Challenge/Part1.lean:16-19` and the record describe exactly this restriction.
The common bounds, marked empirical convergence to a fixed probability law,
and limit-law Conditions 1 and 2 are the canonical standing assumptions;
both random and deterministic conclusions are retained. Coordinate
measurability supplies ordinary random population observations, and positive
population sizes make their empirical probability laws well-defined.

The restriction excludes actual canonical examples. On the uniform probability
space [0,1], let N_r=r+1 and give every unit Y=D=1. Mark every unit sampled
exactly when omega is at least 1/(r+2). The empirical law converges in probability
to the point mass at (1,1,1), which satisfies both conditions with c=a=1.
The empty-sample probability is 1/(r+2)>0 at every stage. The estimator, with
its Lean value 0 on empty samples, still converges in probability to 1.
A deterministic sequence with only its initial sample empty likewise meets
the canonical convergence premise. These are examples of the disclosed loss
of scope, not counterexamples to the restricted statement.

For truth of T2, put b=c*a. At any supported degree, positivity gives b>0.
Mean ignorability and the degree profile give E[S/D]=b and E[SY/D]=b*E[Y].
Both integrands are bounded and continuous on the common state space.
The empirical convergence premise therefore gives convergence of their two
averages, and division by the nonzero limit b gives each stated conclusion.
None of these hypotheses assumes consistency itself.

[scratch/Check.lean](scratch/Check.lean) supplies Lean nonvacuity checks using
only the definitions: an outcome-1, degree-1, always-sampled Dirac law, with
positive populations and both empirical convergence premises. It checks the
negative-scale choice as well. Validation uses
`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`; output is saved in
[scratch/Check-output.txt](scratch/Check-output.txt). The file compiled
successfully, and the printed witness dependencies contain no `sorryAx`.
This checks the witnesses, not the Challenge stubs or a Solution.

[scratch/exact_check.py](scratch/exact_check.py) independently checks all T1
ratios and the T2 numerator and denominator for a nonconstant-outcome law with
degree probabilities (1/2,0,1/2), inclusion probabilities (1/4,3/4) on its
support, and mean 1/2. An eight-unit block with the indicated integer
multiplicities realizes this law exactly; repeating the block gives growing
populations with a nonempty sample and both convergence premises. The missing
degree also checks that no null-stratum division convention carries the result.

The [paper's preprint](https://arxiv.org/pdf/1504.03574) was consulted as a
secondary check of the two displayed results; the journal transcription and
canonical standing assumptions supplied in `claims.json` govern this audit.

Python validated both output JSON files, their required fields, unique target
coverage, and correspondence with the recorded theorem names.
