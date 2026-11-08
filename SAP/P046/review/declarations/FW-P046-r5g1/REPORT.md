# P046 declaration review

All five declarations are **faithful**, with severity **none**. Each states
the whole canonical claim. The five recorded `whole` decisions and null
restrictions are correct; no claim-stage assessment changed after reading the
record. Their docstrings describe the statements accurately and explicitly
assume the usual measure-theoretic conditions.

The blind reading and all dependency definitions were reviewed before opening
the claims; [reading.md](/home/ubuntu/sap/tasks/FW-P046-r5g1/reading.md) was saved
first. The [claim-stage assessments](/home/ubuntu/sap/tasks/FW-P046-r5g1/claim-stage.json)
were saved before opening the record. All 79 generated proof helpers in the
combined closure were inspected as well as the source definitions.

| Declaration | Assessment |
| --- | --- |
| T1 | Includes the exact continuous design, standing assumptions, statistic reductions, category and count laws, exclusion tests, 5151 states, 1946 failures, exact probability, and both coverage and tail failures. |
| T2 | Includes the positive event, pointwise design equations, actual conditional mean, conditional tail one, and full right side 1/20. Conditioning uses the original sample law. |
| T3 | Includes all five corrected-proof steps, the corrected population tail and coverage, the width rate with a constant chosen before n, and the known-bound alternative. |
| T4 | Includes exact empirical fits and minimizer characterizations, population criterion, summand table and probabilities, moments, finite-sample variances, both Gaussian limits, and exclusion of zero from the weighted closure. |
| T5 | Includes both the zero-benchmark family theorem and the direct risk-comparison theorem, with the stated Gaussian limits and ordering, fixed-summand variance identity, and norm equivalence. |

The counterexample readings and conditions were checked individually:

* **T1:** the printed interval must cover the population mean under repeated
  independent samples. The witness has independent full-data units and
  conditional assignments, binary outcomes and treatment, uniform continuous W,
  consistency, unconfoundedness, known scores, and strict positivity with
  delta=1/200. It satisfies every condition and has strict noncoverage above alpha.
* **T2:** the printed conditional display centers at the population mean under
  that same sampling setting. The specified independent uniform/Bernoulli
  design satisfies all conditions, including positivity with delta=1/20.
  Its failing covariate event has probability 2^(-100)>0. This witnesses the
  conditional proof-step failure asserted by the canonical claim.
* **T4:** the efficiency assertion uses empirical weighted squared error on
  treated training cases, as fixed by the canonical definitions. Independent
  W,Z and conditional assignment, binary variables, consistency,
  unconfoundedness, known scores, positivity with delta=1/8, balanced opposite
  folds, a one-parameter family, and exact empirical minimization all hold.
  The zero-inclusion condition is absent from that printed assertion.

These are whole statements of the canonical counterexamples; none is labelled
`refuted`. Audit-history notes and finite lemmas were not promoted to extra
clauses of the claims.

No operative junk value changes a statement. All measured probabilities are
finite; conditional expectations have integrable inputs and valid conditioning
sigma algebras. T4's real L2 error is identically zero. In T5 the family-member
L2 premises protect its real risk and closure integrals, while the direct
theorem uses extended errors and risks that retain infinity. Its risk bound
forces finite limit risk and L2 membership. Gaussian variance zero is a point
mass. Empty-sample average identities are harmless total extensions; the
nontrivial finite-sample mean and variance formulas require positive n.

[scratch/Check.lean](/home/ubuntu/sap/tasks/FW-P046-r5g1/scratch/Check.lean)
compiled successfully, including a complete T3 premise instance and complete
instances of both T5 premise sets. The explicit validity and balance facts
used there are projections of the supplied certified closed witnesses; the new
learner, empirical-minimization and convergence obligations are proved directly.
[The arithmetic check](/home/ubuntu/sap/tasks/FW-P046-r5g1/scratch/audit_arithmetic.py)
independently reproduces T1's exact integer numerator and all failure states
using rational logarithm bounds, and checks T4's eight latent atoms and every
sample at n=2 and n=4 with exact fractions. Results are in
[scratch/arithmetic.json](/home/ubuntu/sap/tasks/FW-P046-r5g1/scratch/arithmetic.json).

[findings.json](/home/ubuntu/sap/tasks/FW-P046-r5g1/findings.json) contains exactly
the five requested declarations and their fingerprints copied from the closure.
