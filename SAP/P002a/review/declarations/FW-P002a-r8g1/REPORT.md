# Declaration review

All three declarations are **faithful**, severity **none**. Their `whole` decisions
and current docstrings agree with the canonical claims. No correction is needed.

The blind reading and totalization audit are in [reading.md](reading.md), saved
before opening the canonical claims or review history. Every declaration listed
in each target's closure was read, including the generated constructors,
projections and auxiliary proofs. The latter were printed in
[scratch/BlindCheck.lean](scratch/BlindCheck.lean) and contain only numeral-instance
proofs. The claim-stage judgments are in [claim-stage.json](claim-stage.json);
none changed after reading the record.

- **T2:** Both corrected finite variance bounds, the entire guarded complier chain,
  the scaled population and residual-square bounds, both negative-delta inclusions,
  and agreement with the printed nonnegative-delta bounds are present. The raw
  statistic has the required scaling. The adjusted oracle uses the two
  potential-response population fits. The singleton convention is canonical;
  the intermediate chain separately requires at least two compliers. Zero
  variances introduce no artificial premise or undefined quantity.
- **T7:** All four limits have the correct feasible statistic, pooled-coefficient
  oracle, oracle-variance scale and variance estimator. One conull event covers
  all positive thresholds, after each deterministic subsequence is fixed. Strict
  positivity of both population OLS residual variances is explicitly part of the
  current canonical claim, separately at each size, without a uniform lower bound.
  The marginal law permits arbitrary coupling across sizes. The finite conditional
  probability holds the observed response fixed and exactly represents fresh
  independent reassignment. Division by zero agrees with the specified convention;
  finite-size conditional-variance positivity is not silently assumed.
- **T9:** The finite component states every block entry, the exact minimum
  eigenvalue, and the quadratic bound for every vector. The real infima are over
  nonempty unit spheres and nonnegative bounded quadratic values. The sequence
  component uses the correct observed-arm coefficient error and a common
  path-dependent vanishing error for both arms. It imposes no cross-size
  independence or residual positivity. A pathwise error sequence is a faithful
  rendering of the almost-sure remainder here: an explicit measurable choice can
  be recovered from the minimum of the two quadratic-form ratios, taking zero
  when the coefficient-error vector is zero.

The OLS definition selects a genuine least-squares minimizer on singular arms;
finite real least squares always has one, so its final no-minimizer fallback is
unreachable. Population fits under Xi are nonsingular. For these deterministic
finite-population sequences all statistics, including the selected singular fits,
are measurable functions of finite assignment spaces. Gaussian tail conversion
never sees infinite measure. Valid designs exclude all empty-arm, empty-design,
population-variance and LATE zero denominators.

Nonvacuity was checked independently of the Challenge stubs by compiling
[scratch/Nonvacuity.lean](scratch/Nonvacuity.lean), which imports only Defs.
It constructs a nondegenerate four-cell model at delta=0 and delta=-1/2, verifies
T9's finite spectral hypotheses, and builds the growing repeated-cell family
with sizes `4*(j+1)`, residual variances `n/(n-1)>0`, and a genuine infinite product
of uniform assignment measures. The full marginal identity and all T7 and T9
sequence premises are proved, including a strict subsequence. The log is
[scratch/Nonvacuity.log](scratch/Nonvacuity.log).

The single supplied earlier issue is **fixed**: `record.json:56` now correctly
identifies residual positivity as part of the canonical T7 claim. The earlier
restricted descriptions in the architect report are marked historical and
superseded. This resolution is recorded in `findings.json`; there is no current
issue to retain. The supplied proof certification was taken as given; scratch
checks establish nonvacuity and inspect elaboration, rather than reprove the
three audited claims. No package source was edited.
