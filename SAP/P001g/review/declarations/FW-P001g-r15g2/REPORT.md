# Declaration review

All five current declarations are **faithful**, with severity **none**.
The `refuted` decisions for T121/T124 and `whole` decisions for T125–T127
are correct. Their docstrings accurately describe their statements. There
were no changes to the independent claim-stage conclusions after reading
the record.

`reading.md` was saved before opening claims or review history. Every
declaration in `closure.json`, including its generated proof auxiliaries,
was read. `claim-stage.json` was saved before reading `record.json`;
`earlier.json` and `architect-report.md` were read between those stages.
The supplied canonical excerpts suffice for these comparisons; no other
review, architect, or referee sources were consulted.

**T121.** The printed reading is: if a nonempty subset of mixture
components generates the true conditional law, the full-vector product-MLE
is consistent and asymptotically efficient.

Its conditions and the current witness are:

- IID observations on a probability space: take the infinite product of
  q=(√2/4,√2/4,1−√2/2) on the three outcomes.
- A true parametric mixture and a nonempty generating subset: the first
  component is q, the second is the affine circle family in
  `Defs/WholeW2.lean:26`, and the first component alone generates q.
  A constant covariate, or a zero-length covariate vector, realizes the
  conditional-model setting. Both components have positive normalized
  masses throughout their parameter domains.
- The full-vector estimator is a measurable, unique product-likelihood
  maximizer: `CircleMLEW2` at `Defs/WholeW2.lean:66` requires precisely
  this for every positive-size sample, including samples of probability
  zero. Its satisfaction is checked below.
- Consistency is for the full true vector: every t_b=(1,b), b∈S¹, is a true
  vector under the same law. No identification premise occurs in the claim.

To check that the argmax condition is genuine, put z=(1−p)b. The mixture
law is A(z) on the closed Euclidean unit disc. The likelihood is positive
and continuous, hence attains a maximum. If at least two outcome counts
are positive, the log likelihood is strictly concave: any two of the
three affine-coordinate gradients are linearly independent. If only one
count is positive, maximizing its nonconstant affine coordinate over the
disc has a unique solution. Thus the disc maximizer is always unique.
At z=0 its gradient can vanish only if the empirical outcome proportions
equal q. That is impossible at positive n because √2/4 is irrational.
Consequently the maximizer z* is nonzero and has exactly one full-vector
preimage: p=1−‖z*‖₂, b=z*/‖z*‖₂. At n=0 choose any point of Θ.
Every sample domain is finite, so these estimators are measurable.

Under the same IID law this single estimator cannot converge in probability
to both (1,1,0) and (1,−1,0), by uniqueness of probability limits. This
contradicts the canonical consistency assertion, and therefore its
conjunction with efficiency. `scratch/Counterexamples.lean` independently
compiles the probability law, IID sequence, distinct true vectors and their
identical laws. The all-sample uniqueness argument above is a mathematical
check rather than a separate recompiled proof.

Both earlier issues are **fixed**: the current statement retains unique
argmax and uses a different witness; consequently the current docstring
and `refuted` label are justified. This conclusion does not depend on the
architect's account of an adjudication.

**T124.** The printed reading is: under IID sampling and W ⟂ D | X,
the conventional added-variable OLS F test using its reference quantile
has limiting rejection probability at most its nominal level.

Its conditions and the witness can be checked explicitly:

- Let X be uniform on {−1,0,1}, let Z be equiprobable on {−1,1} conditional
  on X, set W=X²+Z/2, and draw D independently of Z given X, with
  P(D=1|X=0)=1/4 and P(D=1|X=±1)=3/4. All 12 cell probabilities are
  positive and sum to one. Their infinite product gives IID units.
- W ⟂ D | X holds by construction. W can be generated before D with
  W(0)=W(1)=W, so it is unaffected by treatment. Constant potential
  outcomes extend the witness to the causal setting; treatment overlap
  holds as well. Nonlinear treatment propensity is allowed by the claim.
- The test is the actual OLS RSS F statistic in `Defs/Part3.lean:50`,
  with one added regressor and residual degrees of freedom n−3. The
  critical value is a genuine median of F(1,n−3), corresponding to α=1/2.
- The population restricted/full Gram determinants are 2/3 and 17/54.
  Their residual risks are 35/144 and 59/272. All these equalities, the
  population coefficients, and the resulting positive ratio
  (risk_R−risk_F)/risk_F=64/531 compile independently in
  `scratch/Counterexamples.lean`.
- The strong law for the finite cell frequencies gives almost-sure
  eventual nonsingularity and positive full risk, exactly the
  `placeboGood` conditions at `Defs/Part7.lean:50`. It also gives
  F_n/n→64/531 almost surely. The F(1,n−3) medians are bounded for large n,
  since those reference laws converge to the continuous, strictly
  increasing χ²₁ law on positive arguments. Hence guarded rejection
  occurs eventually almost surely and its probability tends to one.

This is a counterexample to the canonical size assertion itself, even with
the regression-validity guards. It uses neither dependent replicates nor
singular-regression defaults. The infinite-sample argument is checked
mathematically; it was not independently re-proved in scratch Lean.

**T125.** The arithmetic sample mean and `CP` exactly match the canonical
definitions. L² on a probability space is equivalent to finite variance
with the standing existence of the mean. Inclusion of zero variance
matches footnote 10 in the canonical statement. The Chebyshev bound in
`finite_lemmas` is not an additional asserted conclusion. No hidden
substantive assumption or docstring discrepancy remains.

**T126.** Both printed CLT forms, the two exact standardization formulas,
the sample-mean standard deviation, and the standardization moments are
present. Standardization uses population moments, as required. `CD` is
CDF convergence at continuity points; Gaussian parameters are variances.
L² and positive variance express exactly the stated finite-moment domain.

**T127.** The canonical statement itself includes the preceding
continuous-PDF condition. `HasPDF`, the rectangular kernel, the arithmetic
kernel average, deterministic positive bandwidths and both bandwidth
limits correctly render that statement. The conclusion holds separately
at every real x; it makes no uniform-convergence assertion. The unused
finite-sample identities are not extra required clauses.

`scratch/Nonvacuity.lean` compiles independent examples satisfying all
hypotheses of these three results: IID standard Gaussian coordinates with
variance 1 and finite second moment; also a constant sequence for T125;
and, for T127, the continuous Gaussian PDF and h_n=1/(√n+1), with
positivity and both bandwidth limits proved. For the positive-sample
conjunct of T126, n=1 supplies its remaining hypothesis.

The full junk-value inventory is in `reading.md`. None changes the
meaning: probability measures prevent infinite probability values,
finite-moment premises protect means and variances, positive variance
protects positive-sample standardization, the F guard protects the
regressions, and bandwidths are positive. Empty-sample totalizations do
not affect the asymptotic conclusions. No SAP definition is a placeholder
or builds its required conclusion into a hypothesis.

Validation used only `sap-lean`, with at most two Lean processes at once.
`scratch/BlindCheck.lean`, `scratch/Nonvacuity.lean`, and
`scratch/Counterexamples.lean` all completed successfully. The first emits
only the expected warnings for printing generated auxiliary declarations.
Both result JSON files were parsed and their target/fingerprint coverage
checked against `closure.json`. No package source was changed.
