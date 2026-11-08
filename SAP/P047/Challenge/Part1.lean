import SAP.P047.Defs.WholeW1
import SAP.P047.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open SAP.P047

/-- P047-T1; Section 1, first bullet, second sentence, p. 85 (PDF p. 2).
The known-propensity estimators have the stated conditional and unconditional
means, contribution bounds, Hoeffding tails, finite-sample interval coverage,
and exact root-n ATE interval width, including the one-mean component under
its weaker one-arm conditions. -/
theorem SAP.P047.T1 : T1Statement := by sorry

/-- P047-T2; Section 1, first bullet, first sentence, p. 85 (PDF p. 2).
The known-propensity ATE estimator is uniformly root-n tight with the explicit
exponential bound and has a fixed-law centered normal limit with variance
at most B squared over epsilon squared, including zero variance. -/
theorem SAP.P047.T2 : T2Statement := by sorry

/-- P047-T3; Section 1, second bullet, pp. 85–86 (PDF pp. 2–3).
The usual measure-theoretic conditions are assumed. With unknown propensity,
uniform covariate, binary potential outcomes, joint ignorability and common
overlap [1/4,3/4], every sample-only estimator has worst-case error at least
1/2 at tolerance 1/12 for every positive sample size, and uniform consistency
is impossible. The concrete baseline S belongs to this model, has propensity
1/2 and effect 1/2. For every asymptotically honest interval at level 1-alpha,
0 < alpha < 1/2, its probability under S of width greater than 1/6 has limit
inferior at least 1-2*alpha > 0. Width therefore fails to shrink in probability
under S and uniformly over the model. All conclusions hold for every
containing class of probability laws in which the mean effect exists,
without assumptions on its additional laws. They allow an arbitrary
independent random seed and measurable extended-real interval endpoints.
Thus leaving both nuisance functions unrestricted precludes the two desired
properties; no sufficiency or separate mathematical notion of testability
is asserted. -/
theorem SAP.P047.T3 : SAP.P047.T3WholeStatement.{u} := by sorry
