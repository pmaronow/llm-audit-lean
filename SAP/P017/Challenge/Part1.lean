import SAP.P017.Defs
import SAP.P017.Defs.WholeW1
import SAP.P017.Defs.WholeW2
import SAP.P017.Defs.WholeW3

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u1 u2 u3 u4 u5

/-- P017-T1; Proposition 1 and its proof fact, PDF p. 2; Assumption 1, PDF p. 1.
The uniform-effect IID inverse-probability estimator is asymptotically normal and
has positive-probability realizations clipping to either unattainable endpoint. -/
theorem SAP.P017.T1 : SAP.P017.T1Statement := by sorry

/-- P017-T2; the fact cited after Proposition 1, PDF p. 2, corrected.
An admissible weighted mean is attainable exactly at an atom or between positive
masses on both sides, with all interior, endpoint and exterior support consequences.
The prescribed normalized atom indicator and two-region mixture are bounded,
nonnegative, admissible, and have weight mean one and weighted-effect mean equal
to the target; the conditional means straddle the target and the specified
mixing coefficient is strictly between zero and one. -/
theorem SAP.P017.T2 : SAP.P017.T2WholeStatement.{u1} := by sorry

/-- P017-T3; Proposition 1 and its gloss, PDF p. 2, corrected.
The original clipped target is representable exactly when strictly between the
effect-support bounds or at a support endpoint with positive mass. A strictly inside estimate equals its
target and satisfies the full chain of clipping and support bounds. Infinite
radius, atoms at binding clipping endpoints, and almost surely finite-valued
effects give representation on every realization. Under root-n asymptotic
normality, both the strictly inside and representation probabilities tend to one. -/
theorem SAP.P017.T3 : SAP.P017.T3WholeStatement.{u1, u2} := by sorry

/-- P017-T4; Proposition 1 and Definition 2, PDF p. 2, corrected.
A positive finite radius smaller than the population radius always exists and
makes every clipped estimate representable, with the repaired finite companions
and support corollary and the obstruction to substituting a larger radius. -/
theorem SAP.P017.T4 : SAP.P017.T4Statement.{u1, u2} := by sorry

/-- P017-T5; proof of Proposition 3, PDF p. 2.
The shifted normal sample mean has nonzero intermediate error with probability
one and violates the printed every-positive-sequence assertion, while its actual
clipping error vanishes on the stated central event. -/
theorem SAP.P017.T5 : SAP.P017.T5Statement := by sorry

/-- P017-T6; proof of Proposition 4, PDF p. 3.
The shifted normal estimator satisfies the remainder condition but at size 25
has positive central intermediate error and a mean-square gap above the printed
tail bound, while both true mean-square limits still hold. -/
theorem SAP.P017.T6 : SAP.P017.T6Statement := by sorry

/-- P017-T7; proof of Proposition 3, PDF p. 2, corrected on 2026-11-04.
With the finite population mean and positive, possibly infinite effect radius
of Assumption 1, the actual clipping error has its exact zero region and
exceedance-event inclusion and probability bound at every positive sample size.
Consistency alone gives every fixed-radius tail limit, the clipping-failure
probability limit, o_p(a_n) actual error for every deterministic sequence
positive at n ≥ 1, and root-n actual error o_p(1). Definition 1 additionally
gives root-n boundedness in probability and consistency, hence all these limits.
At infinite radius the target is the estimate and both the actual error and its
root-n scaling are identically zero. The clipping-event deduction requires no
normal decomposition or rate for the clipping-failure probability.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P017.T7 : SAP.P017.T7WholeStatement_W3 := by sorry

/-- P017-T8; proof of Proposition 4, PDF p. 3, corrected.
The Lipschitz clipping and residual inequalities give the finite Gaussian fourth-moment
bounds, both mean-square limits, and zero actual error at infinite radius.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P017.T8 : SAP.P017.T8Statement.{u1, u2, u3} := by sorry

/-- The printed claim is false: the universal empirical-statistic representation
assertion fails even with IID full-data draws from G, measurable observed records
and an estimator given by a measurable functional of the observed empirical law,
integrable effects, positive radius, and asymptotic normality.
The counterexample samples independently from the specified population G;
IID sampling supplies a valid counterexample to the printed all-realizations assertion.
P017-T9; Proposition 1 and its all-realizations gloss, PDF p. 2.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P017.T9 : SAP.P017.T9SamplingStatement := by sorry

/-- P017-T10; Corollary 1, its proof, and its two support remarks, PDF p. 2, corrected.
Estimator support inside the clipping interval gives probability one of zero error;
full real effect support gives the identity target, while nonnegative effect support
and negative estimates give the stated strict loss of equality probability.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P017.T10 : SAP.P017.T10Statement.{u1, u2, u3, u4, u5} := by sorry

/-- P017-T11; the normal-tail display in the proof of Proposition 4, PDF p. 3,
corrected. The displayed Lebesgue tail integral equals its closed form, the
truncated second moment of any random variable with the specified Gaussian law,
and the scale-s density/CDF expression. The standardized density integral has
the stated integration-by-parts value. The relevant integrands are integrable,
and the common value decays faster than every positive power of sample size.
At infinite radius the tail set is empty, its integral and truncated moment are
zero, and the same power limits hold.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P017.T11 : SAP.P017.T11WholeStatement := by sorry

/-- P017-T12; the sentence after Proposition 3, PDF p. 2.
The IID rare-outlier construction realizes every positive vanishing clipping-
failure sequence under the stated hypotheses. It is a statistic of the observed
empirical distribution and has the stated exact events, normal decomposition,
finite moment bounds, central-event probability bounds and probability limits.
The logarithmic example has the stated numerical values and slow rates, and
fails the mean-square remainder condition. For each prescribed positive
vanishing rate r, the explicit sequence min(1, sqrt(r)) equals sqrt(r) eventually,
tends to zero, and its ratio to r tends to infinity; the same construction
realizes it. These facts refute a universal-rate interpretation of "quickly";
the printed sentence specifies no numerical rate. -/
theorem SAP.P017.T12 : SAP.P017.T12WholeStatement := by sorry

/-- P017-T13; the sentence after Proposition 3, PDF p. 2, corrected.
The clipping interval is exactly the zero-error event with probability tending to one,
every prescribed positive vanishing failure rate is realizable, and a finite normal-plus-
remainder probability bound retains the uncontrolled remainder probability.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P017.T13 : SAP.P017.T13Statement.{u1, u2, u3} := by sorry

/-- The printed claim is false: P017-T14; Proposition 3 and its printed proof,
PDF p. 2. In the admissible shifted-normal example the intermediate error from
the actual target fails a positive-sequence little-o assertion, and its nonzero
probability is one rather than the asserted Gaussian tail. The proposition's
actual root-n error conclusion remains valid under all its original assumptions.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P017.T14 : SAP.P017.T14WholeStatement.{u1, u2} := by sorry

/-- The printed claim is false: P017-T15; Proposition 4 and its printed proof,
PDF p. 3. The shifted-normal example satisfies the exact Gaussian-plus-remainder
condition and its moment rate, yet has positive intermediate squared error in
the central region at size 25 and an intermediate mean-square error strictly
above the printed Gaussian-tail bound. The proposition's actual mean-square
conclusion remains valid without independence.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P017.T15 : SAP.P017.T15WholeStatement.{u1, u2} := by sorry

/-- P017-T16; Proposition 2 and its pointwise proof, PDF p. 2.
The clipped target minus the population mean, multiplied by sqrt(n), is bounded
in probability under root-n asymptotic normality, with zero and infinite radius allowed. -/
theorem SAP.P017.T16 : SAP.P017.T16Statement.{u1, u2} := by sorry
