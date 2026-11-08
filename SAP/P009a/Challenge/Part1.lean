import SAP.P009a.Defs.WholeW1
import SAP.P009a.Defs.WholeW2
import SAP.P009a.Defs.WholeW3
import SAP.P009a.Defs.WholeW4
import SAP.P009a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/--
P009-T1. Section 6.1, p. 689, equation (1); Definition 10, p. 691;
Propositions 8–10, pp. 692–693.
The fair Bernoulli family y₁(z)=z₁, yᵢ(z)=0 for i>1 satisfies every clause (a)–(h) of the
counterexample: all real moment orders, full-cube bounds and diagonal interference, the exact
estimands, estimator moments, four coincident variance estimates, finite two-point scaled errors
and lower-tail cutoff, equation (1), vanishing scaled expected bias, contribution variances and
all dispersion and graph-rate conditions. Part B's positive mean-square lower bound fails.
For every alpha in (0,1), each of the four plug-in intervals has coverage exactly 1/2, with
the stated pointwise interval cases; every relative underestimation probability is 1/2 and the
normalized true variance tends to zero. Thus the printed conservative-inference implication fails.
-/
theorem SAP.P009a.T1 : SAP.P009a.T1WholeStatement := by sorry

/--
P009-T2. Section 6.1, p. 689, corrected sentence; Definition 10, p. 691.
For unbiased square-integrable statistics with positive finite variance and nonnegative measurable
variance estimates, plug-in noncoverage is at most the relative underestimation probability plus
alpha/(1-eta). Vanishing relative tails give liminf coverage at least 1-alpha. Additive scaled
lower-tail control and an eventual positive normalized-variance floor give relative control,
including the finite event inclusion. The literal iterated Definition-10 condition gives all
fixed-cutoff limits. Bernoulli HT is unbiased and has the stated coverage under this variance
floor. Scaled bias may vanish and coverage may fail without the floor, as the sparse family shows.
-/
theorem SAP.P009a.T2 : SAP.P009a.T2WholeStatement := by sorry

/--
P009-T3. Supplement A, pp. 8, 22, 23, 25, proofs of Lemmas A9, A22, A23, A25.
The three specified two-unit experiments refute each printed replacement of unequal positive
weights by a common upper bound inside a signed covariance sum. The full-cube outcome bounds
and Assumption 1 at every real q≥2 and s≥1 are included. The signed example has B~Bernoulli(3/16),
variance 39/256, the stated covariance matrix and muHat=(4/3)B. The count example has arm-size
ratio 2 or 2/3 with probabilities 1/4 and 3/4. The square example has W=0,16/9,16 with probabilities
3/16,9/16,1/4, mean 5, second moment 592/9 and variance 367/9>39. The final lemma rates stand.
-/
theorem SAP.P009a.T3 : SAP.P009a.T3WholeStatement := by sorry

/--
P009-T4. Supplement A, pp. 3, 8, 22–23, 25: Lemma A3 and corrected variance chains.
For square-integrable real random variables on any probability space, the weighted variance is
the double covariance sum and is bounded by K squared times the absolute covariance sum.
Assumption 1B alone gives the absolute power-covariance bound. Under Assumption 1, every
intermediate inequality and equality of A9, A22, A23 and A25 holds, including cancellation,
all diagonal mixing terms, and the final two-arm variance comparison. Moment orders may be
finite or infinite; zero mixing to the zeroth power means zero. The chains hold for every
admissible order, hence also for the maximum in Definition 9 whenever that maximum exists.
-/
theorem SAP.P009a.T4 : SAP.P009a.T4WholeStatement := by sorry

/--
P009-T5. Supplement A, pp. 6–7, proof of Proposition 1.
The printed claim is false: a regular fair Bernoulli interference family has density tending
to the positive limsup one quarter, yet attains that threshold at only the four positive
sizes 1, 2, 3 and 4. Its full interference and dependence graphs, exact density, parity gaps,
and failure of Assumption 2 are stated. This refutes the limsup selection step.
-/
theorem SAP.P009a.T5 : SAP.P009a.T5WholeStatement := by sorry

/--
P009-T6. Supplement A, pp. 6–7, proof of Proposition 1.
Every threshold strictly below a positive finite limsup is met infinitely often; the threshold
at the limsup need not be met. Failure of restricted interference supplies a limsup in (0,1].
Retaining the designs and using the displayed outcomes with lambda equal to that limsup on the
selected indices, and zero elsewhere, gives uniform regularity and an HT error bounded away
from zero with probability one infinitely often. Consequently HT is inconsistent for EATE.
-/
theorem SAP.P009a.T6 : SAP.P009a.T6WholeStatement := by sorry

/--
P009-T7. Section 6.3, p. 693.
The printed normal-approximation sufficiency fails: both explicit fair Bernoulli families
have all finite regularity orders and diagonal interference dependence, but their standardized
HT statistic is exactly 2 Z1 - 1. Its distance from every continuous distribution function is
at least one quarter. The first family's EATE is 1/n; the second family's EATE is one.
Both have true variance 1/n squared and fail standard normal convergence.
-/
theorem SAP.P009a.T7 : SAP.P009a.T7WholeStatement := by sorry

/--
P009-T8. Section 6.3, p. 693.
Under Assumption 1, Bernoulli assignment, uniformly bounded maximum dependence, and an
eventually positive lower bound on n times the true HT variance, the variance is eventually
positive and HT centered at EATE and scaled by its true standard deviation is asymptotically
standard normal. Any values at the earlier zero-variance indices give the same limit.
Without the variance lower bound the sparse Bernoulli counterexample fails normal convergence.
-/
theorem SAP.P009a.T8 : SAP.P009a.T8WholeStatement := by sorry

/--
P009-T9. p. 688 (PDF p. 16), first paragraph before Proposition 5, third sentence.
The printed claim is false: for every r ≥ 1, n = 4r+2 and h = 2r+1, complete
randomization with h treated units admits the stated half-population outcome schedule.
All outcomes are in [0,1], all treatment marginals are 1/2, and Assumption 1 holds
with k = 2 at every finite q ≥ 2 and s ≥ 1. The incoming sets are the disjoint
halves A and B for units 1 and 2 and singletons for the other units. Thus d₁₂ = 0,
the dependence sum is 3n-4, d_AVG = 3-4/n < 3, c₁ = c₂ = 1 and all other cᵢ = 2,
C₁ = 2-2/n and C_∞ = 2. On the design support T_B = h-T_A. The respective
majority and minority events belong to the sigma-algebras generated by the two
masked assignments, coincide almost surely, and each, as well as their intersection,
has probability 1/2. Their discrepancy and the pair mixing coefficient are 1/4
for every r, refuting all-pairs vanishing along this growing family.
-/
theorem SAP.P009a.T9 : SAP.P009a.T9WholeStatement := by sorry

