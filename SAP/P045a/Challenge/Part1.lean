import SAP.P045a.Defs.WholeW1
import SAP.P045a.Defs.WholeW2
import SAP.P045a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P045-T1; p. 310 (PDF p. 22); definitions on pp. 308–309 (PDF pp. 20–21).
The four-unit, two-group co-member schedule refutes Bernoulli arm-ratio unbiasedness.
It has the stated individual, group and population estimands, pointwise arm formulas,
positive conditioning domains and every own-arm and both-arm conditional expectation.
Direct, indirect and total ratios fail as quantified, whereas the overall estimator is unbiased.
The usual measure-theoretic conditions are assumed; here all laws and sums are finite. -/
theorem SAP.P045a.T1 : SAP.P045a.T1WholeStatement := by sorry

/-- P045-T2; p. 310 (PDF p. 22).
Bernoulli arm ratios can be biased even conditional on a positive denominator.
HT group means, uniform first-stage averages and their direct, indirect and total
contrasts are unbiased for the Bernoulli marginal targets. Fixed-count assignment
instead makes the original ratios unbiased for that design's marginal targets,
which differ under interference. Overall means remain unbiased for arbitrary local
laws. The joint results require only the stated conditional group marginals, allow
cross-group dependence, and include empty Bernoulli arms. All four-unit formulas
and the numerical HT contrast expectations are retained.
The usual measure-theoretic conditions are assumed; all spaces here are finite. -/
theorem SAP.P045a.T2 : SAP.P045a.T2WholeStatement := by sorry

/-- P045-T3; p. 310 (PDF p. 22) and p. 311 (PDF p. 23).
In the actual six-group joint toy design, all 14,580 supported outcomes are equally
likely. The additive schedule has direct estimand and estimator mean one, but
variance 1/2 and expected singleton-drop variance estimate 1/3 at either regime.
The singleton and direct-statistic distributions, two-unit sample variance and
expected between-group sample variance give the stated bias -1/6 and ratio 2/3.
The dilated schedules are also downward biased, and the zero-control schedule
gives upward bias. The dropping convention is part of the specified estimator.
The usual measure-theoretic conditions are assumed; all laws here are finite. -/
theorem SAP.P045a.T3 : SAP.P045a.T3WholeStatement := by sorry

/-- P045-T4; p. 310 (PDF p. 22); toy example, pp. 310–311 (PDF pp. 22–23).
The corrected direct variance formula is conservative on its proper domain, with the stated equality
characterization and singleton-drop bias formulas.
Restriction: Retains mathematical parts (a)-(d), including the exact bias, nonnegativity, equality
if and only if within-group effects are constant, both general singleton-drop biases, both dilated
biases and their strict negativity criterion, and undefined corrected toy variance on every
admissible toy assignment. Omits execution of an R implementation that propagates undefined arm
variances to NA and emits a warning, and replacement of the reported toy output entries by NA. The
optional regenerated six-by-six toy is not asserted. -/
theorem SAP.P045a.T4 : SAP.P045a.T4Statement := by sorry

/-- P045-T5; p. 305 (PDF p. 17); staged package R/make_exposure_map_AS.R, lines 104–121.
The stipulated all-control event is the complement of all-treated, and differs
from the documented all-untreated event. The two-vertex count/event tables,
probabilities and all four HT values for the linear and threshold schedules
exhibit the exact failure and the case where the expectation does not move.
The usual measure-theoretic conditions are assumed; all spaces here are finite. -/
theorem SAP.P045a.T5 : SAP.P045a.T5WholeStatement := by sorry

/-- P045-T6; p. 305 (PDF p. 17); staged package R/make_exposure_map_AS.R, lines 112–121.
Closed-neighborhood event characterizations justify the corrected extreme-event HT contrast and the
complement-event conditional-mean formula.
Restriction: Retains mathematical event characterizations and all corrected/complement expectation
formulas, including threshold sufficiency. Omits the cited numerical two-unit bias instance, literal
execution of the repaired R code, recomputation of software weights, and outcome-generation or
population-size changes. The general event identity is stated for a genuine finite design with
positive event probability; the population contrast requires a positive population size and positive
probabilities for both extreme events. -/
theorem SAP.P045a.T6 : SAP.P045a.T6Statement := by sorry

/-- P045-T7; p. 303 (PDF p. 15), Figure 16.5 p. 304 (PDF p. 16); staged R/functions.R, lines 36 and 55.
Storage-order copying has the stated triangle-order mismatch from dimension four.
The single-edge witness produces exactly the two asserted nonzero entries, is
asymmetric, changes both exposures, and 32 of the 64 binary upper triangles fail
symmetry. At each deletion probability q in [0,1), the complete output law is
(1-q) at the faulty matrix and q at zero; intended deletion instead has (1-q)
at the original matrix and q at zero. No other outputs occur.
The usual measure-theoretic conditions are assumed; these are finite laws. -/
theorem SAP.P045a.T7 : SAP.P045a.T7WholeStatement := by sorry

/-- P045-T8; p. 303 (PDF p. 15); network of p. 295 (PDF p. 7).
In the printed-network witness every Hajek ratio is defined, yet absolute bias strictly decreases
over zero, one, and two deleted ties.
This refutes a universal monotonic-bias reading of the missing-tie guidance. -/
theorem SAP.P045a.T8 : SAP.P045a.T8Statement := by sorry

/-- P045-T9; p. 303 (PDF p. 15); staged package R/functions.R, lines 36 and 55.
The transposed copy preserves the stated deletion/addition bounds, and missing ties give the stated
HT mixture bias without universal Hajek monotonicity.
Restriction: Retains corrected-copy symmetry, deletion/addition bounds and unchanged-upper recovery,
all four exposure implications, the HT mixture and bias formulas and positive-spillover sign, and
the Hajek zero-deletion bias and zero-to-one-deletion absolute-bias comparison. Omits the explicit
matrix decomposition U+transpose(U)+diag(M), the separate zero-diagonal conclusion,
implementation/output recomputation and simulation-reporting instructions, and any assertion about
probability-approximation bias or approximate centering. -/
theorem SAP.P045a.T9 : SAP.P045a.T9Statement := by sorry

/-- P045-T10; p. 305 (PDF p. 17); staged package R/make_tr_vec_bernoulli.R,
lines 76–82 and 122–128.
On the four-path, use labels 0 through 3, nearest-centre clusters with ties to the smallest
label, and independent fair cluster treatment. The radius-two balls are {0,1,2}, all vertices,
all vertices, and {1,2,3}. Each initial centre has probability 1/4. After initial centre 0,
each retry draw is uniform on all four vertices and each eventual second distinct centre
has conditional probability 1/3; initial centre 3 forces 0, and centres 1 or 2 finish at once.
The coded terminal law is {0,1}:1/12, {0,2}:1/12, {0,3}:1/3, {1}:1/4, {2}:1/4, zero
elsewhere, and normalized; separation fails with probability 1/6. The cluster partitions
{0}|{1,2,3}, {0,1}|{2,3}, and {0,1,2,3} have masses 1/12, 5/12, 1/2 and exhaust the law.
The coded treatment law is 0000:3/8, 1111:3/8, 1100:5/48, 0011:5/48, 1000:1/48,
0111:1/48, zero elsewhere. The repaired terminal law is {0,3}:1/2, {1}:1/4, {2}:1/4,
zero elsewhere; these are exactly the separated covering three-nets. Its treatment law is
0000:3/8, 1111:3/8, 1100:1/8, 0011:1/8, zero elsewhere. All terminal series converge,
and the treatment distributions differ. The usual measure-theoretic conditions are assumed. -/
theorem SAP.P045a.T10 : SAP.P045a.T10WholeStatement := by sorry

/-- P045-T11; p. 305 (PDF p. 17); staged package R/make_tr_vec_bernoulli.R, lines 77 and 123.
Every admissible repaired greedy run has distinct separated centers, strict progress, a length
bound, and a covering completion.
Restriction: Retains the deterministic guarantees for every admissible choice sequence and existence
of a completed run; marked vertices and admissible choices are specified by definition. Omits all of
the uniform-choice four-path instance, namely center-set probabilities and the resulting
cluster-treatment distribution, and actual software replacement/recomputation. -/
theorem SAP.P045a.T11 : SAP.P045a.T11Statement := by sorry

/-- P045-T12; p. 301 (PDF p. 13).
The ten-cycle with exactly two uniformly chosen treated units and exposure outcomes (2,1,1,0)
is the exact counterexample to the printed second equality. Each own-treatment probability
is 1/5; the d11, d10, d01, d00 probabilities are 2/45, 7/45, 1/3, 7/15. All five are
positive and the two treated-exposure probabilities sum to 1/5. Of the 45 assignments,
ten treat adjacent units and give (L,R,H)=(2,9,9); the other 35 give (1,9/7,0), where
L and R are the two printed sides and H is the correct d11 HT mean. Thus L differs from
R on every assignment. The all-treated mean and mu(d11) are 2, and mu(d10)=1.
E[L]=11/9, E[R]=3=mu(d11)+mu(d10), and E[H]=2. The bias of L is 11/9-2=-7/9,
also exactly the negative mean of (pi(d10)/pi)(y(d11)-y(d10)). The usual measure-theoretic
conditions are assumed. -/
theorem SAP.P045a.T12 : SAP.P045a.T12WholeStatement := by sorry

/-- P045-T13; p. 301 (PDF p. 13); lead-in on p. 300 (PDF p. 12).
For any positive finite population, fixed undirected loopless network, correctly specified
first-degree outcomes and design with positive own-treatment probabilities, the two
treated-exposure indicators partition own treatment. The corrected pointwise expansion
uses the common own-treatment denominator. Its expectation is the unitwise mixture of
y(d11) and y(d10), with nonnegative weights pi(d11)/pi and pi(d10)/pi summing to one.
Its bias for mu(d11) is the negative mean of (pi(d10)/pi)(y(d11)-y(d10)). Nonnegative
spillovers give nonpositive bias, strictly negative exactly when some unit has both
pi(d10)>0 and strictly positive spillover; nonpositive spillovers give nonnegative bias.
When both treated-exposure probabilities are positive, the individual d11 HT mean has
expectation mu(d11), and the sum of the d11 and d10 means has expectation mu(d11)+mu(d10).
With no isolated units, the all-treated mean equals mu(d11). Two adjacent independently
fair-treated units with y(d11)=(2,1), y(d10)=(1,2), and untreated outcomes zero give
naive estimates 0,2,1,3 and mean 3/2=mu(d11), despite unequal treated-exposure outcomes
at both units. The usual measure-theoretic conditions are assumed. -/
theorem SAP.P045a.T13 : SAP.P045a.T13WholeStatement := by sorry

/-- P045-T14; p. 312 (PDF p. 24); the estimator is defined on p. 310 (PDF p. 22).
The six-group tract witness separates the pooled estimator from the printed sum and exhibits empty
subclasses.
Restriction: Retains the actual 450-unit witness and its arm means, pooled and printed values and
direct contrasts, the 20-design/8-empty-subclass counts and possible subclass sizes, undefined
printed ratios with a defined pooled ratio, and the general discrepancy identity for positive
counts. Omits the explicit count 12 of the other assignments, the strict-positivity conclusion for
positive numerators, and the equal-subclass-mean doubling assertion. -/
theorem SAP.P045a.T14 : SAP.P045a.T14Statement := by sorry

/-- P045-T15; p. 312 (PDF p. 24); setting on p. 311 (PDF p. 23).
The own-psi groups are the disjoint union of those with psi partners and those with phi
partners, for any finite group population and tract pairing. Counts and sums partition
accordingly. With positive total count, the selected-group mean is the pooled ratio;
with both subclass counts positive, its positive group shares sum to one and give the
weighted mixture of subclass means. An empty first subclass has zero numerator and leaves
the other mean. The scalar pooling identities and the complete normalized 450-unit
two-stage witness are included: the two group direct effects are 7/8 and 3/4, the psi-psi target
is 7/8, expected shares are 2/5 and 3/5, and the mean estimator is 4/5 with bias -3/40.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P045a.T15 : SAP.P045a.T15WholeStatement := by sorry

/-- P045-T16; p. 298 (PDF p. 10); definition on p. 297 (PDF p. 9); network on p. 295 (PDF p. 7).
The printed-network HT contrast remains numerical for an empty exposure cell, and the stated support
restrictions change its expectation.
Restriction: Retains all four probability formulas and positivity, the printed assignment
empty/nonempty-cell and HT calculations, support sizes 20 and 19, and all unconditional and
restricted-support means. Omits separately stated population totals 20 and 10 and true effect 1, the
equivalence between a nonempty d11 cell and adjacency of the treated pair, and identification of the
exceptional adjacent pair {3,9} with an empty d00 cell. The theorem still states that the
unconditional contrast mean is 1. -/
theorem SAP.P045a.T16 : SAP.P045a.T16Statement := by sorry
