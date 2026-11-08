import SAP.P022.Defs.WholeW1
import SAP.P022.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P022 Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

/-- The printed claim is false: P022-T1; p. 860 (PDF p. 11), proof on pp. 860–861.
The fixed negative-reciprocal witness satisfies conditions 1–4 but has population and
sample CDF error one, certain tails, and a persistent error at the required partition
knot zero. The bounded perturbed four-corner witness satisfies conditions 1–4 with a
nonsingular limit and has CDF error at least one half and certain tails. Thus both
conclusions of printed Lemma 2 fail, even with a nonsingular limiting law.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P022.T1 : SAP.P022.T1WholeStatement := by sorry

/-- P022-T2; p. 860 (PDF p. 11); proof on pp. 860–861 (PDF pp. 11–12).
Convergence of left limits at atoms gives uniform CDF convergence and both scaled tail bounds with the explicit universal integer function. -/
theorem SAP.P022.T2 : T2Statement := by sorry

/-- P022-T3; pp. 867–869 (PDF pp. 18–20); statement of Proposition 2 on p. 863 (PDF p. 14).
Bounded outcomes give the stated finite second moments, both deterministic endpoint errors, finite tail bounds, and the allocation-only asymptotic bound. -/
theorem SAP.P022.T3 : T3Statement := by sorry

/-- P022-T4; p. 861 (PDF p. 12).
Both sampled CDFs are unbiased, have the corrected Bernoulli-factor variances, and satisfy the quarter-factor upper bounds. -/
theorem SAP.P022.T4 : T4Statement := by sorry

/-- The printed claim is false: P022-T5; p. 861 (PDF p. 12).
The four-unit constant-one example refutes equation (11), and equality in its quarter-factor bound holds exactly when the population CDF is one half. -/
theorem SAP.P022.T5 : T5Statement := by sorry

/-- P022-T6; pp. 865 and 867–868 (PDF pp. 16 and 18–19), Proposition 2 on p. 863.
The corrected upper seven-term budget uses sum nu=epsilon1/2 and last tolerance
epsilon1/2, and is centered at the sharp upper bound. The finite decomposition,
event inclusion, union bound and last-term CDF bound hold. Conditional on the
Lemma 2 conclusions, universal positive nonincreasing integer functions give the
corrected last-term limit; conditional also on (17)–(22), the concluding bounds
hold. The cubic-root allocation attains their minimum and gives a positive rate
function independent of the sequence. The lower endpoint retains sum nu=epsilon1
and last tolerance epsilon2+epsilon3, with its decomposition, finite budget and
conditional limits. The reciprocal thresholds require C>0; at C=0 both last
integrals vanish. The usual measure-theoretic conditions are assumed. -/
theorem SAP.P022.T6 : SAP.P022.T6WholeStatement := by sorry

/-- The printed claim is false: P022-T7; p. 868 (PDF p. 19), Proposition 2 on p. 863.
The nested four-corner population satisfies the stated assumptions. The admissible
split (1,1,1) makes (23) a probability-one event. On N=4r the exact moments give a
scaled centering gap tending to one half; the centered error has the stated
51200/(N delta^2) tail bound. The wrongly centered absolute error tends to one half
in probability, its small-threshold probabilities tend to one, and their N-scaled
values diverge, refuting both finite printed bounds. The usual measure-theoretic
conditions are assumed. -/
theorem SAP.P022.T7 : SAP.P022.T7WholeStatement := by sorry

/-- P022-T8; p. 869 (PDF p. 20); equations (8)–(9) on p. 854 (PDF p. 5).
Using the original partition widths and midpoint quantile selections returns the sharp covariance and variance estimates, with the stated rank and overlap-weight identities. -/
theorem SAP.P022.T8 : T8Statement := by sorry

/-- The printed claim is false: P022-T9; Appendix B, p. 869 (PDF p. 20), (8)–(9) on p. 854.
In real arithmetic the all-ones four-unit example has constant observed samples,
zero effect, variance and sharp estimates, but the printed routine returns the
negative value -1/50331648. Its shifted weights sum to 1-2e. Under the stated
cell-width condition both endpoint discrepancies and the exact translation defect
hold, while the mathematical sharp estimates are translation invariant.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P022.T9 : SAP.P022.T9WholeStatement := by sorry

/-- P022-T10; p. 850 (PDF p. 1); p. 852 (PDF p. 3); Appendix B, p. 869 (PDF p. 20).
Fixed observed samples give the independent-means estimator limit, and bounded marginal variances with eventual fixed arm sizes give the corresponding actual-variance approximation.
Restriction: Retains the fixed-observed-sample identity and limit, and the actual-variance limit under uniformly bounded marginal variances and eventual fixed arm sizes. Drops the exact finite-N remainder identity for actual randomization variance, the (0,1) sample formulas and numerical examples, and any assertion about execution of the R branch. -/
theorem SAP.P022.T10 : T10Statement := by sorry

/-- P022-T11; p. 857 (PDF p. 8).
Closed rounding bins and a common positive Wald multiplier imply the endpoint-only upper bound, the combined six-percent bounds, and the exact displayed-input percentage. -/
theorem SAP.P022.T11 : T11Statement := by sorry

/-- P022-T12; p. 858 (PDF p. 9); Table 1 on p. 857 (PDF p. 8).
Neyman’s upper estimator has nonpositive sharp-null bias, and the finite Wald-width and rounded-number calculations establish the corrected incompatibility statement. -/
theorem SAP.P022.T12.{u} : T12Statement.{u} := by sorry

/-- P022-T13; p. 853 (PDF p. 4); equation (2) on p. 851 (PDF p. 2); proof of Lemma 1 on pp. 859–860 (PDF pp. 10–11).
Difference in means is unbiased with the printed variance, and the covariance and variance endpoints bound and attain all compatible finite rearrangements and probability couplings. -/
theorem SAP.P022.T13 : T13Statement := by sorry

/-- P022-T14; p. 854 (PDF p. 5); (4) and (6) on pp. 852–853 (PDF pp. 3–4); Introduction, p. 850 (PDF p. 1).
When the full population is sampled, every assignment obeys the five-estimator ordering from Neyman’s lower estimate through the conventional upper estimate. -/
theorem SAP.P022.T14 : T14Statement := by sorry

/-- P022-T15; p. 855 (PDF p. 6); proof on pp. 862–863 (PDF pp. 13–14).
Conditions 1–4 give second moments for all compatible laws, both sharp population limits, and joint bound-estimator consistency at scale one over population size. -/
theorem SAP.P022.T15 : T15Statement := by sorry

/-- P022-T16; p. 863 (PDF p. 14); Remark 3 on p. 856 (PDF p. 7); proof on pp. 863–869 (PDF pp. 14–20).
Bounded outcomes give both stated scaled tail limit-superior bounds uniformly over admissible sequences with the same limiting law and allocation parameters. -/
theorem SAP.P022.T16 : T16Statement := by sorry

/-- P022-T17; Corollary 1, p. 856 (PDF p. 7), Remark 4, p. 857 (PDF p. 8).
Conditions 1–3, uniformly bounded third moments and a nonsingular limiting law
give the actual and upper variance limits, gamma in (0,1], the studentized normal
limit, and the stated Wald coverage limit at least nominal. No positivity of
every finite estimate is assumed; division is totalized on exceptional rows.
The sharp upper variance is the least leading variance input assuring nominal
Wald coverage uniformly over admissible joint laws with the given marginals.
Every smaller nonnegative input is defeated by a nonsingular compatible law and
a nested fixed-outcome population realizing it. The usual measure-theoretic
conditions are assumed, and existence of the moments and extrema is concluded. -/
theorem SAP.P022.T17 : SAP.P022.T17WholeStatement := by sorry

/-- The printed claim is false: P022-T18; p. 860 (PDF p. 11); proof on pp. 860–861 (PDF pp. 11–12).
There exists a sequence satisfying conditions 1–3 for which the joint conclusion of printed Lemma 2 fails. -/
theorem SAP.P022.T18 : T18Statement := by sorry
