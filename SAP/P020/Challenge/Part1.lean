import SAP.P020.Defs
import SAP.P020.Defs.WholeW1
import SAP.P020.Defs.WholeW2
import SAP.P020.Defs.WholeW3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P020-T1; p. 40 (PDF p. 2); p. 42 (PDF p. 4).
The explicit three-cluster population has persistent bias and probability-one error, yet its difference in means beats HT and every fixed-coefficient Des Raj estimator at every positive within-cluster replication. -/
theorem SAP.P020.T1 : SAP.P020.T1Statement := by sorry

/-- P020-T2; p. 40 (PDF p. 2); p. 42 (PDF p. 4).
Finite-law MSE decomposes into variance and squared bias, nonzero limiting bias implies eventual inferiority to a vanishing-MSE comparator, and a Markov bound gives consistency from vanishing MSE, with a counterexample when the comparator condition is dropped. -/
theorem SAP.P020.T2 : SAP.P020.T2Statement := by sorry

/-- P020-T3; p. 61 (PDF p. 23); definition of n_j on p. 44 (PDF p. 6).
The printed logistic link is strictly increasing, and the raw-count treatment
shift 2/5 - (9/10)n is at most -1/2 for every real n at least one. Consequently
every individual probability contrast and every finite nonempty average contrast
is negative, excluding the reported 7/1000, for arbitrary real control predictors
and sizes at least one. The scalar instance N = 1, n = 1, control predictor zero
has control probability 1/2 and treated probability L(-1/2) < 1/2.
The usual measure-theoretic conditions are assumed; the displayed quantities are
finite real expressions. The scalar instance specifies no randomized cluster
design. -/
theorem SAP.P020.T3 : SAP.P020.T3WholeStatement_W2 := by sorry

/-- P020-T4; p. 61 (PDF p. 23).
Conditionally replacing cluster size by its value in thousands gives the equivalent raw-count slopes and the stated real, integer, probability and average sign thresholds. -/
theorem SAP.P020.T4 : SAP.P020.T4Statement := by sorry

/-- P020-T5; Appendix B, pp. 70-71 (PDF pp. 32-33); pp. 57-58 (PDF pp. 19-20).
For every coefficient estimated from the same experiment, both complete arm-total
expectation calculations (29)-(30) hold, and the corrected ATE expectation is Delta
plus M/N times (control covariance minus treatment covariance), while the bias
equals that covariance correction. -/
theorem SAP.P020.T5 : SAP.P020.T5WholeStatement := by sorry

/-- P020-T6; p. 71 (PDF p. 33).
The explicit nondegenerate OLS witness has mean one eighth instead of one half and bias minus three eighths, with the assignment values and both covariances in the corrected formula. -/
theorem SAP.P020.T6 : SAP.P020.T6Statement := by sorry

/-- P020-T7; pp. 55-56 (PDF pp. 17-18); transformation defined on p. 49 (PDF p. 11).
Individual affine transformation and the matching coefficient transformation give both potential-total identities and all nondefinitional equalities of the corrected Des Raj chain. -/
theorem SAP.P020.T7 : SAP.P020.T7Statement := by sorry

/-- P020-T8; pp. 71-72 (PDF pp. 33-34).
Centered differencing preserves means, gives both arm variance expansions, and satisfies every line of the corrected covariance expansion. -/
theorem SAP.P020.T8 : SAP.P020.T8Statement := by sorry

/-- P020-T9; p. 56 (PDF p. 18); p. 72 (PDF p. 34).
Two admissible populations refute the printed control subscript and expectation bracket, with the bracket expression evaluated at both clusters. -/
theorem SAP.P020.T9 : SAP.P020.T9Statement := by sorry

/-- P020-T10; pp. 51-52 (PDF pp. 13-14).
The individual sharp null identifies observations with both potentials, gives all corrected total moment identities, and makes actual HT variance equal to its exact observed-total formula. -/
theorem SAP.P020.T10 : SAP.P020.T10Statement := by sorry

/-- P020-T11; pp. 44-45 (PDF pp. 6-7).
For every finite-support probability law with denominator positive on its support, the ratio identity holds, and complete cluster randomization gives the exact difference-in-means expectation and bias.
Restriction: Equation (7), canonical clause (a), is stated only for finite-support probability laws with nonnegative real weights summing to one and denominator positive on the support; its general probability-law assertion, including infinite-support or continuous laws with the required expectations and covariance, is omitted. The complete-cluster-randomization expectation and bias formulas in clause (b), equation (8), are retained in full. -/
theorem SAP.P020.T11 : SAP.P020.T11Statement := by sorry

/-- P020-T12; pp. 48-49 (PDF pp. 10-11); Appendix A, p. 70 (PDF p. 32).
HT estimates both potential totals and the ATE without bias, obeys the affine shift identity, and fails location invariance in the stated nonzero-shift cases; an admissible counterexample exists. -/
theorem SAP.P020.T12 : SAP.P020.T12Statement := by sorry

/-- P020-T13; p. 54 (PDF p. 16), equations (20)-(22) and the following display;
pp. 58-59 (PDF pp. 20-21), Section 5.4.
Under complete random allocation of fixed positive numbers of clusters to both
arms, the Des Raj estimators with any fixed common size coefficient, and with
any finite collection of fixed covariates and coefficients, unbiasedly estimate
both potential-outcome totals and their difference divided by the population
size. Equation (22) averages the selected cluster or arm mean: the fixed
coefficient factors out of expectation, the centered arm mean has expectation
zero, and so does its fixed multiple. The combined size and covariate arm-mean
adjustment also has expectation zero. Both adjusted arm-total estimators have
the same expectations as HT. Covariate totals and all coefficients are fixed
before analysis; zero covariates and zero size or covariate variance are allowed.
The usual measure-theoretic conditions are assumed; here all expectations are
finite design sums. -/
theorem SAP.P020.T13 : SAP.P020.T13WholeStatement_W3 := by sorry

/-- P020-T14; pp. 56-57 (PDF pp. 18-19); Appendix C, pp. 71-73 (PDF pp. 33-35).
The differenced means, explicit variance expansions, first and second derivatives,
and scaled design-variance quadratic hold. When the size variance is nonzero,
the arm and common coefficients are unique stationary minima, all first-order
rearrangements and coefficient formulas hold, and every efficiency inequality is
equivalent to the stated sign intervals. Equal cluster sizes give HT for every k. -/
theorem SAP.P020.T14 : SAP.P020.T14WholeStatement := by sorry

/-- P020-T15; pp. 50-51 (PDF pp. 12-13); p. 53 (PDF p. 15); p. 55 (PDF p. 17).
The exact HT variance components and upper bound, two-clusters-per-arm conservative estimators for HT and fixed-coefficient Des Raj, and independent-block unbiasedness, variance and conservative estimation formulas all hold. -/
theorem SAP.P020.T15 : SAP.P020.T15Statement := by sorry

/-- P020-T16; p. 52 (PDF p. 14); explicit form on p. 52 and, for the Des Raj estimator, p. 55 (PDF p. 17).
The sharp-null variance estimator is conservative in expectation when cluster-total effects are constant or arm cluster counts are balanced. -/
theorem SAP.P020.T16 : SAP.P020.T16Statement := by sorry

/-- P020-T17; pp. 45-47 (PDF pp. 7-9); Figure 1 on p. 46 (PDF p. 8).
Consistency means convergence in probability along populations whose total and
both realized arm counts strictly increase. Independent exact copies have a
common path realization with the stipulated uniform prefix laws, all growth
certificates, all four weak laws, positive denominators and pooled consistency.
Within-cluster replication with a common draw has the same strict growth but
preserves the target, estimates, law and bias; nonzero bias implies inconsistency.
The sizes (1,2,4), control totals (0,1,1), treatment totals (0,0,0) give N_h=7h,
ATE=-2/7, bias=-1/315 and error probability one at tolerance 1/25 for every h. -/
theorem SAP.P020.T17 : SAP.P020.T17WholeStatement := by sorry
