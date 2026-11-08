import SAP.P027a.Defs.WholeW2
import SAP.P027a.Defs.WholeW1
import SAP.P027a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P027-T1, Supplement pp. A3–A4 and Table A3 (p. A8), with A from main p. 234: the full eight-unit periodic witness has A=-16, the stated samplewise values and moments, downward bias -1/4 and relative bias -5/36; C2 remains conservative and WR is zero. The same alternating populations at every listed size have A=-N²/q and mean-scale bias -1/q, which do not vanish at fixed q. The cumulative-size uniform-start law and demeaning are included explicitly. The usual measure-theoretic conditions are assumed. -/
theorem SAP.P027a.T1 : SAP.P027a.T1WholeStatement := by sorry

/-- P027-T2, Supplement pp. A3–A4, Section C, and main p. 234: the centered periodic cumulative-size PPS design has q disjoint phases with the stated probabilities, A=-sum(T_g²), and exactly the stated nonpositive design bias and relative-bias bounds. Under mean-zero uncorrelated finite-variance errors the second moments and both ratios of outcome-averaged quantities are as displayed. The printed calibration follows from the empirical size variance; at fixed q and nonzero rho its bias is uniformly separated from zero and tends to -900 rho²/q. Demeaning does not cancel the bias. Ratios have the positive variance guards in the claim. The usual measure-theoretic conditions are assumed. -/
theorem SAP.P027a.T2 : SAP.P027a.T2WholeStatement := by sorry

/-- P027-T3, main p. 237, Section 3.1, with C2 from Section 3.2: the full probability tables, zero-pair lists and before/after estimator values for the two cluster witnesses. Totalling preserves the total and its variance but raises the conservative C2 biases from 8 to 9 and from 9/8 to 49/16, although the ordered zero-pair count falls from four to two. The usual measure-theoretic conditions are assumed. -/
theorem SAP.P027a.T3 : SAP.P027a.T3WholeStatement := by sorry

/-- P027-T4, main p. 237, Section 3.1: for every partition into nonempty almost-sure clusters, totalling preserves the HT total and the uncorrected estimator on every possible sample, and preserves variance and A. In the exponent-2 setting both A-star formulas and the exact ordered-pair-factor-1/2 bias change hold. Constant outcomes, strict increase for unequal linked sizes, the equal-size sufficient condition, the degree bound, the within-group squared-difference identity and both conservativeness formulas are included. The explicit examples reduce C2 bias from 20 to 0 and increase it from 8 to 9. The usual measure-theoretic conditions are assumed. -/
theorem SAP.P027a.T4 : SAP.P027a.T4WholeStatement := by sorry

/-- P027-T5, Supplement Table A3 (p. A8), rows 21, 31, 41 and 51, interpreted
with the aggregation instruction on main p. 237: four rounded table pairs
violate the proposed grouped upper bound, and the 120-unit population has
the displayed original and grouped estimator moments.
Restricted: omits the universal population and finite-collection bounds, the
four stronger numerical lower bounds for relative bias, the individual phase
totals, and the displayed table columns other than true variance, C2 and q.
Retains the scalar 120-unit witness and its mean-scale values using 120^2.
No identification of the reported column with a particular implementation or
with averages of grouped design expectations is asserted. -/
theorem SAP.P027a.T5 : SAP.P027a.T5Statement := by sorry

/-- P027-T6, correction to Supplement Section C, pp. A3–A4 and Table A3 (p. A8):
the original-unit and totalled periodic estimators have the displayed finite
correction formulas, comparison, bounds and outcome-averaged ratio.
Restricted: states the finite phase law, without a continuous uniform-start
identification. Adds integrability of the model variance, grouped expected
estimator and every squared group total. Omits separate assertions for the
expectation of the unit-level correction and A-star, the expectation of the
grouped correction, E_y(S)=qL and V's expression in terms of E_y(S), explicit
mean-scale identities, separate grouped HT total/uncorrected-estimator and
variance-preservation identities, and the original eight-unit representation of the
realized-ratio example (its grouped totals are retained). No assertion about
which implementation produced the table or figure is made. -/
theorem SAP.P027a.T6 : SAP.P027a.T6Statement := by sorry

/-- P027-T10, Supplement p. A3, Section C and Table A2: the full positive-size witness (1,3,...) has the specified cumulative-size uniform-start law, marginal and joint probabilities, 48 ordered zero pairs, samplewise estimates, total/mean moments and downward bias. Its sizes have positive probability under the normalized offset negative-binomial generator and obey the PPS feasibility inequality; its outcomes have the additive residual representation for every beta. The entire stated open box has negative A, while C2 remains conservative. The usual measure-theoretic conditions are assumed.
This witness refutes the inference from x_k >= 1 and the noisy model
y_k = beta*x_k + epsilon_k to conservativity for every realized finite
population. It does not refute the literal assertion for outcomes
proportional to the positive size vector. -/
theorem SAP.P027a.T10 : SAP.P027a.T10WholeStatement := by sorry

/-- P027-T11, correction to Supplement Section C, p. A3: conditional on the
positive size vector, mean-zero errors with finite second moments and zero
cross moments give E[y_k y_l] = beta^2 x_k x_l for distinct units, E[A] =
beta^2 sum_Z x_k x_l >= 0, and average mean-scale sampling bias E[A]/N^2 >= 0.
The eight-unit coefficient is 176 (396 at beta = 3/2), whereas the displayed
fixed outcome vector has A = -16 and mean-scale bias -1/4. For each fixed
population conservativity is equivalent to A >= 0; outcomes all of one sign
suffice. Thus the average guarantee supplies no guarantee for every realized
population. The usual measure-theoretic conditions are assumed; the nonzero
population size is presupposed by the population mean. -/
theorem SAP.P027a.T11 : SAP.P027a.T11WholeStatement := by sorry

/-- P027-T12, witness concerning Supplement Section C, p. A3 and Table A2:
the positive-probability offset-negative-binomial size vector gives a printed
inclusion probability exceeding one, and each of the six configurations has
such a positive-probability witness. -/
theorem SAP.P027a.T12 : SAP.P027a.T12Statement := by sorry

/-- P027-T13, correction to the PPS display in Supplement Section C, p. A3:
for N >= 2, positive sizes and 0 < m < N, the printed probabilities require
m max(x) <= sum(x). The cap-sum map is continuous, nondecreasing, starts at
zero and eventually equals N; a positive cap multiplier gives sum m. Under
feasibility, m/sum(x) retains the printed formula. Ordered intervals with
these probabilities and a uniform start in [0,1) give exactly m distinct
units, the prescribed marginals and the intersection-measure joint probabilities.
For sizes (30,1,1,1,1,1,1,1), m = 2, redistribution gives (1,1/7,...,1/7):
the same continuous design draws each {1,j} with probability 1/7, with the
stated joints, whereas naive capping sums to 51/37 != 2. The formula-preserving
recipe independently redraws full offset-NB vectors until feasibility;
acceptance has positive probability, termination is almost sure and the output
law is the original law restricted to feasibility and normalized. The alternative
retains the original size law and uses the capped ordered design and its joints.
The usual measure-theoretic conditions are assumed. No assertion about which
recipe generated the unavailable simulation runs is made. -/
theorem SAP.P027a.T13 : SAP.P027a.T13WholeStatement := by sorry
