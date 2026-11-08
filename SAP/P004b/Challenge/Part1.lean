import SAP.P004b.Defs
import SAP.P004b.Defs.WholeW1
import SAP.P004b.Defs.WholeW2
import SAP.P004b.Defs.WholeW3

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

/-- P004-T16; p. 752 (PDF p. 9), paragraph 'For an interpretable sufficient condition ...';
p. 753 (PDF p. 10), polygon-intervention spacing sentence; footnote 25, p. 763.
The zero-radius rectangle witness, every prescribed separation L>5, and the positive-radius
two-atom witness refute the range-only cutoff, with exact distances, averages, interference
indicators and covariance. Disjoint area-one thin polygons have the stated exact squared
distances and an unbounded radius-two neighborhood count, refuting area-only spacing.
-/
theorem SAP.P004b.T16 : SAP.P004b.T16WholeStatement := by sorry

/-- P004-T17; p. 752 (PDF p. 9), paragraph 'For an interpretable sufficient condition ...'; p. 753 (PDF p. 10), sentence on polygon-intervention experiments after C4; footnote 25, p. 763.
A diameter bound gives the corrected local-interference cutoff and, with positive polygon area and disjoint interiors, the stated neighborhood count bound, while the two missing-bound counterexamples remain available.
-/
theorem SAP.P004b.T17 : SAP.P004b.T17Statement.{u} := by sorry

/-- P004-T18; Supplement A p. 4 (Lemma A.3), p. 5 (Lemma A.4), and eq. (27), p. 11.
Under C1-C4 the corrected displayed Hajek linearization has root-N negligible error and
O_p(N^-1) remainder, with zero as each empty arm's mean. It equals the augmented class
member. The balanced fixed-outcome witness at p=1/4 has the exact printed-minus-corrected
formula and scaled variance 4/3, and the printed expansion fails even along even sample
sizes. The printed and corrected linearizations coincide at p=1/2.
-/
theorem SAP.P004b.T18 : SAP.P004b.T18WholeStatement := by sorry

/-- P004-T19; Supplement A p. 6 (Lemma A.5).
Both exact bounded dependency-neighborhood counterexamples satisfy the printed hypotheses
and fail the normal limit. The first has one fair sign and zero remaining variables; the
second has one unpaired fair sign and cancelling independent sign pairs, with every
marginal variance one and closed neighborhoods of size at most two. Their sums and
standardized sums are exactly the unpaired fair sign.
-/
theorem SAP.P004b.T19 : SAP.P004b.T19WholeStatement := by sorry

/-- P004-T20; Supplement A p. 6 (Lemma A.5), and its use in Propositions 2 and 3.
Uniformly bounded centered arrays with bounded-degree dependency graphs and a linear
sum-variance lower bound satisfy the corrected normal limit. The unit-sum-variance
normalization also holds. The specified HT and linearized Hajek contrasts have their
exact centered identities, bounds 2b/min(p,1-p) and 4b/min(p,1-p), the shared-source
dependency graph of eventually bounded degree, and the two variance-conditional CLTs.
-/
theorem SAP.P004b.T20 : SAP.P004b.T20WholeStatement := by sorry

/-- P004-T21; Supplement A pp. 9-10 (A.4.2, Proposition 2 and its first proof identity);
eq. (24), p. 9, and article eq. (20), p. 755 (PDF p. 12).
The corrected node variance equals both the expanded squares-of-first-means expression
and its compact residual-mean-difference form. The corrected finite SAH bound holds,
including its spatial C3 specialization. The two explicit two-node schedules give
variance 1/6 versus printed bound zero (corrected bound 2/3), and node variance 3/4
versus printed expression 15/16. The excluded feasible-estimator consistency claim is
not asserted.
-/
theorem SAP.P004b.T21 : SAP.P004b.T21WholeStatement := by sorry

/-- P004-T22; Supplement A pp. 15–16, equations (37)–(40) and the bound under C 2.
The corrected five-term variance formula has both pair signs and the neighbour's own fit.
Its third and fifth terms form the full negative residual-effect quadratic, yielding the
corrected homophily bound. This includes the population projection-fit linear estimator
and the three-node witness: true and corrected variance 2/9, printed sum 4/9.
-/
theorem SAP.P004b.T22 : SAP.P004b.T22WholeStatement := by sorry

/-- P004-T23; Supplement A pp. 14–16, C 2, observational HAC, and Proposition 4(i)–(ii).
The corrected homophily uses O_j at the neighbour, and the residual uses its own fitted
propensity. The actual inverse-Gram treatment row yields the scalar treatment sandwich
entry and the inverse-propensity residual quadratic. The numerator is the fitted IPW
estimator. Genuine normal quantiles have opposite signs and give all three equivalent
event presentations, for both SAH and HAC. These are exact identities, without a coverage claim.
-/
theorem SAP.P004b.T23 : SAP.P004b.T23WholeStatement := by sorry

/-- P004-T24; Supplement A p. 17, Appendix A.7 and equations (44)–(45).
The corrected leverage and residual-maker matrices satisfy all projection, treatment-row,
norm, reciprocal normalization and sandwich identities. The uniform kernel gives the
stated residual quadratic. The trace adjustment uses degrees of freedom 2 mu²/nu on its
domain nu ≠ 0. Each printed defective product has compatible dimensions exactly when N=2.
-/
theorem SAP.P004b.T24 : SAP.P004b.T24WholeStatement := by sorry

/-- P004-T25; Supplement A p. 26, the summands preceding Lemma C.2 and equation (57).
Subtracting tau_i/N gives mean zero, the exact augmented-estimator sum and its HT
specialization. Conditioning on a ball containing the own coin gives corrected (57).
The printed summand has mean (1/N-1)tau_i; the eight-node example gives -7/8 instead
of zero. The own-coin affine transformation also preserves uniform L2-NED of size -4.
-/
theorem SAP.P004b.T25 : SAP.P004b.T25WholeStatement := by sorry

/-- P004-T26; Supplement A pp. 34–35, Lemma C.10, equation (122) and Remark 1.
The exterior-tail envelope, bounded outcomes, quadratic spacing and kernel conditions
give convergence of the centered-effect kernel form to zero, liminf zero and C 6.
The explicit radius b_N^(1/6) diverges and its cube divided by b_N tends to zero.
The printed inside-ball premise also implies the conclusion, bounds the diagonal
heterogeneity and the kernel form, and forces eventual exact homogeneity for fixed phi.
Effects use S3 marginalization, including Bernoulli endpoints; regularity is only eventual.
-/
theorem SAP.P004b.T26 : SAP.P004b.T26WholeStatement := by sorry

/-- P004-T27; Supplement A p. 35 (Proposition 6(v)); compare Proposition 5,
p. 29; assumptions on pp. 26, 27, 32, 34.
Under the reading of Proposition 6(v) with uniform spacing bound C_b(1+s^2),
the sparse Bernoulli witness is a counterexample to its coverage assertion:
it satisfies the NED, kernel, bandwidth and homophily assumptions, but its valid
Wald intervals have coverage tending to one half, both at nominal 95 percent
and with critical values plus/minus two.
The statement includes the all-distance NED assertion, exact variance,
conditional binomial count law, exceptional probability, estimator and
studentized formulas, conditional limits, and the variance rates and bias.
-/
theorem SAP.P004b.T27 : SAP.P004b.T27WholeStatement := by sorry

/-- P004-T28; Supplement A p. 35 (Proposition 6); proof pp. 35--39.
Under the corrected uniform quadratic spacing condition and the stated NED,
kernel, bandwidth and homophily assumptions, the independent five-term V1 is
the random row sum, all three raw scaled approximation errors vanish in
probability, and the asymptotic bias is nonnegative. With the claimed variance
lower bound, defined Wald intervals have conservative liminf coverage for
every alpha in (0,1). Gaussian quantile existence is a conclusion.
-/
theorem SAP.P004b.T28 : SAP.P004b.T28WholeStatement := by sorry

/-- P004-T29; Supplement A p. 33 (Lemma C.9(iii)); p. 34 (eqs. (114)-(121)); pp. 36-37 (eqs. (130)-(136)); pp. 37-38 (eqs. (144)-(148) and footnote 22).
The exported far-pair covariance bound and corrected HAC and epsilon identities hold under their stated regularity conditions.
Restriction: The far-pair covariance bound is asserted only under the exported stronger uniform quadratic spacing, metric distances, well-defined averages at every sample size, and bandwidth at least one at every sample size. Retains the corrected five-term HAC expansion, cross-arm epsilon-product prefactors, and corrected epsilon means and N^-2 mean-product scale. Omits the equality between the independent five-term V1 formula and the random row sum, a separate V2 definition clause, and both numerical checks of the misprinted displays. The far-pair covariance bound is specialized to the deterministic population arm centers (barMu true, barMu false) at each sample size; the bound for arbitrary bounded deterministic centers is not asserted.
-/
theorem SAP.P004b.T29 : SAP.P004b.T29Statement.{u} := by sorry

/-- P004-T30; p. 751 (PDF p. 8), end of Section 3; Supplement A p. 13,
eq. (33), with eq. (32) on p. 12.
Complete randomization gives uniform conditional remainder laws with N1-1
and N1 treated nodes, positive conditioning events, and disjoint supports.
Under Bernoulli assignment the two remainder laws coincide. The corrected
arm centers give the explicit linearized Hajek estimator and the same variance;
the wrong equal-center fit agrees identically exactly when the centers agree.
The approximation in (33) has the exact nonnegative quadratic remainder in
the interaction correction Delta, with the constant independent of both fits.
-/
theorem SAP.P004b.T30 : SAP.P004b.T30WholeStatement := by sorry

