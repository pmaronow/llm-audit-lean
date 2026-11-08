import SAP.P042.Defs
import SAP.P042.Defs.WholeW1
import SAP.P042.Defs.WholeW2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P042-T1; pooling on p. 31 (PDF p. 7), intervals on pp. 31–33, shared control on p. 36.
The two constructed sharp-null shared-control witnesses have true pooled variance
three halves of the precision calculation's diagonal variance. The six-voter witness
has the stated 90 allocations and exact moments. The independent binomial-arm witness
has all stated moments, weights, exact coverage sums, reduced fraction, and strict
coverage bounds. Its coverage thresholds are 19 and 24 both for 1.96 and for the actual
standard normal 0.975 quantile, indeed for every multiplier in [1.9599, 1.96].
The usual measure-theoretic conditions are assumed; these finite laws satisfy them.
These are constructed witnesses, with no assertion about historical interval coverage. -/
theorem SAP.P042.T1 : SAP.P042.T1WholeStatement := by sorry

/-- P042-T2; pooling method and mail comparison on p. 31, shared control on p. 36.
Fixed-coefficient pooling has the stated mean, full covariance variance, precision-weight
identities, shared-control formulas, bounds, signed-pool comparison and randomization covariance.
Restriction: Retains the general mathematical content (i)–(viii) and the variance-based
half-width identities. Omits application to the actual historical contrasts and pools,
estimation of their covariance matrices, numerical pool and mail-comparison recalculations,
the staged-size recalculation, block/overlap-specific numerical bounds, relabeling the
printed inference, and the requested rejection of the old GGL-only covariance certification. -/
theorem SAP.P042.T2 : SAP.P042.T2Statement := by sorry

/-- P042-T3; Note 5 on p. 40 (PDF p. 16), with the declared pooling method on p. 31.
On the two stipulated deposited recorded-call inputs, all displayed exact fixed-effects
and DerSimonian–Laird calculations hold. The fixed-effects estimate and interval do not
round to Note 5's figures, whereas the DerSimonian–Laird ones do. The endpoint statements
hold throughout [1.9599, 1.96] and at the actual standard normal 0.975 quantile. The stated
square-root-free comparisons and endpoint-check monotonicity hold as well.
The usual measure-theoretic conditions are assumed. The inputs are stipulated exact
rationals; agreement with a calculation makes no assertion about historical intent. -/
theorem SAP.P042.T3 : SAP.P042.T3WholeStatement := by sorry

/-- P042-T4; Note 5 on p. 40, corrected using the pooling method on p. 31.
The fixed-effects calculation rounds to 1.866 and (0.963, 2.768), stays above zero,
and has variance 1/W under the stipulated zero covariance; the alternative method reproduces Note 5.
Restriction: Omits the assertion that the standard normal 0.975 quantile belongs to
[1.9599, 1.96]; endpoints use that explicit multiplier range. Omits implementation of the
replacement sentence, replication-program analysis command and alternative method disclosure. -/
theorem SAP.P042.T4 : SAP.P042.T4Statement := by sorry

/-- P042-T5; pooling and mail comparison on p. 31, nine pooled intervals on pp. 31–33.
The audit's unconditional diagonal-variance readings for a pooled mean and a difference of pools fail.
Restriction: Retains only the negations of the two audit-supplied variance formulas.
Omits reproduction or rejection of all nine historical point estimates, treatment counts
and intervals, the mail-type significance assertion, and the qualitative assertions about
study size, common outcome scales and treatment similarity. This refutes those variance
readings, without declaring the printed empirical claims false. -/
theorem SAP.P042.T5 : SAP.P042.T5Statement := by sorry

/-- P042-T6; p. 30 (PDF p. 6), Note 2 on pp. 39–40 (PDF pp. 15–16),
and contact/CACE and the Michelson illustration on p. 32 (PDF p. 8).
Random assignment independent of subjects' potential outcomes balances the
two arms in expectation. Uniform complete randomization gives the finite
potential-outcome mean identities and an unbiased observed assignment contrast;
a uniformly sampled subject's treatment is independent of their fixed attributes.
Under one-sided contact, exclusion and no interference, ITT equals Complier
share times CACE, the expected treated contact fraction is that positive share,
and the ratio of the expected turnout contrast to the expected contact fraction
equals CACE. The same population identities hold on arbitrary probability spaces
under independent assignment. The realized estimator is the turnout contrast
divided by its positive realized contact fraction. Never-taker effects are not
identified, even with binary turnout. The illustration is (9.4 - 7.0)/0.50 = 4.8
percentage points. The usual measure-theoretic conditions are assumed.
No unbiasedness or consistency of the realized ratio is asserted. -/
theorem SAP.P042.T6 : SAP.P042.T6WholeStatement_W2 := by sorry
