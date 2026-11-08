import SAP.P004c.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P004c

/-- P004-T31; pp. 754, 756 and 761, eqs. (16), (18), (19), (21)-(22),
footnotes 14-15 and 22. The corrected count identities hold for every assignment;
with both arms nonempty the OLS fit is unique, the two sandwich formulas agree,
and eigenvalue truncation gives the stated semidefinite ordering and treatment-entry
bound; the sharp null indexes outcomes by x. -/
theorem SAP.P004c.T31.{u} : T31Statement.{u} := by sorry

/-- P004-T32; Supplement A pp. 2-3, Lemma A.2 and its corrected proof displays.
The HT variance has the exact local expansion, the corrected component and total
bounds, and order 1/N under the stated boundedness and neighborhood conditions. -/
theorem SAP.P004c.T32.{u} : T32Statement.{u} := by sorry

/-- P004-T33; Supplement A pp. 5-6, Lemma A.4 and A.3.1.
The corrected linearized Hajek variance has the stated expansion and homophily
identity, its second-moment bound holds exactly when C5 holds, and the corrected
positive-variance HT summands have the stated sum, zero means and unit sum variance. -/
theorem SAP.P004c.T33 : T33Statement := by sorry

/-- P004-T34; Supplement A p. 36, eqs. (127)-(129), and p. 35, eq. (124).
The corrected absolute-value identities, finite kernel cross-sum bound and Bernoulli
denominator order hold, together with the scalar witness arithmetic.
Restricted: omit the composed bandwidth conclusion O_p(N^(-1/2)b_N^2)=o_p(1)
and the realization of the eight-node assignment, residuals and kernel (including
the certified value S=-1/4); only its scalar arithmetic is retained. Require positive
sample size and bandwidth for the finite kernel bound, and use zero denominator
error on empty treated arms, so no reciprocal of a zero count is asserted there. -/
theorem SAP.P004c.T34 : T34Statement := by sorry

/-- P004-T39; p. 754, Proposition 1, eq. (14).
For positive sample size and an interior common Bernoulli probability, the HT
estimator is unbiased for the AME defined by forced-coordinate marginalization,
without a restriction on interference. -/
theorem SAP.P004c.T39 : T39Statement := by sorry

/-- P004-T40; pp. 756-757, eqs. (23)-(25).
For additive potential outcomes and genuine spatial averages, every marginal design
law gives the point effect g_i(x), its spatial average as the node effect, and their
node mean as the AME, independently of the assignment law. -/
theorem SAP.P004c.T40.{u} : T40Statement.{u} := by sorry

/-- P004-T41; p. 754, Proposition 2, eq. (15), and Supplement A Lemma A.2.
Under C1-C4 the HT variance is O(1/N), and under the eventual positive N-times-variance
lower bound its AME-centred, actual-variance-standardized statistic tends to N(0,1). -/
theorem SAP.P004c.T41.{u} : T41Statement.{u} := by sorry

/-- P004-T42; p. 754, Proposition 3, eq. (17), and Supplement A pp. 4-6.
Under C1-C4 and the eventual positive N-times-AVar lower bound, the Hajek statistic
centred at the AME and standardized by the variance of the corrected linearization
tends to N(0,1), with zero means assigned to empty arms. -/
theorem SAP.P004c.T42.{u} : T42Statement.{u} := by sorry

/-- P004-T44; Supplement A pp. 28-29, Lemma C.4 and Proposition 5, eq. (80).
The HT estimator is unbiased with variance O(1/N), the root-N linearization error
vanishes in probability, and the nondegenerate Hajek statistic tends to N(0,1).
Restricted: replace the printed radiuswise-eventual C_b*s^2 spacing condition by
C_b*(1+s^2), with one eventual sample-size threshold valid for all radii at once;
the weaker radiuswise condition is not claimed to suffice. Finite unbiasedness is
asserted for positive sample sizes with genuine spatial averages. The eventual
regularity and the metric node-distance premise are explicit. No headline conclusion
is dropped under these premises. -/
theorem SAP.P004c.T44.{u} : T44Statement.{u} := by sorry
