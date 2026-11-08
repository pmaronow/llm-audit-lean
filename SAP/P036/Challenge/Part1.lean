import SAP.P036.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P036-T1; Section III, pp. 595–596 (PDF pp. 2–3), with Table 1 on p. 595
and Table 2 columns (1) and (4) on p. 596.
With Peers as the indicator and β₁ its coefficient, the zero-conditional-mean
models give the stated conditional means, unadjusted OLS has the unique
arm-mean minimizer, and the two response-count inputs give the exact and
rounded coefficients printed in the tables. -/
theorem SAP.P036.T1 : SAP.P036.T1Statement := by sorry

/-- P036-T2; corrected note to Table 2, p. 596 (PDF p. 3), and the counts
in Table 1, p. 595 (PDF p. 2).
For unadjusted specifications under complete randomization with fixed potential
outcomes and at least two units per arm, the genuine HC2 sandwich equals the
Neyman estimator, the OLS and variance moments have the stated exact formulas,
its nonnegative expectation gap vanishes exactly for constant unit effects,
and the two count inputs give the exact variances and rounded standard errors. -/
theorem SAP.P036.T2 : SAP.P036.T2Statement := by sorry
