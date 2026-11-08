import SAP.P053.Defs
import SAP.P053.Defs.WholeW1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P053-T1; Section 4, p. 348 (PDF p. 3); Introduction (iii), p. 346 (PDF p. 1).
For fixed binary sharp-null outcomes, the difference in means identifies the table,
every table statistic has the explicit common factor, symmetric arm-sample statistics
are table statistics, and table constancy exactly characterizes factorization. -/
theorem SAP.P053.T1 {S : Type*} : SAP.P053.T1Statement S := by sorry

/-- P053-T2; Section 4, p. 348 (PDF p. 3).
The specified four-unit and repeated-block examples refute the unrestricted reading
allowing labelled and fixed-covariate statistics. Both statistics have the stated values
and fail to factor through the difference in means. The six four-unit assignments each
have probability 1/6. The same repeated populations have means 1/2, variances m/(4m-1),
zero effect variance and average effect, raw fourth-moment average one, and the full S5
regularity certificate with limits (1/2,1/4,1/4,0,0).
The usual measure-theoretic conditions are assumed and hold automatically here. -/
theorem SAP.P053.T2 : SAP.P053.T2WholeStatement := by sorry

/-- P053-T3; Section 4, p. 348 (PDF p. 3); Introduction (iii), p. 346 (PDF p. 1).
Absolute differences and signed differences give the specified distinct inclusive upper-tail
p-values on six and four units, whereas strictly increasing transformations preserve those p-values. -/
theorem SAP.P053.T3 : SAP.P053.T3Statement := by sorry

/-- P053-T4; Section 3, p. 348 (PDF p. 3).
The variance-limit inequality has exactly the stated allocation/standard-deviation sign
criterion, with the stated difference identity. -/
theorem SAP.P053.T4 : SAP.P053.T4Statement := by sorry

/-- P053-T5; Section 2, p. 347 (PDF p. 2); Introduction (i), p. 346 (PDF p. 1).
Under S5, Fisher and pooled OLS variances have all three stated first-order expansions
and both stated scaled probability limits. -/
theorem SAP.P053.T5 : SAP.P053.T5Statement := by sorry

/-- P053-T6; Section 2, pp. 346–347 (PDF pp. 1–2); Introduction (i), p. 346.
Local effects give the variance difference and ratio limits, constant effects give the
two variance approximations, and Fisher's null gives the normal Wald limit and nominal size.
Restriction: omit equivalence of the FRT and Wald tests under local alternatives, including
conditional FRT distribution, quantile, p-value and rejection-rule comparisons; additionally,
the variance-ratio and studentized conclusions require eventual positivity of the OLS
variance at every supported assignment, so ordinary division is defined. -/
theorem SAP.P053.T6 : SAP.P053.T6Statement := by sorry

/-- P053-T7; Sections 2–3, p. 347 (PDF p. 2), with the sentence beginning on p. 346.
The Neyman and OLS expansions and limits satisfy the stated difference identity and
necessary conditions, and the local Fisher comparison has the same expansion and limits. -/
theorem SAP.P053.T7 : SAP.P053.T7Statement := by sorry

/-- P053-T8; Section 3, pp. 347–348 (PDF pp. 2–3).
The actual variance obeys Neyman's bound, constant effects give equality and agreement,
and the specified heterogeneous Neyman-null sequence has all stated finite formulas
and the actual/OLS/Neyman limiting coefficients 81/4, 10 and 85/4. -/
theorem SAP.P053.T8 : SAP.P053.T8Statement := by sorry
