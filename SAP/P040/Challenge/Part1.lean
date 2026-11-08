import SAP.P040.Defs
import SAP.P040.Defs.WholeW1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P040-T1; p. 3, right column, manipulation check (PDF p. 3).
Under the independent common-probability binomial model for fifteen detections,
the mass of count 14 at p = .80 is .13194139533312. Every deterministic count-based
set excluding .80 there, and every lower bound above .80 there, has coverage at
most .86805860466688, so cannot guarantee .95 or .975 uniformly. The printed
interval and every lower endpoint rounding to .81 exclude .80. The Wald rule
with multiplier 1.96 reproduces the printed endpoints, with the stated rational
arithmetic and brackets. For every multiplier in [1.9599,1.9601], membership,
two-sided coverage .814815425593344, lower coverage .832874232578048 and lower
failure probability .167125767421952 have the stated exact values. The actual
standard normal .975 quantile exists uniquely in that range and also reproduces
the printed endpoints, with prefixes .807099 and 1.059567. This is the canonical
finite-sample calibration counterexample under the added binomial model. -/
theorem SAP.P040.T1 : SAP.P040.T1WholeStatement := by sorry

/-- P040-T2; p. 3, right column, manipulation check (PDF p. 3), corrected.
Under the independent common-probability binomial model, the exact equal-tailed
and one-sided intervals have the stated unique endpoints, rounding, inclusion of
.80, and uniform coverage of at least 95%, while excluding .80 at count 14
prevents that coverage guarantee. -/
theorem SAP.P040.T2 : SAP.P040.T2Statement := by sorry

/-- P040-T3; p. 3, right column, paragraph beginning "In our sample of 15
customers" (PDF p. 3).
The observed proportion rounds to .93 and the reconstructed Wald endpoints
round to .81 and 1.06 with the stated brackets and an upper endpoint above one.
This states the canonical passage's retained mathematical content P1 and P2;
the customer counts are inputs and no exact coverage claim is attributed to it. -/
theorem SAP.P040.T3 : SAP.P040.T3Statement := by sorry

/-- P040-T4; p. 4, left column, Methods, and p. 5, left column, last paragraph
(PDF pp. 4-5); Table 1, p. 5.
The actual adjusted cafe and bulk regressions have the stated exact coefficients,
HC1 variances, statistics and decimal rounding; their normal-reference p values
round to .58 and .28, whereas the printed .59 and .29 use the Student-t reference. -/
theorem SAP.P040.T4 : SAP.P040.T4Statement := by sorry

/-- P040-T5; p. 4, left column, Methods and right-column significance statement;
p. 5, left column, last paragraph and Table 1 (PDF pp. 4-5), corrected.
The recorded designs give 28 and 21 residual degrees of freedom, Student-t
reference values .59 and .29, and all eight effects have p greater than .10 under
both references with the stated minimum, while the normal alternative gives .58
and .28; the reference calculation does not assert an exact null distribution. -/
theorem SAP.P040.T5 : SAP.P040.T5Statement := by sorry
