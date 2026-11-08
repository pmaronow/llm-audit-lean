import SAP.P033.Defs
import SAP.P033.Defs.WholeW1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P033-T1; p. 7 (PDF p. 7), Results, paragraph beginning “Panel 3(c)”;
Abstract, p. 1; Introduction, p. 2; Concluding remarks, p. 10.
In the stipulated eight-score Gaussian sharp RD model, both weighted estimators
are unbiased and have exact Gaussian inference, although the replacement has a
larger standard error and loses realized significance. Includes both Gram and WLS
certificates, every one-side variance and covariance, and the population and
conditional-kernel construction. This is a pointwise witness at the specified
affine means, with no claim of uniform coverage over a smoothness class. -/
theorem SAP.P033.T1 : SAP.P033.T1WholeStatement := by sorry

/-- P033-T2; Abstract, p. 1; Introduction, p. 2; Results, p. 7, paragraph
beginning “Panel 3(c)”; Concluding remarks, p. 10 (printed and PDF pages agree).
The affine model and its smooth quartic alternative induce the same conditional
data law but different coverage. Includes the general Gaussian coverage formula,
the polynomial and cutoff identities, bias and tail bounds, all study-count and
nonidentification conclusions, and the square-integrable bias-adjustment variance
identity. All conditional mean functions and the perturbation are C-infinity.
The empirical counts in the replacement prose are expressly outside its formal claim. -/
theorem SAP.P033.T2 : SAP.P033.T2WholeStatement := by sorry

/-- P033-T3; p. 7 (PDF p. 7), Methodology; p. 9 (PDF p. 9), Power analysis and Table 2; Table 3, p. 10 (PDF p. 10); Figures 3 and 4, p. 8 (PDF p. 8).
The ten-cluster sign model and its noisy extension have zero estimated variances despite positive true variances, with the stated WLS certificates and zero-width coverage counts. -/
theorem SAP.P033.T3 : SAP.P033.T3Statement := by sorry

/-- P033-T4; Methodology, p. 7; Power analysis and Table 2, p. 9;
Table 3, p. 10, election panel (printed and PDF pages agree).
Within-cell nearest-neighbour residuals cancel in nested clusters. The full
n(n+1)-cluster-per-side physical grid, with five records per cluster and h=b=1/n,
has exactly n positive triangular weights per side and the stated normalized
linear and same-bandwidth bias-corrected fits. The true sign-model variances
are V_n and (6/5)V_n with record noise, n V_n tends to 48/5, and estimated
nearest-neighbour variances are zero for every outcome array. Includes the
independent finite-second-moment cluster plug-in identities, the ten-cluster
examples, and the stipulated table-share arithmetic. -/
theorem SAP.P033.T4 : SAP.P033.T4WholeStatement := by sorry

/-- P033-T5; Power analysis and Table 2, p. 9, row 0.1, column 95;
Table 3, p. 10, second panel, row 0.1, column 95; Figure 4, p. 8.
The binary individual-outcome fuzzy RD witness has individual squared Cohen
effect 4/75 but count-standardized squared effect 1/80000. Doubling all cell
counts preserves the Wald effect and individual standardization, while dividing
the count-standardized squared effect by four. In general positive count scaling
preserves the Wald ratio, scales the sample standard deviation, and divides the
count-standardized effect by the scale. Wald and standardization denominators
are nonzero, and sample standard deviations use at least two observations. -/
theorem SAP.P033.T5 : SAP.P033.T5WholeStatement := by sorry

/-- P033-T6; p. 9 (PDF p. 9), Power analysis and Table 2 (row 0.1, column 95); Table 3, p. 10 (PDF p. 10), ‘Studies not using election data’ (row 0.1, column 95).
Binary outcomes bound the standard deviation and the specified stored-SE normal power below 95%, with the stated derivative, root, sample-size, table and ratio conclusions. -/
theorem SAP.P033.T6 : SAP.P033.T6Statement := by sorry

/-- P033-T7; p. 5 (PDF p. 5), left column and the continuation under Table 1; Table 1.
Selection-free linear, polynomial and Gaussian study populations have unequal caliper-side probabilities and the stated excess rejection tails. -/
theorem SAP.P033.T7 : SAP.P033.T7Statement := by sorry

/-- P033-T8; p. 5 (PDF p. 5), left column and the continuation under Table 1; Table 1.
For the specified normalized density, caliper counts obey the stated conditional binomial laws, mass criteria, monotonicity, finite-width bounds and small-window limits. -/
theorem SAP.P033.T8 : SAP.P033.T8Statement := by sorry

/-- P033-T9; p. 9 (PDF p. 9), Power analysis, left column, and Table 2; Table 3, p. 10 (PDF p. 10), ‘Studies using election data’.
The declared Gaussian test has the stated normal power, and reducing its standard error by the cluster-count factor increases power and gives the stipulated arithmetic corrections. -/
theorem SAP.P033.T9 : SAP.P033.T9Statement := by sorry

/-- P033-T10; p. 7 (PDF p. 7), Results, right column, paragraph beginning ‘We can disaggregate the information in Figure 3’; Figure 4, p. 8 (PDF p. 8).
The printed funnel slope misclassifies the displayed point, and variance and standard-deviation scaling give different coordinates with the same t ratio. -/
theorem SAP.P033.T10 : SAP.P033.T10Statement := by sorry

/-- P033-T11; p. 7 (PDF p. 7), Results, right column, paragraph beginning ‘We can disaggregate the information in Figure 3’; Figure 4, p. 8 (PDF p. 8).
Common scaling preserves the t ratio, significance has reciprocal boundary slope, and the binary control sample has the stated variance and standard-deviation enclosure. -/
theorem SAP.P033.T11 : SAP.P033.T11Statement := by sorry

/-- P033-T12; Supplement, Figure S9 (printed supplement p. 18) and Section S9 (printed supplement p. 16), text extraction only; main text p. 8 (PDF p. 8), right column, top paragraph.
For bias bounds one and one half, exactly honest Gaussian intervals produce pseudo p-values that over-reject at level one fifth. -/
theorem SAP.P033.T12 : SAP.P033.T12Statement := by sorry

/-- P033-T13; Supplement, Figure S9 (printed supplement p. 18), text extraction only; main text p. 8 (PDF p. 8).
The pseudo p-value preserves the interval decision at 5%, and the specified worst-case Gaussian tail is valid at every level. -/
theorem SAP.P033.T13 : SAP.P033.T13Statement := by sorry

/-- P033-T14; Supplement, Section S4 (printed supplement pp. 9–10), text extraction only; main text p. 4 (PDF p. 4), right column, end of the paragraph on Figure 1.
The two interval-imputation rules differ on the recorded inputs and put the second statistic in adjacent histogram bins. -/
theorem SAP.P033.T14 : SAP.P033.T14Statement := by sorry

/-- P033-T15; Supplement, Section S4 (printed supplement pp. 9–10), text extraction only; main text p. 4 (PDF p. 4), right column.
Width-based imputation has the stated reconstruction formulas, recovers centered normal-interval standard errors, and agrees with the upper-endpoint rule exactly at midpoint estimates. -/
theorem SAP.P033.T15 : SAP.P033.T15Statement := by sorry

