import SAP.P016a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P016a

/-- P016-T1; p. 397 (PDF p. 3), Section 2, before equation (1).
The pairing and assignment-design witnesses give both statistic tables, both tail masses and both design covariances. -/
theorem SAP.P016a.T1 : T1Statement := by sorry

/-- P016-T2; p. 397 (PDF p. 3), Section 2, before equation (1), corrected claim.
The simple SSR has the least-squares, moment, ordering, margin and design identities, with the network-alignment and scalar-KS witnesses. -/
theorem SAP.P016a.T2 : T2Statement := by sorry

/-- P016-T3; p. 400 (PDF p. 6), Section 3 and Section 2.2; Fig. 3, p. 401 (PDF p. 7).
The four-unit, six-unit, recorded-table and cutoff witnesses establish the stated affine obstructions, regression minima and rejection-rule discrepancies. -/
theorem SAP.P016a.T3 : T3Statement := by sorry

/-- P016-T4; p. 400 (PDF p. 6), Sections 2.2 and 3; pp. 398 and 401, corrected claim.
The bank-centered model has the stated cancellation, standardization, regression invariance, orientation, nonaffine witnesses and inclusive-tail cutoff identities.
Restriction: The raw similarity-versus-distance identity also requires every bank assignment to have the same treated count as the current assignment; the standardized sign identity explicitly requires positive standard deviations for both exposures. Omits identification with the complete application procedure: the 10,000-assignment saved bank, 500 reference draws, directional application tails, projected maximum-p coordinate bounds, and association of Figure 4 and its coefficient and rectangle with that procedure. It does not identify the released simulation procedure as a whole; it states the doubled-tail formulas and cutoff witnesses only. -/
theorem SAP.P016a.T4 : T4Statement := by sorry

/-- P016-T6; p. 400 (PDF p. 6), Section 3 and Section 2.2; pp. 398 and 401, as printed.
For any map g with across-unit sample variance one on every assignment of a nonempty finite design, the displayed generation equation implies recovery of the baseline outcomes; the printed rejection convention is p < 1/20.
Restriction: This states only the algebraic consistency consequence of the raw-distance display. It imposes no affine-normalization requirement on g and omits the printed description that the indirect effect is linear in the raw distance sums. Unit variance means across-unit sample variance with divisor n-1 on every design assignment. Omits other unit-variance conventions, identification with the complete SSR + Design regression and testing procedure, and the empirical rejection proportions reported for the simulations and figures. -/
theorem SAP.P016a.T6 : T6Statement := by sorry

/-- P016-T7; p. 396 (PDF p. 2), Section 1, steps (2)-(4).
The four-unit mean and seventy-assignment KS witnesses show probability-one rejection of true additive hypotheses by the literal raw-versus-adjusted comparison, with the stated corrected reference probabilities. -/
theorem SAP.P016a.T7 : T7Statement := by sorry

/-- P016-T8; p. 396 (PDF p. 2), Section 1, step (4), corrected claim.
The additive adjustment fixes the true baseline, gives the same observed and reference law with calibrated inclusive upper tails, and removes exactly the raw mean shift. -/
theorem SAP.P016a.T8 : T8Statement := by sorry

/-- P016-T9; footnote 3, p. 396; equation (1), p. 397; equation (2), p. 399.
The signed-KS, pooled-mean and missing-intercept readings give the three specified discrepancies, including the general constant-statistic law and inclusive tails and the complete six-assignment SSR table. -/
theorem SAP.P016a.T9 : T9Statement := by sorry

/-- P016-T10; footnote 3, p. 396; equation (1), p. 397; equation (2), p. 399, corrected claim.
The corrected SSR minima are attained with unique fitted values, KS equals its threshold supremum and is label invariant in [0,1], and symmetric adjacency gives the stated network columns. -/
theorem SAP.P016a.T10 : T10Statement := by sorry

/-- P016-T11; pp. 396-397 (PDF pp. 2-3), the quoted statistic criterion and following sentence.
The weak and strict KS witnesses and the two opposite SSR changes refute effect-increasing monotonicity for both KS versions and both SSR orientations. -/
theorem SAP.P016a.T11 : T11Statement := by sorry
