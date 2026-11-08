import SAP.P034.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P034-T1; amended Study 2 pre-analysis plan, Section 8, PDF pp. 5-6;
Appendix p. 9, Figure OA2a note, and p. 18, Figure OA3 note.
The specified randomized finite population has equal completion rates but
outcome-dependent missingness and a biased complete-case OLS coefficient,
including the nonrejecting sample and the observationally equivalent
independent-completion population with a different treatment effect.
Probabilities and moments use exact finite rational sums; both OLS uniqueness
assertions quantify over real coefficient vectors. -/
theorem SAP.P034.T1 : SAP.P034.T1Statement := by sorry

/-- P034-T2; corrected amended Study 2 pre-analysis plan, Section 8,
PDF pp. 5-6, and Appendix pp. 9 and 18.
Randomization, overlap, finite second moments and independent positive
potential completion preserve arm means and covariate laws, identify the
OLS treatment coefficient, and give a unique solution when nonsingular;
the fixed counterexample shows that equal completion rates do not suffice. -/
theorem SAP.P034.T2 {Ω : Type*} [MeasurableSpace Ω] : SAP.P034.T2Statement Ω := by sorry

/-- P034-T3; online Appendix pp. 13-14, Tables OA5-OA6.
The four specified factorial cells have a unique saturated interpolation
with both main coefficients zero and both equally weighted contrasts one,
separating the averaged-effect interpretation from the printed row labels. -/
theorem SAP.P034.T3 : SAP.P034.T3Statement := by sorry

/-- P034-T4; online Appendix pp. 13-14, corrected Tables OA5-OA6 labels.
The fitted interaction model has the stated reference and weighted contrasts,
with an average equal to its main coefficient exactly when the weighted
interaction is zero, or, for positive weights, when the interaction is zero. -/
theorem SAP.P034.T4 : SAP.P034.T4Statement := by sorry

/-- P034-T5; online Appendix p. 11, Table OA3, corrected Total column.
The two corrected percentages round to 9.2 and 0.8, the two printed values
fail the rounding rule, and all 39 corrected category percentages and
all row and column count totals satisfy the stated arithmetic. -/
theorem SAP.P034.T5 : SAP.P034.T5Statement := by sorry
