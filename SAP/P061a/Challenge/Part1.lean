import SAP.P061a.Defs
import SAP.P061a.Defs.WholeW1
import SAP.P061a.Defs.WholeW2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P061-T1; main p. 14, with the mapping of Section 6.2, pp. 11–12.
Independent uniform treatment versions give AEED 3/2, both raw-coordinate direct averages 1,
a persistent gap, an exposure-schedule obstruction, and the exact HT moments and tail bound.
This refutes the raw-assignment-coordinate reading of the comparison under general exposure mappings. -/
theorem SAP.P061a.T1 : SAP.P061a.T1Statement := by sorry

/-- P061-T2; main p. 14 and Equation (3), p. 5.
The adjacent-pair exposure map has positive target exposures and stable outcomes, but its hybrid
arguments fail the exposure or raw assignment domain tests, also for independent copies of the pair.
This refutes well-definedness of the displayed hybrid readings, rather than an asserted numerical equality. -/
theorem SAP.P061a.T2 : SAP.P061a.T2Statement := by sorry

/-- P061-T3; main p. 14 and footnote 8, p. 7.
Own-coordinate independence identifies the AEED with the feasible raw direct contrast, and
exposure independence does the same for a consistent response schedule on exposure vectors. -/
theorem SAP.P061a.T3 : SAP.P061a.T3Statement := by sorry

/-- P061-T4; main p. 14, supplement's HT contrast.
Independent correlated pairs on the full binary cube have exactly one assignment-dependence
neighbor and one interference neighbor per unit. All clauses (a)–(f) hold: positivity, bounded
responses, the exact AEED, zero direct effect, unbiased HT moments, both variance expressions
and coverage bounds. The target gap vanishes but its standardized value diverges; its exact
population-size normalization and the standard-error limit give the claimed orders.
The usual measure-theoretic conditions are assumed; here every space is finite.
Limits use m=index+2, along the claimed populations N=2m^8. -/
theorem SAP.P061a.T4 : SAP.P061a.T4WholeStatement := by sorry

/-- P061-T5; main p. 14, Equation (8) and footnote 8, p. 7, and supplement p. 5.
For individualistic assignments, a negligible AEED--ADE gap in positive
standard-error units transfers the limiting law under consistent scale estimation.
Both Wald coverages tend to L([-q,q]) for each fixed q>0 with zero limiting mass
at both endpoints; a continuous limiting law automatically satisfies this condition.
A nonzero limiting standardized drift shifts the law. The T4 design has a vanishing
raw gap but a diverging absolute standardized gap and failing direct-effect coverage.
For arbitrary discrete feasible designs with finite neighborhood support, the
range-times-TV envelope bounds the target gap, and an envelope o(s) suffices.
The usual measure-theoretic conditions are assumed. Only the hybrid differences
need finite means for transfer, and estimated scales may be nonpositive on
asymptotically negligible events. -/
theorem SAP.P061a.T5 : SAP.P061a.T5WholeStatement_W2 := by sorry

/-- P061-T6; main pp. 2–3, 5 and Equations (5)–(8), pp. 6–7.
On the common finite domain, EPOs are conditional expected exposure outcomes and the AEED is their
average contrast, specializing to the binary average distributional shift functional. -/
theorem SAP.P061a.T6 : SAP.P061a.T6Statement := by sorry

/-- P061-T7; main Equations (5)–(8), pp. 6–7, supplement Equation (3), p. 2.
The one-unit real-assignment geometric design is a probability measure on the power set,
with identity assignment vector, nonnegative-integer support, finite raw responses and both
exposure probabilities 1/2. Its weighted positive-integer terms alternate +1,-1, giving all
stated finite sign-part sums and no limit of the ordered signed series. The exposure-one
numerator and conditional mean have both sign parts +infinity, whereas the exposure-zero
ordinary EPO is zero. The exposure-one EPO, AEPO, EED and AEED have no ordinary value.
The pointwise finite HT estimator has positive and negative expectations +infinity and no
ordinary finite expectation. The usual measure-theoretic conditions are assumed for existing
quantities; nonexistence of the claimed means is the conclusion being demonstrated. -/
theorem SAP.P061a.T7 : SAP.P061a.T7WholeStatement := by sorry

/-- P061-T8; main pp. 6–7 and supplement Equation (3), p. 2.
Positive target cells with finite targeted absolute moments give ordinary conditional means and
unbiased integrable HT estimates of AEPO and AEED, and the moments are automatic on finite support
or under stability within the targeted exposure cells, with their exact constant-cell values. -/
theorem SAP.P061a.T8 : SAP.P061a.T8Statement := by sorry

/-- P061-T9; main Section 6.3, p. 13 and footnote 10.
The four-unit sampling/treatment designs with sample sizes two and three satisfy positivity and
support stability, but have AEEDs two and three for the same raw response schedule, which fails global stability. -/
theorem SAP.P061a.T9 : SAP.P061a.T9Statement := by sorry

/-- P061-T11; main Equations (4)–(8), pp. 6–7, and the existence assertions on pp. 2, 6 and 14.
Positive target exposures on finite positive-probability support give ordinary conditional exposure
means and their unit and population identities, without SUTVA or stability.
Restriction: Adds finite positive-probability support; the feasible assignment set may remain
infinite and retain zero-mass assignments. All infinite-support cases are excluded, including
those with existing targeted moments. Finite support supplies the targeted absolute moments. -/
theorem SAP.P061a.T11 : SAP.P061a.T11Statement := by sorry
