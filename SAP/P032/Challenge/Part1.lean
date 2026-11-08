import SAP.P032.Defs
import SAP.P032.Defs.WholeW1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P032-T1; pp. 187, 191 and 196, validator counterexamples (a)–(f).
The bounded pair, four-record and six-edge models give the stated population comparisons,
finite residual-estimator expectations, independent realizations and probability limits. -/
theorem SAP.P032.T1 {Ω : Type*} [MeasurableSpace Ω] : SAP.P032.T1Statement Ω := by sorry

/-- P032-T2; pp. 187, 191 and 196, corrected non-incident-dependence comparison.
The OLS variance difference is the omitted weighted covariance sum, whose signs and
positive-semidefinite characterizations give exactly the asserted population orderings. -/
theorem SAP.P032.T2 {R M P Ω : Type*} [Fintype R] [Fintype M] [Fintype P]
    [DecidableEq R] [DecidableEq M] [DecidableEq P] [MeasurableSpace Ω] :
    SAP.P032.T2Statement R M P Ω := by sorry

/-- P032-T3; p. 191 decomposition; dcr.ado lines 108–119 and 163–190, constructed example.
The specified Cox fit has the stated risk sets, scores and component covariances, and
the two subject-id substitutions give the stated incorrect positive values. -/
theorem SAP.P032.T3 : SAP.P032.T3Statement := by sorry

/-- P032-T4; p. 191 display and component definitions; dcr.ado lines 108–119 and 163–190.
Common scores give the exact decomposition and exhaustive coefficient count, while
subject-id substitution and arbitrary residual scaling have the stated discrepancies. -/
theorem SAP.P032.T4 {R M P G : Type*} [Fintype R] [Fintype M] [Fintype P]
    [DecidableEq R] [DecidableEq M] [DecidableEq P] [DecidableEq G] :
    SAP.P032.T4Statement R M P G := by sorry

/-- P032-T5; pp. 187, 191 and 196, formal universal lower-bound readings.
The validators' unrestricted weak and strict population, residual-estimator expectation,
and relative probability-limit readings of the quoted passages all fail, establishing
the canonical assertion that those four readings are false. -/
theorem SAP.P032.T5 : SAP.P032.T5Statement := by sorry

/-- P032-T6; p. 191 footnote 3 and the released PSD option, validator ten-dyad example.
The specified OLS covariance has a positive diagonal and a negative contrast, so the
diagonal gate leaves a matrix that is not positive semidefinite. -/
theorem SAP.P032.T6 : SAP.P032.T6Statement := by sorry

/-- P032-T7; p. 191 footnote 3, corrected PSD operation and validator example.
Unconditional eigenvalue clipping is positive semidefinite, fixes exactly PSD inputs,
has the stated quadratic formula and gate criterion, and gives the stated rank-one example. -/
theorem SAP.P032.T7 {P : Type*} [Fintype P] [DecidableEq P] : SAP.P032.T7Statement P := by sorry

/-- P032-T8; 1_reanalysis_stata.do lines 1312 and 1373–1385; dcr.ado lines 125–238.
The specified five-imputation logit example has the stated fits, components and
strictly negative pooled-first discrepancy, with scalar clipping inactive.
Restricted: the separate equalities of the two completed-data decomposition values
with direct ordered-pair sums are not asserted. -/
theorem SAP.P032.T8 : SAP.P032.T8Statement := by sorry

/-- P032-T9; code/1_reanalysis_stata.do lines 1373–1385; dcr.ado lines 125–238;
p. 191 (PDF p. 6), decomposition display.
For at least two imputations, common coefficient estimates, fixed nonzero component
factors and symmetric completed-data matrices, with no active PSD adjustment, the
pooled-first total is the weighted within-imputation mean plus c times Rubin's full
between-imputation term Q = (1 + 1/M)B. Combining within each imputation and then
pooling gives the same within mean plus Q, so the gap is (c - 1)Q and adding
(1 - c)Q repairs it. The DCR weights sum to one and, when all factors are one,
decomposition commutes with Rubin pooling. For the asylike factors,
c - 1 = -sum_i 1/G_i + 1/G_D + (K - 2)/n; at K = 4, G_i = 13, G_D = 6, n = 24
it is -3/52 and is nonzero. The standalone scalar identity also holds for zero
denominators under Lean's total division. -/
theorem SAP.P032.T9 : SAP.P032.T9WholeStatement := by sorry

/-- P032-T10; p. 196 Section 4.1 and Supplementary Table A.2, p. A3.
Exact recovery from the printed proportions gives four studies at the weak half-loss
threshold and three at the strict threshold, together with all stated neighboring counts. -/
theorem SAP.P032.T10 : SAP.P032.T10Statement := by sorry

/-- P032-T11; pp. 190–191 Section 3, unnumbered decomposition display and footnotes 2–3.
The unadjusted OLS residual sandwich decomposes using the stated member, dyad and record masks.
Restricted: no separate pointwise coefficient identity, conventional multiway-cluster
equivalence, software-computability assertion, square-root rule for standard errors,
or eigenvalue-clipping assertion is stated. -/
theorem SAP.P032.T11 {R M P : Type*} [Fintype R] [Fintype M] [Fintype P]
    [DecidableEq R] [DecidableEq M] [DecidableEq P] : SAP.P032.T11Statement R M P := by sorry

/-- P032-T12; pp. 188–189 Section 2.1, the two unnumbered toy-example displays.
The variance of the two-outcome average has the stated covariance correction and,
for five pairwise uncorrelated finite-variance primitives, all stated sign cases. -/
theorem SAP.P032.T12 {Ω : Type*} [MeasurableSpace Ω] : SAP.P032.T12Statement Ω := by sorry
