import SAP.P013a.Defs.WholeW1
import SAP.P013a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P013-T8; corrected concentration and coverage argument, Appendix A.7,
p. 1943 (PDF p. 32). Conservativeness and vanishing variance of the scaled estimate give
centered concentration, the finite relative lower-tail bound and both coverage lower limits.
If its expectation converges to a finite value, the scaled estimate, variance ratio and
studentized error have the stated limits. Ratios and studentization are extended by zero
where the estimated variance is nonpositive; that event has probability tending to zero. -/
theorem SAP.P013a.T8 : SAP.P013a.T8WholeStatement := by sorry

/-- P013-T9; corrected targets in Appendix A.6, p. 1942 (PDF p. 31), Proposition 6.2,
p. 1926 (PDF p. 15), Appendix A.7, p. 1943 (PDF p. 32), and the sentence preceding
Proposition 4.1, p. 1920 (PDF p. 9). HT means and their contrast are consistent for the
population quantities under Conditions 3 and 4. The corrected Wald conclusion covers the
population contrast, the positive-variance studentization display is an identity, and
simulation guidance bounds relative bias for the fixed population total. -/
theorem SAP.P013a.T9 : SAP.P013a.T9WholeStatement := by sorry

/-- P013-T10; Table 2, WLS rows $\tau(d_{101}, d_{000})$ and $\tau(d_{111}, d_{000})$: estimate and 95% CI, corrected claim; p. 1936 (PDF p. 25).
Both printed WLS triples are incompatible with a symmetric interval even allowing closed three-decimal rounding bins. -/
theorem SAP.P013a.T10 : SAP.P013a.T10Statement := by sorry

/-- P013-T11; Section 9, the two descriptions of the simulation design's exposure probabilities (the degree-39 student; no no-exposure probability below 0.01), corrected claim; p. 1931 (PDF p. 20); design and exposure mapping on p. 1930 (PDF p. 19).
Exact complete-randomization counting links the degree-39 exposure probabilities and proves that the two printed probability descriptions are incompatible. -/
theorem SAP.P013a.T11 : SAP.P013a.T11Statement := by sorry

/-- The printed claim is false: the unrestricted relative-bias bound and the logarithmic replicate guarantee are both refuted on the nonzero-total domain.
P013-T12; Proposition 4.1; p. 1920 (PDF p. 9); proof in Appendix A.3, p. 1938 (PDF p. 27). -/
theorem SAP.P013a.T12 : SAP.P013a.T12Statement := by sorry

/-- P013-T13; Lemma 4.1 and Proposition 4.2; p. 1919 (PDF p. 8); pp. 1920–1921 (PDF pp. 9–10); proofs in Appendix A.2 and A.4, p. 1938 (PDF p. 27).
The exposure total and contrast have the printed expectations, variance formulas and covariance expansion. -/
theorem SAP.P013a.T13 : SAP.P013a.T13Statement := by sorry

/-- P013-T14; Lemma 5.1 and Propositions 5.1–5.2, pp. 1921–1922 (PDF pp. 10–11),
and Appendix A.5, Propositions A.1–A.2 and Corollary A.2, pp. 1939–1942 (PDF pp. 28–31).
The exposure variance estimate has the stated unbiasedness, missing-joint bias and quadratic
conservativeness. For general binary inclusion sampling with positive marginals, including
certainty units, the same bias identity and both conjugate-power and quadratic conservative
corrections hold. All missing-pair sums are ordered and outcomes may have either sign. -/
theorem SAP.P013a.T14 : SAP.P013a.T14WholeStatement := by sorry

