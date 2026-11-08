import SAP.P009c.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P009-T35; Definitions 1 to 3 and the paragraph after Definition 3: p. 677 (PDF p. 5). Definition 4 and the two displayed forms: p. 678 (PDF p. 6). Lemma A8: Supplement A, p. 7.
EATE reduces to ATE under no interference, has its displayed unconditional form, ADSE has its displayed conditional form for interior marginals, and the two coincide under Bernoulli randomization.
-/
theorem SAP.P009c.T35 : SAP.P009c.T35Statement := by sorry

/-- P009-T36; p. 681 (PDF p. 9); proof in Supplement A, Section 3, p. 5.
The complete chain of interference-count inequalities holds for every positive finite population.
-/
theorem SAP.P009c.T36 : SAP.P009c.T36Statement := by sorry

/-- P009-T37; p. 695 (PDF p. 23); proof in Supplement A, Section 14, pp. 38–39.
Under bounded direct effects, the EATE difference between two designs is bounded by twice the effect bound times their total variation.
-/
theorem SAP.P009c.T37 : SAP.P009c.T37Statement := by sorry

/-- P009-T38; p. 695 (PDF p. 23); proof in Supplement A, Section 14, pp. 39–41.
The assignment-conditional ATE satisfies the printed Lipschitz inequality for every real r at least one, with the infinity-count convention at r equal to one.
-/
theorem SAP.P009c.T38 : SAP.P009c.T38Statement := by sorry

/-- P009-T39; p. 696 (PDF p. 24); proof in Supplement A, Section 14, p. 41.
Under bounded direct effects, the EATE difference is controlled by the printed Lipschitz constant times the infimum of expected L_r distance over couplings.
-/
theorem SAP.P009c.T39 : SAP.P009c.T39Statement := by sorry

/-- P009-T40; p. 683 (PDF p. 11); proof in Supplement A, Section 4, pp. 6–7.
For every growing study with uniformly interior treatment marginals and failure
of restricted interference, replacement potential outcomes satisfy Assumption 1,
preserve the same positive interference-density limsup, and make HT inconsistent
for EATE, with designs and population sizes unchanged. Whenever the printed Hájek
ratios exist on the support eventually, the same replacement makes every real
extension of that contrast inconsistent for EATE as well.
Restricted: Hájek inconsistency is asserted only when every positive-mass
assignment has nonempty weighted arms for all sufficiently large populations;
no Hájek inconsistency is claimed for designs failing this condition.
-/
theorem SAP.P009c.T40 : SAP.P009c.T40WholeStatement := by sorry

/-- P009-T41; p. 684 (PDF p. 12); proof in Supplement A, Section 5, pp. 7–9.
Under Assumption 1, Bernoulli randomization and restricted interference, HT and
every real extension of the printed Hájek contrast are consistent for EATE and
both have stochastic order sqrt(d_AVG)/sqrt(n). Thus the conclusions do not
depend on values assigned when a treatment arm is empty.
-/
theorem SAP.P009c.T41 : SAP.P009c.T41WholeStatement := by sorry

/-- P009-T42; p. 685 (PDF p. 13); proof in Supplement A, Section 6, pp. 9–16.
Under regular complete randomization, restricted interference and the C1 condition, both estimators are consistent for EATE with the printed rate.
-/
theorem SAP.P009c.T42 : SAP.P009c.T42Statement := by sorry

/-- P009-T43; p. 685 (PDF p. 13); proof in Supplement A, Section 7, p. 16.
Under Assumption 1, Bernoulli or complete randomization and bounded average
interference dependence, HT and every real extension of the printed Hájek
contrast are consistent for EATE and both have stochastic order 1/sqrt(n).
-/
theorem SAP.P009c.T43 : SAP.P009c.T43WholeStatement := by sorry

/-- P009-T44; p. 686 (PDF p. 14); proof in Supplement A, Section 8, pp. 16–18.
Under regular paired randomization and Assumptions 2 through 4, both estimators are consistent for EATE with all three printed rate terms.
-/
theorem SAP.P009c.T44 : SAP.P009c.T44Statement := by sorry

/-- P009-T45; p. 688 (PDF p. 16); proof in Supplement A, Section 9, pp. 18–22.
Under Assumption 1, restricted interference, design mixing and design separation,
HT and every real extension of the printed Hájek contrast are consistent for EATE
and both have stochastic order sqrt(d_AVG)/sqrt(n) + sqrt(alpha_EXT)/sqrt(n) +
alpha_INT/n. The result holds for every admissible observed and potential moment
index, including infinity, and hence for the maximal indices of Definition 9
whenever those maxima exist. No attainment assumption is needed.
-/
theorem SAP.P009c.T45 : SAP.P009c.T45WholeStatement := by sorry

/-- P009-T46; p. 689 (PDF p. 17); proof in Supplement A, Section 10, pp. 22–24.
Under Assumption 1, restricted interference and design mixing, HT and every real
extension of the printed Hájek contrast are consistent for ADSE and both have
stochastic order sqrt(d_AVG)/sqrt(n) + sqrt(alpha_EXT)/sqrt(n). The result holds
for every admissible observed and potential moment index, including infinity,
and therefore includes every defined maximal-index choice of Definition 9.
Design separation is not assumed.
-/
theorem SAP.P009c.T46 : SAP.P009c.T46WholeStatement := by sorry

/-- P009-T47; Proposition 7: p. 690 (PDF p. 18); equation (1): p. 689 (PDF p. 17); proof and Corollary A5 in Supplement A, Section 11, pp. 24–30.
The scaled variance error converges to the moving bias decomposition, with the no-interference specialization and nonnegative mean squared expected effects.
-/
theorem SAP.P009c.T47 : SAP.P009c.T47Statement := by sorry

/-- P009-T48; p. 692 (PDF p. 20); proof in Supplement A, Section 12, pp. 32–33.
AVG inflation is conservative in the iterated-limit sense of Definition 10 under the stated variance-heterogeneity condition.
-/
theorem SAP.P009c.T48 : SAP.P009c.T48Statement := by sorry

/-- P009-T49; p. 692 (PDF p. 20); proof in Supplement A, Section 12, pp. 33–34.
MAX inflation is conservative in the iterated-limit sense under either printed alternative.
-/
theorem SAP.P009c.T49 : SAP.P009c.T49Statement := by sorry

/-- P009-T50; p. 693 (PDF p. 21); proof in Supplement A, Section 12, pp. 34–36.
SR inflation is conservative under either printed alternative, and the maximum Rayleigh value lies between average and maximum dependence degree.
-/
theorem SAP.P009c.T50 : SAP.P009c.T50Statement := by sorry

/-- P009-T51; p. 693 (PDF p. 21); Definition A4, Lemma A30 and the proof in Supplement A, Section 13, pp. 36–38.
For every regular Bernoulli design sequence, admissible tail level and exponent, suitable outcomes have the stated interference bounds and the normalized HT law converges to the three-point law, which attains the finite Chebyshev bound.
-/
theorem SAP.P009c.T51 : SAP.P009c.T51Statement := by sorry

