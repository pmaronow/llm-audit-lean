import SAP.P007.Defs
import SAP.P007.Defs.WholeW1
import SAP.P007.Defs.WholeW2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P007-T1; Section 3.2, p. 153 (PDF p. 5), with Table 1 and Section 3.1,
p. 152 (PDF p. 4). Every fixed 8580 by 1205 array with the specified observed
total has four-variable expected loss below 99%, with the complete exact certificate. -/
theorem SAP.P007.T1 : SAP.P007.T1Statement := by sorry

/-- P007-T2; Table 1, p. 152 (PDF p. 4), and Section 3.2, p. 153 (PDF p. 5).
The logged-average hypothesis gives corrected counts and 66.3% missingness, the
four-variable population bound, and the comparisons of simulation estimates at
four, five and six variables. Restricted: drops the corrected sentence's assertion
about every variable count above six; only the three displayed estimates are compared. -/
theorem SAP.P007.T2 : SAP.P007.T2Statement := by sorry

/-- P007-T3; proof of Lemma 3, p. 154 (PDF p. 6), and proof of Lemma 8,
Supplement p. 4. The two explicit laws refute both directions of the asserted
equivalence between a zero observation bound and full missingness, and also apply
to two singleton groups. -/
theorem SAP.P007.T3 : SAP.P007.T3Statement := by sorry

/-- P007-T4; proof of Lemma 3, p. 154 (PDF p. 6), and proof of Lemma 8,
Supplement p. 4. Both explicit laws meet the assumptions but have a null
conditioning prefix, while retaining the deletion bound; singleton groups give
the same counterexamples. -/
theorem SAP.P007.T4 : SAP.P007.T4Statement := by sorry

/-- P007-T5; repaired proofs of Lemma 3, p. 154 (PDF p. 6), and Lemma 8,
Supplement p. 4. The prefix recursion, zero-prefix coefficient convention,
product formula and zero endpoint establish the finite bound for variables or groups. -/
theorem SAP.P007.T5 : SAP.P007.T5Statement := by sorry

/-- P007-T6; repaired proof of Proposition 5, p. 154 (PDF p. 6), and
Proposition 10, Supplement pp. 4-5. The corrected finite Bernoulli sandwich,
zero endpoint, positive-domain exponential identity and two-variable group counts hold. -/
theorem SAP.P007.T6 : SAP.P007.T6Statement := by sorry

/-- P007-T7; Figure 4 and its discussion, Supplement p. 2.
All specified equality, rounding, worked-value and actual-probability upper-guarantee
counterexamples hold for the displayed normalized independent-cell laws. -/
theorem SAP.P007.T7 : SAP.P007.T7Statement := by sorry

/-- P007-T8; corrected Figure 4 and its discussion, Supplement p. 2.
The real inverse, integer floor and ceiling, sharp probability guarantees and both
worked values describe the lower bound, with explicit attaining laws and an upper-guarantee counterexample. -/
theorem SAP.P007.T8 : SAP.P007.T8Statement := by sorry

/-- P007-T9; Figure 5 and its discussion, Supplement pp. 2-3.
The specified two-row law has expected deleted fraction 5/8, exceeding 7/16,
and distinguishes that fraction bound from both all-deletion probabilities. -/
theorem SAP.P007.T9 : SAP.P007.T9Statement := by sorry

/-- P007-T10; corrected Figure 5 and its discussion, Supplement pp. 2-3.
The usual measure-theoretic conditions are assumed. For positive integers n,k
and any measurable missingness array on a probability space, Assumption 2 gives
E[D_i]=1-s_ik >= b_k and E[F_n]=(sum_i (1-s_ik))/n >= b_k, where
b_k=1-q^k is independent of n. These conclusions require no row independence.
Every law with mutually independent cells of observation probability q satisfies
Assumptions 1 and 2 and attains E[F_n]=b_k; a normalized independent-cell law
exists for every q in [0,1). The all-deletion lower bound is b_k^n, equals b_k
at n=1, and is strictly smaller for n>=2 and 0<q<1, when 0<b_k<1.
On the entire domain q in [0,1), the bounds coincide if and only if n=1 or q=0;
at q=0 both bounds are one. -/
theorem SAP.P007.T10 : SAP.P007.T10WholeStatement_W2 := by sorry

/-- P007-T11; Section 3.1, p. 152 (PDF p. 4), referring to Assumption 1,
p. 150 (PDF p. 2). Independent rows need not have identical distributions, as
the explicit witness and general product of row-specific deletion probabilities show. -/
theorem SAP.P007.T11 : SAP.P007.T11Statement := by sorry

/-- P007-T12; preprocessing, pp. 151-152 (PDF pp. 3-4), and Table 1,
p. 152 (PDF p. 4). Removing wholly missing columns gives the exact average
identities, rules out the printed retained average, and yields the corrected
average and overstatement under the specified missing-cell count. -/
theorem SAP.P007.T12 : SAP.P007.T12Statement := by sorry

/-- P007-T14; Lemma 3, p. 150 (PDF p. 2).
Under mutual row independence and the printed conditional observation bound,
the probability of deleting all rows is at least (1-q^k)^n. -/
theorem SAP.P007.T14 : SAP.P007.T14Statement := by sorry

/-- P007-T15; Lemma 8, Supporting Information B, Supplement p. 4.
Under mutual row independence and the printed group observation bound,
the probability of deleting all rows is at least (1-q^g)^n. -/
theorem SAP.P007.T15 : SAP.P007.T15Statement := by sorry

/-- P007-T16; Proposition 5, p. 151 (PDF p. 3).
Arbitrary changing joint laws with independent rows, one fixed conditional
observation bound q<1 and superlogarithmic variable counts have all-deletion
probability tending to one, including q=0. -/
theorem SAP.P007.T16 : SAP.P007.T16Statement := by sorry

/-- P007-T17; Proposition 10, Supporting Information B, Supplement p. 4.
Arbitrary changing group-indicator laws with independent rows, one fixed
conditional observation bound q<1 and superlogarithmic group counts have
all-deletion probability tending to one, including q=0. -/
theorem SAP.P007.T17 : SAP.P007.T17Statement := by sorry
