import SAP.P003b.Defs
import SAP.P003b.Defs.WholeW1
import SAP.P003b.Defs.WholeW2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- In a positive balanced design, complementary estimates have the corrected sum, the exact design mean
equals the treatment effect, and every reflected point mass agrees.
P003-T24; p. 18 (PDF p. 18). -/
theorem SAP.P003b.T24 : SAP.P003b.T24Statement := by sorry

/-- P003-T25; p. 21 (PDF p. 21), corrected (B.11)-(B.12).
For every design the possible accepted effects J equal K and lie in the
interval hull and candidate lattice. Under balance J is exactly the lattice
part of the interval, and the upper-half identity holds with the same lattice
intersection. For n=4,m=2,o=(0,2,0,2),alpha=1/2, the candidate set has five
points, the possible maxima are 1/3,1,1,1,1/3, J has three points and the
interval is [-1/4,1/4]. The two impossible endpoint vectors have p=2/3;
the only possible negative endpoint vector has p=1/3. The printed set is
the full candidate set, including both points outside the interval, whereas
1/8 lies in the real interval and outside the lattice. -/
theorem SAP.P003b.T25 : SAP.P003b.T25WholeStatement := by sorry

/-- The enclosed critical values give incompatible reported 50-unit Wald summaries and exact 50- and
100-unit coverage and median benchmarks.
P003-T8; p. 15 (PDF p. 15), Table 2 and its caption; variance estimator (5.9)-(5.11) on p. 11 (PDF
p. 11).
Restriction: Uses a real critical value z in the displayed rational enclosure; it does not identify
z with the normal 0.975 quantile or prove that quantile enclosure. Omits the extensions to every
sqrt(2)<=z<=2 and every z>=1.95, the pointwise variance lower bound V_k>=1/50, the sharper pointwise
HC1 width bound 2*z*sqrt(1/50), and the sharper pointwise HC0 width bound 2*z*sqrt(12/625). Retains
both exact coverage fractions, both design medians, the HC0 classification and 0.54 bound, and the
finite-run sharp median bound and reported-pair incompatibility for the enclosed critical values.
The statement uses the explicit two-type Wald formulas without a separate labeled-assignment-to-k
derivation. The design conclusions certify the displayed values as medians without asserting
uniqueness. -/
theorem SAP.P003b.T8 : SAP.P003b.T8Statement := by sorry

/-- P003-T19; p. 17 (PDF p. 17), Section 8 and corrected footnote 16.
For fixed binary covariates, actual table counts have exactly the two independent
stratum-total restrictions. Their number is the product of the two four-cell
composition counts, at most (n+3)^6/36 and uniformly O(n^6), hence O(n^7).
With only a total restriction the eight-cell count is choose(n+7,7), the stated
convolution, and O(n^7); without covariates it is choose(n+3,3) and O(n^3).
For the fixed 2+2 split of four labels there are 256 tables, 100 realized count
vectors and 330 total-only vectors; (3,0,0,0;1,0,0,0) is not realizable. -/
theorem SAP.P003b.T19 : SAP.P003b.T19WholeStatement := by sorry

/-- P003-T20; pp. 5,12,20,21,26,18 (PDF pages agree).
Binary assignment coordinates correspond bijectively to treated sets and
preserve their uniform law. The legal reuse update is (-1,1,1,-1), the four
B.8 comparisons use n01, and the signed line uses j=u11+u10 and
k=u10-v10. At its feasible minimum k is nonnegative and is positive off
the selected vector; in the balanced discordant case the quoted p-value
comparison follows. The printed index fails at (0,2,0,2). Evenness of
a+2+d implies d congruent to a modulo two. Equal table counts give equal
estimator distributions, but the two swapped tables (11,00) and (00,11)
give estimates 1 and -1 at the same assignment. -/
theorem SAP.P003b.T20 : SAP.P003b.T20WholeStatement := by sorry

/-- The printed claim is false: the legal deterministic n=20, m=3 missingness example has defined
extremal endpoints and coverage 297/380 below 1-109/500.
P003-T26; p. 14 (PDF p. 14), statement; pp. 13-14 (PDF pp. 13-14), Section 6 definitions; p. 29 (PDF
p. 29), proof. -/
theorem SAP.P003b.T26 : SAP.P003b.T26Statement := by sorry

/-- The printed claim is false: the literal binary search does not universally return the required
endpoint within the claimed evaluation count.
P003-T27; p. 20 (PDF p. 20); p. 21 (PDF p. 21). -/
theorem SAP.P003b.T27 : SAP.P003b.T27Statement := by sorry

/-- P003-T30; p. 7 (PDF p. 7); Appendix A.1, pp. 18-19.
In a positive balanced design the possible vector (0,n11+n00,n10+n01,0)
has effect equal to the observed Neyman estimate and exact p-value one.
The explicit table obtained by imputing the complement of each observed
outcome is possible and has exactly these counts, effect and p-value.
Thus the estimate belongs to K and I, K is nonempty, and its genuine
endpoints satisfy L <= T <= U. -/
theorem SAP.P003b.T30 : SAP.P003b.T30WholeStatement := by sorry

/-- Whenever the accepted set is nonempty and both arms are positive, the exact interval satisfies the
printed square-root length bound.
P003-T31; p. 7 (PDF p. 7); proof in Appendix A.3, p. 19 (PDF p. 19). -/
theorem SAP.P003b.T31 : SAP.P003b.T31Statement := by sorry

/-- The balanced permutation p-value increases under the stated discordance-to-concordance update.
P003-T33; p. 8 (PDF p. 8); proof in Appendix B.3, pp. 21-25 (PDF pp. 21-25). -/
theorem SAP.P003b.T33 : SAP.P003b.T33Statement := by sorry

/-- pp. 27–28 (PDF pp. 27–28), corrected Lemma B.15 and its corrected proof.
For every fixed binary table in a positive balanced design, fresh independent
Monte Carlo batches give each of the two stated interval inclusions with probability
at least 1−2D exp(−2K ε²), the second when α−2ε>0. Each endpoint obeys the
midpoint/zero-query decomposition of D. Given every positive-mass preceding history,
the performed indicator and selected table are fixed, the current batch is iid uniform,
and both one-test errors have probability at most exp(−2K ε²). Each endpoint's
bad-event probability is at most D exp(−2K ε²). Absence of the corresponding errors
gives all four deterministic upper/lower comparisons. The inclusion bounds hold
conditionally on the observed counts and jointly over randomization and the draws. -/
theorem SAP.P003b.T7 : SAP.P003b.T7WholeStatement := by sorry

/-- p. 8 (PDF p. 8), Theorem 4.1; Appendix B.2, p. 21.
The corrected sentinel searches construct both exact balanced endpoints with at most
4 n log₂ n tests for n ≥ 15. The actual oracle is equivalent to existence of a
possible accepted table; on the upper search domain its accepted effects form the
initial segment ending at n U. Nonzero queries use at most n+1 tests, zero queries
at most 2(n+1), and each endpoint obeys D at every positive balanced size.
The standalone inequality 2D ≤ 4 n log₂ n holds for every integer n ≥ 15. -/
theorem SAP.P003b.T32 : SAP.P003b.T32WholeStatement := by sorry

/-- The corrected balanced Monte Carlo interval has the printed coverage and exact-interval inclusion
probability bounds.
P003-T34; p. 9 (PDF p. 9); proof in Appendix B.5, pp. 27-28 (PDF pp. 27-28). -/
theorem SAP.P003b.T34 : SAP.P003b.T34Statement := by sorry

/-- pp. 27–28 (PDF pp. 27–28), printed proof of Lemma B.15.
The printed intermediate event identities, the resulting two probability equalities,
and aggregate estimate are false: the stated n=30,m=15 data have positive probability,
candidate numerators −14,…,16 and printed search domain 2,…,16, and 896 distinct
possible count vectors. Both exact intervals are [−1/5,1/3]. The full candidate
lists, individual p-values, exact and A/B/D transcripts, positive path probabilities,
four rounded event probabilities and the K=5000 aggregate counterexample all hold.
These counterexamples concern the intermediate proof assertions. -/
theorem SAP.P003b.T6 : SAP.P003b.T6WholeStatement := by sorry

/-- p. 13 (PDF p. 13), Theorem 5.5(1); Appendix C, p. 28; literal Algorithm 5.3.
The printed claim is false: take n=2,m=1, true counts (0,1,1,0), α=1/4,
any positive K, θ the indicator of that true vector, and R identically zero.
Every rank equals one. The two observations each have probability 1/2; the literal
schedule omits the possible true vector on the all-zero observation and includes it
on the all-one observation. Thus joint coverage is exactly 1/2 < 3/4. -/
theorem SAP.P003b.T35 : SAP.P003b.T35WholeStatement := by sorry

/-- P003-T36; p. 13 (PDF p. 13), Theorem 5.5(2); Appendix C, p. 28.
Algorithm 5.3 has arithmetic cost O(K n^3) under the paper's constant-cost
estimand/statistic and linear-cost fresh-draw model. The B.2-B.3 selector
implements its feasible minimum with constant-size arithmetic, and its reuse
interval enumerates exactly the legal updates. Both the literal first-feasible-j
loop and the full-j loop have at most (n+1)^2 K draws and (n+1)^2 n K updates.
Their nonnegative charged costs lie below the explicit envelope and a single
constant times K n^3, uniformly for positive n,K. The order bound holds jointly
and along every eventually positive K(n), including fixed positive K. -/
theorem SAP.P003b.T36 : SAP.P003b.T36WholeStatement := by sorry

/-- p. 13 (PDF p. 13), corrected Remark 5.7; compare pp. 4 and 9, (1.6), (4.9).
For fixed positive tolerance the balanced arithmetic cost is O(n² log² n), with the
stated finite operation and draw bounds, O(n log² n) draws, and the (1.6) envelope.
The general arithmetic cost is uniformly O(K n³). The dyadic full-shuffle family
has the positive-probability and expected quadratic lower bounds and exceeds every
linear-polylogarithmic expected bound. For n ≥ 15 the printed budget is conservative. -/
theorem SAP.P003b.T18 : SAP.P003b.T18WholeStatement := by sorry

