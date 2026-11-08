import SAP.P009a.Defs.WholeW4
import SAP.P009a.Defs.WholeW2
import SAP.P009a.Defs.WholeW3
import SAP.P009a.Defs.WholeW1
import SAP.P009a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/--
P009-T10. p. 688 (PDF p. 16), first paragraph before Proposition 5, corrected sentence.
For every growing sequence of complete-randomization experiments with 0 < m < n
and eventually bounded average interference, there are exceptional sets E_n of
zero-dependence ordered pairs N₀ whose fraction |E_n|/|N₀| tends to zero. The
maximum mixing coefficient on N₀ minus E_n tends to zero, equivalently the
coefficients there become uniformly small. The denominator and the maximum's
index set are nonempty eventually, without assumptions on initial pair sets.
Exceptions cannot always be empty: a regular sequence with n = 4r+2 and d_AVG < 3
has the fixed pair of units 1 and 2 in N₀ with mixing coefficient 1/4 throughout.
-/
theorem SAP.P009a.T10 : SAP.P009a.T10WholeStatement := by sorry

/--
P009-T11. Section 6.1, p. 691, discussion of Proposition 7.
Under uniform q>=4 regularity, independent Bernoulli assignment and restricted interference,
d_AVG/C1 tending to infinity need not make B2 eventually largest in absolute value among
tau_MSQ/d_AVG, B1 and B2.
This refutes only that reading of the printed dominance guidance.
Restricted: Only the failure of guaranteed eventual largest-in-absolute-value dominance is asserted,
for sequences with uniform q>=4 regularity, independent Bernoulli assignment, restricted
interference, and d_AVG/C1 tending to infinity. The specified square-size m-block fair-Bernoulli
witness and its full outcome schedule are not stated. Omitted witness clauses are: the full-cube
[0,2] bounds and regularity at every moment order; the exact interference and dependence graphs,
C1=2, d_AVG=m=sqrt(n), the ratio m/2 and its divergence, and Assumption 2 for that family; the
expected direct effects all equal to 1, tau_MSQ=1 and tau_MSQ/d_AVG=1/m; the xi and weighted-xi
formulas, reciprocal products and B1=2/m^2>0; the arm-independent conditional covariances, their
alternating-sum cancellations and B2=0; the comparison 0=B2<B1<=tau_MSQ/d_AVG with equality of the
last two terms exactly at m=2; and the extension to every n>=4 with its floor-defined blocks,
isolated units, and exact C1, d_AVG, tau_MSQ, B1 and B2 formulas. The printed big-O bounds and
Proposition 7 are not refuted.
-/
theorem SAP.P009a.T11 : SAP.P009a.T11WholeStatement := by sorry

/--
P009-T12. Section 6.1, p. 691, corrected discussion of Proposition 7.
The finite bounds on B1, B2 and the mean squared effect imply vanishing of the first two
normalized terms when average dependence dominates average outgoing interference, while B2
stays bounded. No positive lower bound on B2 follows: a regular restricted-interference
sequence has B2 zero and both other terms positive. The additional ratio condition implies
relative dominance and the reciprocal limit on its nonzero-denominator domain; an eventual
positive lower bound on the magnitude of B2 suffices for that condition.
-/
theorem SAP.P009a.T12 : SAP.P009a.T12WholeStatement := by sorry

/--
P009-T13. Section 6.1, p. 691, discussion of direct spillovers.
The printed claim is false: in the stated fair three-unit experiment all absolute outcomes
are at most one and regularity holds at every moment order. Changing the first treatment
changes the second outcome by 2 z3 minus 1, always nonzero. Both expected spillovers and the
weighted expected spillover nevertheless vanish, refuting the direct-interference implication.
-/
theorem SAP.P009a.T13 : SAP.P009a.T13WholeStatement := by sorry

/--
P009-T14. Section 6.1, p. 691, discussion of Proposition 7.
Absence of direct interference forces pointwise and expected spillovers to vanish, and a
nonzero expected weighted spillover implies interference. The converse fails in the explicit
three-unit cancellation design. With no interference all off-diagonal expected spillovers and
B1 vanish, on the positive-size and positive-arm-probability domain of its conditional means.
-/
theorem SAP.P009a.T14 : SAP.P009a.T14WholeStatement := by sorry

/--
P009-T15. Supplement A, p. 23, proof of Lemma A23, first display.
The printed diagonal-omission bound fails for every positive size in the fair identity-outcome
family. It satisfies regularity and the three asymptotic restrictions. Interference and
dependence are diagonal, the covariance and mixing entries are one quarter on the diagonal
and zero elsewhere, and both average mixing coefficients vanish exactly. The normalized full
sum and arm-size variance equal 1/n, while the off-diagonal mixing sum is zero. At n=4 the
claimed inequality would be one quarter at most zero.
-/
theorem SAP.P009a.T15 : SAP.P009a.T15WholeStatement := by sorry

/--
P009-T16. Supplement A, p. 23, proof of Lemma A23, first display, corrected.
For every design, arm and positive k, every joint assignment probability difference is bounded
term by term by alpha, including the diagonal. Alpha lies in [0,1/4]. The full-pair mixing sum
bounds the covariance sum and is bounded by k² d_AVG/n plus the nondependent mixing remainder.
Self-dependence, the sum defining d_AVG, and the equivalent off-diagonal formula with the
diagonal Bernoulli variances restored are included. The sample size is positive.
-/
theorem SAP.P009a.T16 : SAP.P009a.T16WholeStatement := by sorry

/--
P009-T17. Supplement A, p. 10, proof of Lemma A12; Definition A3, p. 9.
The two printed hypergeometric laws and the printed likelihood-ratio identity are false:
T_i counts only other interfering units, whose number is incoming(i)-1. Under complete
randomization of two of four units, y₁(v)=v₁+v₂ and yⱼ(v)=vⱼ otherwise give incoming(1)=2,
T₁=Z₂, the full true and printed probability tables at t=0,1,2 for both conditioning arms,
true ratio 4/3 versus printed ratio 2, and true ratio-minus-one 1/3 versus printed right side 1.
The second instance has yⱼ(v)=vⱼ, incoming(i)=1 and T_i=0 surely, but printed zero-count
probability 1/2. Both designs, all marginals, regularity and positive ratio denominators are
certified. The inequality of Lemma A12 is not refuted.
-/
theorem SAP.P009a.T17 : SAP.P009a.T17WholeStatement := by sorry

