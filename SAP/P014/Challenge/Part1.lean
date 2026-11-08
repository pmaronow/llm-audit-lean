import SAP.P014.Defs
import SAP.P014.Defs.WholeW1

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

/-- P014-T1, p. 131 (PDF p. 4), assumptions p. 130: the specified six-row
design satisfies the printed and intended local conditions but has expectation
zero and printed target -1/18, while the weighted target is zero. -/
theorem SAP.P014.T1 : SAP.P014.T1Statement := by sorry

/-- P014-T2, p. 131 (PDF p. 4), assumptions p. 130: with a fixed interior
treated count and common propensities, probability-weighted own-arm averages
are conditional expectations with positive denominators, and the unchanged
difference in means is unbiased for their bracketed window contrast. All four
displayed derivation steps hold. Corrected uniform local score arrangements
imply these hypotheses and this identity for arbitrary potential outcomes,
with the outside allocation and its dependence unrestricted. -/
theorem SAP.P014.T2 : SAP.P014.T2WholeStatement := by sorry

/-- P014-T3, p. 131 (PDF p. 4): conditional uniformity repairs the printed
target, full assignment uniformity suffices, uniform local score permutations
with fixed outside treatments give the uniform law on the choose(n,m) full
assignments with exactly m treated window subjects, no interference is an
alternative, and agreement of the own-arm averages for every outcome function
forces that own-arm conditional law to be uniform. -/
theorem SAP.P014.T3 : SAP.P014.T3Statement.{u} := by sorry

/-- The printed claim is false: P014-T4, pp. 129–131 (PDF pp. 2–4), is refuted
by the explicit design satisfying the printed clauses and equiprobable local
permutations, with positive arm probabilities, expectation zero and target -1/18. -/
theorem SAP.P014.T4 : SAP.P014.T4Statement := by sorry

/-- P014-T5, p. 130 (PDF p. 3): the specified six-row law satisfies the formal
printed clauses but has nonuniform local permutations, unequal propensities,
and a no-interference example with expectation 1/6 and printed target 1/3. -/
theorem SAP.P014.T5 : SAP.P014.T5Statement := by sorry

/-- P014-T6, p. 130 (PDF p. 3): uniform local score arrangements give fixed
interior treatment counts, common propensities, fixed window membership, the
stated empirical CDF and no distinct-subject ties. Adding discreteness and the
printed full-vector mass clause forces exactly one full supported vector per
local arrangement and makes the outside scores an almost surely deterministic
function of that arrangement. Conversely such an outside function gives n!
full support points of mass 1/n!. The specified independent outside example
has twelve points, six of mass 1/18 and six of mass 1/9, and satisfies the
correction while failing the printed full-vector mass clause. -/
theorem SAP.P014.T6 : SAP.P014.T6WholeStatement := by sorry

/-- P014-T7, p. 130 (PDF p. 3): the literal no-ties quantifier holds exactly
for an empty window, differs from the corrected one only on the diagonal, and
the corrected condition holds under corrected local randomization and in all
three specified counterexample designs. -/
theorem SAP.P014.T7 : SAP.P014.T7Statement.{u} := by sorry

/-- P014-T8, p. 131 (PDF p. 4): the bracketed window mean of differences is
the difference of the two sums divided by the nonzero window size. -/
theorem SAP.P014.T8 : SAP.P014.T8Statement := by sorry

/-- P014-T9, pp. 129 and 131 (PDF pp. 2 and 4): the specified comparison
design satisfies local randomization, but its printed target -1/9 differs from
both signs of the Hudgens–Halloran average 1/12, and its estimator bias is 1/36. -/
theorem SAP.P014.T9 : SAP.P014.T9Statement := by sorry

/-- P014-T10, pp. 129 and 131 (PDF pp. 2 and 4): probability-weighted own-arm
averages equal the conditional sum over the other subjects, the corrected
target and estimator use the reverse direct-effect sign, and the printed
averages and target fail these identifications in the specified example. -/
theorem SAP.P014.T10 : SAP.P014.T10Statement := by sorry
