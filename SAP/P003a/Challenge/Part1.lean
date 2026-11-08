import SAP.P003a.Defs
import SAP.P003a.Defs.WholeW1
import SAP.P003a.Defs.WholeW2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P003-T29; p. 7 (PDF p. 7); proof in Appendix A.2, p. 19 (PDF p. 19).
Exact finite randomization inversion covers the population effect with probability at least one minus
the level. -/
theorem SAP.P003a.T29 : SAP.P003a.T29Statement := by sorry

/-- P003-T1; Section 6, pp. 13-14 (PDF pp. 13-14); Appendix D, p. 29.
The printed claim is false: the specified binary twenty-unit population,
three-treated uniform design and assignment-dependent single missing entry
have imputation coverage 297/380, below 1-109/500 by 1/2375. The labeled
critical assignment, its two completions and real intervals refute (D.3);
both actual tails in (D.7) are 83/380, above alpha despite (D.5). Among tables
possible for the upper completion with effect at least -3/20, the maximum
p-value is 248/1140, attained at (8,0,3,9) and (9,0,3,8).
All ten complete-data groups, their multiplicities, intervals and coverage
bits are explicit; the other 1139 assignments retain the complete interval,
whose overall coverage is 892/1140. -/
theorem SAP.P003a.T1 : SAP.P003a.T1WholeStatement := by sorry

/-- P003-T2; p. 14 (PDF p. 14), statement; p. 29 (PDF p. 29), proof.
Balanced designs allow arbitrary dependent missingness, completion inclusion and coverage, with the full
possibility-preserving plus coupling. -/
theorem SAP.P003a.T2 : SAP.P003a.T2Statement := by sorry

/-- P003-T3; p. 14 (PDF p. 14), statement; p. 29 (PDF p. 29), (D.1)-(D.2).
For arbitrary allocation, the completion union and its interval hull have the claimed joint-law
coverage, with the finite completion count and repaired numerical example. -/
theorem SAP.P003a.T3 : SAP.P003a.T3Statement := by sorry

/-- P003-T4; p. 20 (PDF p. 20); Algorithm 4.3, p. 8; proof, p. 21.
The printed claim is false: on [1,2] the literal search queries [1,1] and
returns the wrong all-accept threshold, while all-reject repeats query one
forever, exceeding the printed three-evaluation budget. In the legal balanced
sixteen-unit example its upper endpoint is 14/16 instead of 15/16. The lattice,
first tests, 144 possible vectors, 12870 assignments and two-atom estimator law
are explicit. Three further balanced inputs violate the printed search domain. -/
theorem SAP.P003a.T4 : SAP.P003a.T4WholeStatement := by sorry

/-- P003-T5; p. 20 (PDF p. 20); used on p. 8 (PDF p. 8) and p. 21 (PDF p. 21).
The corrected sentinel search has interior, valid, distinct queries, preserves the
threshold brackets and returns the threshold. For arbitrary chronological replies
it reaches adjacency before exhausting fuel and uses at most floor(log2 d)+1
queries, hence satisfies the printed weaker bound. In a positive balanced design
the upper and lower domains have at most n+1 points. Under the stated per-query
permutation-test costs each endpoint uses at most (n+1)(floor(log2(n+1))+2)
tests, at most the printed relaxed budget, and both use at most 4 n log2 n for n≥15. -/
theorem SAP.P003a.T5 : SAP.P003a.T5WholeStatement := by sorry

/-- P003-T11; p. 19 (PDF p. 19).
The printed claim is false: in every legal experiment and at every interior level,
the rejecting real thresholds form the open half-line above the largest support
point with tail at least alpha, and have no smallest element. For n=2, m=1 and
the all-zero table the effect and both estimates are zero, and the tail is one
on x≤0 and zero on x>0, giving the explicit rejecting half-line (0,infinity). -/
theorem SAP.P003a.T11 : SAP.P003a.T11WholeStatement := by sorry

/-- P003-T12; p. 19 (PDF p. 19).
For every finitely supported real probability law the probability of a tail
p-value strictly below an interior alpha is strictly below alpha. In a legal
experiment the rejecting attained deviations are either absent or have a least
point x; rejection is exactly D≥x and has probability q(x)<alpha. The true
table is possible at every observation and is accepted on nonrejection, putting
its effect in the accepted set and its interval hull. Consequently exact
randomization inversion covers with probability at least one minus alpha. -/
theorem SAP.P003a.T12 : SAP.P003a.T12WholeStatement := by sorry

/-- P003-T13; p. 11 (PDF p. 11).
The treatment effect equals the difference of discordant counts divided by population size, and both
printed-numerator witnesses disagree. -/
theorem SAP.P003a.T13 : SAP.P003a.T13Statement := by sorry

