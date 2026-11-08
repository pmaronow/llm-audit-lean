import SAP.P012a.Defs
import SAP.P012a.Defs.WholeW1
import SAP.P012a.Defs.WholeW2

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P012a

/-- The printed claim is false: P012-T1; Web Appendix pp. 2–3
(supplement PDF pp. 2–3); the kernel K: Web Appendix p. 1; augmented graphs
and Definition 3: p. 155 (PDF p. 3).
All four specified counterexamples hold, including their functional values.
In (a) and (b), for the fixed chosen i,j and either coin outcome, every execution
uses a fresh vertex of either trait and produces exactly the stated old graph
with the removed sampled edge replaced by a sampled–fresh edge and an
old-unsampled–fresh edge. Cleanup deletes nothing. The old unsampled vertex
has no sampled neighbour; the output is incompatible, while conditions 1,2,4
remain true in (a). Every fresh name gives the named output up to renaming
unsampled identities. In (c) both branches fail and cleanup deletes precisely
sampled seed 3, violating vertex preservation and inclusion of the observed
active trait assignment. In (d) every compatible pair is the displayed dyad
on its active domain, so the trait proposal has no vertex to choose.
-/
theorem SAP.P012a.T1 : SAP.P012a.T1WholeStatement := by sorry

/-- P012-T2; Web Appendix pp. 2–3 (supplement PDF pp. 2–3).
Every execution of either corrected mechanism preserves compatibility. In the
unsampled deletion branch exactly one sampled degree is restored, and cleanup
deletes the old unsampled endpoint exactly when its only neighbour was the
selected sampled vertex. In the sampled deletion branch both degrees are
restored and the original second replacement pool remains nonadjacent. In the
addition branch the second endpoint is sampled, two distinct non-recruitment
edges are removed even for a shared unsampled endpoint, both sampled degrees
are restored, and cleanup deletes exactly the selected vertices left isolated.
If neither branch applies the state is unchanged. Recruitment edges, sampled
vertices and traits, and the augmented graph rules are preserved throughout
the returned states. The trait mechanism flips one unsampled trait or returns
the same state when the unsampled set is empty.
-/
theorem SAP.P012a.T2 : SAP.P012a.T2WholeStatement := by sorry

/-- The printed claim is false: P012-T3; Table 1: p. 158 (PDF p. 6);
network counts and seeds: p. 156 (PDF p. 4); bounds: pp. 156–157 (PDF pp. 4–5);
Definitions 3–4: p. 155 (PDF p. 3).
For every admissible data set with 527 sampled vertices, six seeds and sampled
degree total 4487, the opposite-trait private-leaf completion is compatible,
has 521 recruitment edges, 3445 private degree-one leaves and 3972 vertices,
and has positive equation-(1) denominator. Its edge counts and quotient value
obey the uniform real bound -1462/1983 and the sharp integer bound
-178409/241987, attained by the two stated integer triples. The displayed
polynomial certificate is nonnegative. All three printed lower bounds are
violated, with the exact stated gaps exceeding four-decimal rounding error;
even a rounded lower endpoint cannot enclose every compatible homophily value.
The larger completion is allowed because compatibility fixes no population size.
-/
theorem SAP.P012a.T3 : SAP.P012a.T3WholeStatement := by sorry

/-- P012-T4; Table 1: p. 158 (PDF p. 6); network counts: p. 156 (PDF p. 4).
The true lower endpoint obeys both certified bounds and all three gap bounds, and printed endpoints force a degree discrepancy with the nomination network.
-/
theorem SAP.P012a.T4 : T4Statement := by sorry

/-- P012-T5; Table 1: p. 158 (PDF p. 6); network counts: p. 156 (PDF p. 4); the computation described: pp. 156–157 (PDF pp. 4–5).
The opposite-trait leaf completion attains the exact lower homophily endpoint on its stated domain.
Restriction: Retains the exact symbolic attained lower limit, its quotient formula, the lower bound on every defined compatible value, and both uniform bounds under the published totals. Omits the assertion about which recruitment-edge count triples the published paper reports and their recoverability from the paper.
-/
theorem SAP.P012a.T5 : T5Statement := by sorry

/-- P012-T6; Web Appendix p. 1 (supplement PDF p. 1);
Definitions 1, 3 and 4: p. 155 (PDF p. 3).
For admissible observed data with positive sampled degree total in each trait
group, every compatible graph has the positive displayed denominator and the
displayed edge-count and homophily bounds. Opposite-trait and same-trait private
degree-one leaf completions attain the bounds, so their endpoints give the
smallest containing interval. An explicit algorithm scans each sampled-vertex
record and each directed recruitment-edge record once, in any order within
each stream, accumulating the two degree totals and three edge-type counts.
It recovers the spare totals without truncated subtraction and returns the
two exact rational endpoints. The instrumented scan has exactly n+|E_R| visits
and accumulator additions, followed by 26 arithmetic operations, with indexed
trait/degree/parent access and unit-cost exact arithmetic.
-/
theorem SAP.P012a.T6 : SAP.P012a.T6WholeStatement := by sorry

/-- P012-T7; Web Appendix p. 1 (supplement PDF p. 1); Definitions 2–4:
p. 155 (PDF p. 3).
The observed recruitment history and spare degrees give the sharp attained
preferential-recruitment interval. Obligatory child sets are nonempty; every
compatible susceptible fraction has the stated decomposition and sharp bounds.
Same-trait private degree-one neighbours attain p_min, and opposite-trait
private degree-one neighbours attain p_max. The smallest containing interval
is [p_min,p_max]. An exact rational forward algorithm computes
both endpoints in one pass over the supplied chronological records, with positive
event denominators, one read per record, at most n stored cells and at most 32n+4
unit arithmetic and indexed-cell operations, including the final divisions.
-/
theorem SAP.P012a.T7 : SAP.P012a.T7WholeStatement := by sorry

/-- The printed claim is false: P012-T8; Appendix, p. 160 (PDF p. 8); Result 1: p. 155 (PDF p. 3).
An allowed starting graph in the printed Result 1 proof yields an incompatible output with the same induced sampled graph.
-/
theorem SAP.P012a.T8 : T8Statement := by sorry

/-- The printed claim is false: P012-T9; Appendix, p. 160 (PDF p. 8);
Result 2: p. 155 (PDF p. 3).
The specified compatible starting pair has both cross edges already present.
The printed swap leaves degrees (2,2,2,1,1) instead of (3,2,3,2,2), and four
edges instead of six, so its output is incompatible. Its equation-(1)
denominator is 15/8, whereas the starting denominator is 35/12; both are positive
and unequal. This refutes the printed proof step.
-/
theorem SAP.P012a.T9 : SAP.P012a.T9WholeStatement := by sorry

/-- P012-T10; Result 1: p. 155 (PDF p. 3); corrected proof: Appendix,
p. 160 (PDF p. 8).
Two time-ordered sampled vertices not joined by a recruitment edge, each with
positive spare degree, give two distinct compatible augmented graphs and two
distinct compatible sampled induced graphs. The first graph has exactly one shared unsampled neighbour of
the two chosen vertices, s_i-1 and s_j-1 further private leaves there, and s_v
private leaves at every other sampled vertex. The shared vertex has exactly the
two chosen neighbours; every private leaf has degree one. For every binary
assignment extending the observed traits both graphs are compatible. The second
deletes precisely the shared vertex and its two edges, adds {i,j}, and keeps all
remaining traits. The induced edge sets are B and B union {{i,j}}. The graphs
remain distinct under every renaming of unsampled identities, so neither graph
is identified.
-/
theorem SAP.P012a.T10 : SAP.P012a.T10WholeStatement := by sorry

/-- P012-T11; Result 2: p. 155 (PDF p. 3); corrected proof and (A1):
Appendix, p. 160 (PDF p. 8).
Opposite-trait sampled vertices with spare degree make homophily not point
identified. Attach exactly s_v private degree-one neighbours to each sampled
vertex. Any selected private neighbours of the normalized trait-0 and trait-1
vertices can be assigned traits 0 and 1, with all other unsampled traits arbitrary.
The cross edges are absent and the swap is compatible and preserves vertices,
traits, all degrees and edge count. With Q the trait-weighted degree sum, both
denominators equal Q-Q^2/(2m)=Q(2m-Q)/(2m)>0, because Q≥d_j>0 and
2m-Q≥d_i>0. Both forms of (A1) give h_1-h_2=2/D≠0. The stated exact
two-subject instance has m=3, Q=3, D=3/2, h_1=1/3, h_2=-1 and difference 4/3.
-/
theorem SAP.P012a.T11 : SAP.P012a.T11WholeStatement := by sorry

/-- The printed claim is false: P012-T12; Appendix, p. 160 (PDF p. 8); Result 3: p. 155 (PDF p. 3).
The two-recruit witness has preferential-recruitment difference minus five twelfths, disagreeing with both printed (A2) right-hand sides.
-/
theorem SAP.P012a.T12 : T12Statement := by sorry

