import SAP.P012b.Defs
import SAP.P012b.Defs.WholeW1
import SAP.P012b.Defs.WholeW2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P012-T13; Result 3, p. 155; corrected (A2), Appendix p. 160.
A recruiter with spare degree admits two compatible completions with distinct preferential recruitment and the corrected signed full sum, sharp bound and sole-child equality criterion, which also hold at any compatible private-leaf start. -/
theorem SAP.P012b.T13 : SAP.P012b.T13Statement := by sorry

/-- The printed claim is false: P012-T14; Definitions 1, 2 and 4,
p. 155 (PDF p. 3); Web Appendix 1, p. 1.
The four admissible examples A--D exhibit undefined printed quotients.
A and C have unique displayed compatible pairs; B has raw numerator -1/2
and denominator 1/2 and an empty recruitment average at every pair. Every
D graph is a dyad with three private leaves at vertex 2; all eight trait
assignments are compatible, and their trait sum gives h=-3/5,-1/3,-1/7 or
an undefined 0/0, while p=0. A and D have no whole-compatible-set h interval. -/
theorem SAP.P012b.T14 : SAP.P012b.T14WholeStatement := by sorry

/-- P012-T15; Definitions 1, 2 and 4, p. 155 (PDF p. 3);
Web Appendix 1, p. 1.
The denominator identities give the exact individual domains of h and p.
On admissible data the whole-compatible-set domains are exactly positive
sampled degree in each trait class for h and at least one nonseed for p.
Under each condition separately, unique attained endpoints give the smallest
containing interval. If the h condition fails no whole-set h region exists;
the h-defined-only set can be empty (example A), while p still has region {0}.
The hypotheses of Results 2 and 3 imply the respective domain conditions. -/
theorem SAP.P012b.T15 : SAP.P012b.T15WholeStatement := by sorry

/-- P012-T16; Web Appendix pp. 1-2, cooling schedule and display (2).
The corrected logarithmic schedule is positive, nonincreasing, strictly decreasing on its tail and tends to zero, while its depth series diverges for 0 ≤ D*ε ≤ 1; the two printed schedule defects are also certified. -/
theorem SAP.P012b.T16 : SAP.P012b.T16Statement := by sorry

/-- P012-T17; Appendix p. 160 (PDF p. 8), proof of Result 1;
Definition 3, p. 155.
Deleting unsampled vertices preserves compatibility with upper degree bounds.
Exact degrees survive precisely when there is no sampled-to-unsampled edge,
equivalently no unsampled vertex, equivalently the graph equals its induced
graph. The two seeds with one common unsampled neighbour have degrees (1,1)
but induced degrees (0,0); the edge-between-seeds comparison has both (1,1). -/
theorem SAP.P012b.T17 : SAP.P012b.T17WholeStatement := by sorry

/-- P012-T18; Appendix p. 160 (PDF p. 8), proof of Result 2;
p. 155 (PDF p. 3), after equation (2).
Homophily depends only on the displayed augmented graph and its traits,
including agreement of undefined partial values. Preferential recruitment
can change with the recruiter map alone or with entry order alone: on the
fixed four-vertex example the star, chain and reordered star histories give
the defined values -1/12, 1/6 and -1/3 respectively. -/
theorem SAP.P012b.T18 : SAP.P012b.T18WholeStatement := by sorry

/-- The printed claim is false: P012-T19; Web Appendix 2, pp. 2-3; kernel on Web Appendix p. 1.
The literal printed proposal mechanisms do not preserve compatibility for every execution from admissible compatible data. -/
theorem SAP.P012b.T19 : SAP.P012b.T19Statement := by sorry

/-- The printed claim is false: P012-T20; Table 1, p. 158; study totals, pp. 156-157.
No admissible shared study inputs with the reported totals can have all three printed homophily intervals, even allowing their four-decimal rounding tolerance. -/
theorem SAP.P012b.T20 : SAP.P012b.T20Statement := by sorry

/-- P012-T22; abstract p. 153, introduction p. 154,
and text after Result 3, pp. 155--156 (PDF pp. 1--4).
On the stated whole-set domain, joint point identification is equivalent
to zero spare degree and to every compatible graph being the undirected
recruitment graph with its observed traits. A same-trait private-leaf flip
witnesses h variation, with the exact positive edge-count difference.
Preferential recruitment alone is identified exactly when actual recruiters
have no spare degree. In the (1,2)-degree, (0,1)-trait example every graph
has one private leaf at vertex 2: p=0 and h is -1 or -1/3 according to its
trait. Thus the exact value sets are {0} and {-1,-1/3}, and the smallest
containing intervals are {0} and [-1,-1/3], with attained endpoints. -/
theorem SAP.P012b.T22 : SAP.P012b.T22WholeStatement := by sorry

/-- P012-T23; Figure 1 and caption, p. 156 (PDF p. 4).
For the five sampled vertices with degrees (5,4,3,3,2), recruitments
1 to 2, 2 to 3, 1 to 4, 2 to 5, and traits (1,1,1,0,1), the attained marginal
extrema are -5/8, 79/105, -11/80 and 49/120. Every compatible pair lies in
their rectangle inside [-1,1]^2. Some extremal augmented subgraphs are not
unique, even after renaming unsampled vertices. The stated recruitment degrees,
spare degrees, edge and stub counts, phi evaluations and individual preferential
summands hold. The listed trait-specific edge and stub counts use the displayed
coding (1,1,1,0,1). All arithmetic and statistical conclusions hold for every
strictly increasing recruitment time order. The extrema, bounds and nonuniqueness
conclusions hold for either coding of the binary traits; exchanging both labels
preserves compatibility and both defined statistics. -/
theorem SAP.P012b.T23 : SAP.P012b.T23WholeStatement := by sorry

