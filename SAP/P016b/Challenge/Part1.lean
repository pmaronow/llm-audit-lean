import SAP.P016b.Defs
import SAP.P016b.Defs.WholeW1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P016-T12; p. 397 (PDF p. 3), first paragraph, second and third sentences.
The mean contrast is effect increasing on nonempty groups, whereas both KS
statistics fail this directional condition. Every statistic calibrated under a
positive finite assignment law has valid inclusive upper, lower, and doubled
minimum tails, at weak and strict cutoffs. For the uniform two-of-four design
and outcomes (0,1,2,3), the KS scores are (1,1/2,1/2,1/2,1/2,1), the upper
p values are (1/3,1,1,1,1,1/3), and the rejection probabilities are 0, 1/3,
and 1 on the stated threshold ranges. -/
theorem SAP.P016b.T12 : SAP.P016b.T12WholeStatement := by sorry

/-- P016-T13; p. 400 (PDF p. 6), Section 2.2, and p. 397 (PDF p. 3),
validity parenthesis; archived simulation weak-cutoff rule.
Tie-free exchangeable scores have uniform ranks and raw weak-cutoff rejection
probability 2(c+1)/(B+1) whenever c=floor(alpha B/2) and 2c<B. At .05 the
sizes for B=1000 and 10000 exceed .05. In the uniform eight-of-sixteen design
with fixed outcomes 2^i, the SSR has the stated moment formula and 6435 values,
each on a complementary pair. Independent uniform observed and reference draws
give the exact binomial-mixture rejection laws and bounds, including every
positive B for the weak .05 rule. All five reported decimal prefixes are
certified by open rational intervals. The strict .05 sizes are below .05,
and raw p=0 has the stated positive power-sum probability. These witnesses
concern the archived weak cutoff; they do not refute the printed strict rule. -/
theorem SAP.P016b.T13 : SAP.P016b.T13WholeStatement := by sorry

/-- P016-T14; p. 400 (PDF p. 6), Section 2.2, and the validity parenthesis on
p. 397 (PDF p. 3).
Exchangeable references give rank bounds, the printed strict-cutoff guarantees,
valid corrected tails, and iid permutation invariance.
Exact-tail clause (e) uses the strictly positive finite-law domain of its explicit
reference to canonical T12(iii); the iid exchangeability clause permits zero-weight points. -/
theorem SAP.P016b.T14 : SAP.P016b.T14Statement := by sorry

/-- P016-T15; p. 398 (PDF p. 4), last paragraph; footnote 3, p. 396 (PDF p. 2);
and p. 400 (PDF p. 6), Section 2.2.
The specified adjustment, ECDF, and diagonal-hypothesis witnesses establish all
three local mathematical errors. -/
theorem SAP.P016b.T15 : SAP.P016b.T15Statement := by sorry

/-- P016-T16; p. 398 (PDF p. 4), last paragraph; footnote 3, p. 396
(PDF p. 2); p. 400 (PDF p. 6), Section 2.2, first paragraph.
Under additive and nonzero multiplicative hypotheses, control outcomes and
control empirical distributions stay fixed. Treated outcomes have the stated
parameter dependence, with nonzero response for the multiplicative comparison.
The sample ECDF counts observations at or below its argument. Empirical
distributions are asserted on their nonempty-sample domains. The joint family
with separate parameter indices contains the truth (1/2,2), which belongs to
no member of the printed diagonal family. -/
theorem SAP.P016b.T16 : SAP.P016b.T16WholeStatement := by sorry

/-- P016-T17; p. 397 (PDF p. 3), Section 2, first paragraph.
The corrected comparison uses two adjusted group means, whereas the conditional
imputed-treated reading gives the raw contrast, with the stated 2-versus-12 instance. -/
theorem SAP.P016b.T17 : SAP.P016b.T17Statement := by sorry

/-- P016-T18; p. 398 (PDF p. 4), last paragraph and Fig. 2; p. 399 (PDF p. 5),
first sentences; released calibration code.
The specified 256-unit witness attains the global minimum zero of the median
criterion despite 127 unmatched treated units and unequal generated and adjusted mean shifts. -/
theorem SAP.P016b.T18 : SAP.P016b.T18Statement := by sorry

/-- P016-T19; p. 398 (PDF p. 4), last paragraph and Fig. 2; p. 399 (PDF p. 5),
first sentences.
The median criterion sees only the least treated discrepancy, has the stated roots,
and does not match mean reductions, whose unique matching parameter is identified.
Restriction: retain mathematical clauses (a)–(f); omit the Normal-versus-Jittered-Geometric
empirical power ordering and numerical powers, including the four quoted in the repair,
the assertion that the actual simulation's two hypotheses have unequal expected adjusted
mean shifts, its sample-mean approximation 10.069, and its matched-parameter approximation
1.035312. These empirical assertions come from the canonical statement and definitions_needed.
The constructed witness in (f) does not assert a property of that simulated dataset.
The positive half-size makes the median and treated minimum defined; a ≠ 0 in
the inverse-adjustment comparisons (d)–(e) is their existing domain condition.
Recomputed powers and a revised calibration objective are recommendations, not proved conclusions. -/
theorem SAP.P016b.T19 : SAP.P016b.T19Statement := by sorry

/-- P016-T20; p. 396 (PDF p. 2), Section 1, steps (1)–(2); equation (3),
p. 399 (PDF p. 5).
The additive identity and all four network-mapping clauses recover assignment-independent
uniformity outcomes on the stated nonnegative-network and positive-multiplier domain. -/
theorem SAP.P016b.T20 : SAP.P016b.T20Statement := by sorry

/-- P016-T21; p. 400 (PDF p. 6), Section 2.2; Fig. 3 and caption, p. 401 (PDF p. 7).
At the stated true network parameters, adjustment recovers uniformity outcomes,
all three exact tails control rejection at .05, and fresh iid references give
the bounds 50/1001 and 500/10001 for the printed strict rule. -/
theorem SAP.P016b.T21 : SAP.P016b.T21Statement := by sorry
