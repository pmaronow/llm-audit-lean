import SAP.P044.Defs.WholeW1
import SAP.P044.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P044-T1; p. 217 (PDF p. 9), with the simulation recipe on pp. 212, 214, 216.
The exact rational twelve-unit, three-clique witness gives all stated counts,
exact-input moments, two finite-bank joint laws, and fixed-table shortfalls.
It refutes exact expected-variance dominance for these finite simulated inputs. -/
theorem SAP.P044.T1 : SAP.P044.T1Statement := by sorry

/-- P044-T2; p. 217 (PDF p. 9), with p. 213 (PDF p. 5).
Exact supported design inputs give precisely the structural-zero surplus and
conservative HT variance. Finite simulated inputs can fail under independent
and included observations, including 10000 distinct draws and first-draw reuse:
the exhaustive matching family supplies both joint laws. An exact transfer
identity gives a corrected inequality under bounds on the expected
variance-estimate error and the contrast-variance error. The usual
measure-theoretic conditions are assumed (all laws here are finite).
The Hajek sentence is a scope qualification: its linearized approximation and
reported numerical robustness supply no general finite-sample guarantee. -/
theorem SAP.P044.T2 : SAP.P044.T2WholeStatement := by sorry

/-- P044-T3; p. 212 (PDF p. 4), related p. 216 and Note 1, p. 221.
The nonisolated four-unit star under uniform complete assignment of two
treatments has the six stated exposure vectors and exact exposure probabilities.
The two schedules give identical observed data and effects zero and minus one,
so no statistic is unbiased under both. Every observed inverse-probability
term has a positive denominator; the means, contrast, and biases hold without
an extra positivity assumption. Usual measure-theoretic conditions are assumed. -/
theorem SAP.P044.T3 : SAP.P044.T3WholeStatement := by sorry

/-- P044-T4; pp. 212, 216 and Note 1, p. 221 (PDF pp. 4, 8, 13).
Positive exact exposure support gives HT unbiasedness, its failure prevents
unbiased estimation over all schedules, and common-support targets and complete
randomization have the stated corrected formulas and degree criteria. -/
theorem SAP.P044.T4 : SAP.P044.T4Statement := by sorry

/-- P044-T5; p. 216 and the calls on pp. 216-217 (PDF pp. 8-9).
Under the supplied ideal Gaussian generator model, the triangle calculations,
positive-probability negative baselines, different baseline law, and all stated
moments and shifts refute the absolute-standard-normal baseline description.
The connection from that model to the staged generator is external provenance. -/
theorem SAP.P044.T5 : SAP.P044.T5Statement := by sorry

/-- P044-T6; p. 216 (PDF p. 8), correction to the baseline generator description.
The independent Gaussian model has the corrected baseline moments, multiplier
effects, triangle effects, and population expectation and scale comparisons;
the averages whose integrals appear are integrable. -/
theorem SAP.P044.T6 : SAP.P044.T6Statement := by sorry

/-- P044-T7; p. 216, with pp. 212, 214 (PDF pp. 8, 4, 6).
The exhaustive eight-cycle bank has the stated base exposure vector, counts,
positive exact probabilities, smoothed weights, means, constant contrasts and
biases. Its four joint counts give returned entries 1/9 and 1/8 with row sum
17/72, inconsistent with the returned marginal 1/3; the exact joint row sums
to 1/4. Usual measure-theoretic conditions are assumed (finite laws). -/
theorem SAP.P044.T7 : SAP.P044.T7WholeStatement := by sorry

/-- P044-T8; p. 216, with pp. 212, 214 (PDF pp. 8, 4, 6).
Exhaustive counts give exact probabilities and the stated fixed-weight and
smoothed-weight expectations, bias multipliers and nonnormalization, while an
independent with-replacement binomial bank has the stated integrable expectation. -/
theorem SAP.P044.T8 : SAP.P044.T8Statement := by sorry

/-- P044-T9; pp. 210-211 (PDF pp. 2-3), corrected interference notation.
Ordered deletion and insertion reconstruct every treatment profile.
The corrected interference definition is the negation of no interference.
No interference is equivalent to invariance at fixed own treatment.
Row times column equals the treated-peer count, independent of own treatment
on a zero-diagonal network.
The printed pair of rows has incompatible dimensions when N exceeds one.
Exactly one printed product condition holds, selecting the label whose bits
are own treatment and the presence of a treated peer. No symmetry or absence
of isolates is required. Usual measure-theoretic conditions are assumed. -/
theorem SAP.P044.T9 : SAP.P044.T9WholeStatement := by sorry

/-- P044-T10; pp. 213-215 (PDF pp. 5-7), correction to the within-community share.
Identity-block cross probabilities vanish, zero crossing marginals exclude
crossing edges on finite-law support, and nonisolated within-community graph
laws have within-edge share and both expected ratios equal to one.
Restriction: the finite-law consequences assume zero crossing marginals or
explicit accepted-graph no-isolate and no-crossing conditions; no generator law
is constructed and these law hypotheses are not derived from the source-code
premise and rejection loop. -/
theorem SAP.P044.T10 : SAP.P044.T10Statement := by sorry

/-- The printed claim is false: at each supplied nonempty loopless Boolean
network, the ideal Gaussian generator's baseline laws cannot all be the
absolute-standard-normal law.
P044-T13; p. 216 and the calls on pp. 216-217 (PDF pp. 8-9).
Only the baseline-law conjunct is negated; the generator's source-code
identification remains external provenance. -/
theorem SAP.P044.T13 : SAP.P044.T13Statement := by sorry
