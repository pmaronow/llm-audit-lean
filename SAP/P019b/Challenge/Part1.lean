import SAP.P019b.Defs
import SAP.P019b.Defs.WholeW1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P019-T12; Proposition 3, p. 50 (PDF p. 8), and Section 5.3, p. 56
(PDF p. 14): Assumptions 1–3 and defined confessor cells give beta = 1.
With Assumption 4, the studentized estimator tends to a standard normal and
the printed two-sided p-value is asymptotically uniform, for every fixed
completion of undefined sample quantities. Usual measure-theoretic conditions
are assumed; the underlying probability space is arbitrary. -/
theorem SAP.P019b.T12 : SAP.P019b.T12WholeStatement := by sorry

/-- P019-T13; Table A1, p. 61 (PDF p. 19), and Section 5.2, p. 54
(PDF p. 12): the two CNN worlds have independent type, baseline and assignment,
satisfy Assumptions 1–4 for reading-or-watching, and share the complete observable
law, with the stated cell and atom tables, moments, contrasts and placebos.
Watching prevalence is 1/4 versus 1/2; all answers are truthful in A, whereas
the reader-only class becomes withholding watchers in B. Thus no function of
the observable law identifies watching throughout these worlds. Usual
measure-theoretic conditions are assumed (automatic for this finite witness). -/
theorem SAP.P019b.T13 : SAP.P019b.T13WholeStatement := by sorry

/-- P019-T14; Table A1, p. 61 (PDF p. 19), Section 5.2, p. 54 (PDF p. 12),
and Tables 3 and 6, pp. 54,56: truthful CNN questions identify reading-or-watching,
with excess over watching equal to the reader-only share, while both placebo restrictions hold.
Restricted to finite underlying probability spaces with arbitrary real atom masses
and pointwise truthful identities Y = Q and X = R or Q; the extension to arbitrary
measurable spaces with almost-sure truthful identities is not stated. -/
theorem SAP.P019b.T14 : SAP.P019b.T14Statement := by sorry

/-- P019-T15; supplement Appendix D, pp. 3–4, Figure A2, and Proposition 4,
p. 51 (PDF p. 9): corrected normal planning power includes both tails, the missing
tail lies in (0, alpha/2] with equality exactly at the null, and the N = 100 null
example has one-tail power 1/40 and two-tail power 1/20. -/
theorem SAP.P019b.T15 : SAP.P019b.T15Statement := by sorry

/-- P019-T16; supplement Appendix C, pp. 2–3, Figure A1, and Section 4.1,
pp. 50–51 (PDF pp. 8–9): the printed ceiling mechanism has population contrast
1 - (16/625) times the independently mixed affected share.
Restricted to this population contrast for a Binomial(4,2/5) baseline and independent
affected status; omits the liar and false-confessor response rules, all rejection
probabilities (including the approximately 80% and 30% examples), and all plotted
finite-sample power curves and their dependence on sample size or violation share. -/
theorem SAP.P019b.T16 : SAP.P019b.T16Statement := by sorry

/-- P019-T17; Lemma 1, pp. 47–48 (PDF pp. 5–6): under Assumptions 1–4
the combined functional identifies prevalence. Under Assumptions 2–4 its
excess is the false-confession mass, equal to Pr(Y=1)(1-E[X|Y=1]); failure
of almost-sure monotonicity is equivalent to positive false-confession mass
and to E[X|Y=1] < 1, and gives strict overestimation. Usual measure-theoretic
conditions are assumed; the underlying probability space is arbitrary. -/
theorem SAP.P019b.T17 : SAP.P019b.T17WholeStatement := by sorry

/-- P019-T18; Proposition 1, p. 49 (PDF p. 7), Appendix B.1, p. 63 (PDF p. 21):
under the maintained Assumptions 1–4, n times the actual variance of the combined
estimator converges to equation (3), for every fixed real empty-cell completion.
Restricted to iid draws on a finite underlying probability space with arbitrary
real atom masses; the theorem does not state the extension to arbitrary measurable
underlying spaces with bounded list counts. -/
theorem SAP.P019b.T18 : SAP.P019b.T18Statement := by sorry

/-- P019-T19; text after Proposition 1 and Corollary 1, p. 49 (PDF p. 7):
under Assumptions 1–4 the combined estimator is root-n tight and asymptotically normal,
its plug-in variance is consistent, and its Wald intervals have limiting nominal coverage.
Empty means and deficient-cell variance estimates use arbitrary fixed real completions.
Restricted to iid draws on a finite underlying probability space with arbitrary
real atom masses; arbitrary measurable underlying spaces with bounded list counts
are omitted. -/
theorem SAP.P019b.T19 : SAP.P019b.T19Statement := by sorry

/-- P019-T20; Proposition 2, p. 49 (PDF p. 7): under Assumptions 1–4,
both scaled actual variance limits exist and the combined estimator's limit is strictly
smaller than the standard estimator's, for all fixed real empty-cell and empty-arm completions.
Restricted to iid draws on a finite underlying probability space with arbitrary real
atom masses; the two variance limits and strict comparison are not stated for arbitrary
measurable underlying spaces with bounded list counts. -/
theorem SAP.P019b.T20 : SAP.P019b.T20Statement := by sorry

/-- P019-T21; Section 4.1 and Proposition 3, p. 50 (PDF p. 8):
Assumptions 1–3 and defined confessor cells imply equality of the control
conditional law and the treated law shifted down by one. Consequently every
level-alpha test of that distributional null remains level-alpha under these
assumptions. Under Assumptions 1–4, beta = 1, the studentized estimator tends
to a standard normal, and the printed two-sided p-value is asymptotically
uniform, for every fixed completion. Usual measure-theoretic conditions are
assumed; the underlying probability space is arbitrary. -/
theorem SAP.P019b.T21 : SAP.P019b.T21WholeStatement := by sorry

/-- P019-T22; Proposition 4, p. 51 (PDF p. 9): Assumption 3 and positive
treatment arms give delta = 0; with Assumption 4, the studentized estimator has
a standard normal limit and the printed two-sided p-value is asymptotically
uniform for every fixed completion. Restricted to finite underlying probability
spaces with arbitrary real atom masses; the extension to arbitrary measurable
spaces, the general randomized causal-effect interpretation, and the positive
delayed-treatment design implication are not formalized. The additional finite
protocol shows failure of independence when assignment is disclosed before the
direct answer and only physical list display is delayed. This does not refute
the printed design assertion. Usual measure-theoretic conditions are automatic
for these finite models. -/
theorem SAP.P019b.T22 : SAP.P019b.T22WholeStatement := by sorry
