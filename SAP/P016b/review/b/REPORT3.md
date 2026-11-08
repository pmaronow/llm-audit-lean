Revision 3 has **6 correct_whole and 4 correct_restricted** targets. There
are no remaining adverse findings, false statements or vacuous statements.

| Verdict | Count |
| --- | ---: |
| correct_whole | 6 |
| correct_restricted | 4 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity counts: none 10, minor 0, major 0. No target is omitted or labelled
`refuted`.

This review applies the current user's definition of the claim: canonical
`statement`, `definitions_needed` and standing assumptions. A historical
`note` or `finite_lemmas` entry cannot remove an assertion from that claim.
This resolves the earlier T19 scope dispute without relying on a different
workspace's brief or on the architect's account of it.

**Earlier findings.**

T19, the only target with adverse findings in my previous reports, is now
resolved. Each earlier issue was rechecked:

| Earlier issue | Status in revision 3 | Reason |
| --- | --- | --- |
| Round 1: empirical omissions described as restrictions; proposed relabelling as whole. Round 2: same scope objection. | Fixed/resolved by the current scope instruction | The empirical powers, ordering, actual-data mismatch and approximate matching parameter occur in the canonical statement; the sample mean occurs in definitions_needed. The note cannot exclude them. I withdraw the earlier request to label the theorem whole. |
| Round 1: `a ≠ 0` presented as a new restriction | Fixed in revision 2; remains fixed | The docstring calls it the existing domain condition inherited from (d)-(e), rather than a reason for restriction. Positive half-size is likewise described as ensuring the median and minimum are defined. |
| Round 2: the alleged precedence rule was unsupported by the supplied brief | Fixed/resolved by the current scope instruction | The user now states the rule explicitly. The current record no longer relies on the disputed brief citation. |
| Round 2: the broader reading also requires disclosure of the omitted actual-simulation unequal-mean-shift assertion | Fixed in revision 3 | Both the revised docstring and record identify that assertion separately. They also identify the omitted sample-mean approximation 10.069 and cover all simulation-specific powers. |

No earlier issue remains partly fixed or not fixed under the current
instruction. The other nine targets had no adverse findings in my previous
reports. T13's corrected explanation that complement equivalence retains
two-element fibers, and T14's whole label with inherited positivity, remain
accurate.

**Statement and label checks.**

I reread the six Defs parts and the Defs and Challenge roots, and compared
all ten propositions with `reading.md`. No mathematical change was found:
the objects, quantifier order, hypotheses, conjunctions, numerical witnesses
and conclusions still agree with the saved blind reading. The only changed
record entry since revision 2 is T19's restriction; its docstring now gives
the corresponding fuller disclosure. The architect's claims about hashes,
proof modules and external certification were not used to establish this
comparison.

| Target | Verdict | Coverage and disclosure |
| --- | --- | --- |
| T12 | correct_restricted | Mean monotonicity, both KS failures, exact validity, the p-value table and full rejection-probability formula remain. The absent raw KS score table is explicitly disclosed. |
| T13 | correct_restricted | The general tie-free law's added `0 ≤ α < 1` and five absent decimal approximations are disclosed. Exact mixture and zero-p formulas, comparisons with .05 and both numerical counterexamples remain. The complement equivalence retains the two-assignment fibers. |
| T14 | correct_whole | All clauses (a)-(e) remain. Clause (e)'s explicit reference to T12(iii) supplies the positive-weight domain. IID invariance still allows zero weights. |
| T15 | correct_whole | All three canonical local counterexample witnesses remain, including both adjusted vectors, the ECDF values and the diagonal characterization. |
| T16 | correct_restricted | All adjustment, parameter-dependence and joint-hypothesis corrections remain. Positive control-group size and positive whole-sample size are the disclosed guards. |
| T17 | correct_whole | The corrected comparison, conditional imputed-treated interpretation, general identities and 2-versus-12 example remain. |
| T18 | correct_whole | The specified constructed population, variance, coordinate discrepancies, median/global minimum and both kinds of mean shifts remain. The docstring describes the zero-criterion/unequal-shift witness without declaring the paper's qualitative prose false. |
| T19 | correct_restricted | All mathematical clauses (a)-(f) remain. Every omitted simulation-specific assertion is now disclosed, as detailed below. |
| T20 | correct_whole | The additive identities and every network clause (b1)-(b4) remain on the canonical domain. |
| T21 | correct_whole | Uniformity recovery, all three exact tails and both IID strict-cutoff guarantees remain. The canonical statement itself excludes the reported empirical null-rejection rates; this exclusion does not depend on its note. |

For T19, the revised
[docstring](/home/ubuntu/sap/tasks/CHFID-P016b-b/SAP/P016b/Challenge/Part1.lean:62)
and `record3.json` now disclose:

- The empirical Normal-versus-Jittered-Geometric power ordering and all
  simulation-specific numerical powers, including the four quoted in the
  repair.
- The assertion that the actual simulation's two hypotheses have unequal
  expected adjusted mean shifts.
- The actual-data sample-mean approximation 10.069 and matched-parameter
  approximation 1.035312.

The disclosure explicitly distinguishes the constructed witness in (f) from
the simulated dataset. Its parameter 495/478 is not offered as certification
of the simulated-data approximation. The mathematical adjustment target,
general matching formula and complete witness remain formalized.
Recomputing powers and redesigning the calibration objective are requests
in the quoted repair, not additional affirmative mathematical conclusions;
the docstring identifies them as recommendations. The restriction is now
accurate and complete.

The counterexample labels remain appropriate. T13, T15 and T18 assert the
counterexamples specified by their own canonical claims; they do not
contradict those claims. T13 identifies the archived weak-cutoff algorithm
and retains the distinction from the printed strict rule. T17 explicitly
conditions its diagnostic reading on interpreting the undefined treated
outcome as an imputed potential outcome. T18 identifies the precise failure
of treating a zero median criterion as a match of effects: its witness has
unequal generated and adjusted mean shifts. None states that the paper's
qualitative assertion is false. No `refuted` label is needed.

**Nonvacuity and junk values.**

No new mathematical domain was introduced. The earlier explicit instances
therefore still apply. In particular:

- T13's tie-free exchangeability assumptions are realized by the uniform
  law on all coordinate permutations of the distinct real vector
  (0,...,B), for every B>0, including 1000 and 10000. The finite design is
  nonempty and its RSS fibers contain the assignment and its distinct
  complement.
- T14 admits the Dirac law at a constant reference vector and the
  nonconstant permutation law. Its IID clause permits zero weights; its
  exact-tail clause admits a strictly positive uniform finite law.
- T19 has the nondegenerate example m=2, y=(1,2,3,4), z=0011, t=1 and
  treated coordinate j=2. At the root a=4/3 the overall median discrepancy
  is zero while the other treated discrepancy is 1/3; the matched-mean
  parameter is 5/3. The full 256-unit witness is a second concrete
  instance, with 127 unmatched treated units.

Positive half-size puts both median positions in bounds, makes the treated
minimum a nonempty finite minimum, and makes the balanced-design averaging
domain nonempty. Inverse adjustments use a nonzero multiplicative parameter;
network multipliers are positive. All reference-count denominators are
positive where used, count events are Borel and probability measures are
finite. The binomial exponents have k ≤ c < B, and the fixed strict-cutoff
indices B/40-1 do not truncate improperly. No empty-type, total-division,
infinite-measure or conclusion-assuming hypothesis was found to do the work.

The existing `scratch/Check.lean` compiled against the refreshed Defs
through the authorized `sap-lean` wrapper with exit code 0 and no output.
Only one Lean process was used. It imports Defs only and covers
the balanced-assignment cardinality, genuine uniform weights, nonempty
groups, both KS failures, nonzero parameter domains, a symmetric binary
network, an exchangeable probability instance and injective reference
vectors. Per-target nonvacuity details are retained in `findings3.json`.

The new JSON uses the original schema and covers every target exactly once.
The previous readings and reports, canonical claims, records and Lean
sources were left unchanged. No external architect workspace or Solution
module was read.
