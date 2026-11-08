Ten targets were audited. No false or vacuous theorem was found. There is one
minor issue in the description of T19's scope; its mathematical statement
covers the whole canonical target.

| Verdict | Count |
| --- | ---: |
| correct_whole | 5 |
| correct_restricted | 4 |
| restriction_inaccurate | 1 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity counts: none 9, minor 1, major 0.

**P016-T19 — restriction_inaccurate, minor.**
[The theorem docstring](/home/ubuntu/sap/tasks/CHFID-P016b-b/SAP/P016b/Challenge/Part1.lean:63) and its record
entry label the omission of empirical power comparisons, quoted powers and
the simulated-data approximation 1.035312 as a restriction. The canonical
claim's own note explicitly excludes the powers and the simulated-data
mismatch assertion from the target. Its mathematical content is (a)-(f),
all of which [T19Statement](/home/ubuntu/sap/tasks/CHFID-P016b-b/SAP/P016b/Defs/Part5.lean:35) states. The
dataset-specific approximation is contextual; the mathematical witness uses
the exact matched value 495/478. Also, the nonzero multiplicative parameter
is already required by canonical (d), whose reductions appear in (e).
These are scope clarifications rather than losses of canonical content.

Change the record's T19 decision to `whole` with no restriction, and replace
the docstring's restriction paragraph with:

> All canonical mathematical clauses (a)-(f) are included. The half-size is
> positive so the median and treated minimum are defined, and inverse
> multiplicative adjustments use a != 0 as in clause (d). The empirical
> power comparisons, dataset-specific approximation 1.035312, recomputed
> powers and a redesigned calibration objective are outside this
> mathematical target.

The theorem needs no mathematical change. This finding preserves the
`whole` reading saved for T19 in step 2; reading the record did not change
any step-2 comparison.

The other record decisions agree with the audit:

| Target | Record decision | Assessment |
| --- | --- | --- |
| T12 | restricted | Accurate: the raw six-entry KS score table is not an explicit conjunct; the p-value table and complete size formula remain. |
| T13 | restricted | Accurate: the general law requires 0 <= alpha < 1; five decimal approximations and a separate two-element-fiber certificate are absent. The complement equivalence still implies two-element fibers, so this last item loses no mathematical content. |
| T14 | restricted | Accurate as a conservative full-support convention for generic exact-tail clause (e); the referenced T12(iii) already uses the same positivity premise. IID exchangeability still permits zero weights. |
| T15 | whole | All three local witnesses are present. |
| T16 | restricted | Accurate: positive control size and positive sample size exclude the stated empty-case extensions. |
| T17 | whole | The adjusted comparison, diagnostic interpretation and 2-versus-12 instance are present. |
| T18 | whole | The complete constructed calibration witness and global minimum claim are present. |
| T20 | whole | The additive identity and all four network-map clauses have the canonical domain. |
| T21 | whole | Uniformity recovery, all three exact tails and both IID strict-cutoff guarantees have the canonical scope. |

The blind readings were saved in `reading.md` before `claims.json` was
opened. `claim-stage.json` was saved before `record.json` was opened. No
step-2 verdict was revised after reading the record. There are no omitted
targets, so no omission justification is needed. The source Defs,
Challenge, claims and record files were left unchanged.

Nonvacuity evidence is recorded per target in `findings.json`.
`scratch/Check.lean` imports only `SAP.P016b.Defs`, not the Challenge or any
Solution. It checks the two nonempty-group KS failures, positive half-size
and parameter domains, the 256-unit balanced assignment, a genuine uniform
law with the required binomial weights, a symmetric binary network, an
exchangeable probability-law instance, and distinct-coordinate vectors of
every reference length. It was compiled using the authorized `sap-lean`
wrapper. Only one Lean process was run at a time.

An explicit nonvacuity instance for the exchangeable tie-free hypotheses
at every B is the uniform probability law on all permutations of the
distinct real vector (0,...,B). Each permutation has weight 1/(B+1)!;
coordinate permutation bijects its atoms, and each atom is injective.
Consequently the B=1000 and B=10000 assumptions are satisfiable without
appealing to continuous distributions.

`scratch/audit_numeric.py` independently enumerates all 12870 assignments
of the 16-unit design with exact rational arithmetic, confirming 6435 RSS
values of multiplicity two. It checks the calibration arithmetic exactly
and evaluates the five finite-design mixtures at both 60 and 90 digits.
The weak-cutoff probabilities are approximately 0.051792651793 and
0.050039580347; the strict-cutoff probabilities are approximately
0.049794649795 and 0.049839600345; the B=1000 zero-p probability is
approximately 0.001846625096. The high-precision values support the
comparisons and are not substituted for formal proof certificates.

All denominators used as sample or group sizes are positive in the
substantive clauses. In T19 the infimum is a minimum of a nonempty finite
set of nonnegative discrepancies, and both median positions are in
bounds. Natural subtraction in the binomial exponents has k <= c < B;
the fixed strict-cutoff indices B/40-1 are positive. Probability measures
are finite, and the count events are Borel, so `Measure.real` does not hide
infinite-measure conventions. No integrals, limsups or circular
conclusion-assuming hypotheses occur. The archived weak-cutoff witnesses
are kept distinct from the printed strict-cutoff guarantee, and the
constructed calibration witness asserts no empirical power comparison.
