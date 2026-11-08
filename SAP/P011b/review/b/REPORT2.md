# Delta statement audit

**14 targets: 10 correct_whole, 4 correct_restricted; 0 outstanding defects.**
All severities are `none`. The previous finding concerned one target,
T18, with two issue entries: **both fixed**, neither partly fixed nor
unfixed. No new problem was found.

The requested original JSON schema is preserved. `refuted` is a decision
in `record2.json`; the verdicts in `findings2.json` describe whether the
canonical counterexample is completely or partially represented.
Consequently, the four complete counterexamples T18, T20, T23 and T26
receive `correct_whole`; T15 receives `correct_restricted` because its
accurately disclosed omissions remain. All **6 whole, 3 restricted and
5 refuted** record decisions are appropriate. There are no omitted
targets, false statements, vacuous statements, or inaccurate restrictions.

## Earlier T18 issues

| Earlier issue | Status | Evidence in revision 2 |
| --- | --- | --- |
| The bare arithmetic identity involving −70 was not linked to the bracket-only repaired moment expression. | **Fixed** | `cwBracketOnlyRepair` now defines that moment expression, and `T18Statement` asserts its value is −70. |
| The old `whole` record and docstring claimed a comparison absent from the proposition. | **Fixed** | `T18Statement` explicitly asserts `cwActualCovariance ≠ cwBracketOnlyRepair`; the revised docstring describes the actual expressions, and the record correctly labels the result `refuted`. |

The new
[definition](/home/ubuntu/sap/tasks/CHFID-P011b-b/SAP/P011b/Defs/Part4.lean:82)
is F − (J + 119P), where F is the weighted fourth-moment block,
J is the printed bracket, and P = E[Y₀Y₁] E[Y₂Y₃]. The first coefficient
inside J changes from 1 to 120. Every other coefficient stays as printed,
including the fifth term's coefficient −20 rather than the fully repaired
−40. This is precisely the opening-bracket-only correction in canonical
T18(d). It is an expression in the witness's moments, rather than a
constant assigned the desired value.

The revised
[proposition](/home/ubuntu/sap/tasks/CHFID-P011b-b/SAP/P011b/Defs/Part7.lean:26)
retains every previous conclusion and adds both missing assertions. Thus
all five canonical clauses (a)–(e) are now represented: actual covariance
zero, first printed expression 9/4, last printed expression 93009/16,
bracket-only repair −70, and fully corrected expression zero. The
original printed expressions still represent the printed errors.

## Changed statements and labels

I reread all ten definition parts, the definition root, and both Challenge
files and compared their mathematics with the saved `reading.md`.
T18 has the substantive mathematical change described above. T15, T20,
T23 and T26 have revised refutation labels and docstrings, with their
mathematical content matching the previous reading. The remaining nine
targets also match that reading. Adding the named T18 expression changes
no model, estimator, probability, moment domain or hypothesis elsewhere.

| Target | Revised decision | Delta and label assessment | Verdict |
| --- | --- | --- | --- |
| T15 | refuted | Same forced-star OLS counterexamples; all previous omissions and clipped-coverage scope remain expressly disclosed. | correct_restricted |
| T16 | restricted | Same Scaling domain, moving-bias identity and limit, vector shifts, and conditional residual results; complete omission list retained. | correct_restricted |
| T17 | whole | Same separate moment domains, corrected pair/fourth expansions, Mathlib covariance correspondence, and constant-centering expansion; no canonical clause lost. | correct_whole |
| T18 | refuted | Actual partial-repair expression and its value/comparison added; both previous issues fixed, all canonical clauses retained. | correct_whole |
| T19 | restricted | Same positive-common-variance domain, factorization, remainder limit and vanishing-spread implication; omissions accurately disclosed. | correct_restricted |
| T20 | refuted | Same fair-sign certificate, strict inside-event probabilities and limit one, plus explicit universal printed-assertion negation. | correct_whole |
| T21 | whole | Same pairwise correlations, variance identity, pointwise bound, canonical zero-variance convention, and distinct-correlation path witness. | correct_whole |
| T22 | whole | Same graph/upper-edge bijection, constraints, objectives, factor two, maximizers and variable count. | correct_whole |
| T23 | refuted | Same infeasible nonzero-product rule, mandatory-edge failure, and unique feasible optimum. | correct_whole |
| T24 | restricted | Same graph-only formal clause (i); all omitted statistical and textual corrections remain disclosed. | correct_restricted |
| T25 | whole | Same five helper-correction clauses on n > 1, including both optimizer equivalences and the discrepancy bound. | correct_whole |
| T26 | refuted | Same three helper/paper discrepancies, exact ratios, failure of a multiplicative bound and positive-probability admissible witness. | correct_whole |
| T27 | whole | Same finite generic maximum/oracle bound and all matrix/upper-edge program clauses, including the positive-variance converse for V2. | correct_whole |
| T28 | whole | Same oracle/maximal/truncated-degree bounds and cap-attainment equality implication, without new statistical assumptions. | correct_whole |

The three `restricted` decisions and T15's retained restriction field
match their Challenge omission text verbatim. No extra hypothesis or
undisclosed loss of scope was found. All five `refuted` docstrings open
with “The printed claim is false:”. Their mathematical refutations are:

| Target | Why the printed reading fails |
| --- | --- |
| T15 | Scaling, valid constraints, correct OLS mean model and singleton compatible set hold, but the scaled underestimation event at ε = 3/256 has probability tending to **one**, contradicting the printed conservativeness limit zero. The clipped-coverage claim remains explicitly limited to that interval. |
| T18 | For a legitimate four-coordinate constant-outcome law the actual covariance is **zero**, whereas the two printed expressions equal **9/4** and **93009/16**. The partial repair now separately equals **−70**. |
| T20 | Independent fair signs satisfy the printed assumptions but the probability of the **strict inside event** tends to **one**. The same strict-sign universal statement is explicitly negated. |
| T23 | The printed nonzero-product assignment violates degree caps in the first example and omits a forced edge in the second. Feasible alternatives exist; the first problem's optimum is uniquely attained. |
| T26 | At admissible data the stipulated helper formulas differ from the printed estimators: the empty-graph example gives **1/3** versus **2/9**, and the other two examples retain their exact discrepancies. The first vector has positive probability in a family satisfying the statistical assumptions. This comparison uses the helper formulas supplied in the canonical text; it does not claim execution of the package. |

## Junk values, nonvacuity and verification

The changed T18 statement adds no hypothesis. Its model still has n = 4
and a genuine probability law supported on (1,1,1,1), with weights
(2,3,4,5). Every real-valued function is integrable against this Dirac
law. Thus all mixed and fourth moments are genuine integrals, and the
covariance is the Mathlib centered-product covariance. The mean's divisor
is four; no empty type, division by zero, truncated subtraction or
nonintegrable-function convention produces any of the values. A
degenerate law is a valid counterexample to the canonical universal
moment identity.

The relabelled targets preserve their previous nonvacuity witnesses.
T15 uses K = k+1 positive independent star blocks with bounded outcomes
and nonzero scaled limiting variance; T20 uses nonempty fair-sign laws
with n Var(β̂) = 1; T23 has actual three-vertex feasible problems; T26
has the independent three-point family and an event of probability 1/27.
The earlier fair-sign intercept-design witness for T16 and the positive
variance/zero-spread witness for T19 remain valid. Every target's instance
is recorded in `findings2.json`; the more detailed unchanged witnesses
are in `scratch/nonvacuity.md`.

The new
[scratch/DeltaCheck.lean](/home/ubuntu/sap/tasks/CHFID-P011b-b/scratch/DeltaCheck.lean:15)
writes all sixteen partial-repair bracket terms directly and proves
that the revised SAP expression has exactly those coefficients. It also
proves integrability under the witness law and independently proves the
**entire revised `T18Statement`**. The command
`/home/ubuntu/sap/tools/sap-lean scratch/DeltaCheck.lean` completed with
exit code 0. It imports only `SAP.P011b.Defs`; no Challenge stub, Solution
or Bridge is used. Only one Lean process ran at a time, and no `lake`
command was run.

`findings2.json` parses and preserves the original eight-field schema,
one object for each of the fourteen canonical targets. The earlier
reading and review artifacts, supplied claims and records, architect
report, and revised SAP sources were left unchanged. This is a statement
audit; the architect's separate proof-certification status is outside
these verdicts.
