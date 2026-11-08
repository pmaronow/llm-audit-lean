All five declarations are faithful, with severity none. Their current
`whole` decisions and docstrings accurately describe the canonical claims.
No restriction, label correction, or source change is needed.

The blind readings and all closure definitions, including the generated
instance proofs, were recorded in `reading.md` before opening
`claims.json`. The five comparisons in `claim-stage.json` were saved
before opening `record.json`. The record required no revision to those
comparisons. No external review files or web sources were used.

| Declaration | Assessment |
|---|---|
| SAP.P010.T16 | `Defs/Part5.lean:85` and `:93` specify exactly the three canonical strata independently crossed with a nondegenerate binary assignment. `Defs/Part6.lean:213` includes every corrected numerical assertion, the zero unit effects, the three zero stratum effects, and the selected contrast of positive one half. A constant covariate adds verified conclusions without restricting the specified potential-variable law. |
| SAP.P010.T17 | `Defs/Part3.lean:42` defines precisely the corrected all-arm positivity assumption, incorporated into admissibility at `:45`. `Defs/WholeW1.lean:100` characterizes that requirement and proves its dependence only on the observable joint law. This is an imposed assumption; it does not claim positivity follows from ignorability. The active statement is `T17WholeStatement`; the old `T17Statement` mentioned in record history is outside this declaration's closure. |
| SAP.P010.T18 | `Defs/Part4.lean:92` states the complete corrected always-passer identity under Assumptions 1–3, common potential checks almost surely, and the two first-moment conditions explicitly attached to the canonical claim. The condition inside the expectation and the order of both arm differences agree. |
| SAP.P010.T19 | `Defs/Part4.lean:102` includes both component mean identities and their intent-to-treat difference under Assumptions 1–2 and exactly the stated first-moment conditions. It adds no passing or common-check premise. |
| SAP.P010.T20 | `Defs/Part4.lean:112` states common potential checks imply observed check-assignment independence under Assumptions 1–2. Its contrapositive supplies the printed testable implication. Positive passing and outcome integrability are unnecessary and are not required. |

The shared definitions implement consistency by coordinate evaluation and
ignorability separately for each pair `(Y(a),S(a))`, as printed. They do
not strengthen it to independence of the full potential vector. All
population spaces are finite products of standard Borel spaces.

No conclusion relies on a junk value. T16's three conditioning strata
each have mass 1/3, and its selected arm masses are 2q/3 and 2(1−q)/3.
For T17 the probability-law and design premises make every displayed
denominator positive and finite. For T18, common checks identify observed
passing with always-passing almost surely; positive passing rates then
give a positive always-passer mass. Its integrability hypotheses ensure
ordinary finite restricted integrals. T19 has positive finite arm masses
and integrable restricted outcomes. T20 contains no ratios or integrals.
The empty-arm case admits no probability measure on the population
space, while nonempty examples establish that the theorems are not
vacuous.

Three scratch files compiled successfully with the permitted `sap-lean`
command. `scratch/BlindClosure.lean` prints every generated proof in the
closures. `scratch/Check.lean` independently evaluates T16 at q=1/2:
probability normalization, positive arms, all three principal-stratum
masses, passing rates, full potential-vector independence from assignment,
observed check independence, integrability, zero unit and stratum effects,
zero average check effect, and selected means 0 and 1/2.
`scratch/Nonvacuity.lean:56` onward supplies explicit examples for every
hypothesis of T17–T20 using fair binary assignment and constant potential
outcomes 0 and 1. The all-pass version satisfies the complete population
assumptions; the all-fail version satisfies the design and common-check
conditions but fails positive passing. This also checks that T17's
admissibility condition is substantive and that T19–T20 require no
positive-pass premise. These two numerical/nonvacuity files import only
Defs and use no Challenge theorem.

`findings.json` contains exactly the five requested entries, with the
fingerprints copied from `closure.json`.
