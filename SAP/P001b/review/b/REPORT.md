# Referee report

19 targets audited: **9 correct_whole, 10 correct_restricted**. There are zero
restriction_inaccurate, not_faithful, vacuous, false, omission_ok, or
omission_questionable verdicts. Severity: 19 none, 0 minor, 0 major.

There are no adverse findings. Every declared restriction accurately identifies
the omitted claim components or added hypothesis, and appears in the associated
Challenge docstring. No target is omitted.

| Target | Verdict | Assessment of the architect's decision |
| --- | --- | --- |
| P001-T20 | correct_restricted | Retains the overlap algebra and finite-support converse; discloses the missing conditional-support/normalization bridge and infinite-support counterexample. |
| P001-T21 | correct_whole | The specified four-atom electorate, voter rule, dependence witness, contrast, and ATE are all present. |
| P001-T22 | correct_restricted | Retains only the T21 counterexample; explicitly drops the common-response implication and ATE identification formula. |
| P001-T23 | correct_whole | Correct occurrence direction, failure of its reverse on proper subsets, all basic rules, and addition rule are present. |
| P001-T24 | correct_whole | Both total-probability formulas, strict positivity for ratios, the partition repair, binary split, and arithmetic example are covered. |
| P001-T25 | correct_restricted | Retains the constant-zero counterexample and explicitly drops the Bernoulli example. |
| P001-T26 | correct_restricted | Retains the integer-tail and missing-mass identities and criterion; explicitly drops the die specialization. |
| P001-T27 | correct_restricted | Retains a genuine normalized atomic CDF refutation; enumerates the omitted range, level-sum, and point-mass assertions. |
| P001-T28 | correct_whole | Covers the countable CDF formula, ordered finite formulas, constancy, and all six die values. |
| P001-T29 | correct_whole | Covers all three actual density versions and both endpoint derivative failures with their difference quotients. |
| P001-T30 | correct_restricted | Covers the univariate and continuous joint corrections; explicitly drops the separate discrete PMF assertion. |
| P001-T31 | correct_restricted | Uses the actual fat Cantor construction and normalized subtype law; explicitly drops the geometric-series calculation and component bounds. |
| P001-T32 | correct_whole | Gives atomlessness and uncountability, plus a valid interval-free-range witness using the irrational points of [0,1/2]. |
| P001-T33 | correct_whole | The true algebraic generalization covers the entire pointwise equality claim. |
| P001-T34 | correct_restricted | Retains the normalized negative-rectangle refutation and explicitly drops the uniform-square example. |
| P001-T35 | correct_whole | Covers the corrected triangle, the missing negative-Y mass, and the exact equality criterion. |
| P001-T36 | correct_restricted | Retains the genuine infinite-slice density refutation and enumerates the omitted formulas and derivative assertions. |
| P001-T37 | correct_restricted | Adds Borel measurability only to the conditional normalization branch, exactly as disclosed. |
| P001-T38 | correct_whole | Gives the zero-normal-combination refutation and vanishing denominators at both printed correlation endpoints. |

The blind reading was saved in `reading.md` before `claims.json` was opened.
The independent comparisons were saved in `claim-stage.json` before
`record.json` was opened. No step-2 classification was changed after reading
the record. T33 remains classified as `broader` at step 2 because it drops
irrelevant probability hypotheses; its final `correct_whole` verdict records
that this true generalization covers all of the canonical claim. Extending
functions off their original domains does not change either side of the
range-restricted equivalence.

The scope review compared the actual propositions with every canonical claim
and its standing assumptions, then with the record. A separate mechanical
check confirmed all 19 theorem mappings and that all 10 record restriction
texts match the Challenge docstrings after whitespace normalization. Credited
row names were not treated as evidence of statement correctness. In
particular, accepting T22's disclosed narrower scope does not independently
certify the record's claims about unavailable declarations or `wrong_credit`.

`scratch/Check.lean` imports only the supplied Defs and compiled successfully
with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` (exit 0). It checks a
normalized nonempty overlap instance; the electorate's weights, conditioning
masses, conditional means, ATE, and dependence; a positive measurable
partition; a normalized summable integer law; the die's normalized ordered
model; actual Gaussian and product Gaussian density instances, including
marginals and a positive finite slice; a nonconstant function-equality
instance; real analyticity of the infinite-slice density; and vanishing normal
endpoint denominators. These checks use the Defs directly and do not import
the Challenge stubs. Only one Lean process was run at a time; `lake` was never
invoked.

For the remaining fixed examples, `findings.json` gives explicit mathematical
nonvacuity arguments. The dyadic weights sum by levels to one. The fat Cantor
stages have component length `2^(-n-1)+2^(-2n-1)` and total length
`1/2+2^(-n-1)`, so their intersection has positive measure. The negative
rectangle is a measurable unit-area support. The infinite-slice density
normalizes through the logistic derivative; its zero slice diverges, while
every nonzero slice has integrable tails. These are closed concrete
assertions, not implications with impossible premises.

Two Mathlib conventions needed special attention. In T36, `ContDiff ℝ ⊤`
asserts real analyticity in this version of Mathlib. The stronger property is
true for the explicit formula, was independently compiled, and entails the
smoothness described in the docstring; it adds no hypothesis. In T38, the
separately documented totalized expression is zero at singular correlation.
That is not an ordinary value of the paper's undefined expression. The
meaningful endpoint certificate is that its actual denominators vanish for
parameters permitted by the printed range.

The other potentially troublesome conventions do not manufacture the results:
event measures passed to `toReal` are finite; probability ratios have positive
denominators where used; real tail sums are summable; density integrals have
genuine integrability; Fubini handles exceptional sections; and the divergent
slice is expressed with the extended nonnegative integral. Pointwise range,
pointwise equality, and the paper's positive-density notion of support are
kept distinct from essential range and topological support.

Both JSON output files were parsed with Python, with target coverage,
uniqueness, required fields, and verdict counts checked. No supplied Lean
source file was modified.
