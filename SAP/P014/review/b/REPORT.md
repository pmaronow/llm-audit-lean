# P014 statement audit

Ten targets audited: **8 correct_whole, 2 correct_restricted**. All ten have
severity **none**. There are **0 restriction_inaccurate, 0 not_faithful,
0 vacuous, 0 false, 0 omission_ok, and 0 omission_questionable** verdicts.
No corrective statement or docstring edit is required.

The `correct_whole` verdict for T4 accepts the complete, explicitly declared
**refutation** of the printed positive assertion. It does not assert that the
paper's original unbiasedness formula is true.

## Blind order and scope

I saved `reading.md` after reading only the Defs, Challenge, and relevant
Mathlib sources. I then read `claims.json`, performed the claim comparisons and
nonvacuity checks, and saved `claim-stage.json`. Only afterward did I open
`record.json`. No claim-stage classification was changed after reading the
record.

There are no nonaccepted items to enumerate. The two narrower statements are
accurately disclosed restrictions, and the one changed proposition is a valid
declared refutation, as explained below.

| Target | Claim-stage relation | Final verdict | Assessment of the record |
|---|---|---|---|
| P014-T1 | whole | correct_whole | Every condition and numerical value of the canonical six-row counterexample is retained. |
| P014-T2 | narrower | correct_restricted | The assignment-law theorem and four derivation steps are complete; the missing score-law application is disclosed exactly. |
| P014-T3 | whole | correct_whole | All five parts, including the binomial full-assignment law and necessity for every outcome function, are present. |
| P014-T4 | different | correct_whole | The declared refutation addresses the actual printed target under both the printed clauses and the intended local-permutation law. |
| P014-T5 | whole | correct_whole | The local-permutation defect and its no-interference downstream counterexample are both represented. |
| P014-T6 | narrower | correct_restricted | Only the forward direction of (d) is omitted; (a)–(c), the converse of (d), and (e) are retained. |
| P014-T7 | whole | correct_whole | The impossible diagonal requirement is diagnosed, and the corrected condition is realized nonvacuously. |
| P014-T8 | whole | correct_whole | The nonempty finite mean identity has exactly the intended grouping. |
| P014-T9 | whole | correct_whole | The conditional other-subject averages, both signs, and all concrete arithmetic are represented. |
| P014-T10 | whole | correct_whole | The conditional-average identification, reverse sign, estimator consequence, and printed-definition failure are retained. |

## Accepted restrictions and refutation

**T2.** `Defs/Part4.lean:T2Statement` quantifies over a finite assignment law
with fixed interior treated count and common local propensities. It includes
positive conditioning probabilities, the indicator/moment calculations,
fixed estimator denominators, linearity, and the final weighted-target
identity. It does not quantify over running variables or transfer their
corrected local law to these assignment-law hypotheses. The canonical target's
final paragraph requires that transfer and its unbiasedness application.
Both the Challenge docstring and the record identify exactly this missing
application and correctly say that no further assignment-law assumption was
added. This warrants `correct_restricted`.

**T6.** `Defs/Part5.lean:T6GeneralPart` preserves fixed counts, marginal
propensities, window membership, empirical CDF, and distinct-subject no-ties
under the corrected local score law. The deterministic-outside premise is
confined to the converse of (d); it does not restrict (a)–(c). The theorem
also includes the full independent-outside twelve-point example. The missing
forward half of (d) would start with the additional discrete full-vector mass
clause and conclude one full supported score vector above each local
arrangement, hence almost sure reconstruction of outside scores from the
local arrangement. Both the docstring and the record describe exactly this
omission. The retained converse includes existence, cardinality, and masses
of the full score law. This warrants `correct_restricted`.

**T4.** The claim-stage classification remains `different`: the canonical
positive unbiasedness assertion and the formal explicit counterexample are
different propositions. The record correctly chooses `refuted`, which the
Challenge docstring already declares. The supplied witness satisfies the
actual assumptions: fixed membership, common empirical CDF, full-vector
mass 1/3!, distinct-subject no-ties under standing R6, interior treated count,
and every local permutation with probability 1/6. It even has positive
individual arms and common treatment probabilities 1/3. Nevertheless the
unchanged difference in means has expectation 0 while the printed average
over distinct supported assignments is -1/18. It therefore refutes the
printed reading, including its stronger intended local-randomization
interpretation. The final verdict accepts this complete target disposition;
it does not revise the saved claim-stage comparison.

## Nonvacuity and mathematical checks

A common nonvacuity model for the general theorems has N=3,
S={0,1}, b=1, n=2, m=1, and two equally likely score vectors
(-1,1,-2) and (1,-1,-2). Use the powerset sigma-algebra on a two-point sample
space. The two local permutations each have probability 1/2=1/2!, v=(-1,1)
is injective, and the genuine outside subject has constant score -2 and
treatment false. The assignment law is uniform on (false,true,false) and
(true,false,false), with each local conditioning event having probability
1/2. For own-treatment potential outcomes, the estimator and both targets
are 1 and the control-minus-treatment direct-effect average is -1. The
necessity premise is also satisfiable: each own arm contains exactly one
supported assignment, so its two averages agree for every outcome function.

`scratch/Check.lean` imports only `SAP.P014.Defs`. It compiles with
`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` and no `sorry`, verifying
validity of that assignment law, fixed counts, common marginals, positive
arms, conditional uniformity, noninterference, positive denominators,
nonzero estimator/target values, a necessity-premise instance, the finite
sum identity, and the genuine inverse reconstruction by `insertOwn` and
`removeOwn`. The final compilation exited 0 with one stylistic tactic-linter
warning. No `lake` command was run; Lean checks ran sequentially.

`scratch/check_exact.py` independently enumerates the concrete laws using
`fractions.Fraction`. All assertions pass. Its results are saved in
`scratch/check-results.json`.

| Concrete design | Estimator expectation | Printed target | Weighted target | Other comparison |
|---|---:|---:|---:|---|
| T1/T4 | 0 | -1/18 | 0 | Bias 1/18 |
| T5 | 1/6 | 1/3 | 1/3 | Local treatment probabilities 1/6, 1/6, 2/3 |
| T9/T10 failure | -1/12 | -1/9 | -1/12 | Direct-effect average 1/12; bias 1/36 |

The checks also verify full support sizes and weights, threshold linkage,
all required local permutation probabilities, positive arms, distinct local
values, and constant window membership. Equality of the sorted local score
multisets verifies the empirical CDF equality for every real threshold,
rather than testing a finite selection of thresholds. The T6 outside example
has twelve full score atoms, six of each mass 1/18 and 1/9, local mass 1/6
for every arrangement, and the stated product probabilities proving
independence.

The remaining general identities have the expected mathematical content:
finite-sum linearity with fixed positive arm sizes gives T2; conditional
uniformity or constant own-arm outcomes gives T3; distinct uniformly
permuted local values give disjoint exhaustive permutation events and T6's
counts and propensities; the diagonal event is the whole probability space
in T7; splitting a Boolean vector into its own coordinate and all other
coordinates gives T10's conditional sum and sign. None assumes its claimed
unbiasedness conclusion. T3's agreement-for-every-outcome premise is used
only in the intended necessity implication.

No zero-division, truncated-subtraction, infinite-measure, integrability, or
empty-index convention supplies an unintended result. The count hypotheses
force n≥2, m>0 and n-m>0; positive arms make conditional and support-average
denominators positive. `eventProbability` always occurs under a probability
measure in these theorems, so Mathlib's `toReal` convention at infinity is
irrelevant. Assignment and outcome sums are finite. The empty S in T7 is the
explicit case of its diagnosed literal condition, not a hidden premise of
an unbiasedness theorem.

The comparison uses the supplied canonical transcription and standing
assumptions. Attempts to retrieve the
[paper through its DOI](https://doi.org/10.1353/obs.2017.0001) and publisher PDF
were blocked; no mathematical assessment relies on a secondary web source.
The comparison-effect definition and its attributed sign are exactly those
specified in `claims.json`; the cited second paper was not separately
searched. This is an audit of the statements and decisions, not an audit of
proof transport or of the record's claims about which external proof rows
were used.
