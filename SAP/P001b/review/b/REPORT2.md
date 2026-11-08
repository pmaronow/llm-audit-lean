# Delta referee report

19 targets rechecked: **9 correct_whole, 10 correct_restricted; 0 adverse
findings**. Severity: 19 none, 0 minor, 0 major. All revised record decisions
are justified: **6 whole, 5 restricted, 8 refuted, 0 omitted**.

`findings2.json` preserves the requested original verdict schema, which has no
`correct_refuted` value. For accepted refutations, `correct_whole` means the
canonical counterexample content is fully covered (T21, T29, T38), and
`correct_restricted` means some auxiliary witness clauses remain omitted and
accurately disclosed (T25, T27, T31, T34, T36). All eight `refuted` labels are
accepted; these five scope verdicts do not reject their refutations.

My round-1 `findings.json` contained no adverse issues. Consequently there
are **0 earlier issues requiring a fix: 0 fixed, 0 partly fixed, 0 not fixed**.
All nineteen earlier favorable mathematical assessments remain valid. The
architect's table correctly reproduces my prior verdicts. The T36 objection
attributed to the other referee in `architect-report.md` is **fixed**: both
the theorem description and its scope disclosure now explicitly state real
analyticity, as does `record2.json`. This fixes the stated disclosure concern;
the theorem's analytic assertion was already true and was already identified
in my blind reading.

I re-read every Defs part and both Challenge parts against `reading.md`.
There is no change to any mathematical object, hypothesis, quantifier order,
or conclusion. The eight counterexample docstrings now identify the printed
claim as false; five retain their omitted-witness disclosures under `Scope`.
T36 additionally replaces the smoothness-only description with real
analyticity and its consequence, smoothness. The other eleven labels and
their mathematical scope are unchanged. This conclusion comes from the
source/readings comparison, rather than relying on the architect's account
of unchanged statements.

| Target | Revised decision | Recheck |
| --- | --- | --- |
| P001-T20 | restricted | The conditional arm-support identities and normalization bridge, infinite-support counterexample, and nondiscrete probability formulation remain explicitly omitted. The retained algebra and finite-support converse are sound. |
| P001-T21 | refuted | The specified fully coded electorate model has positive treatment masses but conditional joint probability 3/8 versus product 1/4. It refutes the printed implication. |
| P001-T22 | restricted | Retains corrected clause (i) only; the common-response implication and discrete ATE identification formula remain explicitly omitted. |
| P001-T23 | whole | Covers both occurrence directions as appropriate, every basic probability rule, and the addition rule. No canonical clause is lost. |
| P001-T24 | whole | Covers both countable formulas, the strict positivity requirement, nonempty event/complement criterion, partition repair, binary split, and 5/24 arithmetic. |
| P001-T25 | refuted | An actual one-point integer law gives lower-tail probability one and printed sum zero. The unused Bernoulli witness remains disclosed. |
| P001-T26 | restricted | Both corrected integer-tail clauses and the equality criterion remain; the fair-die specialization remains explicitly omitted. |
| P001-T27 | refuted | A countable normalized atomic law has a CDF continuous at 1/3 but locally nonconstant there. All previous auxiliary witness omissions remain disclosed. |
| P001-T28 | whole | Covers the countable point-mass sum, all ordered finite-range formulas and constancy, and all six die values. |
| P001-T29 | refuted | The three genuine density versions contradict pointwise uniqueness; the endpoint quotient failures contradict everywhere differentiability. |
| P001-T30 | restricted | Retains all listed univariate and continuous joint corrections; the separate discrete PMF factorization assertion remains explicitly omitted. |
| P001-T31 | refuted | The normalized fat Cantor subtype has a density and literal range containing no nondegenerate interval. Omitted length calculations remain disclosed. |
| P001-T32 | whole | Covers every zero point mass, uncountable range and source space, and the unconditional interval-free-range existence assertion. |
| P001-T33 | whole | The arbitrary-function equivalence covers the full pointwise random-variable claim; functions on domains containing the range may be extended off their domains. |
| P001-T34 | refuted | The normalized negative-rectangle law gives printed event probability one and printed integral zero. Omission of the second witness remains disclosed. |
| P001-T35 | whole | Covers the corrected triangular probability, exact negative-Y decomposition, and necessary and sufficient zero-missing-mass criterion. |
| P001-T36 | refuted | The positive normalized analytic density has an infinite zero-slice integral. Analyticity is now explicit; every previous omitted witness assertion remains enumerated. |
| P001-T37 | restricted | Global Borel measurability remains confined to conditional-slice normalization, exactly as disclosed; marginal finiteness and all finite nonnegative versions have no such extra premise. |
| P001-T38 | refuted | Both the zero-normal-combination defect and the two singular correlation endpoints contradict the printed readings. |

Each `whole` decision covers all canonical clauses, not merely a selected
consequence. T24's binary split occurs beneath a partition quantifier, but
the always available one-cell partition supplies it on every probability
space. T28's finite-weight presentation represents every ordered finite-range
law by its point masses. T32's irrational-interval witness is allowed by the
canonical existential assertion. T33 is a true generalization that removes
irrelevant probability hypotheses, preserving pointwise equality on the
literal range.

The new `refuted` labels do not depend on proving every auxiliary fact listed
for a witness. They do require actual counterexamples to the printed
assertions. T27 has a genuine discrete probability law because its positive
summable weights total one; continuity at 1/3 excludes a jump while the
nonconstancy assertion directly contradicts the printed local-flatness
reading. T31 explicitly supplies the probability measure, measurable random
variable, density, and interval-free literal range. T34 supplies a normalized
integrable density, so its unequal integrals are actual unequal event and
printed-formula values.

T36 also works under the paper's printed mixed-derivative notion of a joint
PDF. Write its displayed density as f. For each finite a,
`0 <= f(u,y) <= exp(2u)/pi` on `u <= a`, an integrable bound independent of y.
It justifies differentiating its joint CDF in y under the integral over u.
Continuity and the fundamental theorem of calculus then give the mixed
derivative f at every finite (a,y). Its total mass is one because integrating
in y gives the logistic derivative `exp(u)/(1+exp(u))^2`. At y=0 its integrand
tends to `1/pi`, so the nonnegative marginal integral is infinite. Thus the
printed assertion that this integral defines a finite PDF value at every y
is refuted. These mathematical checks establish the witness's applicability;
the separately omitted CDF and mixed-derivative assertions are still omitted
from the Lean conjunction, as its scope correctly says.

Junk values and nonvacuity were rechecked. T20 and T24 guard probability
ratios by positive denominators; T21 supplies conditioning masses one and
one half; T26 assumes summability and T27 asserts it. The uniform and
rectangle functions are genuinely integrable, while arbitrary-density
triangle integrals have joint integrability and Fubini's theorem available.
T37 assumes an integrable selected slice and a strictly positive real
integral. T36 uses an extended nonnegative integral for the divergent slice,
and both denominators in its explicit density are positive. T38's endpoint
refutation uses the separate zero-denominator assertions at admissible unit
scales, rather than interpreting Lean's totalized zero values as ordinary
values of the undefined printed expression. No new empty-index or
inconsistent-premise mechanism appears.

The unchanged nonvacuity examples remain applicable. I recompiled
`scratch/Check.lean` against the refreshed Defs with
`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`; it exited successfully
with no diagnostics. It independently checks the nonempty overlap instance,
electorate arithmetic and dependence, positive partition, summable integer
law, ordered die, Gaussian and product Gaussian density instances and
positive finite slice, nonconstant function-equality instance, analyticity
of the actual T36 formula, and both T38 endpoint denominators. The closed
dyadic, fat Cantor, uniform, and rectangle witnesses retain the mathematical
normalization and nonvacuity arguments recorded in `findings2.json`. Only one
Lean process was run at a time; `lake` was not invoked.

A mechanical check verified the exact nineteen target/theorem mappings,
all eight false-claim docstring openings, all five restricted disclosures,
and all five limited-refutation scope disclosures against `record2.json`.
The JSON was parsed with Python and checked for the original field schema,
valid verdicts, unique and complete target coverage, and counts. There are
no adverse items to carry forward. The original review files and supplied
Lean sources were left unchanged.
