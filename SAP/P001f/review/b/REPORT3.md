# Round 3 delta statement review

19 targets: 18 theorem stubs and one omission. No outstanding adverse findings
or new mathematical problems were found under the current claim rule.

| Verdict | Count |
| --- | ---: |
| correct_whole | 7 |
| correct_restricted | 11 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

Severity: 19 none, 0 minor, 0 major.

The record has 7 whole, 9 restricted, 2 refuted and 1 omitted decisions.
The unchanged output schema has no `correct_refuted` verdict; its two direct
refutations, T103 and T104, are counted as `correct_restricted` because they
correctly disclose the unaddressed components of their canonical passages.
The `false` verdict would describe a false Lean statement, not a successful
refutation of a false printed assertion.

## Earlier findings

My only adverse target in rounds 1 and 2 was T113. Both related issues are
resolved; the earlier objection is withdrawn under the current explicit user
instruction, “What the claim is.”

| Earlier finding | Status | Resolution |
| --- | --- | --- |
| T113 nuisance-integrability restriction said to conflict with an implicit premise in the canonical note | Fixed under the clarified scope rule | The note is audit history and adds no hypothesis. The statement, definitions and standing convention require the outcome and combined-score expectations, but no separate population moment of the arbitrary nuisance regression in the correct-propensity branch. |
| T113 response invoked a note-precedence rule not present in my earlier review packet | Fixed | That rule is now supplied directly by the user. The architect report cites the current clarification instead of relying on the old brief citation. No missing-context objection remains. |

The T113 theorem is unchanged and sound as far as I can tell. Its restriction
is genuine and the current docstring accurately discloses it. For independent
uniform X,U on (0,1), set Y=0, R=1 when X<1/2 and R=1_{U<1/2} otherwise,
q=p=1 below 1/2 and 1/2 above it, and m(x)=1/x for 0<x<1/2, zero elsewhere.
The response/nonresponse probabilities are 3/4 and 1/4; MAR and a positive
uniform response bound hold. The combined augmented score is identically zero,
whereas integral |m(X)| diverges. Each dyadic interval
(2^{-(k+1)},2^{-k}), k>=1, contributes at least 1/2 to that absolute integral.
Thus both displayed expectations genuinely exist while the separate nuisance
moment does not. This case is admitted by the canonical statement under the
current rule and excluded by the Lean premise, exactly as disclosed. The
correct-regression branch's separate moment is redundant; the disclosure says
it is required in both branches and correctly identifies exclusion in the
correct-propensity branch.

T108's earlier restriction disclosure, accepted in round 2 after the other
referee's finding, remains fixed. An infinite iid sequence is stronger than
an arbitrary finite iid family on the original space, and the docstring
continues to say so explicitly.

## Revised targets and comparison with reading.md

I reread all five Defs parts, both root modules and the Challenge part and
compared their expanded propositions with the saved blind mathematical
reading. No mathematical definition body, theorem type or quantifier scope
changed. The PDA predicate's comment and the Challenge documentation changed.
There are four changed target records relative to `record2.json`:

| Target | Revision | Judgment |
| --- | --- | --- |
| T96 | refuted to whole; false-claim notice removed | Correct. The canonical statement itself records the eighteen-unit counterexample. The theorem establishes all its fitted probabilities, unique ML fit, observed fractions, score arithmetic, estimates and gap. It does not contradict the canonical counterexample. |
| T99 | refuted to whole; false-claim notice removed | Correct. The canonical statement itself records the two-atom counterexample, ignorability, positivity bounds, unnormalized effect, ATT and normalization. All those assertions remain present. |
| T102 | refuted to restricted; reading and omitted content now specified | Correct. The theorem negates the interpretation that support differentiability guarantees a common actual derivative at the mean for all CEF versions. The printed guidance does not itself quantify over every extension. The docstring names the reading, omits the fixed-CEF population identity and discrete-slopes recommendation, retains the guarded sample formula, and no longer says “The printed claim is false.” |
| T113 | restriction explanation updated to apply the current canonical-scope rule | Correct. The explicit integrability premise remains in both branches; the actual exclusion and a.e. version conventions are accurately disclosed. Earlier objection resolved as above. |

The latest rule also confirms the unchanged refuted labels:

- T103 negates the canonical statement's own assertion (A), universal
  maximizer existence for the specified mixture. Positive n=1, y=1 is an
  admissible subclass; restricting the counterexample to it does not weaken
  its contradiction of that universal assertion. The omissions of (B),
  consistency, efficiency and plotted-fit assessment remain disclosed.
- For T104 let O denote equal positive-mass supports and P uniform two-sided
  positivity. Canonical (A) says P implies O; canonical (B) says not-P implies
  not-O, hence O implies P. Their conjunction implies the equivalence negated
  by the theorem on admissible countable laws. This is a contradiction of
  canonical assertions, without relying on the hedged interpretation of (C).
  The separate proof of (A), isolation of the directed failure, hedged (C)
  and regional example values are still explicitly omitted.

## Remaining labels

| Targets | Accepted decision | Scope checked |
| --- | --- | --- |
| T100 | whole | Propensity mean, both weighted-effect identities, positive normalization, ATT and equality criterion. |
| T106 | whole | Linearity, variance formula, affine variance and standard-deviation rules, standardized Chebyshev with the appropriate moments. |
| T109 | whole | Weierstrass, population polynomial minimizer existence, and eventual approximation for every minimizing family on the paper's full PMF/PDF interval-support domain. |
| T110 | whole | Every positive-size binary sample, endpoint cases, uniqueness, sample-mean equality and the three-flip example. |
| T112 | whole | Balance, MAR after propensity conditioning, true conditional response version and uniform lower bound, with no outcome moment premise. |
| T97 | restricted | Positive real cell masses and cell outcome sums; raw-unit identities and outcome-vector transfer remain omitted as disclosed. |
| T98 | restricted | True-score expectation assertions; omitted estimator/convergence/efficiency content and pointwise infinite-sequence assumptions remain disclosed. |
| T101 | restricted | Relative-complement identity; omitted erroneous-equality characterization and numerical illustration remain disclosed. |
| T107 | restricted | Iterated expectation alone; total variance and all best-prediction components remain disclosed omissions. |
| T108 | restricted | Infinite iid initial segments, separate moment scopes; arbitrary finite-family transfer omitted. |
| T111 | restricted | MCAR, both MAR identifications and sample numbers; population integrability is explicitly retained rather than derived. |
| T114 | restricted | Complete population interval, width and sharpness plus final ATE endpoints; four constituent sample estimates remain omitted. |
| T105 | omitted | Reasonable on the visible evidence: no mathematical predicate is supplied for informational completeness. A larger-domain negation without binary treatment and that premise would not refute the stated implication. |

T111's retained integrability premise is mathematically redundant under its
uniform response lower bound and the restricted-law integrability already
present. Its conservative label accurately describes the premise being
retained, and does not assert that otherwise valid models are excluded.
For T105 I have not independently inspected the credited row or its status;
the omission judgment concerns the supplied statement and visible definitions.
Audit notes were not used to add or remove clauses in any of these judgments.

## Junk values and nonvacuity

The included examples and guards from the earlier audit still apply; every
target has its own instance or explanation in `findings3.json`. For the changed
or relabelled content:

- T96 has positive treated/control counts and interior logistic probabilities.
  Every log argument and divisor is positive. The sample occurs with positive
  probability under an iid population with a correctly specified logistic
  propensity and deterministic potential outcomes given the covariate.
- T99 uses positive normalized masses 3/4 and 1/4; conditioning probabilities
  and the propensity mean used for normalization are positive.
- T102 has a genuine joint-density witness: independent X with density 1/2
  on (-2,-1) union (1,2), and centered uniform Y on (-1,1). Both m0=0 and
  m1(x)=x for |x|<1, zero elsewhere, are conditional-mean versions and
  differentiable everywhere the chosen density is positive. At E[X]=0
  their actual derivatives differ, 0 versus 1. This uses K=1 and finite
  means. The sample formula also has n=1 and a nonempty coordinate-type
  instance with a coordinate-projection estimator of actual derivative one.
- T113 has included four-atom examples in both correctness branches:
  independent fair X,R, Y=X, true p=1/2, with m=X,q=1/4 for regression
  correctness or m=42,q=1/2 for propensity correctness. The additional
  cancellation example above has score divisors 1 and 1/2 and a genuinely
  integrable score, not a default value for a nonintegrable integral.
- T103's n=1, y=1 likelihood is unbounded along valid parameters
  (1,0,1,s,0,1,1), s>0: it is 1/(s sqrt(2 pi)). Each individual parameter
  has finite likelihood; a zero scale is never used.
- T104's t_k=4^{-(k+1)}, c_k=2^{-(k+1)}-4^{-(k+1)} are positive and
  summable with totals 1/3 and 2/3. Both supports are all natural numbers,
  but the propensity 2^{-(k+1)} tends to zero. No empty index set,
  nonsummable default sum or zero-total-cell ratio does the work.

The independent definition-only `scratch/Delta3.lean` compiled successfully
with `/home/ubuntu/sap/tools/sap-lean` and exit code 0. It checks actual
coordinate derivatives, a nonempty sample-PDA instance, and the cancellation
algebra using the supplied censored-outcome definition. The distributional
and nonintegrability witnesses above were checked mathematically; the scratch
file does not claim to formalize those full examples. Earlier definition-only
nonvacuity checks remain preserved in `scratch/Check.lean`.

Python independently checked the T96/T99 rational arithmetic, the response mass
in the cancellation example, record/theorem coverage, all decision notices and
T102's interpretation disclosures. It parsed `findings3.json`, checked the
original schema and all 19 unique target IDs, and verified both report counts.
No Solution or Comparator proof was read or used as evidence, and no broader
kernel-certification claim is made by this statement review.
