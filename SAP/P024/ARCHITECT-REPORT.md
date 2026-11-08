P024: 5 whole, 2 restricted, 0 refuted, 1 omitted. All seven listed theorems
have completed Solution proofs. There are no open glue tasks.

| Target | Decision | Current conclusion |
| --- | --- | --- |
| P024-T1 | whole | Complete four-period timing counterexample, including variance and exact test calibration. |
| P024-T2 | whole | Corrected overlap estimation, uniform sharp-null testing, and actual before-after bias. |
| P024-T3 | omitted | No credited Lean declarations. |
| P024-T4 | whole | Complete dominant-cluster counterexample under independent and ancillary complete assignment. |
| P024-T5 | whole | Corrected consistency, weight equivalence, appreciable finite-sample bias, and failure without no dominance. |
| P024-T6 | restricted | Individual-mean unbiasedness under fixed counts almost surely or conditional-on-count uniform laws. |
| P024-T7 | whole | Full corrected conditional clustering claim, including the closed positive event probability. |
| P024-T8 | restricted | Actual-probability HT identity and unbiasedness under fixed quotas and common actual block marginals. |

P024-T3 has no Lean rows. Its multi-message design comparison, robustness
assertion, testing procedure, and claimed advance over prior work have no
separate theorem here. The precise timing counterexample and corrected
estimation/testing conclusions remain T1 and T2.

P024-T6 adds sufficient joint-law conditions to the paper's individual
equal-probability description. It requires either a treatment count m fixed
almost surely, 0<m<N, with every actual marginal m/N, or a law on proper
nonempty subsets uniform conditional on its treatment count. Complete
individual randomization and independent common-p assignment conditioned on
nonempty arms are included. Arbitrary equal-marginal dependent laws with
varying counts are excluded. The four positive branches in
T6WholeStatement_W2 are retained; a fixed count is required only on assignments
of positive mass. Every conclusion uses observed individual group means.

P024-T8 adds a predetermined interior quota 0<m_b<N_b in every block on every
assignment and actual common within-block probabilities m_b/N_b. It excludes
variable block counts and unequal within-block propensities. The retained
statement uses the actual-probability HT estimate and population-share weighted
ordinary block differences in means, proves their pointwise identity and both
unbiasedness conclusions, and certifies positive denominators. Uniform
subsets within blocks and independent assignments across blocks are unnecessary;
balanced nonuniform fixed-quota laws are included.

T5 now uses the supplied T5WholeStatement and its existing W1 proof. Beyond
consistency and the maximum-share/squared-share equivalence, it includes a
24-cluster example with 69 individuals, 12 treated clusters, effect 2/3,
expected estimate 23/57, and bias -5/19. It also includes the dominant-cluster
failure without no dominance for every empty-arm extension. Its consistency
hypothesis uses one outcome bound and one fixed positive probability margin
uniformly over the entire sequence; probabilities and effects may vary.

T7 now uses the supplied T7WholeStatement and its existing W1 proof. It
includes Pr(A)=1-p^K-(1-p)^K>0 for every K>=2 and 0<p<1, actual normalized
conditional masses, equal-size unbiasedness and allocation formulas, arbitrary
empty-arm extensions, and the individual-level unequal-size witness. The
accepted canonical scope excludes consistency and blocking recommendations.

The route remains shared SAP definitions and structural Bridges. Challenge
and Solution import the same statement modules, whose mathematical dependencies
are Mathlib and earlier SAP definitions. Bridge.toDesign preserves all masses
and validity certificates; Bridge.toPopulation preserves positive integer
sizes and individual potential outcomes. Correspondences for probabilities,
expectations, variances, exposures, estimators, populations, concrete witnesses,
and conditional laws are rfl or Iff.rfl. Supplied W1, W2, and W3 proof modules
were already present when this review began. This round adds no proof and
changes no mathematical statement, definition body, import, or proof term.
Only documentation and manifest scope classifications are corrected.

T1 and T4 establish their canonical counterexamples rather than refuting those
canonical assertions, so both remain whole. T4 includes all independent
finite bounds and nonconvergence claims for arbitrary empty-arm values,
conditional mean, complete-design distribution and moments, population-share
identity and limit, and the six-cluster checks. The complete design is
explicitly separate from independent assignment.

All interpreted quantities have their required domains. T1 uses only the two
overlap periods; T2 requires nonempty strict overlap and nonempty uniform
testing spaces. Cluster sizes are positive. T4/T5 explicitly supply arbitrary
empty-arm values. T6 uses nonempty arms on positive-mass support or on its
conditional domain; zero-mass allocations cannot affect its finite means.
T7 has a positive conditioning probability. T8 has nonempty arms in every
block on every allocation and actual propensities strictly between zero and
one. All means are finite sums; no integrability assumption or infinite-real
conversion is hidden in them.

## Round 1 referee findings and revision 2

The earlier referee findings concerned the then-restricted T8. Both referees
correctly observed its coverage of balanced nonuniform fixed-count laws, and
that generality was documented. Their requested whole relabeling relied on a
diagnostic note. The [precedence rule](/home/ubuntu/sap/wt/ARCH-P024/brief.md:30)
does not let notes narrow the canonical statement. The governing
[T8 statement](/home/ubuntu/sap/wt/ARCH-P024/work.json:1829) does not fix counts
or require common within-block marginals, and T8 has no accepted correction.
The report therefore rejected that relabeling with these citations. Round 2
below reaches the same distinction for the subsequently supplied W3 version.

## Declaration review round 1

Both findings on T1 and T4 were accepted. Their labels were corrected from
refuted to whole because the [T1 canonical claim](/home/ubuntu/sap/wt/ARCH-P024/work.json:37)
and [T4 canonical claim](/home/ubuntu/sap/wt/ARCH-P024/work.json:382) already
assert the counterexamples. Both docstrings identify exactly the readings
being refuted: no-trend necessity under randomized timing, and cluster-count-only
consistency without control of population shares. The statements and proofs
were unchanged. The [T1 finding](/home/ubuntu/sap/wt/ARCH-P024/fw/round1/T1/r1g1/findings.json:9)
and [T4 finding](/home/ubuntu/sap/wt/ARCH-P024/fw/round1/T4/r1g1/findings.json:34)
were resolved along with their associated docstring issues.

Before round 2, supplied proof extensions added T5's finite-sample bias and
failure clauses, T7's event-probability formula, and the current W2/W3 positive
versions of T6/T8. Those versions supersede the original narrower statements.
Their names containing Whole do not establish whole coverage; the canonical
statement still determines that classification. The full incoming report
history is preserved in scratch/report-before-round2.md.

## Declaration review round 2

Every open finding is accepted after checking the current canonical statements,
statement definitions, and existing proofs. A findings file covers multiple
declarations; only each requested declaration's entry was used.

- T5, restriction_inaccurate/minor: the [finding](/home/ubuntu/sap/wt/ARCH-P024/fw/round2/T5/r6g1/findings.json:41)
  is correct. The [canonical hypothesis](/home/ubuntu/sap/wt/ARCH-P024/work.json:865)
  and T5Statement quantify one eta>0 before the sequence-wide inequality
  eta<=p_K<=1-eta. Pointwise interiority does not express that hypothesis.
  Both the Challenge and WholeW1 docstrings now state the fixed uniform
  margin explicitly, and say that varying probabilities retain the same
  outcome bound and probability margin. T5's whole label and proposition
  are unchanged; the supplied statement includes all canonical clauses.
- T6, label_wrong/major: accepted the [finding](/home/ubuntu/sap/wt/ARCH-P024/fw/round2/T6/r6g1/findings.json:57).
  The [canonical wording](/home/ubuntu/sap/wt/ARCH-P024/work.json:1516) specifies
  equal individual probabilities without the four sufficient joint laws
  required by W2. The manifest now says restricted and discloses the precise
  retained design subclasses and excluded dependent random-count laws. Both
  current docstrings make the same disclosure. Complete assignment and the
  conditional Bernoulli branch remain proved, as do fixed counts almost
  surely and uniformity conditional on the count. This corrects coverage,
  without substituting a refutation or the obsolete W1 counterexample.
- T8, label_wrong/minor: accepted the [label finding](/home/ubuntu/sap/wt/ARCH-P024/fw/round2/T8/r6g2/findings.json:20)
  and its [docstring finding](/home/ubuntu/sap/wt/ARCH-P024/fw/round2/T8/r6g2/findings.json:21).
  The canonical statement and definitions do not impose W3's fixed quotas
  and actual common marginals; those were supplied only as a diagnostic
  formal reading. The manifest now says restricted with those additional
  conditions and omitted cases. Both current docstrings remove assertions
  that a supplied note determines the printed scope and instead describe
  the fixed-quota specialization. They retain actual HT, observed block
  means, positive denominators, and allowance for balanced nonuniform laws
  and dependent assignments across blocks.

The W2/W3 assembly comments were also aligned with their restricted scopes.
Historical W1 counterexample declarations were moved from rows_used to
rows_not_used for T6/T8; they do not prove the retained positive specializations.
All original credited rows remain accounted for, with additional supplied
supporting declarations distinguished in the same manifest. No declaration
body changed, so no shared mathematical dependency was changed by this round.

The incoming verification/comparator-result.json records an accepted earlier
seven-theorem run through all three kernels. Its source and manifest hashes
predate these documentation and scope corrections, so it is historical evidence,
not a fresh certificate for the revised files. comparator.json retains the
same seven theorem names and kernel configuration. No external certification
result was rewritten or newly claimed in this round.

Round 2 validation: all 24 Lean modules were recompiled with sap-lean in
dependency order, with exit status 0. The order and complete output are in
scratch/declaration-round2-build-order.json and scratch/declaration-round2-build.txt.
All seven dependency checks were rerun through scratch/P024Axioms.lean;
scratch/P024Axioms.txt reports exactly propext, Classical.choice, and Quot.sound
for every listed theorem. Both JSON files parse and agree on the seven proved
theorem names. All original 87 credited rows are accounted for. The token,
implicit-option, signature, restriction-disclosure, and line-limit checks passed.
Comparison with scratch/declaration-round2-before.json confirms unchanged code
in all 24 modules after removing comments, including all mathematical definition
bodies, generated-proof source expressions, imports, Bridge, and Solution proofs.
Only docstrings and assembly comments changed in Lean. No new proof or open
glue task was introduced.
