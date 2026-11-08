# P014 package

Seven whole targets, two restricted targets, one refuted printed claim, zero
omitted targets. All ten retained theorems are proved; there are no open glue
tasks. Only the ten targets in `unit_targets` are packaged.

| Target | Decision | Packaged result |
| --- | --- | --- |
| P014-T1 | whole | The complete specified six-row counterexample, assignment masses, arm means, estimator values, and weighted comparison. |
| P014-T2 | restricted | Corrected assignment-law unbiasedness and all four displayed derivation steps. |
| P014-T3 | whole | All five alternative-repair clauses, including the general-space fixed-outside application, uniform law on the choose(n,m) full assignments with exactly m treated window subjects, common-value characterization, and necessity. |
| P014-T4 | refuted | The explicit positive-arm counterexample satisfies both formal printed conditions and uniform local score permutations. |
| P014-T5 | whole | All six local-arrangement probabilities, three assignment masses, unequal propensities, and the no-interference estimator discrepancy. |
| P014-T6 | restricted | General-space consequences (a)–(c), the full-law converse in (d), and the independent-outside example (e). |
| P014-T7 | whole | General-law diagonal obstruction and decomposition, the nonempty-window obstruction, the corrected-local implication, and all three witnesses. |
| P014-T8 | whole | The bracketed contrast identity for a finite nonempty window. |
| P014-T9 | whole | The specified score law, conditional and printed averages, genuine other-subject direct effects, both sign discrepancies, pointwise estimator, and bias. |
| P014-T10 | whole | Conditional-sum identification, sign convention, estimator consequence, and explicit failure of the printed definition. |

## Restrictions

- **P014-T2:** Omits the final application from corrected running-variable
  randomization. In particular, the theorem does not transfer the general score
  law to an induced finite assignment law, derive its A1 and A2, or conclude
  unbiasedness directly from the score hypotheses. It retains the corrected
  finite assignment-law identity, positive denominators, arm moments, the
  fixed-count pointwise estimator, the linear expectation calculation, and its
  final factor cancellation. There are no extra assignment-law hypotheses.
- **P014-T6:** Omits only the forward direction of (d): adding the printed
  full-vector mass clause forces exactly one full supported vector above every
  local arrangement and consequently makes the outside scores a function of the
  local arrangement. The supplied finite-fiber theorems take a uniform local
  marginal on the full support as a premise. This package does not supply the
  identification of those fibers with the corrected general-space score law.
  It therefore does not add that identification as a new premise. The existing
  general-space converse constructs the full law directly and is retained,
  including existence, cardinality, masses, and its probability link to X.
  Parts (a)–(c) have exactly the canonical hypotheses; all of (e) is retained.

No targets are omitted. No retained theorem is awaiting a proof writer.

## Definitions and bridges

The shared-definition route is used. Six `Defs/Part*.lean` files import only
Mathlib and preceding Defs parts. Both Challenge and Solution import their
common compiled root. No project declaration is recreated in the project
namespace. Treatment and subject indices use `Fin N`, starting at zero.

`FiniteDistribution` contains distinct atoms and weights, with positivity and
normalization in the explicit `IsDistribution` premise. `toAudit` merely bundles
these premises into the project's `FiniteLaw`; `fromAudit` projects its two
data fields. Their data round trip and the probability, expectation, arm,
estimator, local-condition, and direct-effect correspondences are definitional
equalities. Pushforward atoms are a set image and their weights aggregate all
preimages, so repeated assignments are counted once.

- `Bridge/Part1.lean` contains the adapters and definitional equalities. Its two
  additional arm lemmas use the exported sum-to-one identity and elementary
  fraction algebra to establish positive denominators.
- `Bridge/Part2.lean` assembles T2, all five parts of T3, and T8 by instantiation,
  conjunction, substitution, and the exported fixed-count expectation identity.
  T3's law `A` explicitly represents the actual binary threshold distribution;
  it imposes no fixed or discrete outside-score requirement beyond the
  canonical fixed-outside-*treatment* assumption in that clause.
- `Bridge/Part3.lean` assembles T1, T4, and T9 from the exported witness facts.
  Zero-valued arms and pointwise numerical values use finite arithmetic on the
  exported four assignment atoms, masses, and outcome tables. Support counts
  use the existing injective-pushforward cardinality result. The bias
  differences use the exported expectations and targets.
- `Bridge/Part4.lean` assembles T5. Its finite enumeration is the six-row table
  already used in the source counterexample. The exported constant-arm-means
  theorem gives the common outcome value, and direct substitution checks the
  definition of no interference for this example.
- `Bridge/Part5.lean` instantiates the existing general-space randomization,
  full-law converse, diagonal, conditional-sum, and direct-effect-sign results.
  It adds only logical projections, numerical count inequalities, and transport
  of the already enumerated score permutations in the outside example.

Some components use usable rows credited elsewhere in this same unit. The
manifest records these in `cross_target_rows_used`. In particular, T7's local
implication is exactly the no-ties projection of T6's general randomization
row. The current packet explicitly supplies T2's A1 and A2, resolving the
historical missing-reference concern for T10(c). T4 uses T1's explicit witness
form of the refutation; its two credited universal-negation rows are accounted
for as not separately used.

The two `narrower` rows are not enlarged: the pushforward-only `expect_map` row
is not separately invoked, and the finite-law diagonal row is superseded here
by the already existing general-law result. The three canonical counterexample
targets T1, T5, and T9 are classified as whole, since their canonical claims
already assert refutations. T4's canonical claim is positive and is classified
as refuted.

## Verification and certification status

All sixteen Lean package files were compiled with the prescribed `sap-lean`
command, in dependency order: every Defs part and root, every Bridge part and
root, the Challenge part and root, and Solution. The expected Challenge stub
warnings were the only warnings in the completed compilation. Every file under
`SAP/P014/` has at most 300 lines.

`scratch/P014Axioms.lean` imports only Solution and prints the dependencies of
all ten theorems. The successful output is in `scratch/P014Axioms.log`; every
theorem uses exactly `propext`, `Classical.choice`, and `Quot.sound`. Those
results are recorded per theorem in the manifest. Both JSON files parse;
target coverage, row accounting, declaration names, identical Challenge and
Solution statement expressions, import boundaries, and the two implicit-variable
options were checked. The only proof placeholders are in the Challenge stubs.

`comparator.json` lists all ten proved theorems, the shared-definition policy,
the permitted dependencies, and the requested external-kernel commands.
**Comparator certification was not run in this session:** no Comparator tool or
executable was available, and `con-ron` and `nanoda_bin` were absent from PATH.
The package has passed Lean compilation and dependency checks; no claim of a
completed three-kernel certificate is made.

Existing project sources, input records, and pilot files were left unchanged.

## Declaration review round 1

- **SAP.P014.T3 — not_faithful/minor, docstring terminology:** Accepted the
  finding in [the T3 review entry](/home/ubuntu/sap/wt/ARCH-P014/fw/round1/T3/r2g1/findings.json). Independently
  checked canonical T3(c), `T3FixedOutsidePart` in
  [Defs/Part4.lean](/home/ubuntu/sap/wt/ARCH-P014/SAP/P014/Defs/Part4.lean:74), and its direct use of
  `AronowAudit.P014.fixed_outside_uniform_assignments` in
  [Bridge/Part2.lean](/home/ubuntu/sap/wt/ARCH-P014/SAP/P014/Bridge/Part2.lean:59). They specify uniform mass
  `1 / choose(n,m)` on the full assignments with exactly `m` treated window
  subjects. Corrected the docstring and the table above to describe this law.
  The previous phrase “binomial law” was inaccurate. No shared definition,
  theorem statement, proof, hypothesis, or decision changed; T3 remains whole.

The manifest records this correction on T3. The Comparator configuration was
regenerated and checked to preserve every configuration value. All sixteen
Lean package files recompiled successfully with `sap-lean` in dependency order;
only the expected Challenge stub warnings occurred. The fresh reports in
`scratch/P014Round1Axioms.log`, produced from
`scratch/P014Round1Axioms.lean`, confirm exactly `propext`, `Classical.choice`,
and `Quot.sound` for each of the ten proved theorems. Both JSON files parse,
all target names and statement expressions match, all SAP sources have both
implicit-variable options, and all package files remain within 300 lines.
Checksums confirm that shared definitions and proofs are unchanged. Counts
remain seven whole, two restricted, one refuted, zero omitted, ten proved, and
zero open glue tasks. Comparator certification status remains as stated above.

## Whole versions (new proofs)

The new whole proofs replace the restricted versions of P014-T2 and P014-T6.
The earlier restriction descriptions and counts above record the previous package.
Both Challenge stubs in [Challenge/Part1.lean](SAP/P014/Challenge/Part1.lean)
and the proved declarations in [Solution.lean](SAP/P014/Solution.lean) now use
the whole statements; [manifest.json](SAP/P014/manifest.json) records both as
`whole`, with no restriction and proof status `proved`.

- **P014-T2** (`SAP.P014.T2`): `SAP.P014.T2WholeStatement`
  from [Defs/WholeW1.lean](SAP/P014/Defs/WholeW1.lean), assembled as
  `SAP.P014.WH.W1.T2_whole` in
  [WH/W1/Proofs/T2.lean](SAP/P014/WH/W1/Proofs/T2.lean), using
  [WH/W1/Leaves.lean](SAP/P014/WH/W1/Leaves.lean) and the proved leaves
  [P/T2_L1.lean](SAP/P014/WH/W1/P/T2_L1.lean) and
  [P/T2_L2.lean](SAP/P014/WH/W1/P/T2_L2.lean).
  Old restriction now removed: Retains the complete corrected assignment-law identity, positive arm denominators, and all four displayed derivation steps under A1, A2 and 0<m<n. Omits the final application from corrected local running-variable randomization: the score-law-to-assignment-law transfer establishing A1 and A2, and unbiasedness under those score-law hypotheses. Adds no assignment-law hypothesis.

- **P014-T6** (`SAP.P014.T6`): `SAP.P014.T6WholeStatement`
  from [Defs/WholeW1.lean](SAP/P014/Defs/WholeW1.lean), assembled as
  `SAP.P014.WH.W1.T6_whole` in
  [WH/W1/Proofs/T6.lean](SAP/P014/WH/W1/Proofs/T6.lean), using
  [WH/W1/Leaves.lean](SAP/P014/WH/W1/Leaves.lean) and the proved leaves
  [P/T6_L1.lean](SAP/P014/WH/W1/P/T6_L1.lean) and
  [P/T6_L2.lean](SAP/P014/WH/W1/P/T6_L2.lean).
  Old restriction now removed: Retains (a)-(c), the converse direction of (d), and the complete independent-outside example (e). Omits only the forward direction of (d): that adding the printed full-vector atom-mass clause forces exactly one full supported vector above every local arrangement and hence makes the outside scores an almost surely deterministic function of the local arrangement. No additional hypotheses are imposed on (a)-(c).
