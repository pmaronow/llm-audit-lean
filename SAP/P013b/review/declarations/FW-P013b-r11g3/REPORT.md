# Declaration review

All three declarations are **faithful**, with severity **none**. The record's
`whole` decisions and the three docstrings accurately describe the statements.
No step-2 conclusion changed after reading the record.

The review followed the required order: full blind source and closure inspection,
saved `reading.md`, canonical-claim comparison saved in `claim-stage.json`, then
`record.json`. All 76 distinct closure entries were inspected with Lean `#print`,
including generated numeral and finite-bound proofs. They introduce no hidden
assumptions. Each declaration was checked independently.

## T27

`Defs/Part10.lean:79` covers the canonical formal reading: binary fixed wearing
potentials, consistent observations, the five Section 10 exposures, positive
exposure probabilities, four differences of proportions, and unbiased HT
contrasts. General N includes the stated analysis population. The injection
models its inclusion in the full student network. Symmetry is supported by the
paper's undirected school network; self-neighbors are excluded as in its
zero-diagonal adjacency matrix ([paper, Section 10](https://arxiv.org/pdf/1305.6156#page=25)).
The observed-outcome definition implements Condition 2 directly and the
indicator-sum identity is explicitly concluded. The theorem does not claim to
verify empirical outcome coding or Table 2's numeric estimates.

## T26

`Defs/Part10.lean:16` contains every formal clause (a)–(h): support counts,
inclusion and a missing assignment, all marginal and pair laws, exact signed
differences, student-level marginal and same-school joint preservation, and
different-school no-exposure joint probabilities. The supports are actual full
finite assignment sets. Product averaging enforces the common student law's
independence from the school lottery. The arbitrary four-valued student code
includes the Section 10 own/peer code; a compiled Boolean case-check verifies
that specialization. Thus this abstraction drops no case of the claim.

## T25

`Defs/Part9.lean:16` contains all counterexample clauses (a)–(e), including
consistent binary school potentials, HT and expression (7), correct-input
equality, both signed wrong-input biases, and strict underestimation.

The reading being contradicted is: **the specified unblocked lottery can replace
the specified blocked lottery, including its joint-probability inputs, without
changing the design or losing expression (7)'s guarantee.** This is the reading
identified by the canonical counterexample and the docstring. The article's
printed block-randomization assertion is not refuted; `whole` is the correct
label for a theorem affirming this canonical counterexample.

The witness satisfies its conditions individually: 56 schools in 14 blocks of
four; uniform independent two-of-four choices for B; uniform 28-of-56 choices
for C; deterministic exposure equal to hosting, hence no interference; exactly
two distinct active schools with hosted outcome one and all other potentials
zero; consistent observed outcomes; exact hosting marginals 1/2; and positive
actual and supplied pair probabilities. The first-seven-blocks host set has
28 schools and belongs to C but cannot belong to B. Under B the two actual pair
probabilities are 1/6 and 1/4, while the supplied C probability is 27/110.
The resulting biases are respectively 52/81 and −1/27. Under C the correct-input
expectation equals the variance, 108/55. No dependent-replicate or undefined-
quantity construction is involved.

## Validation and junk values

`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean` completed successfully,
with no diagnostics. It imports only Defs and uses no Challenge theorem:

- Lines 12–62 construct all T27 hypotheses simultaneously, with nonconstant
  binary outcomes and every exposure probability exactly 1/5.
- Lines 65–116 construct members of both full school supports and independently
  prove that the separating assignment has 28 hosts, belongs to C, and is
  impossible under B.
- Lines 119–133 construct a normalized nonnegative student law with both
  same-school and different-school student pairs and check the exposure coding.
- Lines 136–153 instantiate all generic T25 moment premises with independent
  fair bits, p=1/4 and q=27/110.

Exact Python integer and rational checks independently reproduce the support
sizes, combinatorial ratios and all variance/bias values; results are saved in
`scratch/exact-arithmetic.json`.

Although real division assigns a value at zero, no target conclusion relies on
it: T27 assumes N>0 and positive exposure probabilities; both concrete school
supports are nonempty; the generic T25 marginal hypotheses exclude empty
supports; every variance-input denominator is positive. All sums are finite.
There are no nonintegrable expectations, infinite-to-real casts, problematic
extrema or limits, or partial-function defaults. The usual measure-theoretic
conditions hold automatically for these finite laws. The JSON outputs were
parsed and their target coverage and fingerprints checked against `closure.json`.
