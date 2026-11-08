# P020 statement review

Both declarations are **faithful**, with severity **none**. The record correctly
labels both `whole`, and both Challenge docstrings accurately describe their
statements. No step-2 conclusion changed after reading the record.

The blind reading of both full statement closures, including generated proof
declarations, was saved in `reading.md` before opening `claims.json`.
`claim-stage.json` was saved before opening `record.json`.

## SAP.P020.T16

`SAP/P020/Defs/Part4.lean:204` matches the entire canonical claim: expected
conservativeness for the specified observed-total sharp-null variance statistic
under either constant **cluster-total** effects or balanced cluster counts.
The definitions use uniform complete cluster randomization and finite-population
variance with divisor M. The conclusion is an expectation inequality, exactly
as required; it makes no pointwise conservativeness claim. The Des Raj citation
in the docstring is a source location, not an additional asserted result.

Both alternatives are nonvacuous, independently of each other. The compiled
examples have true variance versus expected variance estimate of 3/8 versus
1/2 for unbalanced constant effects, and 1/9 versus 2/9 for balanced varying
effects. Every relevant denominator is positive under the population fields.

## SAP.P020.T17

`SAP/P020/Defs/WholeW1.lean:272`, including its `T17Statement` conjunct, covers
the canonical replication constructions, unchanged targets, four weak-law
limits, pooled convergence, and the fixed-cluster invariance and persistent
bias. The product cluster set and its arm counts match the printed population.
Although the generic `DesignConsistent` definition expresses convergence
without size data, `W1ReplicationGrowth` separately certifies strict growth of
total size and both realized individual arm sizes for both claimed sequences.

The independent-copy design is explicitly the uniform law on all finite tuples
of supported assignments and is realized by an infinite product probability
measure. Its coordinate independence, finite prefix laws, and event-law bridge
are conclusions. Reusing one draw occurs only in the within-cluster sequence,
where it correctly realizes the unchanged randomization distribution.

The compiled witness has bias -1/315 and error probability one at tolerance
1/25. Its three estimator values persist for every positive within-cluster
replication factor, while its size is 7h. It satisfies the printed setting and
supports the claim that large N alone need not give consistency. It does not
refute the canonical independent-copy convergence assertion.

All population ratios exclude h=0; zero prefixes are used only in valid
finite-law identities. `Measure.real` is applied to probability measures, so
conversion of infinite mass to zero cannot affect any conclusion. Finite
discrete statistics and their finite-prefix realizations are measurable.
There are no substantive hidden assumptions, encoded conclusions, vacuous
premises, or relevant junk-value dependencies.

## Validation

`scratch/Inspect.lean` compiled and printed every generated closure auxiliary.
`scratch/Check.lean` compiled successfully without using either audited theorem
in its proofs. Besides the numerical checks, it constructs positive population
data and individual outcomes and verifies that two independent copies have
nine possible assignment pairs, with probability 1/9 for an explicit pair of
distinct draws. The JSON outputs were parsed and checked with Python 3.
