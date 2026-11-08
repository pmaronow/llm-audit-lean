All five declarations are faithful. No changes to the statements, definitions,
docstrings, or record decisions are needed.

| Declaration | Record decision | Verdict | Severity |
|---|---|---|---|
| `SAP.P002a.T1` | whole | faithful | none |
| `SAP.P002a.T2` | whole | faithful | none |
| `SAP.P002a.T3` | refuted | faithful | none |
| `SAP.P002a.T4` | whole | faithful | none |
| `SAP.P002a.T5` | whole | faithful | none |

The review followed the required order: `reading.md` was saved after reading
every closure entry and before opening the claims; `claim-stage.json` was saved
before opening the record. No step-2 conclusion was changed after reading the
record. T3's step-2 classification as “different” describes its negation of the
printed assertions; that is exactly the record's justified refutation decision.
T1 and T4 have canonical counterexample assertions, which their whole labels
correctly reflect.

T1 includes the complete finite counterexample, the repeated-block family,
the explicit evaluations and the failed arithmetic step. T2 states both
corrected variance bounds and every corrected chain and inclusion in its
canonical statement. The pointwise adjusted bound gives every subsequence term.
T4 states all four canonical counterexample parts, including the individual rank
constants, arbitrary singular-fit completions, the grid witnesses, class-infimum
bounds and the six-unit enumeration. Counting nonzero absolute studentized
statistics is equivalent to the canonical count of nonzero squared statistics.
T5 states both unrestricted liminf lower bounds on nonempty sizes and the
same-class necessary sequence conditions of the corrected Remark. Its additional
raw sharpness and degenerate-class conclusions are consistent with that claim.

For T3, the printed reading is: **each variance lower bound with factor
`1-delta` holds for every admissible model, including each adjusted subsequence
term, for the stated constants with `delta<1`.** The twelve-unit witness meets
each relevant condition:

- Exclusion is built into outcomes indexed only by receipt; every unit complies,
  so receipt is monotone, the complier set is nonempty and LATE is zero.
- `n=12`, `n1=2`, `r=1/6` give a valid, balanced design; all 66 treatment subsets
  have probability `1/66` under complete randomization.
- `delta=-1/2<1`, `A=B=2` and the covariance and fourth-moment bounds hold.
  Both potential-outcome variances and both population residual variances equal
  `12/11>0`, satisfying the Supplement's positivity convention as well.
- The single covariate is centered, its fourth moment is one, and its population
  Gram eigenvalue is one, above `e=1/2`. Both population OLS coefficients are zero.
- The raw variance is `5/396<65/4752`; the oracle variance is `36/55<39/55`.
  Repeating the blocks gives the same failures at unbounded sizes with fixed
  constants. The refutation uses neither dependent replicates nor undefined
  quantities.

The finite-sum definitions implement the paper's design distribution directly.
Population denominators are protected by valid designs; singleton complier
covariances are zero as prescribed. Finite least squares always has a minimizer,
so its fallback for nonexistence is unreachable. The studentization convention
at zero is explicit in the canonical setting and essential to T4. Empty
`ENNReal` fibers have infimum infinity. In T5, a bounded set of nonempty sizes
gives the bottom size filter and liminf infinity; this disclosed vacuous case
does not restrict or trivialize the assertions on cofinal nonempty sizes.

Validation used only the authorized Lean wrapper, with one Lean process at a
time. `scratch/Generated.lean`, `scratch/Check.lean` and `scratch/Sequence.lean`
all compiled. The first prints all 33 generated closure auxiliaries. The second
independently constructs the nondegenerate twelve-unit hypotheses and both
collapsed-class instances. The third independently constructs an infinite
balanced-sign sequence satisfying every raw sharpness hypothesis, including
positive baseline variance at every size. These witness proofs import no
Challenge theorem. Exact rational enumeration in `scratch/enumerate.py` confirms
both finite variance failures and the six-unit count of 312 nonzero reassigned
statistics among 400 pairs. The output JSON files were parsed and their target
coverage, fingerprints and verdict/severity consistency were checked with Python.
