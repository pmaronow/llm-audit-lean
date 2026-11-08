# Review of SAP.P005b.T15–T19

All five declarations are **faithful**, with severity **none**. T15–T18 state
their complete canonical claims; T19 correctly refutes the canonical uncentered
covariance lemma. The architect's four `whole` decisions and one `refuted`
decision are accurate, and the docstrings describe the elaborated statements.
No step-2 conclusion changed after reading `record.json`.

I saved [reading.md](reading.md) before opening the canonical claims, and saved
[claim-stage.json](claim-stage.json) before opening the record. Every closure
entry was read, including generated numeral proofs, structure projections and
arm eliminators. The definitions use the correct finite population and arm
averages, uniform complete randomization, covariance normalization, residuals,
Gram contraction and normalized maximum leverage. No relevant assertion relies
on a junk value or inconsistent hypotheses.

| Declaration | Coverage and evidence |
|---|---|
| T15 | Both coefficient identities, the intermediate fraction, and the covariance combination in `Defs/Part3.lean:33`. A compiled instance has two nonzero covariances and combined value 5/18. |
| T16 | All corrected indicator calculations, decomposition, coefficient identities, complement relation, and both third moments in `Defs/Part3.lean:48`. A compiled centered nonzero instance has third moments 2/9 and -2/3. |
| T17 | `Defs/WholeW1.lean:47` includes the entire original contraction/order statement, the actual residual-star variance bound, and the stochastic order. The audit-history exclusion in `finite_lemmas` was not treated as removing a canonical clause. Positive-dimensional and zero-dimensional sequence hypotheses both compile. |
| T18 | `Defs/Part4.lean:59` includes the three bracketed vectors, weighted normal equation and identification with the actual residual star. A standardized positive-dimensional instance has star=1/6. |
| T19 | `Defs/Part5.lean:13` negates precisely the printed universal conjunction; `Challenge/Part1.lean:29` accurately describes that conjunction's failure. The expectation identity need not fail to refute it. |

For T19, the printed reading asserts both formulas for every fixed pair of
arbitrary, uncentered vectors under complete randomization. With n=6, m=5,
the treated arm, a=(20,1,1,1,1,1) and b=(1,20,20,20,20,20), the covariance is
-1444/25 on five assignments and zero on the sixth. Its variance is
521284/1125, while the printed bound is 54027/125, a strict difference of
35041/1125. The expectation identity still holds. Every printed condition is
checked in [the witness record](scratch/t19-witness.md); the failure concerns
the claim's own assertion.

Validation: `scratch/BlindCheck.lean`, [scratch/Check.lean](scratch/Check.lean),
and [scratch/SequenceCheck.lean](scratch/SequenceCheck.lean) all compiled using
the prescribed `sap-lean` command. The latter two import definitions only and
contain no `sorry`, `admit`, or added axioms. The zero-dimensional check proves
that both kappa and the actual star are zero, including the zero-rate stochastic
order. JSON validation confirms exactly five findings and exact fingerprint
matches with `closure.json`.
