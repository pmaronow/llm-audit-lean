# P030 review: T1–T5 (Aronow 2012, two-tailed rule and Equation (1))

Process: a blind reading (`reading.md`), then a comparison with `claims.json` (`claim-stage.json`), then a comparison with
`record.json`. Every SAP declaration in each closure was read. The `_proof_*` entries are auxiliary proof terms
(Fin-bound and similar proofs) and cannot affect meaning.

| Theorem | Record decision | Verdict | Severity |
|---|---|---|---|
| SAP.P030.T1 | whole | faithful | none |
| SAP.P030.T2 | whole | faithful | none |
| SAP.P030.T3 | whole | faithful | none |
| SAP.P030.T4 | refuted | faithful | none |
| SAP.P030.T5 | whole | faithful | none |

## Definitions (shared closure)

- `averageRank` is the midrank `#{<} + (#{=}+1)/2`, as in (S8f).
- `centeredRanks` subtracts `(n+1)/2`.
- `spearman` is the Pearson correlation of midranks with the square root (the corrected form of the definition).
- `nearestDistance` is the distance to the nearest *treated variant* unit (S7). It returns the junk value 0 on an empty set,
  but every use states that the set is nonempty.
- `uniformProbability` is the multiplicity-counting ratio (S8c). It returns the junk value 0 on an empty set, but every use is
  on a nonempty set: stated cardinalities 2, 6 and 10, `Fin 2`, `Fin 6`, or an explicit `Nonempty` hypothesis.
- `NoInterference` is H0'' with the `Z_i = Z'_i` reading.
- `NoEffects` is H0'.
- `conditionalAssignments` is Ω' (S8a).
- `statistic` and `referenceStatistic` are `t_z` and the imputed `t_0` (S8b).
- `printedReject` is the complement of the closed interval `[α/2, 1−α/2]`.
- `correctedReject` uses strict inequalities on both inclusive tails.
- `twoTailP` is `min{1, 2 min}`.

None of these is a placeholder, encodes a conclusion, or relies on a junk value that the claim presupposes away.

## Per declaration

- **T1** states every clause of the five-unit counterexample: the design, nonexperimental fixed units, Ω' = Ω with mass 1/2,
  constant outcomes for every z ∈ {0,1}^5, the distances, ranks, ρ = 1, both tails equal to 1, printed size 1 for every
  0 < α < 1 (including the α = 1/20 interval), and corrected size 0. The law on `Fin 2` is the conditional law, because the
  indexing is injective and each assignment has mass 1/2 (both stated).
- **T2** states every clause of the Table 1 null realization: the design and the conditional mass 1/6, the constant
  population, all rank details, exact values, squares, order and roundings, tails computed through `referenceStatistic`, the
  printed rule rejecting exactly the rows with p = 1 for 0 < α ≤ 2/3 with size 1/2, size above α for every α < 1/2, the
  corrected rule rejecting nothing, and three distinct values.
- **T3** states the claim's formal content: an arbitrary finite law and statistic, 0 < α < 1, and every proof step (i)–(vi),
  with strictness shown by the conjoined `T1Statement`. The restriction α < 1 is necessary: at α = 1 the equivalence in (vi)
  fails (checked in Lean). The link to the test under H0 is delegated by the claim itself to P030-T6.
- **T4**: `PrintedTwoTailedExactness` is exactly the printed universal claim. It quantifies over every design, every S, every
  observed assignment with nonempty Ω', every Y with no interference, every statistic of (Y_fixed, Z), α ∈ [0,1], the uniform
  conditional law, and the imputed lower-tail p with multiplicity. Because the canonical claim implies it, its negation
  contradicts the canonical statement's own assertion, so the label `refuted` and the docstring "The printed claim is false"
  are correct.
  - Printed reading, in one sentence: for every finite binary design, fixed subset chosen in advance, and statistic of
    (Y_fixed, Z_variant) with equally likely Z ∈ Ω' and every level α, if H0'' holds then the probability that the rule
    rejects is at most α.
  - Witness check: I compiled an in-class witness in `scratch/T4Witness.lean`, with no `sorry`. It uses the paper's own
    Spearman/D_nearest statistic on the T1 design, nonexperimental fixed units, Ω' = Ω uniform, no interference, and
    α = 1/20, and gives size 1. α = 0 cannot witness.
- **T5** states every clause of the Equation (1) counterexample:
  - H0' and H0'' hold, with the fixed-outcome null on Ω'.
  - The actual statistics differ at z^(2) and z^(5), both in Ω', and take exactly three values.
  - All numerics are stated.
  - p at the observed z^(7) is 1/3, rounding to 0.333.
  - Abstract point-mass contrast: a constant statistic gives P(t = t_obs) = 1 and p = 1.

## Scratch files

- `scratch/Check.lean`: `#check` and `#print` of the statements.
- `scratch/T4Witness.lean`: the in-class refutation witness for T4.
- `scratch/Nonvac.lean`: inhabitants for the internal hypotheses (a `FiniteLaw`, the α and u ranges, a constant statistic on a
  nonempty finset), the counterexample to clause (vi) at α = 1, and unit-index sanity checks.
- `scratch/notes.json`: per-declaration notes.

All files compile.

No issues found; every verdict is faithful with severity none.
