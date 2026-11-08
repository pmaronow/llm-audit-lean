# Review report: SAP.P008b.T20, T21, T22, T23, T25

I worked in the required order. `reading.md` (the blind reading) was written before I opened `claims.json`,
`claim-stage.json` before I opened `record.json`. The record did not lead me to change any step-2 conclusion.

| Theorem | Record decision | Verdict | Severity |
|---|---|---|---|
| SAP.P008b.T20 | restricted | faithful | none |
| SAP.P008b.T21 | restricted | faithful | none |
| SAP.P008b.T22 | refuted | faithful | none |
| SAP.P008b.T23 | restricted | faithful | none |
| SAP.P008b.T25 | whole | faithful | none |

## Per declaration

- **T20.** States all of formal content (a)–(c):
  - the 8-neighbour raster boundary, with the edge and area count means;
  - the 5×5 block: 25 cells, 16 on the boundary, a central 3×3 interior;
  - `{x | infDist x (frontier P) = 0} = frontier P`, with interior points at positive distance;
  - the T19 contrasts 0 and 9/25, and the AMRs 0 and 9/50.

  The one omission is the corrected sentence about the smoothed curve, and it is disclosed. The
  nonempty-raster-boundary hypothesis is a disclosed extra hypothesis. It is equivalent to R ≠ ∅ for finite R
  and is not needed for the identities. The nonempty frontier is already in `definitions_needed`, and it is
  needed, because `infDist x ∅ = 0`. No junk value can be reached.
- **T21.** States only formal content (i), −0.0321 < −0.0304. The restriction names exactly what is dropped:
  the actual assignment law and its quantiles, the significance inference, and the empirical conclusions.
- **T22.** A correct refutation of (i) under the type-7 percentile rule that (S9)(i) fixes and that is in the
  claim's `definitions_needed`. I checked the witness against every condition of the printed reading:
  - the field, the Euclidean circles, and positive, finite, integrable circle averages;
  - complete randomization of 2 of 4, so the permutations cover all six assignments;
  - the sharp null;
  - the Hájek estimator with both arms nonempty;
  - δ = 0.05, the strict rule, and the cumulative statistic over [0.1, 0.5].

  The rejection probability is 1/3. I re-derived the statistics, the quantiles ∓15/8 and the probability 1/3 in
  `scratch/Nonvac.lean`. A fully measurable witness exists (Dirac atoms, one per circle). Part (B) refutes (ii)
  in its error-rate reading. Part (C) confirms the nominal reading, and the docstring says so.
- **T23.** Exactly identity (i), for any finite design law, any matrix D and any cutoff. The restriction
  discloses everything dropped, including clause (ii), which per the note fails. T23 asserts nothing about
  (ii), so `restricted`, not `refuted`, is the right label for this theorem.
- **T25.** States (a)–(c) in full. `marginal` is exactly E over Z₋ᵢ with its marginal law, as in (S3)/(S4).
  `validCircle` contains only the claim's existence conditions: positive, finite circle measure and
  integrability for the overrides in the support. It also requires the circle to be measurable, which "the
  ζ-measure of the circle" presupposes. This is a usual measure-theoretic condition, covered by the docstring's
  "every existing circle average".

## Nonvacuity (compiled)

- `scratch/Check.lean`:
  - T21's and T22's numeral comparisons;
  - T20(A): a 3×3 raster has a nonempty boundary;
  - T20(C): the closed unit ball has a nonempty frontier.
- `scratch/Nonvac.lean`:
  - T22's arithmetic;
  - a T23 instance with genuinely zero cross-covariances and Var = 1/2, with the theorem applied;
  - a T25 counting-measure model satisfying `validCircle`, with parts 1 and 2 applied.

## Observations (not defects)

- T20's first docstring sentence is loose: it says that "zero-boundary-distance sets differ from whole-polygon
  summaries, as the explicit contrasts … demonstrate", but the continuous part is shown by the set identity,
  not by contrasts. Nothing in it is false.
- T25 does not literally say "the usual measure-theoretic conditions are assumed". Its only condition beyond the
  claim's explicit text is circle measurability, which the claim presupposes.
