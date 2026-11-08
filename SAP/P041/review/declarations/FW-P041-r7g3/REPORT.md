# Declaration review

Both current declarations are **faithful**, with severity **none**. Every closure declaration was read, including the generated numeral proofs. `reading.md` was saved before the canonical claims and prior review were opened; `claim-stage.json` was saved before the record. The record required no change to the claim-stage conclusions.

| Declaration | Canonical comparison | Record assessment |
| --- | --- | --- |
| `SAP.P041.T11` | Narrower: the three numerical P1 calculations and bounds | The `restricted` decision and disclosure accurately describe the retained subset and its omissions. |
| `SAP.P041.T12` | Full coverage of symmetric arithmetic, directions, and the three individual directional failures | The `refuted` decision correctly addresses the three printed directional percentages. |

For T11, the earlier issue is fixed. `SAP/P041/Challenge/Part1.lean:96` and `record.json:6` now expressly omit the living-subgroup compatibility existence assertion, rather than merely cautioning that the central value does not round to 0.70. The numerical statement is unchanged, and its other omissions remain disclosed. All included SAP definitions correctly implement the stipulated Wald formula, standard-normal probability and rounding rectangles.

For T12, the canonical statement itself explicitly supplies the directional reading and the three count pairs. The theorem separately disproves each printed directional rounding, gives exact values and corrected roundings, and retains all symmetric-percentage and direction clauses. It therefore contradicts the printed numerical assertions themselves. Its documentation expressly limits the refutation to these percentages. The claim-stage `whole` classification records coverage of the canonical formalizable material; the record's `refuted` label describes its relation to the printed percentages. The detailed printed reading and condition-by-condition checks are in `claim-review.md`.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully with no diagnostics. It constructs simultaneous center witnesses for all T11 rectangle hypotheses, proves domain safety throughout every rectangle, verifies the T12 proportions, denominators and count bounds, and independently proves the entire closed T12 proposition by unfolded arithmetic. No reviewed statement uses a junk value, circular definition, inconsistent premise or encoded conclusion. No source changes are needed.
