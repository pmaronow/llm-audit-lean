# Review of SAP.P044.T13

**Verdict: faithful; severity: none.** The record's `refuted` decision is correct.
The printed description asserts that the generated baselines have the absolute
standard normal law. T13 contradicts that conjunct for every nonempty loopless
Boolean network under the supplied ideal Gaussian generator model. Refuting this
conjunct refutes the combined description; the multiplier and observation clauses
need not also fail. The docstring accurately states this scope and discloses that
identifying the model with the external R source is external provenance.

All closure entries were inspected, including the generated numeral proof.
The degree counts, scale, independent nondegenerate Gaussian product, baseline
map, and half-normal pushforward are concrete definitions. No extra substantive
hypothesis, vacuity, encoded conclusion, or operative junk value was found.

`scratch/Nonvacuity.lean` compiled successfully using `sap-lean`. It constructs a
triangle satisfying every hypothesis and independently proves that its baseline
law gives positive mass to negative values while the half-normal law gives zero.
The witness is a positive-probability rectangle, and all maps are Borel measurable.
The blind reading is in `reading.md`; the pre-record comparison and explicit
printed-reading condition checks are in `claim-stage.json` and `claim-audit.md`.
The record required no change to the claim-stage conclusion.
