# P016a review: T1, T2, T3, T4, T6

Process: blind reading (`reading.md`), then claims (`claim-stage.json`), then record. Scratch checks are in
`scratch/Print.lean`, `scratch/Nonvac.lean` (nonvacuity instances) and `scratch/AuxCheck.lean`. All compile with no
errors. I recomputed the numeric witnesses exactly with Python fractions.

| Theorem | Record | My reading | Verdict | Severity |
|---|---|---|---|---|
| SAP.P016a.T1 | whole | whole | faithful | none |
| SAP.P016a.T2 | whole | whole | faithful | none |
| SAP.P016a.T3 | whole | whole | faithful | none |
| SAP.P016a.T4 | restricted | narrower, restriction accurate | faithful | none |
| SAP.P016a.T6 | restricted | narrower, restriction accurate | faithful | none |

## Notes

- **T1.** Every clause of (i) and (ii) is stated with the claim's witnesses, orderings and conventions: the divisor-1/2
  listed-order covariance, inclusive tails, and population covariance under the design. `rss`/`ks` are exactly R/D of (S9).
  The complete and blocked designs are characterised as sets, and both enumerations are injective. One observation, not
  a defect: `pairedCovariance2` takes the literal lists (0,2),(1,3) / (0,2),(3,1). These are by inspection the
  treated/control values of u, u' under (1,1,0,0), which matches the claim's "listed order" pairing.
- **T2.** (A)–(G) map one-to-one onto the eleven conjuncts. `lsRSS` is a genuine infimum, and its attainment is stated.
  The FiniteLaw-with-`assign` form of (C)/(E) is a pushforward, so it covers every finite design. No junk value is
  reachable.
- **T3.** All four witness blocks match. I checked the recorded decimals digit by digit and recomputed both
  determinants exactly.
- **T4.** The added `hm` hypothesis on the raw identity (Defs/Part4.lean:83) is disclosed. Combined with `hbank`, it
  forces 0 < m < n, so the claim's m ∈ {0, n} cases are not asserted (`scratch/AuxCheck.lean`). This follows from the
  disclosed hypothesis, and the restriction describes that hypothesis exactly. The extra positivity premise on the sign
  identity (Part4:89) is disclosed and implied by the claim's own premise. The prose of the procedure (10,000-assignment
  bank, 500 draws, application tails, max-p bounds, Fig. 4 association, the simulation procedure as a whole) is
  disclosed as omitted. (b) is stated for an arbitrary vector, which is stronger than the claim. (d) and (e) are
  covered by the four-unit conjunct together with the embedded `T3Statement`.
- **T6.** The theorem states only the cancellation consequence of the display, for any g whose output has sample
  variance 1 on every design assignment. That includes the natural reading g = standardization. It also states the
  definitional p < 1/20 rule. Both are trivially true, but the triviality comes from the printed passage, which is only
  a model definition and a description. The docstring/restriction says exactly what is stated and what is omitted:
  arbitrary g, no affine normalisation, the linearity clause, SSR + Design identification, and empirical rejection
  rates. `IsDistanceMatrix` (including the triangle inequality) renders the claim's own "distance matrix Γ". It only
  narrows a statement that holds for every Γ. `restricted` is the right label: nothing in T6 contradicts the printed
  assertion.

No adverse findings.
