# Review of P010-T11–T15

All five declarations are faithful, with severity **none**.

| Declaration | Record decision | Verdict |
| --- | --- | --- |
| SAP.P010.T11 | whole | faithful |
| SAP.P010.T12 | whole | faithful |
| SAP.P010.T13 | refuted | faithful |
| SAP.P010.T14 | whole | faithful |
| SAP.P010.T15 | whole | faithful |

The blind statements and every dependency listed in `closure.json` were read
before opening the claims or record. Generated auxiliary declarations were
printed with Lean; they only support numerals and scalar operations.
`reading.md` was saved before the claim comparison, and `claim-stage.json`
was saved before reading `record.json`. The record required no change to the
claim-stage conclusions. Its labels and the five docstrings are accurate.

T11 supplies the complete two-cell logistic example and explicitly identifies
the exact-distribution-matching reading it challenges. T12 covers every Bayes,
transport, scaling, finite-normalizer and infinite-mass clause, using true
propensities. T13 contradicts the printed upper-bound inequality itself:
its valid normal witness has target mean zero and a strictly negative printed
lower-tail bound. The printed readings and condition-by-condition witness
checks appear in `claim-checks.md`.

T14 includes fixed-mass optimization and attainment, monotonicity, the union
bound, and the corrected potential tail bound. Its claim-stage classification
as broader records a valid strengthening: random assignment is unnecessary
for this potential-variable result. Every canonical clause is still covered,
so the record's whole label is accurate. T15 includes both law and trimming
share identities and the corrected observable bound, with passing retained
in the conditioning event. Its tail-mean identity covers the domain where
the ordinary conditional means exist; atomless tails at ratios at least one
have zero probability.

The totalized divisions, conditional laws, integrals, extended-real conversions,
and quantiles introduce no defect. In particular, the zero quantile is kept
extended and selects the entire law. T12 handles infinite normalizers as
extended masses rather than treating a nonintegrable Bochner integral as
a normalizer. All population maps used here are measurable, so Mathlib's
default pushforward for nonmeasurable maps is irrelevant.

Independent Lean checks compiled with `sap-lean`:

- `scratch/Nonvacuity.lean`: logistic probabilities, weighting counterexample,
  and all T12 hypotheses for distinct finite distributions.
- `scratch/InfiniteMass.lean`: positive probability densities satisfying all
  density hypotheses with infinite square-ratio mass.
- `scratch/OneArm.lean`: explicit Gaussian instances satisfying every T14
  and T15 hypothesis, with the finite-branch condition active.
- `scratch/NormalWitness.lean`: T13's actual population normalization,
  positive always-passer mass, Gaussian observed law, atomlessness and
  integrability. Independence and the remaining Gaussian witness facts
  were checked directly as documented in `claim-checks.md`.

These mathematical checks import definitions without invoking Challenge
theorems. No SAP source was changed. `findings.json` contains exactly the five
requested declarations and their supplied fingerprints.
