# Declaration review

All five declarations are **faithful**, with severity **none**. T21 and T31 are
faithful to their accurately disclosed restrictions; T22, T29 and T30 cover their
canonical mathematical claims in full.

| Declaration | Claim coverage | Record decision | Verdict |
| --- | --- | --- | --- |
| `SAP.P037b.T21` | Narrower | restricted | faithful |
| `SAP.P037b.T22` | Whole | whole | faithful |
| `SAP.P037b.T29` | Whole | whole | faithful |
| `SAP.P037b.T30` | Whole | whole | faithful |
| `SAP.P037b.T31` | Narrower | restricted | faithful |

T21 states both exact local probability vectors and exposure histograms, the
positivity/cutoff comparisons, supported seed/nonseed selections, and the
supported simulated-frequency witness. Its docstring and record correctly
disclose the omitted conditional selection masses and complete outcome-specific
membership-change certificate. The local block is the relevant marginal of a
legal four-block, 48-eligible school.

T22 covers the corrected population inclusions, five-label normalization,
supported strictness witness, scalar and joint cutoff probabilities under
independent draws, inverse-frequency bound, seed exclusion, corrected
nonconstancy condition, and outcome-specific prediction averages. Its explicit
constant nonempty analysis-set example correctly shows why positive seed
probability alone is insufficient. The supplied prediction table represents
existing fitted predictions; its values need no further restriction for the
claimed averaging identity.

T29 implements the canonical synthetic 40-eligible design, unique avoiding pair,
all probability and error claims, and independent-draw moments. Both the
Challenge and definition docstrings correctly attribute
`127007/161310320640000` to the **frequency** variance. Independence is encoded by
the product masses; the frequency-grid obstruction holds pointwise.

T30 covers the exact law, all moments and precision bounds, finite frequency
grid, one-sided positivity error, and general blocked-avoidance formula with all
four numerical examples. Actual peer subsets ensure subtraction is within its
natural domain, and legal draw sizes keep the binomial denominators positive.

T31 accurately states its retained support counts, representative pair
probabilities, eight-school second moments, and general identity conditional on
half marginals. Its restriction correctly discloses the omitted support and
pair-law assertions, variance identifications, and actual 56-school variance
examples. The displayed eight-school quantities are described as uncentered
second moments.

The blind reading was saved in `reading.md` before opening the claims;
`claim-stage.json` was saved before opening the record. No step-2 classification
changed after reading the record. Every closure declaration was inspected,
including all 83 generated auxiliary declarations. Their print check compiled.

`scratch/Check.lean` compiles concrete nonvacuity and supported-witness checks
using only Defs imports. `scratch/finite_checks.py` passes independent exact
enumerations of the 924-subset local designs, 63,504 rare-exposure peer pairs and
70/36 eight-school laws, together with exact arithmetic checks. No audited
assertion depends on a junk value or inconsistent hypotheses. `findings.json`
contains the five closure fingerprints and empty issue lists.
