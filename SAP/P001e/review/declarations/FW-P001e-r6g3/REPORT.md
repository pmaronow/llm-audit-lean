# Declaration review

The blind reading was saved in `reading.md` before any claim, record, or earlier
review was opened. Every closure entry was read, including the eleven generated
numeral certificates printed in `scratch/ClosureChecks.lean`. `claim-stage.json`
records the independent comparison with the canonical statements. The prior
review and architect report were read after the blind stage and before the
record stage.

At the claim stage, T87–T90 cover their canonical mathematical content. T91
covers a narrower, explicitly disclosed identification result. The definitions
use ordinary conditional-mean versions, measurable indicator factorizations,
weighted sums and integrals. Positive cells or integrability protect all queried
conditional means and sums. No statement depends substantively on a junk value.

For T90 the printed reading is: conditional independence of the supported
potential-outcome process and treatment given discrete covariates, together with
a positive treatment density on the support, identifies every supported-dose
average contrast from the observable law, without requiring continuity.
The witness meets each condition:

| Condition | Check |
| --- | --- |
| Probability space and dose | Restricted Lebesgue measure on [0,1] has mass one; D is the identity and has density one. |
| Discrete covariates | X is constant zero. |
| Process independence | Both potential-outcome processes are deterministic functions of dose, hence independent of D conditionally on X. |
| Consistency | The observable is the zero or spike curve evaluated at D. |
| Measurability and finite quantities | The singleton indicator is Borel and bounded; the deterministic coordinates and observed diagonal are measurable and integrable. |
| Supported queried doses and positivity | 0, 1/4 and 1/2 lie in the stated uniform support; in particular both 1/4 and 1/2 are interior points with positive density. |
| Sampling | Independent product copies preserve both model laws and process independence. |
| Failure of identification | The observable maps agree except at the null singleton {1/2}, while the contrasts at both queried pairs are 0 versus 1. |

Thus this witness attacks the printed assertion itself; it does not attack a
continuity-qualified interpretation or exploit undefined conditioning on a
singleton. The full closed T90 proposition is checked independently in scratch.

The record-stage review leaves the claim-stage readings unchanged:

| Declaration | Record decision | Verdict | Main check |
| --- | --- | --- | --- |
| T87 | whole | faithful, none | All four corrected CEF clauses are present; neither an exact working model nor a numerical fit is asserted. |
| T88 | whole | faithful, none | Both sharp observable endpoints, all compatible mean effects, positive-sample unbiasedness, and consistency are present under observable IID sampling. |
| T89 | whole | faithful, none | The exact latent law, full corrected PMF, all conditional arithmetic, and the failure of conditional independence are present. |
| T90 | refuted | faithful, none | The witness meets the printed conditions listed above and changes both target contrasts while preserving the observable law. |
| T91 | restricted | faithful, none | The all-real process premises and curve-state contract are visible; the docstring and record accurately disclose what is added and omitted. |

All three earlier T91 issues are **fixed**. The current closure contains
`T91ContinuousIdentification` and its measurable state/evaluation contract,
rather than the old cylinder-only diagonal witness
(`SAP/P001e/Defs/DoseIdentification.lean:21–60`). The Challenge docstring now
describes identification with restrictions and makes no refutation claim
(`SAP/P001e/Challenge/Part1.lean:113–131`). The record now labels T91
`restricted` and expressly disclaims deriving the continuous result from
supported-cylinder independence alone (`record.json:68–77`). The architect's
current explanation agrees with these changes. The old diagnostic outside the
current closure supplies no premise or conclusion of this declaration.

`scratch/Nonvacuity.lean` compiled successfully using `sap-lean`; no Challenge
theorem is invoked by its checks. It constructs a fair binary response model
for every T87 premise, a genuine infinite independent-coin sequence for every
T88 premise, and verifies normalization, positive conditioning cells, the
covariate effect and the adjusted contrast in T89. The six-atom law's three
latent-variable values each occur once in each treatment arm, which also checks
its asserted randomization directly. For T90 the complete closed proposition,
spike measurability and integrability, and process independence are checked.
For T91 both clauses have complete premise instances: a fair binary dose with
Y(t)=t for (a), and a uniform continuous dose with Unit-valued curve state,
evaluation e(t,s)=t, and distinct interior doses 1/4 and 3/4 for (b). The latter
check proves neighborhood positivity for every positive radius and constructs
a continuous observed CEF version.

No current issues remain. `findings.json` has exactly five entries, with the
fingerprints copied from `closure.json`; the output JSON files are checked
with Python.
