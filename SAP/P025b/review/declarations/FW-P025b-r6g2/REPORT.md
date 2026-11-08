# Statement review

All five declarations are **faithful**, with severity **none**. The record's
five `whole` decisions are correct. No step-2 conclusion changed after reading
the record, and no fixes are needed.

| Declaration | Result | Coverage |
|---|---|---|
| `SAP.P025b.T17` | faithful | Count uniqueness, six exact corrections, all 42 rounding checks, the 36 unchanged cells, and the full gallery/exchange comparison grid. |
| `SAP.P025b.T18` | faithful | Both physical attainable sets, the normalized set, both extrema, and the singleton box and sample mean at ratio one. |
| `SAP.P025b.T19` | faithful | Corrected least cuts and physical optimizers, tied weights, the adjacent-cut equivalences, and every specified Supplement proof step. |
| `SAP.P025b.T20` | faithful | The entire binary attainable interval, both extrema, all boundary cases, and the class-sum derivation and monotonicities. |
| `SAP.P025b.T21` | faithful | Iid Brewer replication, both separation inequalities over the valid finite range, actual pooled extrema, and their almost-sure convergence to the class-box extrema. |

The definitions match the canonical notions. In particular, the corrected
lower cut uses `≤`; cuts test only existing next observations; physical weights
are normalized by a positive scale; and outcome classes are genuinely nonempty
and strictly ordered. A finite-state design loses no generality for a finite
population: every sampling law pushes forward to the finite set of population
subsets. The finite measurable spaces introduce no substantive restriction.

Every relevant nonempty-sample objective denominator is positive and every
attainable image used for a real infimum or supremum is nonempty and bounded.
For T21, `jointLaw` is a probability product measure with independent draws.
Initially empty pooled samples have totalized endpoints zero; the conclusion
explicitly supplies eventual nonemptiness, so those initial values cannot affect
the limits. Separation is jointly satisfiable, rather than an implicit
vacuity. None of the five items is a refutation.

The blind readings and full dependency accounting are in `reading.md`;
`scratch/ClosurePrint.lean` and its captured output inspect all 51 generated
auxiliary declarations as well as the source definitions. The unused real
empty-set extremum defaults were clarified in a marked post-blind addendum.
`claim-stage.json` was saved before opening `record.json`.

Validation: `/home/ubuntu/sap/tools/sap-lean scratch/AuditChecks.lean` exits
successfully. Its independent checks verify all 42 table cells, admissible
same-ratio bound pairs, both actual least cuts for `(0,0,1,1)`, binary mixed
and boundary instances, and a random singleton-sampling design satisfying every
T21 hypothesis. That design's product law has total mass one and independent
coordinates. The checks do not invoke any of the five audited theorems.
`findings.json` and `claim-stage.json` were parsed and checked for exactly the
five requested declarations, with fingerprints copied from `closure.json`.
