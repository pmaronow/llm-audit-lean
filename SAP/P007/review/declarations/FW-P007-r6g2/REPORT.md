All five declarations are faithful to their canonical claims. Each record
decision of `whole` is accurate, and the docstrings describe the statements
without a material omission or overstatement.

| Declaration | Verdict | Severity | Coverage checked |
| --- | --- | --- | --- |
| `SAP.P007.T6` | faithful | none | Finite Bernoulli sandwich, probability inequalities, zero endpoint, log identity, group counts |
| `SAP.P007.T7` | faithful | none | Every specified equality, rounding, worked-value and actual-probability counterexample |
| `SAP.P007.T8` | faithful | none | Real inverse, integer boundaries, sharpness, probability guarantees, both worked values |
| `SAP.P007.T9` | faithful | none | Complete normalized 2×2 witness, least observation bound, expectations and all-deletion probabilities |
| `SAP.P007.T10` | faithful | none | Arbitrary probability spaces, independence-free expectations, independent-cell attainment, complete endpoint comparison |

The blind expansion was saved in `reading.md` before opening the claims. Its
SHA256 is `cb0b429d080af9bd34a66472a6fb8805f2926da31a9829de30723c6255976a1a`.
Every closure declaration was read, including the 22 generated numeral
proofs inspected by compiling `scratch/Closure.lean`. `claim-stage.json` was
saved before opening the record; no claim-stage conclusion changed afterward.

`claim-audit.md` gives the clause comparisons and explicitly lists the printed
readings and every counterexample condition. The product weights enforce
mutual cell independence and normalization. A finite law represents every
joint distribution of a finite Boolean array, so T6–T9's representation adds
no substantive restriction. The conditional-ratio guards match the printed
positive-prefix proviso. The supplied canonical assertions control these
verdicts; the publisher's [Figure 4–5 discussion](https://static.cambridge.org/content/id/urn%3Acambridge.org%3Aid%3Aarticle%3AS1047198722000055/resource/name/S1047198722000055sup001.pdf#page=2)
was also consulted for context.

`scratch/Check.lean` constructs normalized product laws and proves their row
independence, checks positive-q and q=0 admissible instances, independently
proves the entire T9 witness, and constructs a measurable probability-space
instance for T10 with a defined integral. It imports definitions and uses no
Challenge theorem or `sorry`. Exact rational enumeration of the small
witnesses and 90-digit numerical checks of both large worked examples are
saved in `scratch/numeric-evidence.json`; the decimal calculations are sanity
checks, while certification of the audited statements is given in the task.
The Lean commands for `scratch/Closure.lean`, `scratch/Check.lean`, and the
isolated `scratch/Space.lean` all completed with exit code 0. Python validation
confirmed the JSON schemas, exactly five entries, and every copied fingerprint.

No statement relies on division by zero, an out-of-domain logarithm or real
power, a truncated floor, a default nonintegrable integral, or conversion of
infinite measure to zero. No fix is required.
