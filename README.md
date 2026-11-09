# llm-audit-lean

Lean formalizations accompanying the [self-audit of P. M. Aronow’s work](https://pmaronow.github.io/llm-audit/). These formalizations were built as part of the verification effort, and are being provided without warranty as a potentially helpful resource. They have not been vetted to the standards of other posted formalizations, e.g., on Palomar.

[Browse results by paper](docs/works/README.md). Each target links directly to its formal statement, proof and definitions, with any restriction or omission explained.

| Recorded release scope | Results |
| --- | ---: |
| Works with formal targets | 50 |
| Targets | 1,021 |
| Whole | 805 |
| Restricted | 110 |
| Refuted | 73 |
| Omitted | 33 |
| Proved formal statements | 988 |

These are the certified release's recorded classifications. **Whole** records complete coverage of the selected formal target, which may itself be a counterexample; **restricted** records narrower coverage; **refuted** records a counterexample to the selected assertion or reading; **omitted** has no assigned current theorem. The selected object can be a corrected statement or a compound containing printed proof assertions. The current scope notes in the paper guides qualify correspondence to the published claim, including restrictions missed by the recorded classification. These labels do not certify an entire paper or every possible reading of its text.

The code and statement reviews were produced with AI agents; adapted third-party code is credited in [NOTICE](NOTICE). A checked proof establishes its formal statement. Whether that statement captures the intended paper claim is a separate judgment. Some archived supporting results assume named published theorems; current target assumptions are stated in each Challenge and its definitions.

## Use a result

Import its Solution entry, for example:

```lean
import SAP.Works.P009.Solution

#check SAP.P009b.T21
```

Challenge files expose the same statements with intentional proof placeholders. Use their links to inspect statements, and import Solutions to use proofs. Keep Challenge and Solution entries in separate Lean environments.

The project pins Lean and Mathlib 4.34.1. To build and check the full library, every current statement/proof entry and the axioms of all 988 proofs:

```sh
lake exe cache get
python3 scripts/build_current.py
```

See [verification and assumptions](docs/VERIFICATION.md) for the checking scope and replay evidence. The [supporting library guide](docs/HIGHLIGHTS.md) describes reusable lemmas.

For scripts, [package/current-results.json](package/current-results.json) maps every current target to exact source locations. The older `catalog/` is preserved as historical component-credit data; it does not define current target outcomes. Source identities, file hashes and documentation adjustments are in [package/source-manifest.json](package/source-manifest.json).

Apache-2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE).
