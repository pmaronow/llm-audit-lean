# llm-audit-lean

Lean formalizations accompanying the [self-audit of P. M. Aronow’s work](https://pmaronow.github.io/llm-audit/).

[Browse results by paper](docs/works/README.md). Each target links directly to its formal statement, proof and definitions, with any restriction or omission explained.

| Scope | Results |
| --- | ---: |
| Works with formal targets | 50 |
| Targets | 1,021 |
| Whole | 805 |
| Restricted | 110 |
| Refuted | 73 |
| Omitted | 33 |
| Proved formal statements | 988 |

**Whole** covers the identified claim under its stated assumptions. **Restricted** proves a narrower statement or adds assumptions. **Refuted** supplies a counterexample to the precise formalized claim. **Omitted** has no current theorem. These labels do not certify an entire paper or every possible reading of its text.

The code and statement reviews were produced with AI agents; adapted third-party code is credited in [NOTICE](NOTICE). A checked proof establishes its formal statement. Whether that statement captures the intended paper claim is a separate judgment. Some results explicitly assume a named published theorem; read the hypotheses.

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

For scripts, [package/current-results.json](package/current-results.json) maps every current target to exact source locations. The older `catalog/` is preserved as historical component-credit data; it does not define current target outcomes. Source identities and exact imported file hashes are in [package/source-manifest.json](package/source-manifest.json).

Apache-2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE).
