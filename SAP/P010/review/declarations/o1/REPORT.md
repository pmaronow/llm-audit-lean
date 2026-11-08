# Review of SAP.P010.T1–T5 (Aronow, Baron & Pinson 2019, Political Analysis)

Process: blind reading (`reading.md`) → claim stage (`claim-stage.json`) → record stage → `findings.json`.
Scratch checks: `scratch/Check1.lean` (#eval of all T1/T2 values), `scratch/Check2.lean` (#print of every
auxiliary closure declaration — all are numeral/`IsScalarTower` instances), `scratch/NonvacT4.lean`
(nonvacuity of T4's hypotheses, compiles cleanly), plus an independent exact-fraction Python recomputation of
the authors' j/n trimming rule.

| Theorem | Record decision | My reading vs claim | Verdict | Severity |
|---|---|---|---|---|
| SAP.P010.T1 | refuted | whole | faithful | none |
| SAP.P010.T2 | whole | whole | faithful | none |
| SAP.P010.T3 | refuted | whole | faithful | none |
| SAP.P010.T4 | whole | whole | faithful | none |
| SAP.P010.T5 | refuted | whole | faithful | none |

Key points:

* **T1** refutes both readings of the printed overlap sentence (pairwise and triple overlap) for the
  unweighted Figure-2 preference bounds. The counts are the canonical supplied inputs, and the
  `keptLower`/`keptUpper` formulas equal the authors' rule (lower j/n < 1 − trim, upper j/n > trim), which I
  confirmed by brute force. The asymmetry 284 vs 285 is the rule itself, not an artefact. Every condition of
  the printed reading holds for the witness.
* **T2** states every exact value and conclusion in (a)–(d) of the corrected text, and also characterises the
  retained counts. Remark, not a defect: the docstring phrase "under both trimming rules" is accurate for the
  preference separations. Approval overlap is stated, and claimed, only for the integer rule. The
  fractional-rule approval intervals also contain 1/2 (I checked this), but that is neither stated nor claimed.
* **T3**: the witness matches the canonical strata exactly and satisfies every hypothesis of the printed
  Proposition 1 (Assumptions 1–3, Pr[A] > 0, continuity, full support, all moments, r = 1/2 < 1, passer
  quantile 0). The printed outer means, which omit S = 1, are ∓3/4 and exclude the target ±1. This contradicts
  the printed display itself, so `refuted` is correct.
* **T4**: hypotheses and conclusions match the corrected finite branch clause for clause, including attainment,
  sharpness over all compatible laws, the L-identities, the r = 0 case and both quantile-integral forms. The
  `meanOn` junk value (a non-integrable integrand) cannot occur for compatible laws, by per-arm ignorability
  and `hi`. `hA` follows from `hr`.
* **T5**: the witness satisfies the printed hypotheses literally (Y has full real support and E|Y|³ < ∞) and
  the else branch (r = 2). The identified set lies in (0,1), with GLB 0 and LUB 1 (finite), which contradicts
  the printed claim that −∞ and ∞ are sharp. `refuted` is correct.

No junk-value convention affects the meaning of any of the five statements. No hidden hypotheses were found.
