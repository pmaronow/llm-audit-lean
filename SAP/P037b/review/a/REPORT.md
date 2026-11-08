# Referee report

15 targets: 13 theorem stubs and 2 omissions.

| Verdict | Count |
|---|---:|
| `correct_whole` | 2 |
| `correct_restricted` | 10 |
| `restriction_inaccurate` | 1 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 2 |
| `omission_questionable` | 0 |

Severity: 1 minor; 0 major. No theorem was found false or vacuous.

P037-T29 — `restriction_inaccurate`, minor.

The restriction at `SAP/P037b/Challenge/Part1.lean:50`, repeated in `record.json`, says it omits the “r=0/r≥1 error equalities.” Canonical (iii) gives an equality at r=0 and an inequality at r≥1: with p=1/127008, the latter is |r/10000−p|≥1/10000−p>p. The Lean theorem retains the common error floor, but does not separately assert this stronger r≥1 bound. The statement is mathematically correct; the disclosure should name the omitted inequality accurately.

Replace “the separate r=0/r≥1 error equalities” with “the separate error equality for r=0 and the stronger error bound |r/10000−p|≥1/10000−p>p for r≥1 (where p=1/127008).” Apply this wording in both the docstring and record. No Lean statement change is needed.

The whole decisions for T25 and T30 are supported. T25 distinguishes the nomination-row and either-direction-row readings without claiming the ambiguous printed assertion itself is false. The remaining ten restricted decisions accurately disclose their omissions. T29 is also narrower as recorded; its only reported defect is the wording above. No step-2 classification was changed after reading the record.

The omissions of T16 and T17 are justified for their complete canonical targets: empirical table/procedure descriptions and an empirical effect claim are not established by the supplied formal objects. The arithmetic fragments and the audit-history interpretation of bootstrap terminology do not establish or refute those entire canonical assertions. No equality with a Dirichlet law was silently added to the printed T16 assertion.

The blind reading was saved in `reading.md` before `claims.json` was opened. `claim-stage.json` was saved before `record.json` was opened: 2 whole and 11 narrower theorem readings. The record restriction text was checked against all 11 corresponding docstrings.

Verification: `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully with no errors or warnings. The scratch file imports only `SAP.P037b.Defs`, and uses no Challenge theorem or sorry. It checks full-rank designs, a nondegenerate probability measure with the required moments, a nonempty analysis population, supported seed sets and positive kept-group denominators. `python3 scratch/audit_finite.py` passed all exact-arithmetic and enumeration assertions; details are in `scratch/finite-checks.json`. These checks supplement the mathematical statement review and do not constitute a proof audit of the Solution or Comparator.

Conventions checked: full rank prevents the singular-matrix inverse fallback; first and product integrability prevent undefined Bochner integrals; positive finite-support masses match the canonical support convention; the four retained exposures are mutually exclusive even when a fifth direct exposure is present. All substantive estimator denominators are positive. Excluded IPW summands reduce to a sum over included units; the empty-block ratio at B=0 has no effect on an atTop limit. Peer cardinalities are at most block sizes, so natural subtraction in the avoidance formula is valid. The quantile defaults are never used with positive interpolation weight in either fixed graph. Nonempty instances are recorded for every quantified theorem in `findings.json`.
