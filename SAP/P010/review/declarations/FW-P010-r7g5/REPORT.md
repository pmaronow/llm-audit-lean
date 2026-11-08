All three declarations are faithful, with severity `none`. The record's three `whole` decisions are correct. No correction to a statement, dependency definition, or docstring is needed.

The blind readings and junk-value audits were saved in `reading.md` before opening `claims.json`. The comparison with the canonical claims was saved in `claim-stage.json` before opening `record.json`; the record caused no change to those conclusions. Every closure declaration was read, including the generated nonzero-numeral and scalar-tower proofs printed in `scratch/Inspect.lean`.

| Declaration | Canonical assertion and result of review |
| --- | --- |
| `SAP.P010.T21` | Under Assumptions 1–3, independence of observed check and assignment does not ensure equality of the selected contrast and always-passer effect. The existential statement asserts exactly this non-implication. Fixing two arms is sufficient to witness the existential finite-arm claim. |
| `SAP.P010.T22` | Under Assumptions 1 and 4, almost-sure agreement of potential checks implies conditional independence of the full covariate vector and assignment given observed check status. `covariateBalance` uses each positive-mass passing or failing stratum, as required. |
| `SAP.P010.T23` | Under Assumptions 1, 3 and 4, conditional covariate balance does not ensure equality of the two conditional contrasts. The existential statement gives precisely this failure at a positive-mass covariate value. Constant covariates are allowed by the canonical reading. |

`Population` and its coordinate definitions implement SUTVA directly. The randomization definitions use joint independence of each arm's outcome/check pair or outcome/check/covariate triple, matching Assumptions 2 and 4. They do not silently require independence of the full potential vector. `sameCheck` and `allPass` correctly distinguish common status from always passing.

The probability assumptions prevent infinite event masses. In T21 and T23, all three actual mean denominators are explicitly positive and every restricted integrand is explicitly integrable. Thus `meanOn` represents an ordinary conditional expectation, with no use of division by zero, `toReal` of infinity, or the zero value of a nonintegrable Bochner integral. The normalization in `covariateBalance` is used only for positive finite masses. The docstrings accurately describe these conditions.

`scratch/Check.lean`, importing only `SAP.P010.Defs`, independently checks full witnesses for T21 and T23. Three equally likely subject types have potential responses/checks `(1,1; false,true)`, `(0,0; true,false)`, and `(0,0; true,true)`. Assignment is an independent fair draw and covariates are zero. The file proves randomization, passing rates `2/3`, check/assignment independence, conditional covariate balance, integrability, conditioning masses `1/3`, and contrasts `1/2` versus `0`. This supports the printed non-implications; it does not refute either canonical claim.

For T22 the same file separately checks all hypotheses in a four-atom model with independent fair bits U,Z, common potential checks U, covariate U, and zero potential responses. There are two arms, nonconstant covariates, and both check strata have probability `1/2`.

Validation: `/home/ubuntu/sap/tools/sap-lean scratch/Inspect.lean` and `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`; JSON parsing, exact target coverage, required fields, verdict/severity consistency, and fingerprint equality are checked with Python. No unit source was changed.
