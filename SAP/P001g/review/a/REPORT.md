# Statement-referee report

Reviewed **14 targets and 13 theorem stubs**. The blind mathematical readings were saved in `reading.md` before opening `claims.json`; `claim-stage.json` was saved before opening `record.json`. No step-2 assessment was changed after reading the record.

| Verdict | Count |
|---|---:|
| correct_whole | 10 |
| correct_restricted | 3 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |
| **Total** | **14** |

Severity: **14 none, 0 minor, 0 major**. There are no adverse findings requiring a corrected statement or docstring.

The ten `correct_whole` findings comprise six positive results (T116, T125, T126, T127, T128, T130) and four faithful refutations (T118, T120, T121, T124). The refutations address the printed readings identified in the claims: positive normal variance, fixed-covariate KL minimization, consistency of the entire mixture parameter vector, and universal placebo F-test validity. Ordinary nonempty probability models witnessing them are described in `findings.json`.

The architect's three restrictions are accurate and appear verbatim in their theorem docstrings:

* **T115:** retains population random-assignment identification and the final ATT/selection-bias decomposition; omits the sample plug-in formula and the two intermediate equalities.
* **T117:** retains IPW and both double-robustness alternatives, while requiring measurable nuisance functions and separate integrability of both nuisance regressions in both alternatives. This is a real restriction: with fair treatment independent of a nonintegrable nonnegative covariate X, zero outcomes, correct propensity 1/2, and nuisance regressions m0(X)=X and m1(X)=−X, the combined augmented score is identically zero. Both separately nonintegrable regressions are excluded, exactly as disclosed.
* **T129:** retains actual-product MLE consistency under the explicitly stated compactness, finite-log, positivity, population-objective and uniform-error-envelope premises. The error envelope is an additional hypothesis covering every sample size, sample point and parameter. The independent expected-log lemma has its own normalized-model, support-domination and integrability domain. The product/log identity, unique sample maximizer, separate pointwise WLLN conclusion and derivation of uniform regularity are accurately listed as omitted.

**T119 omission is justified on the supplied evidence.** The printed criterion omits the square, and the repaired claim does not define “consistent across regions.” The transcription note adopts an integrated L² interpretation, while the record expressly withdraws credit because that interpretation was not established as the printed meaning. No retained candidate theorem for this target is present in the permitted files. Conservative omission accurately reflects this limitation; confidence in the omission assessment is lower than in the inspected theorem types.

For **T127**, global continuity of the density is supported by the p.121 sentence expressly included in the canonical claim. The theorem covers that global-continuity reading. The more general result requiring continuity only at the evaluation point is discussed in the transcription note, but is not additionally certified by this stub. The omitted finite-sample formulas for T127 and T128 are proof auxiliaries rather than additional conclusions of their theorem statements.

Verification used the supplied definitions and Mathlib sources, with no Solution or Comparator inspection. `scratch/Check.lean` imports only `SAP.P001g.Defs` and compiles without `sorry` using `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`. It checks constant and nondegenerate Gaussian iid instances, finite second moments and positive Gaussian variance, a fair binary treatment law with positive arm probabilities and a genuine propensity CEF, a zero CEF, the constant-functional Hadamard condition, positive guarded residual degrees of freedom, and the explicit mixture law. `scratch/population_check.py` checks the placebo population calculations with exact rational arithmetic; its results are saved in `scratch/population_check.json`. These checks support the statement audit; they do not replace the separate certification of theorem proofs.

Both requested JSON reports were parsed and their target coverage and permitted field values checked with Python 3. The supplied Lean files were left unchanged.
