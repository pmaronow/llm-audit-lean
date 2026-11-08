# Review report — SAP.P013a.T11, T12, T13, T14

Process: blind reading (`reading.md`), then a check against `claims.json` (`claim-stage.json`), then a
check against `record.json`. No step-2 conclusion changed at step 3. All scratch files are in `scratch/`
and compile.

| Theorem | Record | Verdict | Severity |
|---|---|---|---|
| SAP.P013a.T11 | whole | faithful | none |
| SAP.P013a.T12 | refuted | faithful | none |
| SAP.P013a.T13 | whole | faithful | none |
| SAP.P013a.T14 | whole | faithful | none |

## T11 (degree-39 student, Section 9)
- The corrected claim's formal content (a)–(d) is stated clause by clause.
- Complete randomization is the uniform law on `n`-subsets of the school `U`.
- `d10` and `d00` match the printed exposure mapping, with 39 neighbours inside the school.
- No junk values: `C(|U|, n) > 0`, and the hypotheses force `|U| ≥ 40` and `n ≥ 1`.
- Nonvacuity: compiled for `|U| = 400, n = 40` and for `|U| = 50, n = 5`. In the second case `p ≤ 0.000675` holds, so the inner implication is not vacuous.

## T12 (Proposition 4.1 and the replicate rule; refuted)
- The printed reading has no sign condition, as the canonical claim states. Every hypothesis of `PrintedBiasBound` and `PrintedReplicateRule` is a condition of that reading:
  - full-support design;
  - replicates i.i.d. from the plan and independent of `Z` (product law);
  - add-one `π̂`;
  - exact `π_0`;
  - `y^T ≠ 0` (this only strengthens the refutation).
- The statement allows `R = 0` and asks for positivity only at `d`. To rule out a degenerate witness, I proved the stronger negations in `scratch/T12Strong.lean`, with `1 ≤ R`, positivity at every exposure and `b < 1`.
  - Witness: `signedReplicationPopulation 2`, `R = 1`.
  - `E = 2/9` and `y^T = 1`, so the relative bias is `7/9`.
  - This exceeds `(2/3)^2 = 4/9`, and also exceeds `b = 1/2`, where `1 ≥ log(1/2)/log(2/3) − 1`.
- "The printed claim is false" is therefore the right label and wording.

## T13 (Lemma 4.1, Proposition 4.2)
- The expectations, the variance formula (2), the contrast variance (5) and the covariance expansion (6), including its diagonal `−Σ y_i(d) y_i(e)`, are all stated exactly.
- Hypotheses: `0 < π < 1` for the exposures involved (a standing assumption), `d ≠ e`, and `N > 0`.
- Nonvacuity: compiled with `sharedPopulation 1`.

## T14 (Lemma 5.1, Propositions 5.1–5.2, Appendix A.5)
- Unbiasedness, the bias identity `E[V̂] = Var + A` (stated unconditionally) and the conservativeness of `V̂ + Â₂` are stated.
- Lean's `x/0 = 0` realizes the paper's `0/0 = 0` convention harmlessly: with full-support weights, `π_ij = 0` forces `1[D_i=d]1[D_j=d] ≡ 0`.
- The general results Prop A.1, Prop A.2 (conjugate exponents, `|y|^a`) and Cor A.2 are included. They allow zero-weight atoms, certainty units and outcomes of either sign.
- Nonvacuity: compiled three cases:
  - all joint probabilities positive;
  - a missing pair with mixed signs (`missingA = −6`);
  - a certainty unit in the general design.

No issues found. The four docstrings describe their statements accurately.
