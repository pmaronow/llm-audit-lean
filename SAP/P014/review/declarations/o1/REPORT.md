# P014 declaration review: T2, T8, T3, T7, T4

Process: I did a blind reading first (`reading.md`), then compared against the claims (`claim-stage.json`), then
against the record. Nonvacuity instances are compiled in `scratch/NV1.lean` … `scratch/NV5.lean`, and all of them
compile.

| Theorem | Record decision | Verdict | Severity |
|---|---|---|---|
| SAP.P014.T2 | whole | faithful | none |
| SAP.P014.T8 | whole | faithful | none |
| SAP.P014.T3 | whole | faithful | none |
| SAP.P014.T7 | whole | faithful | none |
| SAP.P014.T4 | refuted | faithful | none |

## Per declaration

- **T2** (`T2WholeStatement`, WholeW1:111). The assignment part works on any probability space with a measurable Z.
  Under (A1) a fixed treated count m (0<m<|S|) a.s. and (A2) P(Z_i=1)=m/|S|, it states every clause of the corrected
  claim:
  - the weighted Ȳ_i(a) over Supp(Z) (`assignmentLaw` has atoms = the vectors of positive probability) equals
    E[y_i(Z) | Z_i=a];
  - the denominators m/n and (n−m)/n are positive;
  - proof steps (1)–(4) all appear;
  - E[τ̂] = bracketed τ = (1/n)[Σ−Σ].

  The score part derives (A1), (A2) and the identity for every y from the corrected uniform-arrangement assumption,
  with the outside coordinates unrestricted. The extra hypotheses `0<b` and `v ⊂ [−b,b]` are implied by the setting.
  No junk value can be reached: positivity and integrability are asserted.
- **T8** (Part5:97). This is exactly the claim's identity (1/n)Σ[u_i−w_i] = (1/n)[Σu−Σw] for nonempty S.
  `windowContrast` is the bracketed τ.
- **T3** (Part4:107). Its five conjuncts match claims (a)–(e):
  - `ConditionallyUniform` is (U).
  - The fixed-outside part gives C(n,m) support points, m!(n−m)! arrangements per point and weight 1/C(n,m).
    It also gives (A1), (A2), (U) and the printed identity, and shows that every vector with m treated in the window
    is in the support.
  - The necessity part needs only P(Z_i=a)>0, which is more general than the claim.
- **T7** (Part5:91). The literal quantifier holds iff S=∅, and it equals the corrected condition plus the diagonal.
  If 0<m<|S|, the literal condition fails. Distinct-subject no-ties holds under the T6 corrected assumption and for
  the T1, T5 and T9 laws (scores1, scores5 and scores9 under uniformSix, S=localThree).
- **T4** (Part3:40). This is a genuine refutation of the printed assertion under its printed reading. The no-ties
  clause is read for distinct subjects, as the paper's own words and standing assumption R6 say, and this is disclosed
  at Part1:101. Supp(Z) sums are read as sums over distinct vectors (R2). The witness satisfies every condition:
  - all printed clauses of p.130;
  - the prose consequence (all 6 window permutations have mass 1/6);
  - the fixed count and positive arms;
  - arbitrary interference, which is allowed.

  Yet E[τ̂]=0 while the printed RHS is −1/18. I recomputed all of this exactly in Python. The docstring is accurate.

## Observations (not defects of the declarations)

- **Stale record text for T2.** The `rows_not_used` reasons in `record.json` for `prob_map` say "the score-to-assignment
  application is omitted from T2", and the reason for `mem_map_support_iff` is similar. The current statement does
  include it (`T2ScoreWholePart`, WholeW1:90). This is bookkeeping in the record; the statement, the docstring and the
  `whole` decision are right.
- **Measurability in T2/T3/T7.** These statements require Z, or each X_i, to be measurable (WholeW1:84; Part2:16
  inside `CorrectedLocalConditions`), and their docstrings do not mention it. I did not count this as a defect: the
  claim's objects are a "random vector Z" and "random variables X_i", which are measurable by definition, so nothing is
  added beyond the claim's own notions. If the author wants every docstring to say that the usual measure-theoretic
  conditions are assumed, a one-clause addition to the T2, T3 and T7 docstrings would cover it.
- **Redundant hypotheses.** `S.Nonempty` in T8, `0 < b` and `2 ≤ S.card` in the score-based parts are redundant but
  harmless; each is implied by the others or by the setting.
