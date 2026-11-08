# Review report — P005b, T15–T19 (Chang, Middleton & Aronow, Econometrica 2024)

Process: blind reading (`reading.md`), then comparison with `claims.json`
(`claim-stage.json`), then with `record.json`. The elaborated statements were checked with
`#print` (`pp.numericTypes`). Every closure entry was read, including the auxiliary
`_proof_1` terms (numeral `AtLeastTwo` instances) and `armSet.match_1`.

| Theorem | Record | Verdict | Severity |
|---|---|---|---|
| SAP.P005b.T15 | whole | faithful | none |
| SAP.P005b.T16 | whole | faithful | none |
| SAP.P005b.T17 | whole | faithful | none |
| SAP.P005b.T18 | whole | faithful | none |
| SAP.P005b.T19 | refuted | faithful | none |

## Notes per declaration

- **T15.** Clauses (a), (b) (both equalities) and (c) of the claim are stated term by term,
  for n_T, n_C ≥ 2. (c) is the sum of estimators (11) and (12), with the corrected label
  Cov_C(h, y(0)), and it is stated for every population and every assignment. All casts are
  real and no denominator can vanish. The docstring is accurate.
- **T16.** All parts (a)–(e) of the corrected Lemma A.2 computation are present, including
  E[D_iD_j], E[D_iD_jD_s], the expansion of the cube, the coefficient simplification (both
  forms), the treated and mixed third moments, and the complement relations. The hypotheses
  are exactly n ≥ 3, 0 < n_T < n and centred x, y, z. The docstring is accurate.
- **T17.** The (a)–(d) contraction chain (corrected index j) holds under n ≥ 2 and gram = I.
  (e) holds as O(κ/n) and mean(δ²) = O(1) under Assumptions 1–3. Here δ is the actual residual
  difference: `commonResidual` is the p. 1513 residual in its Assumption 2 closed form, and
  Assumption 2 holds eventually. Beyond the claim's list, the statement also gives the two
  printed variance inequalities for the actual term (*) and the printed conclusion
  (*) = O_p(√(κd/n)), with d = 0 allowed. Both extra parts are correct and come from the
  printed passage. κ is the sSup of a finite nonempty set, i.e. the maximum; there are no junk
  values. The docstring is accurate.
- **T18.** (a) and (b) are stated for arbitrary residuals satisfying the weighted normal
  equation, without standardization. (c) uses `standardized` (x̄ = 0 and gram = I) together
  with the common residuals. The gram = I part is presupposed by the standing assumptions,
  which read exact statements at an n where both parts of Assumption 2 hold, and the p. 1513
  residuals have this closed form only then. So it is not a hidden restriction. The docstring
  is accurate.
- **T19.** This is a genuine refutation. The canonical statement explicitly reads Lemma A.1
  for arbitrary, uncentred vectors. `T19Statement` is the exact negation of the universal
  conjunction (i) ∧ (ii) over that domain. I checked the witness n = 4, n_T = 3, arm T,
  a = b = (−1,−1,−1,1) in Lean with the package definitions: Var = 4/27 > 8/81, while (i)
  holds. The refutation needs uncentred vectors (the bound appears to hold for centred ones),
  and the printed reading allows them. The docstring ("the universal conjunction … fails")
  describes the statement exactly. A sharper form (∀(i) ∧ ¬∀(ii)) would say more, but
  nothing stated is incorrect.

## Artifacts

- `scratch/Print.lean`, `scratch/Print2.lean`, `scratch/AuxPrint.lean`: elaborated statements
  and auxiliary declarations.
- `scratch/Check.lean`: nonvacuity instances for T15–T18, including a standardized
  population and a sequence satisfying `wholeW1Standing`.
- `scratch/T19W.lean`: an independent Lean proof of `T19Statement` from the explicit witness.
