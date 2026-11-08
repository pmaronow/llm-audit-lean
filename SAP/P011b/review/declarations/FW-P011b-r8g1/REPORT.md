# Review of SAP.P011b.T16

**Verdict: faithful; severity: none.** The `whole` decision is correct.
No current defect was found in the statement, its dependency definitions,
docstrings, or declared scope.

The blind reading was saved in [reading.md](reading.md) before consulting the
canonical claim or review history. The claim-stage assessment in
[claim-stage.json](claim-stage.json) remains unchanged after reading the record.
Every supplied closure entry was inspected, including structure operations and
the generated proof declarations.

The theorem covers all three canonical clauses: the finite OLS mean/offset
identities and complete raw-oracle bias criteria; unrestricted finite shift
identities and the intercept specialization; and the residual root-n rate,
displayed perturbation bound and its probability limit, oracle consistency,
and conservativeness of every compatible maximum. Finite identities do not
assume asymptotic scaling. Dimension and coefficient index are fixed in the
residual asymptotics; deterministic coefficient vectors and targets may vary
with sample size. Maximum-value measurability covers arbitrary tie choices.

The definitions implement ordinary simple graphs, independence of separated
coordinate vectors, the paper's raw estimator, and weighted regression residuals
without extra sample recentering. Positivity excludes zero normalization;
full rank excludes the singular-matrix inverse branch; the mean-model and
boundedness hypotheses provide the required moments. In particular,
`|meanBias_k| <= (1+c2)c1^2`, so the real-valued `liminf` is an ordinary finite
liminf. Probability measures exclude infinity in `toReal`, and norm square
roots have nonnegative inputs.

Independent verification:

- [scratch/Nonvacuity.lean](scratch/Nonvacuity.lean) compiles a witness satisfying
  **every residual OLS hypothesis**, including validity: independent fair signs,
  `n=k+1`, empty graphs, unit weights, an intercept design, `p=1`, and `b_k=0`.
  The scaling constants are `(1,1,1,2)`, scaled true variance is exactly one,
  and row, outcome and Gram constants are all one.
- [scratch/Witness.lean](scratch/Witness.lean) independently proves the full
  two-point constant-shift witness, with raw values zero and one half.
  Both compiled proofs use only `propext`, `Classical.choice`, and `Quot.sound`;
  neither uses the audited theorem.
- [scratch/check_star.py](scratch/check_star.py) checks the lower-star block by
  exact rational enumeration. Its independent leaves and conditional center
  law give scaled variance `27/128`, bias `-3/128`, and sample-variance limit
  `15/64`. The source law draws blocks independently. Binary bounds, nested
  disjoint stars, Gram `diag(4K,12K)`, correct means and weights, and valid empty
  recruitment verify the witness's conditions. Since the empty graph is feasible
  and its scaled objective tends to `15/64 > 27/128`, every maximum is
  conservative despite negative bias liminf. This verifies the corrected
  claim's nonnecessity assertion; it does not refute the canonical claim.

The single earlier issue is **fixed**. The current note at `record.json:51`
expressly allows arbitrary deterministic `b_k` and varying targets, matching
`Defs/WholeW2.lean:185` and `Challenge/Part1.lean:41`. The architect's repair
account accurately describes the current text. Historical restrictions in that
report are expressly superseded.

The Lean checks used `sap-lean`, with no more than two processes concurrently.
The required JSON outputs were parsed and checked against the sole assigned
declaration and its supplied fingerprint. No unit source was modified.
