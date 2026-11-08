# Review of SAP.P004c.T31

Verdict: **faithful**, severity **none**. The record's `whole` decision is correct; no correction is needed.

The complete closure, including both generated `NeZero 2` proofs, was read and unfolded in `reading.md` before either audit input was opened. `claim-stage.json` records the independent `whole` assessment saved before reading `record.json`; the record did not change that assessment.

The canonical corrected claim is covered clause by clause:

- `Defs/Part4.lean:14-15` and `Defs/Part2.lean:80-81` give the sharp null over outcome points and all assignments. This is the requested corrected definition, without asserting the null for arbitrary outcomes.
- `Defs/Part4.lean:17-19` gives the count identities for every assignment. Lines 20-26 give the unique least-squares intercept and Hajek coefficient when both arms are nonempty.
- `Defs/Part4.lean:27-33` gives the two sandwich formulas with exactly N residual coordinates and N-by-N kernels. Universal quantification over tables, residual vectors and matrices includes the paper's realized circle averages, regression residuals and entries K(distance/cutoff). Their spatial origin imposes no extra requirement on this finite algebraic identity.
- `Defs/Part4.lean:34-43` gives every spectral, Hadamard and sandwich positive-semidefinite assertion, the Loewner difference, and the maximum-with-zero treatment-entry bound. The supplied orthonormal eigen-decomposition is exactly the premise in canonical (c).

The source's sandwich, truncation and point-indexed null notions were also checked against the [paper preprint](https://arxiv.org/pdf/2010.13599), whose equation and footnote numbering differs from the published version cited in the canonical claim. No scope was inferred from the audit-history note.

The definitions use ordinary finite real sums and matrix operations. Empty-arm means are zero by totalized division, but all OLS and matrix conclusions require positive counts. Under those hypotheses det(X-transpose X)=N1*N0>0, so the inverse has its ordinary meaning. The subtraction N-N1 occurs in the reals. The theorem docstring correctly describes these guards and all conclusions.

`scratch/Nonvacuity.lean` compiled successfully using only the definitions. It constructs four nodes with two nodes per arm, nonzero genuine OLS residuals, Gram determinant 4, and an orthonormal eigenbasis with a negative eigenvalue actually changed by truncation. It also constructs a sharp-null outcome function on a nonempty point type. `scratch/BlindCheck.lean` compiled successfully and confirms the elaborated quantifiers, auxiliary proofs and Mathlib matrix notions.
