# Blind reading

This file was saved before opening `claims.json` or `record.json`. The source docstring was read, but no canonical claim or architect record was consulted.

## SAP.P004c.T31

Source: `SAP/P004c/Challenge/Part1.lean:8-13`; statement: `SAP/P004c/Defs/Part4.lean:12-43`. Fingerprint: `5139130ed7258871a49663b4358cbcffda2a30dec19be66ad1188e5d0e58ec19`.

### All dependencies read

The complete closure in `closure.json` was read: `Assignment`, `CircleTable`, `SharpNull`, `T31Statement`, `T31Statement._proof_1`, `armCount`, `armMean`, `bit`, `designMatrix`, `designMatrix._proof_1`, `hajek`, `sandwich`, and `spectralKernel`. Both generated proof declarations were inspected with Lean: each proves `NeZero (1 + 1)` using `Nat.instNeZeroSucc`. They only support numerals in `Fin 2`.

### Statement in ordinary mathematics

All sums below are finite sums over the indicated finite index types. Write (I_N=\{0,\ldots,N-1\}\). An assignment is a function (z:I_N\to\{\mathrm{false},\mathrm{true}\}\). A circle table is an arbitrary real function (R:I_N\times\{\mathrm{false},\mathrm{true}\}^{I_N}\to\mathbb R\); this declaration imposes no spatial realization on that table.

The theorem is the conjunction of these two universally quantified statements, in this order:

1. For every natural number (N\), every type (U\) in universe (u\), and every function (Y:U\times\{\mathrm{false},\mathrm{true}\}^{I_N}\to\mathbb R\), the proposition called `SharpNull Y` is equivalent to
   \[
   \forall x\in U\;\forall z:I_N\to\{\mathrm{false},\mathrm{true}\},\quad Y(x,z)=Y(x,z_0),
   \]
   where (z_0(i)=\mathrm{false}\) for every (i\). `SharpNull` is defined to be exactly the right-hand side, so this part states the definition; it does not assert that arbitrary outcomes satisfy the null.
2. For every (N\in\mathbb N\), every circle table (R\), and every assignment (z\), let
   \[
   t_i=\begin{cases}1&z(i)=\mathrm{true},\\0&z(i)=\mathrm{false},\end{cases}\qquad
   n_a=\sum_{i\in I_N}\mathbf1\{z(i)=a\}.
   \]
   The counts (n_a\) are real numbers. Unconditionally,
   \[
   n_1=\sum_i t_i,\qquad n_0=(N:\mathbb R)-n_1,\qquad n_0=\sum_i(1-t_i).
   \]
   If (n_1>0\), and then if (n_0>0\), all of the following hold. Both antecedents apply to all the OLS and matrix assertions below.

   Set (m_a=(\sum_{i:z(i)=a}R(i,z))/n_a\), (h=m_1-m_0\), and
   (L(\mu,\tau)=\sum_i(R(i,z)-\mu-\tau t_i)^2\). These unfold `armMean` and `hajek`. For every (\mu\in\mathbb R\), then every (\tau\in\mathbb R\),
   \[
   L(m_0,h)\le L(\mu,\tau),\qquad
   L(\mu,\tau)=L(m_0,h)\ \Longrightarrow\ (\mu=m_0\ \wedge\ \tau=h).
   \]
   Thus the displayed pair exists and is the unique minimizer of the unweighted sum of squared residuals.

   Define the (N\times2\) matrix (D\) by (D_{i0}=1\), (D_{i1}=t_i\), and put (A=(D^TD)^{-1}\). For every real vector (e:I_N\to\mathbb R\), there are two further conclusions. In particular, (e\) is arbitrary: it is not required to equal the OLS residual vector.

   First, for every real (N\times N\) matrix (K\), define (M_K\) by ((M_K)_{ij}=e_i e_j K_{ij}\) and (S_K=A(D^TM_KD)A\). Then
   \[
   S_K=A B_K A,\qquad
   (B_K)_{ab}=\sum_i\sum_j D_{ia}D_{jb}e_i e_jK_{ij}\quad(a,b\in\{0,1\}).
   \]
   Here (S_K\) is precisely `sandwich z e K`; `Matrix.of` merely turns the displayed entry function into a matrix.

   Second, for every real vector (v:I_N\to\mathbb R\), then every real (N\times N\) matrix (V\), if (V^TV=I_N\), let
   \[
   K_{ij}=\sum_k v_k V_{ik}V_{jk},\qquad
   Q_{ij}=\sum_k\max(v_k,0)V_{ik}V_{jk},\qquad
   H_{ij}=\sum_k\max(-v_k,0)V_{ik}V_{jk}.
   \]
   These are all instances of `spectralKernel`; the `trim` Boolean selects (v_k\) or \(\max(v_k,0)\). Then, in order,
   \[
   Q-K=H;\quad Q\succeq0;\quad Q-K\succeq0;\quad
   M_Q\succeq0;\quad M_{Q-K}\succeq0;\quad
   S_Q\succeq0;\quad S_Q-S_K\succeq0;\quad
   \max((S_K)_{11},0)\le(S_Q)_{11}.
   \]
   Matrix subtraction is entrywise. For these real finite square matrices, Mathlib's `PosSemidef` means that the matrix is symmetric and its quadratic form \(\sum_{i,j}w_iM_{ij}w_j\) is nonnegative for every real vector \(w\). Its actual definition uses finitely supported vectors; on `Fin N` these represent all vectors. The index (1\) of the (2\times2\) sandwiches denotes the treatment coefficient, following intercept index (0\).

### Totalization, empty cases, and other conventions

- Real division is total, with (r/0=0\). Thus an empty arm has `armMean = 0` (its numerator is also zero), and `hajek` still has a value if either arm is empty. The count equalities require no division. Every asserted OLS or sandwich conclusion is behind both strictly positive count hypotheses, so none relies on an empty-arm mean.
- Mathlib's matrix inverse is the adjugate times the inverse of the determinant, and returns the zero matrix when the determinant is zero over \(\mathbb R\). Here
  \(D^TD=\bigl[\begin{smallmatrix}N&n_1\\n_1&n_1\end{smallmatrix}\bigr]\) and its determinant is \(n_1(N-n_1)=n_1n_0>0\) under the two arm hypotheses. Hence each inverse that occurs in an asserted conclusion is the ordinary inverse, not its singular fallback.
- At (N=0\), `Fin N` is empty, all count sums are zero, and there is one empty assignment. The count identities still hold. The nonempty-arm premise fails, so the OLS and matrix assertions are not imposed. At (N=1\), both arms cannot be nonempty either. The nonempty-arm assertions have genuine instances when (N\ge2\).
- The arbitrary point type (U\) can be empty. In that case the null predicate is vacuous, as is the identical predicate to which it is equated. The first conjunct has no assumption of the null and makes no inference from its possible emptiness.
- The subtraction in (N-n_1\) takes place in \(\mathbb R\), after the natural number (N\) is cast. It is not truncated natural subtraction. The cast is exact. `Fin 2` numerals (0\) and (1\) denote its two distinct entries, supported by the two harmless generated nonzero proofs above.
- The orthogonality hypothesis has instances (for example (V=I_N\)); (v\) may have arbitrary signs. The maximum with zero is explicitly the intended eigenvalue truncation and is always an ordinary finite real maximum.
- There are no logarithms, square roots, real powers, Bochner integrals, infinite measures or `toReal`, conditional expectations, `sInf`/`sSup`, limsup/liminf, infinite sums, or partial function defaults in the statement's SAP closure. There are no further SAP assumptions or encoded conclusions hidden in the definitions. In particular, the `SharpNull` equivalence is definitionally reflexive, whereas the OLS and spectral assertions use the usual real and matrix operations.

### Source docstring, before comparison with a claim

The docstring describes unconditional corrected counts, unique OLS with both arms nonempty, agreement of two sandwich formulas, positive semidefinite ordering and a treatment-entry bound from eigenvalue truncation, and a null indexed by arbitrary outcome points. These features are present in the unfolded statement. The paper-specific intended content and whether the two sandwich displays are the intended pair remain to be checked against the canonical claim.
