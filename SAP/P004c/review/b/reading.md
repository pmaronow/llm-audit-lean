# Blind reading

This file was written from `SAP/P004c/Defs.lean`, all five `Defs/Part*.lean`, `Challenge.lean`, and `Challenge/Part1.lean`, before opening `claims.json` or `record.json`. It reads the theorem types, not the assurances in the docstrings. There are nine theorem stubs.

## Notation and fully expanded common definitions

For each natural number (N), the nodes are \(I_N=\{0,\ldots,N-1\}\), and an assignment is an arbitrary function \(z:I_N\to\{0,1\}\). `Bool.true` means 1. Write (c_i(1)=p_i), (c_i(0)=1-p_i). The assignment weight is (w_p(z)=\prod_i c_i(z_i)); expectation is the finite sum (E_p U=\sum_z w_p(z)U(z)); event probability is (E_p 1_A). For interior (p_i) these are the independent Bernoulli probability law and its expectation. `cov` is (E_p(UV)-E_pU E_pV), and `variance` is (E_pU^2-(E_pU)^2). All assignment sums run over every Boolean assignment, not a subset or an assumed realization.

A circle table is any real function (R_i(z)). Write

* (m_i(a)=E_p[1_{z_i=a}R_i(z)]/c_i(a)), (t_i=m_i(1)-m_i(0)), (t=N^{-1}\sum_i t_i), and (\bar m(a)=N^{-1}\sum_i m_i(a)).
* For any real assignment function (U), (m_{ij}^{ab}(U)=E_p[1_{z_i=a,z_j=b}U]/(c_i(a)c_j(b))). This is an ordinary pair conditional mean when (i\ne j) and the probabilities are interior; pair terms in the statements below always exclude (i=j).
* (H(z)=N^{-1}\sum_i[z_iR_i(z)/p_i-(1-z_i)R_i(z)/(1-p_i)]), the HT statistic.
* (n_a(z)=\sum_i1_{z_i=a}) is a **real-valued** count; (\widehat m_a(z)=\sum_i1_{z_i=a}R_i(z)/n_a(z)); (J(z)=\widehat m_1(z)-\widehat m_0(z)). Real division by zero is zero, so an empty arm has mean zero.
* Given deterministic real fits (g_i(a)), put (C_i^g(z)=z_i(R_i(z)-g_i(1))/p_i-(1-z_i)(R_i(z)-g_i(0))/(1-p_i)), (u_i=t_i-(g_i(1)-g_i(0))), and (A_g(z)=N^{-1}\sum_i[g_i(1)-g_i(0)+C_i^g(z)]). The linearized Hajek statistic is (L=A_g) for (g_i(a)=\bar m(a)).
* Put (s_1=1,s_0=-1). For neighborhoods (B_i\subseteq I_N), let (D_B=\max_i|B_i|), with value 0 for an empty node set. Define
  \[
  M_g={1\over N^2}\left[\sum_i\left({E[(R_i-g_i(1))^2\mid z_i=1]\over p_i}+{E[(R_i-g_i(0))^2\mid z_i=0]\over1-p_i}\right)+\sum_i\sum_{j\in B_i\setminus\{i\}}\sum_{a,b}s_as_bm_{ij}^{ab}((R_i-g_i(a))(R_j-g_j(b)))\right].
  \]
  Here the conditional means of squares are exactly the `marginal` finite quotients above. `varianceExpansion`, written (V_g(B)), is the same expression with (u_i^2) subtracted in each diagonal term and ((m_i(a)-g_i(a))(m_j(b)-g_j(b))) subtracted inside each pair conditional mean. `homophilyQ` is (N^{-1}\sum_i\sum_{j\in B_i}u_iu_j), including the center when it belongs to (B_i). `effectHomophily` is (F(B)=N^{-1}\sum_i(t_i-t)\sum_{j\in B_i}(t_j-t)).

`interferes R i j` means (i=j), **or** there exist two assignments equal at every coordinate other than (j) for which (R_i) differs. Thus every node is stipulated to interfere with itself even for a constant outcome. `sharesSource R i j` means that there exists a node (l) interfering with both (i) and (j). For a real array of distances (D), `ball D i r` is the finite set \(\{j:D_{ij}\le r\}\). `LocalAt R D h` says, for every (i,j), (D_{ij}>h\Longrightarrow\neg\text{sharesSource}(i,j)). No metric axioms for an arbitrary (D) are implicit.

A spatial population on a type (X) has a metric, an arbitrary measurable-space structure, nonempty sets (S_i\subseteq X), a measure \(\zeta\), real outcomes (Y(x,z)), and an arbitrary band function \(\operatorname{bands}:\mathbb R\to\mathcal P(\mathbb R)\). There is no implicit compatibility assumption between the measurable space and the metric. Point-to-node distance is \(\inf_{y\in S_i}\operatorname{dist}(x,y)\). Node separation \(D_{ij}\) is the infimum of all \(\operatorname{dist}(x,y)\) with \(x\in S_i,y\in S_j\). Nonempty sets and the lower bound 0 make these genuine finite infima; the node sets need not be points, disjoint, or closed. The region at radius parameter (d) is
\(A_i(d)=\{x:\operatorname{dist}(x,S_i)\in\operatorname{bands}(d)\}\).
The circle table is \(R_i(z)=\int_{A_i(d)}Y(x,z)\,d\zeta/\zeta(A_i(d))\), where the measure in the denominator is converted from extended nonnegative reals to reals. `WellDefined P d` requires, for every node, that this region be measurable, have strictly positive finite measure, and that (Y(\cdot,z)) be integrable on it for **every** assignment (z).

`SpatialLocalConditions` for a sequence (P_N) is the conjunction of the following, with the quantifier order as displayed:

1. There exists (b>0) such that for all sufficiently large (N), for every outcome point (x) and assignment (z), \(|Y_N(x,z)|<b\).
2. There exists a real function (h(d)), nonnegative at every (d\ge0), such that for each fixed (d\ge0), for all sufficiently large (N), `LocalAt` holds for the radius-(d) circle table and node separations, with cutoff (h(d)). The threshold may depend on (d).
3. There exists a real function (c(r)) such that for each fixed (r\ge0), for all sufficiently large (N), for every node (i), \(|\{j:D_{ij}\le r\}|\le c(r)\). The threshold may depend on (r).

`BoundedOutcomes` is item 1 alone. `Nondegenerate V` means there exists one real (v>0) such that (NV_N\ge v) for all sufficiently large (N); in particular (V_N>0) eventually. `InProb p U` means that for every \(\epsilon>0\), \(P_{p_N}(|U_N|>\epsilon)\to0\). `BigOp p U r` means that for every \(\epsilon>0\) there is (C>0) such that eventually \(P_{p_N}(|U_N|>C|r_N|)<\epsilon\). `NormalLimit p U` means, for **every** real (x), \(P_{p_N}(U_N\le x)\to\Phi(x)\), with \(\Phi(x)\) the measure of \(( -\infty,x]\) for Mathlib's actual Gaussian probability measure of mean 0 and variance 1. Deterministic `IsBigO atTop f (1/N)` means there exists a real constant (C) such that eventually \(|f_N|\le C|1/N|\).

For Appendix C, `MetricNodeDistances P` asserts for every (N) that all \(D_{ij}\) are nonnegative, (D_{ij}=0\iff i=j), (D_{ij}=D_{ji}), and \(D_{ik}\le D_{ij}+D_{jk}\). `QuadraticSpacing P` means there exists (C_b>0) and **one** eventual threshold in (N) such that for every subsequent (N), every node (i), and **every real** (s\ge0), \(|\{j:D_{ij}\le s\}|\le C_b(1+s^2)\).

`conditionOn p J U z` is \(E_p[1_{z'_J=z_J}U(z')]/\prod_{j\in J}c_j(z_j)\). `l2Norm p U` is \(\sqrt{E_pU^2}\). For interior probabilities these are conditional expectation on the displayed coordinates and its ordinary (L^2) norm. `NEDConditions P p d` means there exist a real function \(\psi(s)\), positive node scales \(g_{N,i}\), and one real bound (G), such that: \(\psi(s)\ge0\) for all \(s\ge0\); \(\psi\) is nonincreasing on \([0,\infty)\); \(\psi(s)\to0\) as \(s\to\infty\); there exist a real exponent \(q>4\) and reals \(C,S\), \(S>0\), such that \(\psi(s)\le Cs^{-q}\) for every \(s\ge S\); \(0<g_{N,i}\le G\) for every (N,i); and, for every \(N,i,s\ge0\),
\[
 \|R_{N,i}-E[R_{N,i}\mid (z_j)_{D_{ij}\le s}]\|_2\le g_{N,i}\psi(s).
\]
The law here is the independent Bernoulli law with common probability (p), and the circle table uses radius (d). These conditions hold at every (N), unlike the eventual boundedness and spacing conditions.

`marginalLawEffect w U i` means \(\sum_z w_i(z)U(z^{i\leftarrow1})-\sum_z w_i(z)U(z^{i\leftarrow0})\). Both sums use the same weights; the coordinate is overwritten regardless of its original value. `SharpNull Y` is the definition \(\forall x,z,\ Y(x,z)=Y(x,0)\), where 0 denotes the all-control assignment.

Mathlib semantics checked directly in its sources: `Metric.infDist` is `infEDist.toReal` and has the stated infimum meaning on nonempty sets (`Topology/MetricSpace/HausdorffDistance.lean`); `IntegrableOn` is integrability for the restricted measure; the real Bochner integral is set to zero for a nonintegrable function (`MeasureTheory/Integral/IntegrableOn.lean`, `Bochner/Basic.lean`); `gaussianReal` takes a nonnegative **variance** (`Probability/Distributions/Gaussian/Real.lean`); `Matrix.PosSemidef` means Hermitian and a nonnegative quadratic form on all finitely supported vectors, equivalently symmetric and nonnegative quadratic form here; matrix inverse is the adjugate inverse and is zero on singular matrices (`LinearAlgebra/Matrix/PosDef.lean`, `NonsingularInverse.lean`); finite `sup` is a maximum with empty value bottom, 0 for natural numbers (`Data/Finset/Lattice/Fold.lean`); `Function.update` overwrites precisely one coordinate (`Logic/Function/Basic.lean`); deterministic big-O is an eventual norm inequality (`Analysis/Asymptotics/Defs.lean`). No `limsup` occurs. All divisions and subtractions in the real formulas are real operations; in particular (D_B-1) is not truncated natural subtraction.

## `SAP.P004c.T31` : `T31Statement`

This is a conjunction of two universally quantified assertions, with arbitrary universe (u).

1. For every \(N\in\mathbb N\), every type \(X\) in that universe, and every real outcome array \(Y:X\times\{0,1\}^{I_N}\to\mathbb R\), `SharpNull Y` if and only if \(Y(x,z)=Y(x,0)\) for every (x,z). This part unfolds a definition and has no assumptions on (X) or (N).
2. For every (N), every circle table (R), and every assignment (z), **if both** (n_1(z)>0) and (n_0(z)>0), all of the following hold:
   * \(n_1=\sum_i z_i\), \(n_0=N-n_1\), and \(n_0=\sum_i(1-z_i)\).
   * For **every** pair of reals \(\mu,\tau\), the residual sum of squares at \((\widehat m_0,J)\) is at most that at \((\mu,\tau)\). Equality of these sums implies \(\mu=\widehat m_0\) and \(\tau=J\). Thus that pair is the unique least-squares minimizer of \(\sum_i(R_i(z)-\mu-\tau z_i)^2\).
   * Let (X_{i0}=1,X_{i1}=z_i), (A=(X^TX)^{-1}), and \(S_e(K)=A X^T[ e_i e_j K_{ij}]_{ij}X A\). For **every** real vector \(e\) and **every** real \(N\times N\) matrix \(K\), \(S_e(K)=A[\sum_{i,j}X_{ia}X_{jb}e_i e_jK_{ij}]_{ab}A\).
   * For every vector of real values \(\lambda_k\) and real square matrix \(V\), **if** \(V^TV=I\), define \(K=V\operatorname{diag}(\lambda_k)V^T\), \(Q=V\operatorname{diag}(\max(\lambda_k,0))V^T\). Then \(Q-K=V\operatorname{diag}(\max(-\lambda_k,0))V^T\); each of (Q,Q-K,[e_i e_jQ_{ij}],[e_i e_j(Q-K)_{ij}],S_e(Q),S_e(Q)-S_e(K)) is positive semidefinite; and \(\max(S_e(K)_{11},0)\le S_e(Q)_{11}\). The index 1 is the treatment column. There is no assertion here relating `kernelVariance` or `lambda` to the treatment entry.

Both positive arm counts imply a positive sample size and invertibility of (X^TX); the singular-matrix convention therefore does not supply the regression result.

## `SAP.P004c.T32` : `T32Statement`

This is a conjunction of five separately quantified assertions, using common scalar \(p\) for all nodes.

1. For every \(N,p,R,B\), if \(N>0\), \(0<p<1\), every \(i\in B_i\), and for every \(i,j\), \(j\notin B_i\) implies no shared source, then \(\operatorname{Var}(H)=V_0(B)\). Also it is at most the expression \(V_0(B)\) with only the diagonal negative squares \(-t_i^2\) deleted. The pair subtractions remain. No symmetry of \(B\) is assumed in this clause.
2. For every \(N,p,b,R,B\), assume \(N>0\), \(0<p<1\), \(|R_i(z)|<b\) for every \(i,z\), \(i\in B_i\), \(j\in B_i\iff i\in B_j\), and no shared source outside \(B_i\). Define
   \(D_H=N^{-2}\sum_i[E(R_i^2\mid z_i=1)/p+E(R_i^2\mid z_i=0)/(1-p)-t_i^2]\)
   and \(C_{ac}=N^{-2}\sum_i\sum_{j\in B_i\setminus\{i\}}[m_{ij}^{ac}(R_iR_j)-m_i(a)m_j(c)]\).
   Then \(0\le D_H\le b^2/(Np)+b^2/(N(1-p))\); for every pair of Boolean arms \(a,c\), \(|C_{ac}|\le2b^2(D_B-1)/N\); and \(\operatorname{Var}(H)\le b^2/(Np)+b^2/(N(1-p))+8b^2(D_B-1)/N\).
3. For every fixed \(p,b\) and sequence of tables \(R_N\), if \(0<p<1\) and eventually \(|R_{N,i}(z)|<b\) for every \(i,z\), then \(D_H(R_N)=O(1/N)\). There are no neighborhood assumptions in this clause.
4. For every fixed \(p,b\), sequence \(R_N\), sequence \(B_N\), and natural number \(D\), if \(0<p<1\) and eventually the outcomes are bounded by \(b\), each neighborhood contains its center, and \(D_{B_N}\le D\), then for every pair \(a,c\), \(C_{ac}(R_N,B_N)=O(1/N)\). Neither symmetry nor the shared-source condition is a hypothesis in this clause.
5. For every sequence of metric measurable spaces, spatial populations \(P_N\), and fixed real \(p,d\), if \(0<p<1\), \(d\ge0\), `SpatialLocalConditions P`, and eventually `WellDefined (P N) d`, then the variance of the spatial-circle HT statistic is \(O(1/N)\).

## `SAP.P004c.T33` : `T33Statement`

This is a conjunction of two assertions.

1. For every \(N,p,R,B\), if \(N>0\), \(0<p<1\), \(i\in B_i\) for every \(i\), and no pair \(i,j\) outside \(B_i\) shares a source, take \(g_i(a)=\bar m(a)\). Then \(\operatorname{Var}(L)=V_g(B)\), \(M_g-\operatorname{Var}(L)=F(B)/N\), \(\operatorname{Var}(L)\le M_g\iff F(B)\ge0\), and \(F(B)\ge0\Longrightarrow\operatorname{Var}(L)\le M_g\). Neighborhood symmetry is not assumed. In particular nonnegative homophily is the necessary and sufficient condition for this particular second-moment bound, not a premise for the identity itself.
2. For every \(N,p,R\), if \(N>0\), \(0<p<1\), and \(\sigma_H^2=\operatorname{Var}(H)>0\), define \(W_i(z)=(z_iR_i(z)/p-(1-z_i)R_i(z)/(1-p)-t_i)/(N\sqrt{\sigma_H^2})\). For every assignment \(z\), \(\sum_iW_i(z)=(H(z)-t)/\sqrt{\sigma_H^2}\); every \(E W_i=0\); and \(\operatorname{Var}(\sum_iW_i)=1\).

## `SAP.P004c.T34` : `T34Statement`

This is a conjunction of four assertions.

1. For every \(N,z,p,S\), if \(N>0\), \(n_1(z)>0\), and \(0<p<1\),
   \[
   |N(NS/n_1^2-NS/(N^2p^2))|=|N^2/n_1^2-1/p^2|\,|S|,
   \quad |N^2/n_1^2-1/p^2|=|(n_1/N-p)(n_1/N+p)/(p^2(n_1/N)^2)|.
   \]
2. For every \(N,z,e,D,K,b,K_{\max}\), where \(e\) is an arbitrary real node vector, \(D\) an arbitrary real node-pair array, \(K:\mathbb R\to\mathbb R\), and \(b,K_{\max}\) reals, assume \(N>0\), \(b>0\), \(|K(t)|\le K_{\max}\) for every \(t\ge0\), \(K(t)=0\) for every \(t>1\), and \(D_{ij}\ge0\) for every \(i,j\). Then
   \[
    \left|{1\over N}\sum_i\sum_{j\ne i}z_i z_j e_i e_j K(D_{ij}/b)\right|
     \le K_{\max}(\sup_i|e_i|)^2\max_i|\{j:D_{ij}\le b\}|.
   \]
   No symmetry, triangle inequality, or requirement \(D_{ii}=0\) is assumed. The supremum is over a finite nonempty set because \(N>0\).
3. For every fixed \(p\) with \(0<p<1\), under the \(N\)-node independent Bernoulli-\(p\) law the random variable \(E_N(z)=|N^2/n_1(z)^2-1/p^2|\) when \(n_1>0\), and \(E_N(z)=0\) when \(n_1=0\), is \(O_p(N^{-1/2})\), with the quantifiers in `BigOp` above.
4. Pure scalar arithmetic: \(|8^2/5^2-1/(1/2)^2|\,|-1/4|=9/25\); \((8^2/5^2-1/(1/2)^2)|-1/4|=-9/25\); and \(9/25\not\le-9/25\). No eight-node assignment, residual vector, or kernel realizing the scalar \(S=-1/4\) is asserted. No composed bandwidth rate is asserted.

## `SAP.P004c.T39` : `T39Statement`

For every \(N\), real \(p\), and arbitrary table \(R\), if \(N>0\) and \(0<p<1\), then
\[
 E_pH={1\over N}\sum_i\big(E_p R_i(z^{i\leftarrow1})-E_pR_i(z^{i\leftarrow0})\big).
\]
Expectations on the right use a fresh full Bernoulli assignment before overwriting coordinate \(i\). No interference, geometry, boundedness, or locality hypothesis is imposed.

## `SAP.P004c.T40` : `T40Statement`

For every \(N\), every type \(X\) with a metric and measurable structure, spatial population \(P\), real \(d\), node-specific assignment weights \(w_i(z)\), real functions \(g_i(x)\), and real baseline \(f(x)\), assume \(N>0\), \(\sum_z w_i(z)=1\) for every \(i\), \(w_i(z)\ge0\) for every \(i,z\),
\(Y(x,z)=\sum_jz_jg_j(x)+f(x)\) for every \(x,z\), and `WellDefined P d`. Then:

* for every \(i,x\), the forced-coordinate marginal effect under \(w_i\) is exactly \(g_i(x)\);
* for every \(i\), the forced-coordinate marginal effect on \(R_i\) is \(\int_{A_i(d)}g_i\,d\zeta/\zeta(A_i(d))\);
* the node average of these circle effects equals \(N^{-1}\sum_i\int_{A_i(d)}g_i\,d\zeta/\zeta(A_i(d))\).

The weights may depend on \(i\) and include arbitrary dependence between assignment coordinates. No Bernoulli, metric-distance, nonnegative-radius, or locality condition is added. Integrability of the \(g_i\) on the regions follows from integrability of all potential outcomes and the additive representation.

## `SAP.P004c.T41` : `T41Statement`

For every sequence of metric measurable spaces and spatial populations, and fixed \(p,d\), assume \(0<p<1\), \(d\ge0\), `SpatialLocalConditions P`, and eventual `WellDefined (P N) d`. Then \(\operatorname{Var}(H_N)=O(1/N)\). In addition, **if** there exists \(v>0\) with eventually \(N\operatorname{Var}(H_N)\ge v\), the statistic \((H_N-t_N)/\sqrt{\operatorname{Var}(H_N)}\) has CDFs converging to the standard Gaussian CDF at every real point. The positive variance lower bound is needed only for the normal-limit clause, not for the variance upper bound.

## `SAP.P004c.T42` : `T42Statement`

For every sequence of metric measurable spaces and spatial populations, and fixed \(p,d\), assume \(0<p<1\), \(d\ge0\), `SpatialLocalConditions P`, eventual `WellDefined (P N) d`, and existence of \(v>0\) with eventually \(N\operatorname{Var}(L_N)\ge v\). Then \((J_N-t_N)/\sqrt{\operatorname{Var}(L_N)}\) has CDFs converging to the standard Gaussian CDF at every real point. This uses the actual variance of the corrected \(L_N\) defined above, not the finite-sample variance of \(J_N\). Empty-arm Hajek means are zero; no finite-sample nonempty-arm conditioning is imposed.

## `SAP.P004c.T44` : `T44Statement`

For every sequence of metric measurable spaces and spatial populations, and fixed \(p,d\), assume \(0<p<1\), \(d\ge0\), eventual globally bounded outcomes, eventual `WellDefined (P N) d`, `NEDConditions P p d`, `MetricNodeDistances P`, and `QuadraticSpacing P` with the full quantifier order above. Then all four conclusions hold:

1. For **every** \(N>0\) for which `WellDefined (P N) d` holds, \(E H_N=t_N\). This is a finite-sample assertion, including samples before the eventual regularity threshold when their averages are well defined.
2. \(\operatorname{Var}(H_N)=O(1/N)\).
3. \(\sqrt N(L_N-J_N)\to0\) in probability, under the Bernoulli-\(p\) designs.
4. **If** there exists \(v>0\) with eventually \(N\operatorname{Var}(L_N)\ge v\), then \((J_N-t_N)/\sqrt{\operatorname{Var}(L_N)}\) converges in the CDF sense to the standard Gaussian at every real point.

There is no exact finite-range locality premise here. The strengthened spacing bound is uniform over all radii after one sample-size threshold; boundedness and existence of genuine spatial averages are eventual; NED and the metric-node-distance property hold for every sample size.
