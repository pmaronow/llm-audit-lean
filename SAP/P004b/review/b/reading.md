# Blind reading of the Challenge

This file was written and saved before opening `claims.json` or `record.json`.
It reads the statements, not the `sorry` proofs. All theorem names below have
the prefix `SAP.P004b.`. The common notation is expanded here so that the
individual readings do not leave SAP predicates uninterpreted.

## Common objects and definitions

The node index set is (I_N=\{0,\ldots,N-1\}), Lean's `Fin N`.
An assignment is any function (z:I_N\to\{0,1\}). `bit` sends true to 1
and false to 0. Given real numbers (p_i), put

\[
 w_p(z)=\prod_i p_i^{z_i}(1-p_i)^{1-z_i},\quad
 E_p X=\sum_z w_p(z)X(z),\quad P_p(A)=E_p1_A.
\]

These are literal finite sums; they are the independent Bernoulli law when
all (p_i\in[0,1]). Covariance is (E_p(XY)-E_pX E_pY), and variance is
covariance with itself. No integrability assumption is needed for these
finite, real-valued tables.

For a table (R_i(z)), write (m_i(a)=E_p[1_{z_i=a}R_i]/q_i(a)), where
(q_i(1)=p_i,q_i(0)=1-p_i). For distinct nodes the analogous `pairMarginal`
is (E_p[1_{z_i=a,z_j=b}X]/[q_i(a)q_j(b)]). It is only used for
distinct nodes in the second-moment expression below. Define

\[
 \tau_i=m_i(1)-m_i(0),\quad \tau=N^{-1}\sum_i\tau_i,\quad
 \bar m_a=N^{-1}\sum_i m_i(a).
\]

For deterministic fits (g_i(a)), let

\[
 A_i^g(z)=z_i(R_i(z)-g_i(1))/p_i
       -(1-z_i)(R_i(z)-g_i(0))/(1-p_i),\quad
 \delta_i^g=\tau_i-[g_i(1)-g_i(0)],\quad
 H_g(z)=N^{-1}\sum_i[g_i(1)-g_i(0)+A_i^g(z)].
\]

`residualContrast`, `residualEffect`, and `augmented` are respectively these
three expressions. `linearHajek` is **defined** to be (L=H_g) for
(g_i(a)=\bar m_a), not defined by a limiting argument.
`linearFormula` is (\tau+N^{-1}\sum_i A_i^{\bar m}).
The unused `ht` is the usual (N^{-1}\sum_i[z_iR_i/p_i-(1-z_i)R_i/(1-p_i)]).

Set (n_a=\sum_i1_{z_i=a}), (\widehat m_a=\sum_i1_{z_i=a}R_i/n_a),
(\widehat\tau=\widehat m_1-\widehat m_0), and
(e_i=R_i-\widehat m_{z_i}). These are `armCount`, `armMean`, `hajek`,
and `residual`. `ValidArms` means (n_1>0\land n_0>0).
`armRestricted U` equals (U) on this event and zero elsewhere.
Real division in Lean is total: a zero denominator gives zero, not an
undefined expression. The arm guards are therefore substantive.

`interferes R i j` means either (i=j), **even if the outcome is constant**,
or there exist two full assignments that agree away from (j) and give
different (R_i). `sharesSource R i j` means that some node (l) interferes
with both (i) and (j). Thus every node shares a source with itself.
`LocalAt R D h` means (D_{ij}>h\Rightarrow\neg\text{sharesSource}(i,j))
for all ordered pairs. (B_D(i,r)=\{j:D_{ij}\le r\}) includes the boundary;
`ball` is this finite set. `maxDegree` is the maximum neighborhood size,
with finite-supremum convention at (N=0).

A spatial population (P) consists of a metric space (X), an independently
specified measurable space on (X), nonempty sets (S_i\subseteq X), a measure
(\zeta), a function (Y(x,z)\in\mathbb R), and arbitrary real bands
(\operatorname{bands}(d)\subseteq\mathbb R). There is no implicit assumption
that the measurable space is Borel, that nodes are measurable/compact, or
that bands have a particular shape. Define

\[
 \rho_i(x)=\inf_{s\in S_i}\operatorname{dist}(x,s),\quad
 D_{ij}=\inf_{s\in S_i,t\in S_j}\operatorname{dist}(s,t),\quad
 C_i(d)=\{x:\rho_i(x)\in\operatorname{bands}(d)\},\quad
 R_i(d,z)=\frac{\int_{C_i(d)}Y(x,z)\,d\zeta(x)}{\zeta(C_i(d))}.
\]

`nodeDistance` is Mathlib `Metric.infDist`, the extended-distance infimum
converted to a real. Nonempty nodes avoid its empty-set convention.
`nodeSeparation` is a real `sInf`; its set is nonempty and bounded below by
zero because the nodes are nonempty. These set distances need not satisfy
the triangle inequality or distinguish different nodes.
`circleAverage` uses the Bochner integral against the restricted measure,
and `ENNReal.toReal` in its denominator. The integral is zero when its
integrand is not integrable; `toReal` sends infinite mass to zero.
`WellDefined P d` explicitly excludes those conventions: for every node,
(C_i(d)) is measurable, has strictly positive finite measure, and every
assignment's outcome is integrable on it.
`FiniteSourceRange P b` means: for every source (l), point (x), and
assignments (z,z'), agreement off (l) and (\rho_l(x)>b) imply
(Y(x,z)=Y(x,z')).

`Polygonal S` means a finite union of closed convex hulls of triples of points
in the Euclidean plane (degenerate triangles and an empty union are allowed;
population nodes separately must be nonempty). `rectangle a b c d` is the
closed Cartesian rectangle ([a,b]\times[c,d]). The plane uses Euclidean
distance and its usual area measure, not the sup metric.

For sequences (P_N), `MetricNodeDistances` requires, for **every** (N),
(D\ge0), (D_{ij}=0\iff i=j), symmetry, and the triangle inequality.
`BoundedOutcomes` says there is a real (b>0) such that eventually in (N),
for every point and every assignment, (|Y_N(x,z)|<b).
`SpatialLocalConditions` is the conjunction of this boundedness and:

* There exists a function (h(d)), nonnegative for every (d\ge0), such
  that for each (d\ge0), eventually in (N), `LocalAt` holds at radius
  (h(d)) for the circle table and the set distances.
* There exists a real function (c(r)) such that for each (r\ge0),
  eventually in (N), every node has at most (c(r)) nodes at distance
  at most (r). The eventual threshold may depend on (r), and the
  analogous threshold above may depend on (d).

`QuadraticSpacing` instead says there exists (C_b>0) such that eventually
in (N), **simultaneously for every node and every (s\ge0)**,
(|B_D(i,s)|\le C_b(1+s^2)).

Given a set of assignment coordinates (J), `conditionOn p J U z` is
(E_p[1_{z'_J=z_J}U(z')]/\prod_{j\in J}q_j(z_j)).
For interior probabilities this is the actual conditional expectation.
`l2Norm p U` is (\sqrt{E_pU^2}).
`NEDConditions P p d` has the following quantifier order:
there exist a function (\psi:\mathbb R\to\mathbb R), numbers (g_{Ni}),
and a real (G), such that

* (\psi\ge0) on ([0,\infty)), is nonincreasing there, and tends to zero
  as its real argument tends to infinity;
* there exist a real exponent (q>4), reals (C,S) with (S>0), such
  that for every real (s\ge S), (\psi(s)\le Cs^{-q});
* for every (N,i), (0<g_{Ni}\le G);
* for every (N,i,s\ge0), the (L^2) distance between (R_i(d,\cdot))
  and its conditional expectation on assignments within (D)-distance
  (s) of (i) is at most (g_{Ni}\psi(s)).

`KernelConditions K` requires (K(0)=1), (K(t)=0) for every (t>1),
a real (K_{\max}) with (|K(t)|<K_{\max}) for every (t\ge0), and
reals (0<\epsilon<1,C>0) with
(|K(t)-1|\le C|t|) for (0\le t<\epsilon). It requires neither positivity
nor positive semidefiniteness. The uniform kernel is (1_{[0,1]}).
`distanceKernel D K b` is (Q_{ij}=K(D_{ij}/b)).

The regression design has rows (X_i=(1,z_i)). Let (A=(X^TX)^{-1}),
(M=I-XAX^T), and (\lambda_i=z_i/n_1-(1-z_i)/n_0).
`residualMaker` is (M). `sandwich z e Q` is
(A X^T[(e_i e_j Q_{ij})_{ij}]X A); its treatment entry has index ((1,1))
with zero-based indices. `kernelVariance` is
(V(z;e,Q)=\sum_{ij}\lambda_i\lambda_j e_i e_jQ_{ij}).
Mathlib's matrix inverse is the usual inverse when invertible and the
zero matrix when singular. The nonempty-arm assumptions prevent that
singular convention in the matrix assertions.
The corrected observational weighted residual is
(w_i=(n_1/N)z_i(R_i-g_i(1))/\widehat p_i+
(n_0/N)(1-z_i)(R_i-g_i(0))/(1-\widehat p_i)).

For arbitrary neighborhoods (B_i), define the following expanded finite sums:

\[
 S_g=N^{-2}\left[\sum_i\left\{
 \frac{E[(R_i-g_i(1))^2\mid z_i=1]}{p_i}+
 \frac{E[(R_i-g_i(0))^2\mid z_i=0]}{1-p_i}\right\}
 +\sum_i\sum_{j\in B_i\setminus\{i\}}\sum_{a,b\in\{0,1\}}
 (2a-1)(2b-1) E[(R_i-g_i(a))(R_j-g_j(b))\mid z_i=a,z_j=b]\right],
\]

where the conditional expectations mean the finite marginal formulas above.
This is `secondMomentBound`.
`homophilyQ` is (Q_g=N^{-1}\sum_i\sum_{j\in B_i}\delta_i^g\delta_j^g).
`oracleHAC` is (N^{-2}\sum_i\sum_{j\in B_i}A_i^g A_j^g).
`sahLimit` is (N^{-2}\sum_i |B_i|) times the (i)-th diagonal
second-moment bracket in the display for (S_g).

For constant (p), (\epsilon_i(c)=A_i^c/N), with common arm centers
(c=(c_1,c_0)). Define
(V_i(c)=\sum_{j:D_{ij}\le b}\epsilon_i(c)\epsilon_j(c)K(D_{ij}/b)).
`nedVRow` is this random row, `nedV1` is (\sum_iV_i(\widehat m)),
and `nedV2` is (\sum_iV_i(\bar m)). In particular (V_1) is a row
sum using true (p) and sample centers; it is not a separately defined
five-term formula. The deterministic `kernelHomophily` is

\[
 H_N=N^{-1}\sum_{ij}K(D_{ij}/b_N)(\tau_i-\tau)(\tau_j-\tau).
\]

`tailEnvelope P phi r N` is
(\sup_{i\in I_N}\sum_{j:D_{ij}>r_N}\phi(D_{ij})).
For (N>0) this is a maximum of finitely many finite real sums. At (N=0)
the range is empty; this one initial term cannot affect a limit at infinity.

`InProb p U` means: for every real (\epsilon>0),
(P_{p_N}(|U_N|>\epsilon)\to0).
`BigOp p U r` means: for every (\epsilon>0) there exists a real (C>0)
such that eventually (P_{p_N}(|U_N|>C|r_N|)<\epsilon).
`NormalLimit` means convergence of the assignment CDF at **every** real
(x) to (\Phi(x)). Here (\Phi(x)=(\mathrm{gaussianReal}(0,1)((-\infty,x])).
\mathrm{toReal}): Mathlib's Gaussian variance parameter is 1, so this
is the ordinary standard normal CDF.
`Nondegenerate V` means there exists (v>0) with (v\le NV_N) eventually.
`LiminfAtLeast u a` means for every (\epsilon>0), eventually
(a-\epsilon\le u_N); no real-valued `liminf` is used.
`Conservative coverage alpha` is this property at (a=1-\alpha).
`normalQuantile a` is (\inf\{x:a\le\Phi(x)\});
`FiniteQuantile a` explicitly requires that this set is nonempty and bounded
below. `ValidInterval` means both arms are positive **and** (V(z;e,Q)>0).
`GuardedInterval p R Q lo hi` means the implication

\[
 \operatorname{ValidInterval}\ \Longrightarrow\
 lo\le(\widehat\tau-\tau)/\sqrt{V(z;e,Q)}\le hi.
\]

Thus an assignment with an empty arm or nonpositive variance satisfies this
event automatically. It is not the event “a defined interval covers.”

`DependencyGraph mu V B` requires self neighborhoods, symmetric adjacency,
and for every two finite index sets (I,J) with no edge from any (i\in I)
to any (j\in J), independence of the entire vectors ((V_i)_{i\in I})
and ((V_j)_{j\in J}). `IndepFun` is Mathlib independence of the sigma
algebras generated by these vectors, not just zero covariance or pairwise
independence. `FiniteDependencyGraph` expresses the same vector independence
under the finite design via probability factorization for **all** predicates
on both vectors. Singleton neighborhoods consequently express full family
independence, including independence of a variable from any disjoint group.

Finally, `centeredSummand` is
(W_i=[\mu_1-\mu_0+A_i^{(\mu_1,\mu_0)}-\tau_i]/N).

## T16

No hypotheses; the conclusion is a conjunction of four assertions.

1. In the explicit three-node planar population with closed rectangles
   (S_0=[0,1]^2), (S_1=[10,11]\times[0,1]),
   (S_2=[0,11]\times[2,3]), area measure, exact-distance bands
   (\operatorname{bands}(d)=\{d\}), and outcome (z_2) on (S_0\cup S_1)
   and zero elsewhere: averages at (d=0) are well-defined, the source
   range is 2, (|Y(x,z)|<2) for every point and assignment, and for every
   assignment (R_0=R_1=z_2,R_2=0). Nodes 0 and 1 share an interference
   source, their distance is 9, (4<9), and their covariance at independent
   fair assignment is (1/4).
2. For **every real (h\ge0)** there exist a real (L\ge2) (and a proof
   of that inequality) with (L>h+1), for which the same construction
   replacing 10 by (L), 11 by (L+1), and bands by ([0,d]) has
   well-defined zero-distance averages, source range 2, outcomes bounded
   by 2, polygonal pairwise disjoint nodes, (D_{01}=L-1>h), a shared
   source for 0 and 1, and covariance (1/4). It does not quantify this
   assertion over every prescribed (L).
3. For every integer (n>0), take (n+1) rectangles: (S_0=[0,1]^2),
   and for (i=1,\ldots,n),
   (S_i=[2,2+n]\times[2(i-1)/n,(2(i-1)+1)/n]). Each has area 1,
   they are pairwise disjoint as closed sets, and every (D_{0i}<2).
   Also for every real (C) there exists (n>0) with (n+1>C).
4. For every (n>0), the number of these (n+1) rectangles at distance
   at most 2 from (S_0), including (S_0), is exactly (n+1).

## T17

This is the conjunction of the following universal geometric results and
the no-cutoff, area-spacing, and full-count assertions of T16.

* For every (N), every metric/measurable space (A), every spatial
  population (P) with compact nodes, and every three reals
  (d,\bar d,D\ge0), assume its band at (d) is contained in ([0,d]),
  its averages at (d) are well-defined, it has source range (\bar d),
  and every pair of points in each node is at distance at most (D).
  Then for every distinct (i,j), sharing a source implies
  (D_{ij}\le2\bar d+2d+D); and for **all** (i,j), distance greater
  than this cutoff precludes a shared source.
* For every (N), planar spatial population (P), and real (a>0,D\ge0,r\ge0),
  assume all nodes are polygonal, their interiors are pairwise disjoint,
  each area is at least (a) (as an extended nonnegative real comparison),
  and every node has diameter at most (D). Then for every (i),
  (|B_D(i,r)|\le\pi(r+2D)^2/a).

## T18

For every sequence of metric/measurable spaces and populations (P_N),
every constant (p\in(0,1)), and (d\ge0), assume `SpatialLocalConditions`
and that the (d)-averages are well-defined **eventually** in (N).
Set (R_N=R(P_N,d)) and use independent constant-(p) assignment at every
sample size. Then both

\[
 1_{\{n_1,n_0>0\}}\sqrt N(L_N-\widehat\tau_N)\to_p0,
 \qquad 1_{\{n_1,n_0>0\}}(\widehat\tau_N-L_N)=O_p(N^{-1})
\]

hold, where the indicator notation means the piecewise-zero definition,
not an assertion conditional on the event. No metric property of the
set-distance function is separately assumed.

## T19

No hypotheses. Define (V_{Ni}(z)=2z_i-1) if (i=0) and 0 otherwise.
For every (N>0), each variable is bounded in absolute value by 1 on
every assignment, has mean zero and fourth moment at most 1, has singleton
dependency neighborhoods (full vector independence), and those neighborhoods
have cardinality 1. The sum has variance 1 and CDF value (1/2) at (-1/2).
Furthermore (1/N\to0), (\Phi(-1/2)<1/2), and the sum divided by the
square root of its variance does **not** have CDF convergence to a standard
normal as (N\to\infty). The (N=0) term is totalized by real division.

## T20

For every sequence of measurable spaces (\Omega_N), probability measures
(\mu_N), real variables (V_{Ni}:\Omega_N\to\mathbb R), and finite
neighborhoods (B_{Ni}\subseteq I_N), assume, in this order:

1. Every (V_{Ni}) is measurable.
2. For every (N,i), (\int V_{Ni}\,d\mu_N=0).
3. There exists a single real (M) such that for every (N,i),
   (|V_{Ni}|\le M) almost surely under (\mu_N).
4. At every (N) these variables and neighborhoods form a dependency graph
   as expanded above.
5. There exists a single natural number (D) bounding every neighborhood
   cardinality for every (N,i).
6. There exists (v>0) such that eventually in (N),
   (vN\le\int(\sum_iV_{Ni})^2\,d\mu_N).

Then for **every real (x)**, the probability of

\[
 \frac{\sum_i V_{Ni}}{\sqrt{\int(\sum_iV_{Ni})^2\,d\mu_N}}\le x
\]

tends to (\Phi(x)). The common almost-sure bound and finite sums ensure
the displayed integrals are actual integrals. The lower bound applies to
the unnormalized sum's second moment, which is its variance here.

## T21

For every (N), real (p), table (R), and neighborhood map (B), assume
(N>0), (0<p<1), (i\in B_i) for every (i), symmetric adjacency,
and, for every ordered pair, (j\notin B_i\Rightarrow\neg\text{sharesSource}(i,j)).
Set (p_i=p) and (g_i(a)=\bar m_a). Then for every node (i),

\[
 \operatorname{Var}(A_i^g)=
 E[(R_i-g_i(1))^2\mid z_i=1]/p+
 E[(R_i-g_i(0))^2\mid z_i=0]/(1-p)-(\delta_i^g)^2,
\]

and (\operatorname{Var}(L)\le\operatorname{sahLimit}(p,R,B,g)).
This is a finite-sample inequality, not convergence of a sample estimator.

## T22

For every (N), probability vector (p), table (R), neighborhoods (B),
and deterministic fits (g_i(a)), assume (N>0), all (0<p_i<1),
all self memberships, and that every ordered non-neighbor pair has no
shared source. Symmetry of (B) is **not** required here. Then

\[
 \operatorname{Var}(H_g)=S_g-Q_g/N,
 \qquad Q_g\ge0\ \Longrightarrow\ \operatorname{Var}(H_g)\le S_g.
\]

Both (S_g) and (Q_g) are the full finite sums above, including the
diagonal effect products in (Q_g). No fitted-propensity convergence
or equality to an IPW estimator is asserted.

## T23

For every (N), vector of reals (\widehat p_i), table (R), neighborhoods
(B), deterministic fits (g), and assignment (z), assume (N>0),
(n_1>0,n_0>0), and (0<\widehat p_i<1) for every node.
Then (\lambda_i w_i=A_i^g/N) for every node, and the ((1,1)) entry of
the sandwich matrix with residual (w_i) and kernel
(Q_{ij}=1_{j\in B_i}) equals (N^{-2}\sum_i\sum_{j\in B_i}A_i^gA_j^g).
There is no constraint on how the displayed propensity values were obtained,
no symmetry requirement on (B), and no coverage conclusion.

## T24

For every (N), assignment (z) with (n_1>0,n_0>0), every real vector
(e\in\mathbb R^N), and every real (N\times N) matrix (Q), all seven
assertions hold:

\[
 M^T=M,\quad M^2=M,\quad MX=0,\quad
 (AX^T)_{1i}=\lambda_i\ (\forall i),\quad
 A_{11}=N/(n_1n_0),\quad
 \sum_i\lambda_i^2=N/(n_1n_0),\quad
 [AX^T(e_ie_jQ_{ij})XA]_{11}=V(z;e,Q).
\]

No positivity or symmetry assumption on (Q) is imposed.

## T25

For every (N), vector (p), table (R), and real constants (\mu_1,\mu_0),
assume (N>0) and every (0<p_i<1). Then (E_pW_i=0) for every node,
(\sum_i W_i(z)=H_{(\mu_1,\mu_0)}(z)-\tau) for every assignment, and
for every node

\[
 E_p[W_i+(1/N-1)\tau_i]=(1/N-1)\tau_i.
\]

The last expression is the statement's exact representation of the shifted
summand; it is not a conditional-expectation or NED closure assertion.

## T26

For every sequence of metric/measurable spaces and populations (P_N),
every real (p,d), functions (K,\phi:\mathbb R\to\mathbb R), and real
bandwidth sequence (b_N), assume, in order:

* (0<p<1) (there is **no** (d\ge0) assumption);
* bounded outcomes eventually; well-defined (d)-averages for **every** (N);
* metric node distances for **every** (N); uniform quadratic spacing eventually;
* the kernel conditions; (b_N\to\infty); (b_N>0) for **every** (N);
* (\phi(s)\ge0) for every (s\ge0);
* eventually in (N), for all (i,j),
  (|\tau_i-\tau|\,|\tau_j-\tau|\le\phi(D_{ij}));
* **for every** real sequence (r_N\to\infty),
  (\max_i\sum_{j:D_{ij}>r_N}\phi(D_{ij})\to0).

Then (H_N\to0). There is no explicit shrinking-bandwidth or NED assumption,
and no separately stated auxiliary-radius rate.

## T27

No hypotheses. For every (N), put nodes at planar points
(x_i=((i+1)N^2,0)), let (\zeta_N=\sum_i\delta_{x_i}), use bands
([0,d]), and set (Y_N(x,z)=\sum_i1_{x=x_i}R_i(z)), with
(R_0(z)=1/4+3z_0/4) and (R_i(z)=0) for (i\ne0).
Put (p=1/2,d=1,K=1_{[0,1]}), (b_N=\lfloor N^{1/12}\rfloor)
(natural-number floor cast to a real). The conclusion asserts all of:

* bounded outcomes, uniform quadratic spacing, the above NED conditions,
  and the kernel conditions;
* (b_N\to\infty) and (b_N=o(N^{1/6})) in Mathlib's norm-inequality
  sense of little-o;
* for every (N\ge3) the distance-1 averages are well-defined;
* for every (\epsilon>0), eventually (H_N\ge-\epsilon);
* (N\operatorname{Var}(L_N)\to0);
* (P(\neg G_N)\to0), where (G_N=\{2N/5\le n_1\le3N/5\});
* for every (N\ge10) and every assignment in (G_N), both arms and
  the HAC variance are positive, and the guarded studentized event with
  critical values (-2,2) holds if and only if (z_0=1);
* for every (N>0), (P(z_0=1)=1/2);
* if (\alpha=2[1-\Phi(2)]), then (0<\alpha<1) and (1-\alpha\ge3/4).

An unconditional limit for the coverage probability is not an explicit conjunct.

## T28

For every sequence of metric/measurable spaces and populations (P_N),
every real (p,d), kernel (K), and bandwidth sequence (b_N), assume
(0<p<1,d\ge0), eventual bounded outcomes, well-defined (d)-averages at
every (N), the NED conditions, metric node distances at every (N),
uniform quadratic spacing eventually, the kernel conditions, positive
bandwidths at every (N), (b_N\to\infty), (b_N=o(N^{1/6})), and
(H_N\ge-\epsilon) eventually for every (\epsilon>0).
Use the circle tables, set distances, and residual HAC variance (V_{\rm hac}).
Then the following four unconditional conclusions and one conditional
conclusion hold:

\[
 1_{\mathrm{ValidArms}}N(V_{\rm hac}-V_1)\to_p0,\quad
 1_{\mathrm{ValidArms}}N(V_1-V_2)\to_p0,\quad
 1_{\mathrm{ValidArms}}N(V_2-EV_2)\to_p0,\quad
 \forall\epsilon>0,\ \text{eventually }N(EV_2-\operatorname{Var}L)\ge-\epsilon.
\]

If, **in addition**, there exists (v>0) with (N\operatorname{Var}L\ge v)
eventually, then for every real (\alpha\in(0,1)), if both Gaussian
inverse-CDF sets for (\alpha/2) and (1-\alpha/2) are nonempty and bounded
below, the probability of the **guarded implication event** with those
two quantiles is eventually at least (1-\alpha-\epsilon), for each
(\epsilon>0). Invalid intervals count as successes. The conclusion
does not require the coverage probability to have a limit.

## T29

This is a conjunction of four independently universally quantified statements.

1. **Far covariance.** For every population sequence, real (p,d), functions
   (K,\psi), and bandwidth sequence (b_N), assume (0<p<1), eventual
   bounded outcomes, metric node distances at every (N), uniform quadratic
   spacing eventually, the kernel conditions, nonnegative and nonincreasing
   (\psi) on ([0,\infty)), and a real (G) such that the conditional
   (L^2) approximation error for every (N,i,s\ge0) is at most
   (G\psi(s)). Also assume well-defined averages at every (N) and
   (b_N\ge1) at every (N). No limit or polynomial decay of (\psi),
   no (d\ge0), and no bandwidth divergence is assumed here. Then there
   exists a real (C) such that eventually in (N), for every (i,j)
   with (D_{ij}>3b_N),
   \[
   |\operatorname{Cov}(V_i(\bar m),V_j(\bar m))|
   \le C b_N^2 N^{-4}\max\left\{
   \sum_{k:D_{ik}\le b_N}\psi(D_{ij}/3-D_{ik}),
   \sum_{l:D_{jl}\le b_N}\psi(D_{ij}/3-D_{jl})\right\}.
   \]
2. **HAC expansion.** For every (N,R,D,K), real (b,p), and assignment
   (z), assume (b>0), the kernel conditions, symmetric nonnegative
   (D) with zero diagonal, and (n_1,n_0>0). The parameter (p) is
   unused and unrestricted. Writing (e_i=R_i-\widehat m_{z_i}), the
   residual HAC variance equals
   \[
   \frac{\sum_i z_i e_i^2}{n_1^2}+\frac{\sum_i(1-z_i)e_i^2}{n_0^2}
   +\frac{\sum_{i\ne j}z_i z_j e_i e_jK(D_{ij}/b)}{n_1^2}
   -\frac{2\sum_{i\ne j}(1-z_i)z_j e_i e_jK(D_{ij}/b)}{n_1n_0}
   +\frac{\sum_{i\ne j}(1-z_i)(1-z_j)e_i e_jK(D_{ij}/b)}{n_0^2}.
   \]
3. **Epsilon products.** For every Boolean (z,w), reals
   (N,p,y_i,y_j,h_1,h_0,b_1,b_0), assume only (N\ne0,p\ne0,1-p\ne0).
   Define (E(a,y,c)=a(y-c_1)/(Np)-(1-a)(y-c_0)/(N(1-p))),
   (\Delta_a=h_a-b_a). Then (E(z,y_i,h)E(w,y_j,h)-E(z,y_i,b)E(w,y_j,b))
   is the sum of these four terms:
   \[
   \frac{zw}{N^2p^2}[-(y_i+y_j)\Delta_1+h_1^2-b_1^2],\quad
   \frac{(1-z)(1-w)}{N^2(1-p)^2}[-(y_i+y_j)\Delta_0+h_0^2-b_0^2],
   \]
   \[
   -\frac{(1-z)w}{N^2p(1-p)}[-y_i\Delta_1-y_j\Delta_0+h_0h_1-b_0b_1],\quad
   -\frac{z(1-w)}{N^2p(1-p)}[-y_i\Delta_0-y_j\Delta_1+h_0h_1-b_0b_1].
   \]
4. **Epsilon means.** For every natural (N), real scalar (p),
   table (R), and real (N\times N) matrix (Q),
   assume (N>0,0<p<1). With (\epsilon_i=A_i^{\bar m}/N),
   (E\epsilon_i=(\tau_i-\tau)/N) for every node, and
   \[
   \sum_{ij}Q_{ij}[E(\epsilon_i\epsilon_j)-\operatorname{Cov}(\epsilon_i,\epsilon_j)]
    =N^{-2}\sum_{ij}Q_{ij}(\tau_i-\tau)(\tau_j-\tau).
   \]

## T30

This has three separate universal conjuncts.

1. For every (N,n_1\in\mathbb N) with (1\le n_1\le N-1), every
   (i\in I_N), and Boolean (a), assume the number of full assignments
   with exactly (n_1) treated nodes and (z_i=a) is positive, and the
   number of assignments on (I_N\setminus\{i\}) with exactly (n_1-a)
   treated nodes is positive. Then for **every** remainder assignment (u),
   the fraction of the first support whose remainder equals (u) is the
   reciprocal of the second support's cardinality if (u) belongs to it,
   and zero otherwise. Both (N-1) and (n_1-a) in the Lean supports use
   natural-number truncated subtraction; (n_1\ge1) and (i\in I_N)
   prevent underflow for admissible instances.
2. For every (N,p_i,R,i,a), if all (0<p_j<1), then
   (m_i(a)=E_p[R_i(\operatorname{update}(z,i,a))]), where `Function.update`
   forces just coordinate (i) to (a).
3. For every (N,p,R) with (N>0,0<p<1), the linear estimator equals
   the explicit formula (\tau+N^{-1}\sum_i A_i^{\bar m}) on **every**
   assignment, equals the augmented estimator with the two population arm
   centers as a function, and on **every** assignment
   \[
   H_{g_i(1)=g_i(0)=\bar m_1}-L
      =(\bar m_1-\bar m_0)\left[\frac{n_0}{N(1-p)}-1\right].
   \]

## Mathlib boundary checked during the blind stage

The source definitions inspected were `Metric.infDist` in
`Topology/MetricSpace/HausdorffDistance.lean`, `gaussianReal` in
`Probability/Distributions/Gaussian/Real.lean`, `IndepFun` and its vector
meaning in `Probability/Independence/Basic.lean`, `IntegrableOn` in
`MeasureTheory/Integral/IntegrableOn.lean`, the total Bochner integral in
`MeasureTheory/Integral/Bochner/Basic.lean`, matrix inversion in
`LinearAlgebra/Matrix/NonsingularInverse.lean`, convex hull in
`Analysis/Convex/Hull.lean`, and little-o in `Analysis/Asymptotics/Defs.lean`.
Finite products, sums, filters of `Finset.univ`, and matrix products have
their ordinary finite algebraic meanings. `atTop` on natural sample sizes
means eventually all (N\ge N_0); on real radii it means tending to positive
infinity. `nhds` is the usual topology on the real numbers.

Editorial note after the record stage: the grammatical list of objects in
T29(4) was corrected to state the already intended types of N, p, R, and Q;
two stray inline-math delimiter backslashes were removed. No mathematical
reading or step-2 verdict changed.
