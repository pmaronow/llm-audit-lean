# Blind reading

Saved before opening `claims.json` or `record.json`. I read the five Challenge
docstrings and statements, every source declaration listed in their closures,
and printed all listed generated proof/match helpers in
`scratch/ClosureChecks.lean` (successful compilation). The helpers are just
Option/Sum pattern eliminators, numeral `AtLeastTwo` proofs, and `NeZero`
instances. The listed structure constructors and projections have exactly their
source fields and impose no additional invariants.

## Common mathematical notation (fully expanded definitions)

The index set is (I_n=\{0,\ldots,n-1\}\), including the empty set when
(n=0\). A population consists of arbitrary real numbers (y_i(d)),
binary values (D_i(z)\in\{0,1\}), and an arbitrary natural number (n_1\).
Potential outcomes are indexed by receipt, not assignment; exclusion is
therefore built into this representation. A covariate population additionally
has (x_i\in\mathbb R^k\). A Bool is converted to the real number 0 or 1.

Write (C=\{i:D_i(0)=0,D_i(1)=1\}\). Monotonicity means
(D_i(0)=1\Rightarrow D_i(1)=1\) for every unit. Validity means
(n\ge2\) and (0<n_1<n\). Put (r_n=n_1/n\), (n_0=n-n_1\),
and (\mathcal A=\{S\subseteq I_n:|S|=n_1\}\). Complements below are in
(I_n\). Design probability is exactly
(\Pr(E)=|\{S\in\mathcal A:E(S)\}|/|\mathcal A|\).

For an array (q\), write

* (\bar q=n^{-1}\sum_iq_i\), and
  (\bar q_H=|H|^{-1}\sum_{i\in H}q_i\);
* (V(q)=(n-1)^{-1}\sum_i(q_i-\bar q)^2\),
  (K(q,t)=(n-1)^{-1}\sum_i(q_i-\bar q)(t_i-\bar t)\);
* (K_H(q,t)=(|H|-1)^{-1}\sum_{i\in H}(q_i-\bar q_H)(t_i-\bar t_H)\)
  if (|H|\ge2\), and 0 otherwise; (V_H(q)=K_H(q,q)\);
* (L=|C|^{-1}\sum_{i\in C}(y_i(1)-y_i(0))\);
* (w_i(z;\beta)=y_i(D_i(z))-\beta D_i(z)\), and
  (v_i(z;\beta)=w_i(z;\beta)-n^{-1}\sum_jw_j(z;\beta)\);
* (D_i^O=D_i(1_{i\in O})\), (Y_i^O=y_i(D_i^O)\), and
  (W_i^O(\beta)=Y_i^O-\beta D_i^O\);
* (F_4(q)=\sqrt{\sqrt{n^{-1}\sum_iq_i^4}}\).

Every division here is Lean real division, so division by zero is zero. The
coercions of natural numbers to reals are exact; (n-n_1\), (n-1\), and
(|H|-1\) in the displayed source formulas are real subtraction, not truncated
natural subtraction.

For covariates, let (a_i=(1,x_i)\), with its intercept coordinate indexed by
`none` and the (k\) slope coordinates by `some j`. For a subset (H\),
(G_H=|H|^{-1}\sum_{i\in H}a_ia_i^T\), and
(b_H(q)=|H|^{-1}\sum_{i\in H}a_iq_i\). The coefficient vector (c_H(q)\)
is (G_H^{-1}b_H(q)\) when (\det G_H\ne0\). On a singular arm it is a
fixed classically chosen minimizer of
(\operatorname{RSS}_H(q,c)=\sum_{i\in H}(q_i-a_i^Tc)^2\), if one exists,
and the zero vector otherwise. Finite dimensional real least squares always has
a minimizer, so that final fallback is unreachable. Singular minimizers need
not have unique slopes; the choice is part of the function. This is the full
meaning of the SAP OLS, fitted, Gram, score, RSS, augmented-vector, and slope
dot-product definitions used below.

Define the following real contrasts and scales, for any fixed real (q\):

\[
t_S(q)=n^{-1}\sum_iq_i(1_{i\in S}-r_n),\qquad
s_S^2(q)=r_n^2(1-r_n)^2\left[
 {\sum_{i\in S}(q_i-\bar q_S)^2\over n_1^2}
 +{\sum_{i\notin S}(q_i-\bar q_{S^c})^2\over n_0^2}\right],
\]
\[
T_S(q)=\overline{q_i-x_i^Tc_{S,\mathrm{slope}}(q)}_S
       -\overline{q_i-x_i^Tc_{S^c,\mathrm{slope}}(q)}_{S^c},\qquad
U_S^2(q)={\operatorname{RSS}_S(q,c_S(q))\over n_1^2}
       +{\operatorname{RSS}_{S^c}(q,c_{S^c}(q))\over n_0^2}.
\]

Absolute studentization takes values in (\mathbb R_{\ge0}\cup\{+\infty\}\):
(A(t,0)=0\) if (t=0\), (A(t,0)=+\infty\) otherwise, and
(A(t,s)=\operatorname{ofReal}(|t|/\sqrt{s})\) for (s\ne0\).
Here `ofReal` truncates negative reals to zero and `sqrt` is zero on negative
reals. Thus the unadjusted statistic is (A(t_S(q),s_S^2(q))\), and the
adjusted statistic is (A(T_S(q),U_S^2(q))\).

For a function (h:\mathcal A\to[0,+\infty]\), the full-design critical
value (q_\alpha(h)\) is the smallest attained value (u\) with
(\Pr(h(S)\le u)\ge1-\alpha\), or (+\infty\) if there is no such
value. Both statistics and the quantile comparison use extended order,
including (+\infty\le+\infty\). The coverage functions in T29 and T30 are
respectively the design probabilities of

\[
A(t_O(W^O(\beta)),s_O^2(W^O(\beta)))
 \le q_\alpha(S\mapsto A(t_S(W^O(\beta)),s_S^2(W^O(\beta))))
\]

and the analogous inequality with (T,U\). The same observed vector is held
fixed while computing the reference quantile; the outer probability varies
the observed assignment (O\).

## SAP.P002b.T26

The statement is a conjunction of a universal assertion and three unconditional
concrete membership assertions.

First quantify (n,k\in\mathbb N\), a covariate population, arbitrary real
arrays (Y,D:I_n\to\mathbb R\), and (S\subseteq I_n\). Assume, in order:
validity; (S\in\mathcal A\); (\sum_ix_{ij}=0\) for every coordinate;
(\det G_S\ne0\); and (\det G_{S^c}\ne0\). There is no binary-receipt,
monotonicity, complier, or positive-(k\) assumption in this universal part;
(Y,D\) are arbitrary real vectors. The conclusions are:

1. For every real (\beta\),
   (T_S(Y-\beta D)=T_S(Y)-\beta T_S(D)\).
2. The difference of the two fitted intercepts for (Y\) equals (T_S(Y)\),
   and the corresponding difference for (D\) equals (T_S(D)\). This
   intercept difference is the definition called the interacted treatment
   coefficient. With full rank it is the coefficient on treatment after the
   invertible change from separate arm intercepts to an intercept and treatment
   indicator, retaining separate arm slopes.
3. For every (0<\alpha<1\), **if also** both augmented Grams are invertible
   for every (R\in\mathcal A\), then
   \[
   F_\alpha=\{\beta:A(T_S(Y-\beta D),U_S^2(Y-\beta D))
       \le q_\alpha(R\mapsto A(T_R(Y-\beta D),U_R^2(Y-\beta D)))\}
   \]
   is a finite union of order-connected subsets of (\mathbb R\).
   Explicitly, there exist (m\in\mathbb N\) and sets (I_0,\ldots,I_{m-1}\)
   such that each (I_j\) contains every point between any two of its points,
   and (x\in F_\alpha\) iff (x\in I_j\) for some (j\). This includes empty
   sets, singletons, open/closed/half-open and unbounded intervals.
4. If (T_S(D)\ne0\), then for every (0<\alpha<1\), putting
   (b=T_S(Y)/T_S(D)\), the adjusted contrast at (Y-bD\) is zero, its
   extended-valued statistic is zero, and (b\in F_\alpha\). This clause
   does not require full rank for other assignments.
5. Define regressor rows (X_i=(D_i,1,1_{i\notin S}x_i,1_{i\in S}x_i)\)
   and instrument rows (Z_i=(1_{i\in S},1,1_{i\notin S}x_i,1_{i\in S}x_i)\).
   The index type is the disjoint union of two coordinates and
   (\{0,1\}\times I_k\). Put
   (H=n^{-1}\sum_iZ_iX_i^T\), (J=n^{-1}\sum_iZ_iZ_i^T\), and
   (b^{IV}=H^{-1}(n^{-1}\sum_iZ_iY_i)\).
   If (\det H\ne0\), then if (\det J\ne0\),
   (T_S(D)b^{IV}_0=T_S(Y)\); additionally if (T_S(D)\ne0\),
   (b^{IV}_0=T_S(Y)/T_S(D)\).

The independent concrete assertion uses eight units, (n_1=4\), (k=1\),
(x_i=2i-7\), (O=\{0,1,2,3\}\), potential outcomes equal in both receipt
states with values ((-4,0,2,-2,2,-6,-4,6)\), unit 1 a complier, units
5,6,7 always-takers, and all remaining units never-takers. Set (Y=Y^O\),
(D=D^O\), and (\alpha=1/2\). The conclusion is precisely
(-12\in F_{1/2}\), (10\in F_{1/2}\), and (-7\notin F_{1/2}\).
This entails a nonempty set that is not an interval; it does not explicitly
assert the witness's design/rank conditions in the same conjunction.

Junk-value audit: validity excludes empty population and zero arm denominators
for valid assignments. The observed-arm rank hypotheses exclude arbitrary
singular OLS slopes in the algebraic claims, and the extra all-assignment rank
hypothesis does the same in the interval claim. Wald division is guarded by a
nonzero denominator. Both IV inverses are guarded; Mathlib's singular inverse
would otherwise be zero. Zero residual variance is allowed and the stipulated
zero/infinity studentization affects confidence-set membership. All scales are
sums of squares with nonnegative weights, so negative square roots and negative
`ofReal` inputs do not arise. The quantile fallback is unreachable on a valid
design at an interior level, though a genuine quantile can be infinite.
(k=0\) is allowed, with empty slope sums but an existing intercept coordinate;
(m=0\) in the finite union legitimately describes an empty set. There are no
integrals, logarithms, real powers, asymptotic extrema, or truncated subtraction.
The witness's literal finite indices and numeral instances are in range.

## SAP.P002b.T27

Quantify (M\in\mathbb N\), one six-real coefficient vector (Q_f\), a family
(Q_m\) indexed by (m\in I_M\), and (\alpha\in\mathbb R\), then assume
(M>0\) and (0<\alpha<1\). For (Q=(a,b,c,d,e,f)\), put
(R_Q(\beta)=(a\beta^2+b\beta+c)/(d\beta^2+e\beta+f)\).
Assume the following common-dataset condition, followed by regularity of
(Q_f\) and every (Q_m\).

The dataset condition is existential: there exist (n,k\), a covariate
population, a Boolean choice of adjusted/unadjusted setting, an observed
assignment (O\), and assignments (T_m\), with a valid design, monotone
receipt, nonempty (C\), and (O,T_m\in\mathcal A\). If the setting is
adjusted, require (k>0\), centered covariates, and invertible augmented Grams
in both arms for (O\) and every (T_m\). No distribution or independence of
the (T_m\) is asserted; this is a fixed finite family.

Here are the coefficient equalities in that condition, fully expanded. Fix
(Y=Y^O,D=D^O\). In the unadjusted setting at assignment (S\), set
(a=t_S(D)^2\), (b=-2t_S(Y)t_S(D)\), (c=t_S(Y)^2\),
(d=s_S^2(D)\), (f=s_S^2(Y)\), and
\[
e=-2r_n^2(1-r_n)^2\left[
 {\sum_{i\in S}(Y_i-\bar Y_S)(D_i-\bar D_S)\over n_1^2}
 +{\sum_{i\notin S}(Y_i-\bar Y_{S^c})(D_i-\bar D_{S^c})\over n_0^2}\right].
\]
In the adjusted setting replace (t,s^2\) by (T,U^2\), and replace the
cross term by
\[
e=-2\left[
 {\sum_{i\in S}(Y_i-a_i^Tc_S(Y))(D_i-a_i^Tc_S(D))\over n_1^2}
 +{\sum_{i\notin S}(Y_i-a_i^Tc_{S^c}(Y))(D_i-a_i^Tc_{S^c}(D))\over n_0^2}\right].
\]
(Q_f\) must equal these coefficients at (S=O\), and (Q_m\) those at
(S=T_m\). Regularity means separately for every real (\beta\) that the
denominator polynomial is strictly positive and the numerator polynomial is
nonnegative, for the observed curve as well as every simulated curve.

Put (g_m=R_{Q_m}\). At (\beta\), the empirical critical value (c_\alpha(\beta)\)
is the smallest attained real (\sqrt{g_m(\beta)}\) with at least
((1-\alpha)M\) of the (M\) values less than or equal to it; its fallback
is zero. The quantile index set is
(K_\alpha(\beta)=\{m:\sqrt{g_m(\beta)}=c_\alpha(\beta)\}\).
A crossing is a real (\beta\) with (g_s(\beta)=g_t(\beta)\) for two
functions (g_s\ne g_t\). Function inequality is extensional: identical
curves are excluded, even if their coefficient vectors differ.

Next quantify (l,u\in\overline{\mathbb R}=\mathbb R\cup\{-\infty,+\infty\}\).
Assume (l<u\) and there is no crossing for any real (\beta\) with
(l<\beta<u\). The conclusions, in order, are:

1. For every real (x,y\in(l,u)\), (K_\alpha(x)=K_\alpha(y)\).
2. For every (x\in(l,u)\) and every (a,b\in\mathbb R\), if (l=a\)
   and (u=b\), then (K_\alpha(x)\subseteq K_\alpha(a)\) and
   (K_\alpha(x)\subseteq K_\alpha(b)\).
3. For every (x\in(l,u)\) and every real (b\), if (l=-\infty\) and
   (u=b\), then (K_\alpha(x)\subseteq K_\alpha(b)\).
4. For every (x\in(l,u)\) and every real (a\), if (u=+\infty\) and
   (l=a\), then (K_\alpha(x)\subseteq K_\alpha(a)\).

Junk-value audit: strictly positive denominator polynomials exclude real
division by zero, and nonnegative numerators make every square root legitimate.
(M>0\) and the interior level make the empirical-quantile candidate set
nonempty. The finite valid dataset avoids zero population and arm denominators;
adjusted OLS is evaluated only on the explicitly full-rank arms. Endpoints are
extended reals but are never converted to reals in this assertion; inclusions
are asserted only at finite endpoints. Empty covariate types are allowed in
the raw setting. There are no integrals, `sInf`/`sSup`, or limits.

## SAP.P002b.T28

Quantify (M,Q_f,(Q_m),\alpha\), and impose **exactly** the positivity,
common-dataset, and regularity assumptions expanded in the T27 section. Put
(f=R_{Q_f}\), (g_m=R_{Q_m}\), with the same (c_\alpha,K_\alpha\) and
crossing definition. The empirical confidence set is
(E=\{\beta:\sqrt{f(\beta)}\le c_\alpha(\beta)\}\).

A complete crossing list (J\) is a finite list of real numbers strictly
increasing pairwise, with membership equivalent to being a crossing. For such
a list, zip the left endpoints ((-\infty,J_0,\ldots)\) with the right
endpoints ((J_0,\ldots,+\infty)\) to obtain the ordered gaps, including the
whole line if (J=[]\). The prescribed real gap sample is 0 on the whole
line, (u-1\) for ((-\infty,u)\), (l+1\) for ((l,+\infty)\), or
((l+u)/2\) between finite endpoints.

A piece is a triple (p=(l_p,u_p,m_p)\) of two extended-real endpoints and
an index in (I_M\). Its accepted set is
(E_p=\{\beta:l_p\le\beta\le u_p,\ f(\beta)\le g_{m_p}(\beta)\}\).
The returned set for a finite piece list is (\bigcup_{p\text{ in list}}E_p\).

An Algorithm 1/3 run is a piece list whose endpoint-pair list is exactly the
gap list of a complete crossing list and whose index in each gap belongs to
(K_\alpha\) at its prescribed sample. It imposes no quantile condition
elsewhere as an input hypothesis.

An Algorithm 2/4 run requires a nonempty complete crossing list and a nonempty
piece list. The first piece starts at (-\infty\) and selects an index in
(K_\alpha(J_0-1)\). For each piece (p\), form
\[
C_p=\{\beta:l_p<\beta,\ \exists m,\ g_m\ne g_{m_p},\ g_m(\beta)=g_{m_p}(\beta)\}.
\]
If (C_p\) is nonempty its least element must exist and equal the finite
right endpoint of (p\); if empty the right endpoint is (+\infty\).
For the last piece require right endpoint (+\infty\). For a following
piece (q\), require (u_p\ne+\infty\), (l_q=u_p\), and choose its index
in (K_\alpha\) at the midpoint between (u_p\) and the first crossing in
(J\) strictly greater than (u_p\), or at (u_p+1\) if there is none.
These are corrected pair-preserving interval/index records.

The six conclusions of T28, in order, are:

1. There exists a complete finite crossing list.
2. Every complete crossing list admits an Algorithm 1/3 run.
3. For all crossing lists and pieces, every Algorithm 1/3 run returns (E\).
4. Every nonempty complete crossing list admits an Algorithm 2/4 run.
5. For all crossing lists and pieces, every Algorithm 2/4 run returns (E\).
6. For every complete crossing list, if it is empty, every real sample has a
   nonempty quantile index set, and for every real sample (\beta\) and every
   (m\in K_\alpha(\beta)\), the set (\{x:f(x)\le g_m(x)\}\) equals (E\).

There is no assertion about every prescribed choice policy terminating, a
numerical runtime bound, or the sizes/order/covering properties of runs as
separate conclusions. Existence is not conditional on an already completed run.

Junk-value audit: the T27 safeguards still apply. `EReal.toReal` maps both
infinities to zero, and `List.head!` defaults to real zero on an empty list.
For genuine gaps of a strictly sorted complete list, `gapSample` reaches the
finite-endpoint branches correctly and never uses an infinity's real image.
In Algorithm 2 the initial head is protected by (J\ne[]\). A following step
uses a finite crossing endpoint, and the head of the filtered list is taken
only in its nonempty branch. The definition asks for `IsLeast` rather than
silently taking an infimum of a possibly bad set. List indexing of a piece uses
a bounded finite index; the successor lookup uses `Option`, with `none`
explicitly identifying the terminal step. Empty crossing lists are handled
separately, and an empty returned union is just the empty set. No natural
subtractions, Bochner integrals, logarithms, or real powers occur.

## SAP.P002b.T29

For a fixed (n\), the class specified by parameters (\delta,r,A\) consists
of populations with valid design, monotone receipt, nonempty (C\),
(rn\le n_1\le(1-r)n\), and
\[
K_C(w(1;L),w(0;L))\ge
 -\delta\sqrt{V_C(w(1;L))}\sqrt{V_C(w(0;L))},
\qquad
F_4(v(z;L))\le A\sqrt{V(w(z;L))}\quad(z=0,1).
\]
All of these are the finite sums and square roots expanded above; notably
there is no strictly positive variance requirement.

Let (h_n(\delta,r,A,\alpha)\) be the infimum in ([0,+\infty]\), first over
all real (\beta\), then over all populations in this class with (L=\beta\),
of `ofReal` of their unadjusted coverage at (\beta,\alpha\). Coverage is
exactly the full-randomization probability expanded in the common notation.
An empty inner class contributes (+\infty\). Thus the whole infimum is
(+\infty\) if the class is empty, not zero or a real fallback.

T29 says the following universal statement is **not** true: for every ordered
choice of real (\delta,r,A,\alpha\), if (\delta<1\), (0<r\le1/2\),
(A>0\), and (0<\alpha<1\), then the sequence (n\mapsto h_n\), indexed by
**all** natural population sizes, converges as (n\to\infty\) to the extended
nonnegative real `ofReal`((1-\alpha\)). Equivalently, at least one admissible
choice of these four constants has failure of that exact nominal limit. No
particular witness, subsequence, or reason for the failure is specified in the
statement. There is no lower bound on (\delta\), and no assumption that the
model classes are eventually nonempty.

Junk-value audit: valid populations have (n\ge2\), nonempty assignment support,
nonempty compliers, and positive arm sizes. A single complier gives group
covariance and variance zero by an explicit branch. Zero population variances
and fourth moments are permitted; the moment inequality is then (0\le0\).
All square roots in the parameter class have nonnegative arguments. Studentization
uses zero/infinity at zero scale, as in the common definitions. Infima are genuine
complete-lattice infima of extended nonnegative reals: empty classes yield top,
which can persist for infinitely many sizes and affect the claimed convergence.
There is no `toReal` applied to top, no real `sInf` of an unbounded set, and no
`limsup`/`liminf`; this is ordinary topological convergence in the extended
nonnegative reals. No integrability or measurability failure can arise in this
finite sample space. The declaration's negative claim itself supplies no
nonvacuity construction.

## SAP.P002b.T30

For fixed (n,k\) and real parameters (\delta,e,A,B,r\), define a class of
covariate populations by valid design, monotone receipt, nonempty (C\), and
(rn\le n_1\le(1-r)n\). Let (c_z\) minimize
(\sum_i(w_i(z;L)-a_i^Tc)^2\) by the precise OLS rule in the common notation,
and put \(\epsilon_i(z)=w_i(z;L)-a_i^Tc_z\). Additionally require

\[
K(\epsilon(1),\epsilon(0))\ge
 -\delta\sqrt{V(\epsilon(1))}\sqrt{V(\epsilon(0))},\qquad
F_4(\epsilon(z))\le B\sqrt{V(\epsilon(z))}\quad(z=0,1),
\]
\[
\sum_ix_{ij}=0\quad\text{and}\quad n^{-1}\sum_ix_{ij}^4\le A\quad(\forall j),
\qquad
e\sum_jb_j^2\le n^{-1}\sum_i(x_i^Tb)^2\quad(\forall b\in\mathbb R^k).
\]
This expands the population coefficient, residual, covariance, fourth-norm,
squared-norm, and Rayleigh-inequality definitions in the closure. There is no
strictly positive residual variance assumption and no full-rank sample-arm
assumption. Centering and (e>0\) ensure full rank of the population augmented
Gram when the class is inhabited; sample arms can still be singular and use the
chosen least-squares minimizer.

Let \(h_n( k,\delta,e,A,B,r,\alpha)\) be the infimum in ([0,+\infty]\), first
over \(\beta\in\mathbb R\), then over covariate populations in this class
with (L=\beta\), of `ofReal` of their adjusted coverage at \(\beta,\alpha\).
The adjusted coverage uses the fixed observed adjusted vector and all design
assignments as expanded above. Empty inner classes contribute top.

T30 negates the following universal statement: for every ordered choice of
natural (k\) and real \(\delta,e,A,B,r,\alpha\), if \(k>0\), \(\delta<1\),
\(e,A,B>0\), \(0<r\le1/2\), and \(0<\alpha<1\), then the sequence of these
infima indexed by all natural (n\) converges to `ofReal`((1-\alpha\)).
Equivalently, there is one admissible fixed dimension and tuple of constants
for which the exact nominal limit fails. No witness or eventual nonemptiness
hypothesis appears.

Junk-value audit: the valid-design, complier, covariance, studentization and
extended-infimum conventions in T29 apply. In addition, singular sample OLS
is allowed, but it is a true least-squares minimizer, not an inverse set to zero;
its arbitrary coefficient choice can affect off-arm predictions used in adjusted
contrasts. The fallback zero in the absence of any minimizer is unreachable in
finite real least squares. The population Gram is nonsingular under the positive
Rayleigh bound and centering. (k=0\) is explicitly excluded in the universal
assertion, so empty slope-index quantification is not the proposed refutation.
Empty model classes, including possible dimension/moment/balance incompatibilities,
still contribute top and may determine failure of the limit. No integrals,
logarithms, negative-root inputs, `toReal`, truncated subtraction, or unspecified
partial-function values occur.
