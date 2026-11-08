# Blind reading of P009a T1–T5

This file was written and saved before opening `claims.json` or `record.json`.
The sources inspected were the five docstrings and statements in
`SAP/P009a/Challenge/Part1.lean`, every source declaration appearing in their
`closure.json` entries, and the generated proof declarations printed in
`scratch/closure-print.txt`. No canonical claim or architect decision was used.

The following mathematical notation explicitly expands the common SAP
definitions. Each target below uses this notation, not an uninterpreted SAP
predicate.

* An experiment of size (n\in\mathbb N) consists of a probability mass
  (p:\{0,1\}^n\to\mathbb R), with (p(z)\ge0) and
  (\sum_z p(z)=1), and arbitrary real functions (y_i(z)), (i<n).
  Boolean `true` has real value 1, and `false` value 0. Write
  (E_p f=\sum_zp(z)f(z)), (P_p(A)=\sum_zp(z)1_A(z)),
  (\operatorname{Cov}_p(f,g)=\sum_zp(z)(f(z)-E_pf)(g(z)-E_pg)),
  and (\operatorname{Var}_p f=\operatorname{Cov}_p(f,f)).
  The conditional mean is (E_p[1_A f]/P_p(A)).
* Put (p_{ib}=P_p(Z_i=b)), and let (z^{i\leftarrow b}) replace the
  (i)-th coordinate of (z) by (b). The forced response is
  (y_i(b;z)=y_i(z^{i\leftarrow b})), the individual contrast is
  (\tau_i(z)=y_i(1;z)-y_i(0;z)), the assignment average is
  (n^{-1}\sum_i\tau_i(z)), and its expectation is (\theta).
  The distributional contrast is
  (n^{-1}\sum_i(E_p[y_i\mid Z_i=1]-E_p[y_i\mid Z_i=0])).
* Write (H_b(z)=n^{-1}\sum_i1_{\{z_i=b\}}y_i(z)/p_{ib}),
  (N_b(z)=\sum_i1_{\{z_i=b\}}/p_{ib}), and (H=H_1-H_0).
  No-spillovers means that, for every (i,z,z'), (z_i=z'_i) implies
  (y_i(z)=y_i(z')).
* Write (I_{ij}=1) if (i=j) or if there exist two cube assignments differing
  only in coordinate (i) with unequal responses for unit (j); otherwise
  (I_{ij}=0). This comparison is on the full cube, including zero-mass
  assignments. Write (D_{ij}=1) if some \(\ell\) has
  (I_{\ell i}=I_{\ell j}=1), and zero otherwise. Put
  (d_i=\sum_jD_{ij}), (d=n^{-1}\sum_i d_i),
  (d_{\max}=\sup_i d_i), (d_{\rm rms}=\sqrt{n^{-1}\sum_i d_i^2}),
  and (\rho=\sup_{\sum_iv_i^2=1}\sum_{ij}v_iD_{ij}v_j).
* Independent Bernoulli design means (0<p_{i1}<1) for every (i), and,
  for every (z), (p(z)=\prod_i p_{i1}^{z_i}(1-p_{i1})^{1-z_i}).
  Regularity with real parameters (k,q,s) means (k>0,q\ge2,s\ge1),
  (k^{-1}\le p_{i1}\le1-k^{-1}), (E_p|y_i|^q\le k^q), and
  (E_p|y_i(b;Z)|^s\le k^s), for all indicated units and both arms.
* Put
  (V_B(z)=n^{-2}\sum_i[1_{\{z_i=1\}}y_i(z)^2/p_{i1}^2+
  1_{\{z_i=0\}}y_i(z)^2/p_{i0}^2]).
  The four estimates (V_a), (a=0,1,2,3), are (V_B,dV_B,d_{\max}V_B,\rho V_B),
  in that order. Also put (M=n^{-1}\sum_i(E_p\tau_i)^2),
  (v_i=\operatorname{Var}_p(1_{\{Z_i=1\}}y_i/p_{i1}-
  1_{\{Z_i=0\}}y_i/p_{i0})), and
  \(\sigma_v=\sqrt{n^{-1}\sum_i(v_i-n^{-1}\sum_jv_j)^2}\).
* An experiment sequence has sizes (N_t>0), tending to infinity as
  (t\to\infty), and one experiment of that size at each (t\in\mathbb N).
  Sequence regularity uses the same (k,q,s) at every (t). Sparse dependence
  means (d_t/N_t\to0). A random sequence (X_t) converges to zero in
  probability here if, for every real (\varepsilon>0),
  (P_t(\varepsilon<|X_t|)\to0). A scalar sequence has an eventual positive
  lower bound if some (c>0) satisfies (c\le a_t) for all sufficiently large (t).
  A function (f_t) vanishes relative to (g_t) if (f_t/g_t\to0).
* The conservativeness predicate for (V_a) means that there exists a function
  (L:\mathbb R\to\mathbb R) such that, for every (\varepsilon>0),
  (P_t((N_t/d_t)(V_a-\operatorname{Var}_tH_t)\le-\varepsilon)\to L(\varepsilon)),
  and (L(\varepsilon)\to0) as (\varepsilon\downarrow0). This is an iterated
  limit with existence of every positive-cutoff inner limit.
  The interval predicate is exactly
  \(|T-\theta|\le\sqrt{\widehat V/\alpha}\).

## SAP.P009a.T1

The theorem has no external data or hypotheses. It asserts the following
conjunction for the explicitly fixed sequence (N_t=t+1), uniform mass
(2^{-N_t}), and responses (y_0(z)=z_0), (y_i(z)=0) for (i>0).

For every pair of real orders (q\ge2,s\ge1), this sequence has regularity
with (k=2). For every (t,i,z), the outcomes lie in \([0,1]\); every
treatment marginal in either arm is (1/2). For every (t), the design is
independent Bernoulli, there are no spillovers, and, for every (i,j),
(I_{ij}=D_{ij}=1_{\{i=j\}}). Thus (d=d_{\max}=d_{\rm rms}=\rho=1),
and (d/N_t\to0).

Writing (n=N_t), for every (t),

\[
\theta=\text{distributional contrast}=M=1/n,\qquad
E_pH=1/n,\quad \operatorname{Var}_pH=1/n^2,\quad E_pV_B=2/n^2>1/n^2.
\]

For every cube assignment (z), (H(z)=2z_0/n), (V_B(z)=4z_0/n^2), and
all four estimates agree. For every (i), (v_i=1) when (i=0), and zero
otherwise; \(\sigma_v^2=(n-1)/n^2\).

All four estimates satisfy the iterated-limit conservativeness definition.
For every (t,a,z), the scaled error is

\[
A_{a,t}(z)=(n/d)(V_a(z)-\operatorname{Var}H)
=(4z_0-1)/n=\begin{cases}3/n&z_0=1,\\-1/n&z_0=0.\end{cases}
\]

For every (t,a), each of these two values has probability (1/2). For every
real (\varepsilon>0), if (1/\varepsilon<n), then, for every (a),
(P(A_{a,t}\le-\varepsilon)=0). The centered error
(C_t=n(V_B-\operatorname{Var}H)-M=(4z_0-2)/n) has values (2/n,-2/n),
each with probability (1/2), and converges to zero in probability.

Both \(\sigma_v^2\) and \(\sigma_v\) tend to zero. For every (t),
(d/d_{\rm rms}=1) and
(d_{\max}/(\sqrt n\sqrt d)=\rho/(\sqrt n\sqrt d)=1/\sqrt n).
The last two ratios tend to zero, and \(\sigma_v/(d/d_{\rm rms})\to0\).
The sequence (M_t) has no eventual positive lower bound.

For every (t), then every real (0<\alpha<1), then every (a<4), and every
cube assignment (z): if (z_0=0), (H=V_a=0), both endpoints are zero,
and the interval misses \(\theta\); if (z_0=1),
((H-\theta)^2=1/n^2\le V_a/\alpha) and the interval covers. Consequently,
for every such (t,\alpha,a), coverage is exactly (1/2). For every
(t,0<\eta<1,a), (P(V_a<(1-\eta)\operatorname{Var}H)=1/2).
In particular, coverage at (\alpha=1/20) is (1/2<1-1/20).
Finally, for every (t),
(n(E_pV_B-\operatorname{Var}H)=1/n) and
((n/d)\operatorname{Var}H=1/n); both sequences tend to zero.

Junk-value audit: all sizes (n=t+1), arm probabilities, graph divisors,
and square-root divisors here are strictly positive. The conditional means
are conditioned on probability (1/2). Real division has (x/0=0), but
that case is never used. Square roots have nonnegative arguments, including
zero for the degenerate plug-in interval; this is the intended point interval,
not an undefined standard error. All powers of absolute outcomes have positive
real orders; (0^r=0) for these orders. The graph suprema range over finite
nonempty sets, and the Rayleigh supremum ranges over a nonempty bounded unit
sphere. Thus the real `sSup` empty/unbounded defaults do not contribute.
All expectations are finite sums. There are no Bochner integrals, logarithms,
infinite `toReal` values, natural truncated subtractions, or partial-function
defaults in this target. Natural indices and sizes are cast exactly to reals.

The docstring describes these as a counterexample to a printed implication
from variance conservativeness to conservative plug-in coverage. Assessing
whether that implication has additional printed hypotheses is deferred.

## SAP.P009a.T2

This is a conjunction of five general assertions and a fixed counterexample.
The order of the general quantifiers matters.

First, universally choose a family of types \(\Omega_t\), measurable spaces,
probability measures (P_t), real functions (T_t,\widehat V_t), and real
sequences \(\theta_t,V_t,\delta_t\). Assume, for every (t): (T_t,T_t^2)
are integrable; (T_t,\widehat V_t) are measurable;
(\int T_t\,dP_t=\theta_t);
(V_t=\int(T_t-\theta_t)^2\,dP_t>0);
(\widehat V_t(\omega)\ge0) for every (\omega); and \(\delta_t>0\).
Universally choose a real (0<\alpha<1). The following three statements hold:

1. For every (t\in\mathbb N) and real (0<\eta<1),
   \[
   P_t(|T_t-\theta_t|>\sqrt{\widehat V_t/\alpha})
   \le P_t(\widehat V_t<(1-\eta)V_t)+\alpha/(1-\eta).
   \]
2. If, for every real (0<\eta<1),
   (P_t(\widehat V_t<(1-\eta)V_t)\to0), then
   \(\liminf_tP_t(|T_t-\theta_t|\le\sqrt{\widehat V_t/\alpha})\ge1-\alpha\).
3. If, for every real (\varepsilon>0),
   (P_t(((t+1)/\delta_t)(\widehat V_t-V_t)\le-\varepsilon)\to0),
   and there exist (c>0,t_0) such that
   (c\le((t+1)/\delta_t)V_t) for every (t\ge t_0), then the relative-tail
   limit in item 2 holds for every (0<\eta<1).

Second, for all reals (a,V,\widehat V,\eta,c), if (a>0,\eta>0,c\le aV)
and \(\widehat V<(1-\eta)V\), then
\(a(\widehat V-V)\le-\eta c\). Neither (c>0) nor (V>0) is required
for this elementary inclusion.

Third, for every experiment sequence (S), real (k,q,s,\alpha), uniform
regularity (k,q,s), independent Bernoulli design at every index, and every
family \(\widehat V_t\) of everywhere nonnegative real statistics, assume
(0<\alpha<1), the iterated-limit conservativeness predicate, and an eventual
positive lower bound on \((N_t/d_t)\operatorname{Var}_tH_t\). Then all
fixed relative underestimation probabilities tend to zero, and the liminf
coverage of the interval centered at (H_t) for \(\theta_t\) is at least
(1-\alpha). Sparse dependence is not a hypothesis of this implication.

Fourth, for every (n>0), every experiment (E), and all real (k,q,s),
regularity and independent Bernoulli design imply (E_pH=\theta).

Fifth, choose any family of measurable spaces and probability measures,
any real functions (e_t:\Omega_t\to\mathbb R), and any
(L:\mathbb R\to\mathbb R). If, for every \(\varepsilon>0\),
(P_t(e_t\le-\varepsilon)\to L(\varepsilon)), and
(L(\varepsilon)\to0) as \(\varepsilon\downarrow0\), then every one of
those positive-cutoff probabilities tends to zero. No measurability assumption
on (e_t) is present in this auxiliary assertion: Lean evaluates the measure
of the sublevel set using its total measure function even for arbitrary sets.

Finally, the explicitly fixed uniform-cube sequence of T1, with (n=t+1),
(y_0=z_0,y_i=0) for (i>0), has regularity (2,4,1), independent
Bernoulli design, no spillovers, positive variance, nonnegative (V_B),
(E_pH=\theta), and \(\operatorname{Var}H<E_pV_B\) at every index.
Its coverage at \(\alpha=1/20\) is (1/2); it has iterated-limit variance
conservativeness and (C_t\to0) in probability. The normalized expected bias
and normalized true variance both equal (1/n\to0), and
\(1/2<1-1/20\).

Junk-value audit: general real divisions have nonzero denominators because
\(\delta_t>0,\alpha>0,1-\eta>0\). The experiment implication has
(N_t>0,d_t\ge1) from the diagonal included in (D), and positive arm
probabilities from regularity/Bernoulli design. The generic (V_t>0) is
explicit; the experiment implication only requires positivity eventually.
The square-root argument is nonnegative by \(\widehat V\ge0\). Real
Bochner integrals otherwise default to zero when not integrable, but (T,T^2)
are integrable and \(\theta\) is their actual mean, so the variance integral
is integrable too. Event measures are at most one, making every `toReal`
finite; the liminf is of a bounded probability sequence in a nontrivial
`atTop` filter. Thus the real-order empty/unbounded defaults cannot affect
coverage. The unmeasurable-sublevel possibility in the fifth assertion does
not produce a witness; it merely states a monotonicity consequence for outer
measures too. No logarithm, truncated subtraction, graph supremum, negative
real-power base, or partial-function default affects this target.

The docstring describes a corrected coverage result and specifically states
the normalized-variance floor. Whether its assumptions match the canonical
correction is deferred.

## SAP.P009a.T3

There exist three size-two experiments (E,F,G), simultaneously satisfying
all of the following. In the descriptions below (z_0,z_1\in\{0,1\}).

The designs of (E,G) assign mass
\((1/4)^{z_0}(3/4)^{1-z_0}(3/4)^{z_1}(1/4)^{1-z_1}\), so the two
coordinates are independent, with marginals (1/4,3/4). Their responses are

\[
(y^E_0,y^E_1)=(z_1,-z_0),\qquad
(y^G_0,y^G_1)=(1,1-z_0).
\]

The design of (F) places mass (1/4) on \((1,0)\), mass (3/4) on
\((0,1)\), and zero elsewhere; both responses are constantly one, on the
entire cube. All three experiments have regularity (k=4), for every pair
of real orders (q\ge2,s\ge1), and all their absolute responses are at
most one on the full cube. Independent Bernoulli design is asserted for
(E,G), not (F).

Put (B=z_0z_1). In (E), the treated-arm responses
\(X_i=1_{\{Z_i=1\}}y_i\) are (X_0=B,X_1=-B), and
(H_1=(4/3)B), pointwise. The probabilities of (B=1,0) are
(3/16,13/16), respectively, and \(\operatorname{Var}B=39/256\).
For all (i,j<2), \(\operatorname{Cov}(X_i,X_j)\) is (39/256)
on the diagonal and \(-39/256\) off it. Consequently
(\operatorname{Var}H_1=13/48>0), the signed double covariance sum is
zero, and

\[
\operatorname{Var}H_1>(4^2/2^2)\sum_{ij}\operatorname{Cov}(X_i,X_j).
\]

In (F), \(Z_0+Z_1=1\) with probability one. The treated estimated-size
ratio \(N_1/2\) equals (2) with probability (1/4), and (2/3) with
probability (3/4); its variance is (1/3>0). The signed sum
\(\sum_{ij}\operatorname{Cov}(Z_i,Z_j)=0\), and the corresponding
upper-bound replacement inequality fails strictly with factor \(4^2/2^2\).
This support statement is almost sure, not an assertion on zero-mass cube
assignments.

In (G), put \(A_i=1_{\{Z_i=1\}}y_i^2\) and
(W=\sum_iA_i/p_{i1}^2\). Pointwise, (A_0=z_0),
(A_1=z_1(1-z_0)), and (W=16A_0+(16/9)A_1). Its values
(0,16/9,16) have probabilities (3/16,9/16,1/4), respectively.
Further,

\[
E_pW=5,\quad E_pW^2=592/9,\quad \operatorname{Var}W=367/9,
\quad\operatorname{Var}(A_0+A_1)=\sum_{ij}\operatorname{Cov}(A_i,A_j)=39/256.
\]

Thus \(4^4\sum_{ij}\operatorname{Cov}(A_i,A_j)=39<367/9\), the
third strict failure of replacing the positive unequal weights by their
common upper bound inside a signed sum.

Junk-value audit: the index type has two elements; arm probabilities are
(1/4,3/4) for every experiment, including (F). All displayed divisions
are therefore genuine divisions, with nonzero integer constants as well.
Expectation and covariance are finite sums, including zero masses in (F).
The forced-coordinate responses are finite and bounded on all cube points,
so no off-support undefined potential value is involved. Real powers use
absolute values and positive orders. No square roots, logarithms, `toReal`,
order suprema, asymptotic limsup/liminf, truncated subtraction, or partial
function defaults are used. Naturals (0,1,2\) are legitimate finite indices
or exact real casts, with generated proofs of their bounds.

The docstring says these disprove particular intermediate signed-covariance
weighting steps, while the final lemma rates stand. Determining the printed
conditions for each step is deferred.

## SAP.P009a.T4

This is a conjunction of three universally quantified results.

First, for any measurable space \(\Omega\), probability measure (P),
finite index type (U), real functions \(X_i\) with \(X_i\in L^2(P)\),
weights (w_i\in\mathbb R), and (K\in\mathbb R), assume for every (i)
(0<w_i\le K\). Then

\[
\operatorname{Var}_P\Big(\sum_iw_iX_i\Big)
=\sum_{ij}w_iw_j\operatorname{Cov}_P(X_i,X_j)
\le K^2\sum_{ij}|\operatorname{Cov}_P(X_i,X_j)|.
\]

Here the variance and covariance are Mathlib's probability definitions. Under
the (L^2) hypotheses these are the ordinary integrals of centered squares
and centered products; (L^2) includes almost-everywhere strong measurability.

Second, for every natural size (n) (not required positive in this clause),
experiment (E), real (k>0), extended order
\(q\in\mathbb R\cup\{+\infty\}\), natural exponent (a\in\{1,2\}\)
with (2a\le q), and moment bounds for every observed response, the
following holds for every pair of units (i,j<n) and arm (b\in\{0,1\}):

\[
|\operatorname{Cov}_p(1_{\{Z_i=b\}}y_i^a,
1_{\{Z_j=b\}}y_j^a)|\le k^{2a}.
\]

For finite (q), the moment bound is (E_p|y_i|^q\le k^q). For
(q=+\infty), it means \(|y_i(z)|\le k\) for every point of positive
mass. This second result has no treatment-positivity, potential-moment,
or Bernoulli hypothesis.

Third, universally choose (n>0,E,k,q,s), with extended orders (q,s),
and assume (k>0,q\ge2,s\ge1), treatment marginals between
(k^{-1}) and (1-k^{-1}), observed order bound (k,q), and forced-response
order bound (k,s), using the preceding finite/infinite interpretation.
Put \(\gamma=(q-2)/q\) for finite (q), and \(\gamma=1\) for infinite (q).
For all units define the masked assignment
\(R_i(z)_j=z_j\) if (I_{ji}=1), and zero otherwise. For any finite
random variables (A,B), write

\[
\alpha(A,B)=\sup_{S,T}|P(A\in S,B\in T)-P(A\in S)P(B\in T)|,
\quad m(x,\gamma)=\begin{cases}0&x=0,\\x^\gamma&x\ne0.\end{cases}
\]

The supremum ranges over arbitrary subsets of their codomains. Put
\(R=\sum_{ij}(1-D_{ij})m(\alpha(R_i,R_j),\gamma)\),
\(e=R/n\), \(A=\sum_{ij}\alpha(Z_i,Z_j)\), and
\(A_0=\sum_{ij}(1-D_{ij})\alpha(Z_i,Z_j)\).
All sums here include the diagonal.

For each arm (b), put \(X_i=1_{\{Z_i=b\}}y_i\),
\(S_1=\sum_{ij}|\operatorname{Cov}(X_i,X_j)|\), and
\(S_{1D}=\sum_{ij}D_{ij}|\operatorname{Cov}(X_i,X_j)|\).
The asserted mean chains consist of all of these clauses:

* \(\operatorname{Var}H_b\le(k^2/n^2)S_1\).
* If the design is independent Bernoulli, every
  \((1-D_{ij})\operatorname{Cov}(X_i,X_j)=0\),
  \(S_1=S_{1D}\), and \((k^2/n^2)S_{1D}\le k^4d/n\).
* For every pair with (D_{ij}=0),
  \(|\operatorname{Cov}(X_i,X_j)|\le10k^2m(\alpha(R_i,R_j),\gamma)\).
  For every pair with (D_{ij}=1), its absolute covariance is at most (k^2).
* \((k^2/n^2)S_1\le k^4d/n+10k^4R/n^2\), and the last expression
  equals \(k^4d/n+10k^4e/n\).

For each arm let \(C_i=1_{\{Z_i=b\}}\) and
\(S_C=\sum_{ij}|\operatorname{Cov}(C_i,C_j)|\).
The count chains assert every term in

\[
\operatorname{Var}(N_b/n)\le(k^2/n^2)S_C\le(k^2/n^2)A
\le k^2d/n+(k^2/n^2)A_0\le k^2d/n+k^2e/n,
\]

and, for every (i,j), \(|\operatorname{Cov}(C_i,C_j)|\le\alpha(Z_i,Z_j)\).

If also (q\ge4) and the design is independent Bernoulli, set
\(B_{bi}=1_{\{Z_i=b\}}y_i^2\),
\(W_b=\sum_iB_{bi}/p_{ib}^2\),
\(S_{2b}=\sum_{ij}|\operatorname{Cov}(B_{bi},B_{bj})|\), and
\(S_{2Db}=\sum_{ij}D_{ij}|\operatorname{Cov}(B_{bi},B_{bj})|\).
For both arms, \(\operatorname{Var}W_b\le k^4S_{2b}\), every
\((1-D_{ij})\operatorname{Cov}(B_{bi},B_{bj})=0\),
\(S_{2b}=S_{2Db}\), and \(k^4S_{2Db}\le k^8nd\).
It also asserts both comparisons

\[
\operatorname{Var}(nV_B)\le(2/n^2)\sum_{b\in\{0,1\}}\operatorname{Var}W_b
\le4k^8d/n.
\]

Junk-value audit: the first assertion permits an empty (U); it then reduces
to \(0=0\) and \(0\le0\), without invalidating its nonempty cases. A probability
space cannot be empty. The (L^2) assumptions ensure finite ordinary variance
and covariance, avoiding Bochner-integral and variance `toReal` defaults.
The second assertion permits (n=0) but quantifies over (i,j<0), so that
branch is empty and has no claimed numerical covariance. All meaningful
finite-population chains require (n>0); arm divisions are protected by
(k>0) and marginal bounds. Extended orders use `untopD 0`, but the top
branch is handled separately, so its default zero is not substituted as a
moment order or denominator. Finite (q\ge2) protects division by (q).
All real powers have nonnegative bases; the explicit convention
\(m(0,0)=0\) differs from ordinary \(0^0=1\) and is intentional in every
mixing sum. Mixing coefficients have nonempty bounded supremum sets (zero
comes from empty events, and every discrepancy is bounded), so real `sSup`
defaults do not enter. There are no logarithms, square roots, truncated
subtractions, limsup/liminf values, or partial-function defaults in the chains.

The docstring says these are corrected chains rather than a refutation of
the final rates. It also says all admissible moment orders are covered, hence
any largest admissible order when one exists. There is no formal maximum-order
existence assertion or sequence-level maximum hypothesis in this theorem.

## SAP.P009a.T5

There are no external hypotheses. For positive integers (n), put
\(m_n=\max(1,\lfloor n/2\rfloor-1)\), where the subtraction is truncated
natural subtraction, and let

\[
f_n=\frac{m_n^2+n-m_n}{n^2}.
\]

The fixed experiment sequence has size (n=t+1), independent fair Boolean
coordinates, and response (y_i(z)=z_0) for (i<m_n), zero otherwise.
It has regularity (k=3,q=2,s=1) uniformly in (t); every design is
independent Bernoulli. For every positive (n), every (i,j<n), the
full-cube interference relation is

\[
I_{ij}=1\quad\Longleftrightarrow\quad i=j\ \text{or}\ (i=0\ \text{and}\ j<m_n),
\]

and shared-cause dependence satisfies

\[
D_{ij}=1\quad\Longleftrightarrow\quad i=j\ \text{or}\ (i<m_n\ \text{and}\ j<m_n).
\]

Consequently (d/n=f_n), both for every positive (n) and at every
sequence index. The density sequence converges to (1/4), and its real
filter limsup equals (1/4>0). It is not sparse-dependent, meaning
\(d_t/N_t\not\to0\).

For every positive (n), \(f_n\ge1/4\) if and only if (n\le4\).
Equivalently, for every (t\in\mathbb N),
\(d_t/N_t\ge1/4\) if and only if (t+1\le4\). The first four densities
are (1,1/2,1/3,1/4). For every natural (r\ge3),

\[
1/4-f_{2r}=\frac{r-2}{4r^2}>0,
\]

and for every natural (r\ge2),

\[
1/4-f_{2r+1}=\frac{8r-11}{4(2r+1)^2}>0.
\]

The set of sequence indices satisfying \((1/4)N_t\le d_t\) is finite
(indeed exactly \(\{0,1,2,3\}\) by the earlier equivalence). Thus a positive
limsup need not itself be attained infinitely often. The assertion says
nothing about thresholds strictly below (1/4).

Junk-value audit: the truncated natural subtraction in (m_n) is substantive
and makes the cluster have size one for the first few (n). It is correctly
reflected by the max/floor formula, and (1\le m_n\le n\) for (n>0\).
The subtraction in the real numerator (m_n^2+n-m_n) and the parity gap
formulas is ordinary real subtraction. Although the standalone definition
sets (f_0=0) through division by zero, the theorem only uses (f_n) for
positive sizes. Every parity-gap denominator is positive under its displayed
lower bound. Every arm probability is (1/2), all expectations are finite
sums, and the order powers have nonnegative bases and positive exponents.
The density is in \([0,1]\) and converges, so its real `limsup` is neither
an empty-filter nor unbounded-sequence default. The reference unit zero is
constructed with the explicit positive-size proof; there is no out-of-range
index or default coordinate. No Bochner integral, logarithm, square root,
infinite `toReal`, or partial-function default occurs.

The docstring calls the printed claim false and specifies the limsup
selection step. Whether that is the canonical assertion itself, rather than
just a proof step for some other assertion, is deferred to the next stage.

## Closure bookkeeping

The structure constructors and field projections in the closure were read
with their structures: finite distribution (mass/nonnegativity/total mass),
finite experiment (design/outcome), and sequence (size/positive sizes/growth/
experiment). The 33 line-zero generated declarations were all printed and
read. They prove numeral-instance obligations, finite-index positivity,
positivity/normalization of uniform mass, and positivity/growth of (t+1).
They add no data-dependent assumption. Their source proofs and the printed
terms are retained in `scratch/ClosurePrint.lean` and
`scratch/closure-print.txt`.
