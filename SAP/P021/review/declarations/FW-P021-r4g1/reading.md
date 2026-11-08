# Blind reading

This file was saved before opening `claims.json`, `record.json`, `earlier.json`, or
`architect-report.md`. Sources read: `closure.json`, all three definition modules,
the definition import module, and both Challenge modules. Every unit declaration
listed in either target's closure was read. Only the two requested theorems are
being reviewed; the older `T2Statement` is not the statement of T2.

## SAP.P021.T1

Source: `SAP/P021/Challenge/Part1.lean:7–11`; statement expanded from
`SAP/P021/Defs/Part2.lean:39–65`.

### Objects, definitions, and quantifiers

For every real number B, every natural number K, and every Borel measure F on

    X = [-B,B] × ({0,…,K−1} × {false,true}),

assume F is a probability measure (F(X)=1). The interval is a subtype of the
reals with its induced topology and measurable structure; the finite factors have
their usual discrete topology and measurable structure. A state x=(y,k,s) has
`outcome x = y`. Its degree label is k. The numerical degree attached to a label
elsewhere in the package is k+1, but the numerical degree is not used by T1.

Define the following real quantities using Mathlib's real Bochner integral:

* I(x)=1 if s=true, and 0 otherwise (`sampleIndicator`).
* A_k(x)=1 if x's degree label equals k, and 0 otherwise (`degreeCell`).
* C_k(x)=A_k(x) I(x) (`sampleCell`).
* m=∫y dF (`populationMean`).
* p_k=∫A_k dF (`degreeMass`).
* q_k=∫C_k dF (`sampledMass`).
* u_k=∫A_k y dF (`degreeMoment`).
* v_k=∫C_k y dF (`sampledMoment`).
* t=∫I dF (`sampleFraction`).
* π_k=q_k/p_k (`samplingProbability`).
* b_k=u_k/p_k (`degreeMean`).
* d_k=v_k/q_k (`sampledMean`).
* h_k=q_k/t (`observedDegreeMass`).
* D={k in {0,…,K−1}: p_k>0} (`degreeSupport`, a filtered finite set).
* H={k in {0,…,K−1}: h_k>0} (`observedSupport`).

After choosing B,K,F and assuming F(X)=1, quantify over every real c and every
function f:{0,…,K−1}→ℝ. The two hypotheses are exactly:

1. For every k with p_k>0, d_k=b_k and π_k>0 (`Ignorability`). This is equality of
   conditional means, not independence or equality of conditional distributions.
2. For every k with p_k>0, π_k=c f(k) (`KnownSampling`). There is no separate sign
   assumption on c or f and no condition on unsupported labels.

The conclusion is the conjunction of ALL of the following:

1. t>0.
2. D=H.
3. c≠0.
4. For every k∈D, all five assertions hold:
   q_k>0; c f(k)>0; f(k)≠0;
   p_k=h_k t/π_k; and p_k=(t/c)(h_k/f(k)).
5. W:=∑_{k∈D} h_k/f(k) equals c/t.
6. W≠0.
7. m=(∑_{k∈D} d_k(h_k/f(k)))/W.
8. m=(∑_{k∈D} b_k(t/c)(h_k/f(k)))/
       (∑_{k∈D} (t/c)(h_k/f(k))).
9. The ratio in item 8 equals
   (∑_{k∈D} b_k(h_k/f(k)))/(∑_{k∈D} h_k/f(k)).

The source's nested `∑ k ∈ degreeSupport F` is summation over the finite set D.
There are no additional existential quantifiers or assumptions about independence,
a network, a finite population, or the sign of the profile away from D. The
docstring describes identification and the printed Bayes/cancellation identities
with sums over positive-mass degrees.

### Total operations and possible junk values

* All divisions are in ℝ, where a/0=0. Off support p_k=0 gives q_k=u_k=v_k=0;
  the conditional quantities are then assigned zero. The hypotheses and the
  conclusion's stratum formulas only use k∈D. Positive π_k on D forces q_k>0.
  Since F is a probability on finitely many strata, D is nonempty and t>0 follows.
  Thus the denominator t in h_k is positive; c≠0 and f(k)≠0 on D follow from the
  profile condition. W=c/t≠0, and the scaled denominator in items 8–9 equals 1.
  These formulas do not derive their meaning from division by zero.
* Mathlib's Bochner integral of a nonintegrable or non-a.e.-strongly-measurable
  real function is zero. The definitions by themselves allow arbitrary measures,
  so this convention exists. Under this theorem's probability hypothesis all
  displayed integrands are Borel measurable and bounded, hence integrable. The
  outcome lies in a compact interval and all indicator functions are measurable.
* A finite sum over an empty set is zero. K=0 makes X empty. B<0 also makes X
  empty. Neither permits a probability measure, so neither creates a countercase
  under the hypotheses. B=0 is allowed and represents an outcome constantly zero.
  D cannot be empty for a probability measure on the finite degree labels.
* There is no truncated subtraction: −B is real negation. There are no `log`,
  `sqrt`, `rpow`, `toReal`, extrema, limsup/liminf, partial-function defaults, or
  integer casts in the statement's closure. The natural-number degree convention
  k+1 is not used by this target. No infinity is cast to a real number.

## SAP.P021.T2

Source: `SAP/P021/Challenge/Part1.lean:13–20`; statement expanded from
`SAP/P021/Defs/WholeW1.lean:11–39`.

### Shared objects and definitions

The state X, F, y, k, I, A_k, C_k, p_k, q_k, u_k, v_k, m, π_k, b_k, and d_k have
exactly the integral definitions given in the T1 section. The definitions
`sampleFraction`, `observedDegreeMass`, and the two supports do not occur in T2's
closure, although the sampling fraction ∫I dF is useful for interpreting it.

Here the numerical degree is explicitly δ(k)=(k:ℝ)+1 (`degreeValue`), so all
degrees are in {1,…,K}. A population of size n is an indexed list
z:Fin n→X, with repetitions of a state allowed. For any real test function g,

    A(z,g) = (∑_{j=0}^{n−1} g(z(j)))/(n:ℝ)

is `empiricalAverage`. The finite sample J(z) (`sampleSet`) is precisely the
subset of population indices j for which the Boolean mark of z(j) is true.
The estimator (`vhEstimator`) is

    V(z) = [∑_{j∈J(z)} y(z(j))/δ(k(z(j)))] /
           [∑_{j∈J(z)} 1/δ(k(z(j)))].

This is an index sample, so two population units with identical states are
counted separately. The joint state includes the realized sample membership.

### Random assertion: quantifiers, hypotheses, conclusion

The first conjunct quantifies, in order, over:

1. An arbitrary type Ω (at the declaration's universe level) and a measurable
   space structure on Ω.
2. B∈ℝ, K∈ℕ, and a measure P on Ω, assuming P(Ω)=1, B≥0, and K>0.
3. A probability measure F on X.
4. A function N:ℕ→ℕ, assuming N(r)>0 for every natural stage r.
5. A family z with z(r,ω):Fin(N(r))→X, assuming that for each r and each valid
   population index j, ω↦z(r,ω,j) is measurable.
6. Weak convergence in probability of realized joint empirical laws, meaning
   exactly: for EVERY continuous g:X→ℝ, A(z(r,·),g) converges in P-measure to the
   constant ∫g dF as r→∞.
7. c,a∈ℝ, assuming a≠0, `Ignorability F`, and
   `KnownSampling F c (fun k => a*δ(k))`.

The last two hypotheses unfold to: for every k with p_k>0,

    d_k=b_k,    π_k>0,    π_k=c a δ(k).

The conclusion is that V(z(r,·)) converges in P-measure to the constant m as
r→∞. For real variables on a probability space this is convergence in
probability: for every ε>0, P{|V(z(r,ω))−m|≥ε}→0. At the Mathlib level,
`TendstoInMeasure` quantifies over ε∈ℝ≥0∞ with ε>0 and requires convergence to
zero of P{ω: ε≤edist(V(z(r,ω)),m)} along the natural-number `atTop` filter.
This has the stated real-probability interpretation.

`EmpiricalWeakInProbability` imposes this scalar convergence for each continuous
test function separately; it does not require a single common exceptional set
for all test functions. Ω's measure and F are fixed, not stage dependent. There
is no hypothesis that N(r)→∞, that population units are independent, or that
samples are nonempty at every stage.

### Deterministic assertion: quantifiers, hypotheses, conclusion

Independently of the first conjunct, for all B∈ℝ,K∈ℕ with B≥0,K>0; every
probability F on X; every N:ℕ→ℕ with each N(r)>0; and every deterministic family
z(r):Fin(N(r))→X, assume

    for every continuous g:X→ℝ,
    A(z(r),g) → ∫g dF as r→∞.

Then for every c,a∈ℝ with a≠0, mean ignorability with strictly positive sampling
on every positive-mass degree, and π_k=c a δ(k) on those degrees,

    V(z(r)) → m as r→∞.

Both appearances of ordinary convergence are Mathlib `Filter.Tendsto` from
`atTop` on ℕ to the real neighborhood filter of the displayed limit. There is
no assumption about nonempty samples at finite stages in this conjunct either.
The docstring explicitly states the common bounded support, empirical weak
convergence, both modes of convergence, and the zero extension at empty samples.

### Total operations and possible junk values

* The degree cast is the exact cast ℕ→ℝ of k.val, followed by addition of 1.
  Thus δ(k)>0; neither reciprocal degree nor outcome divided by degree ever
  divides by zero.
* `empiricalAverage` is zero for N=0 by empty summation and real 0/0=0, but each
  N(r)>0 is an explicit hypothesis. The cast N(r):ℝ is positive.
* The estimator's denominator is positive exactly when J(z) is nonempty.
  If J(z) is empty, both sums are zero and real division assigns V(z)=0.
  This convention is explicitly documented and is permitted at finite stages.
  Under F's ignorability and probability hypotheses, ∫I dF>0. The continuous
  degree/mark test function I/δ has strictly positive F integral. Empirical weak
  convergence therefore makes the estimator's normalized denominator converge
  to a positive number. Deterministically the samples are consequently
  eventually nonempty; randomly the probability of an empty sample tends to
  zero. A value assigned on empty samples cannot control the asymptotic result.
* The conditional ratios π_k,b_k,d_k use the same real-zero convention as T1.
  Their conditions apply only when p_k>0; π_k>0 then forces q_k>0. The joint
  law has at least one such stratum, so c a>0 and c≠0 follow. No unsupported
  stratum contributes spurious conditioning information.
* All F integrals of outcome, indicators, their products, and continuous test
  functions are genuine integrals: X is compact, the functions are measurable
  and bounded, and F is a probability. Thus the nonintegrable-integral default
  cannot affect this theorem. Each random coordinate is measurable; finite
  sums and total real division give measurable estimator statistics.
* B=0 is legitimate, but B<0 and K=0 are explicitly excluded. P cannot be a
  probability measure on an empty Ω. Finite samples can be empty, as above;
  population index types cannot. There are no other partial-function defaults,
  natural truncated subtractions, `log`, `sqrt`, `rpow`, `toReal` of infinity,
  sInf/sSup, or limsup/liminf operations. No unbounded-sequence convention is
  used by `Tendsto`; it is genuine filter convergence.
