# Blind reading

This file was saved before opening either `claims.json` or `record.json`.
The five Challenge docstrings and the complete closures in `closure.json` were
read. Source definitions were read with line numbers. All 114 distinct generated
`_proof_` declarations were also printed and read (`scratch/PrintClosure.lean`,
`scratch/PrintClosure.out`); 113 certify particular natural numerals are at least
two, and the remaining one supplies the ordinary continuous real scalar action.
They introduce no statistical assumptions, alternative operations, or conclusions.
In particular a dependency named after another target does not import that
target's statement: the shared auxiliary numeral proofs have only their printed
types.

The mathematical abbreviations used below are entirely expanded here:

* Write \(G_\theta\) for Mathlib's `gaussianReal θ 1`: the Borel measure on
  \(\mathbb R\) with density
  \((\sqrt{2\pi})^{-1}\exp(-(x-\theta)^2/2)\) relative to Lebesgue measure.
  `normalCDF` is \(\Phi(x)=G_0(( -\infty,x])\), using real-valued measure
  `(G₀ (Iic x)).toReal`. `normalQuantile p` is
  \(\inf\{x\in\mathbb R:p\leq\Phi(x)\}\). `normalCritical` is this infimum
  at \(p=39/40\); call it \(z\). `normalDensity` is
  \(\phi(x)=(\sqrt{2\pi})^{-1}e^{-x^2/2}\).
  `normalPower` is the function
  \(P(a)=\Phi(a-z)+\Phi(-a-z)\) on all real \(a\).
* For an array \(y:\mathrm{Fin}(n)\to\mathbb R\), `sampleMean` is
  \(\bar y=n^{-1}\sum_{i=0}^{n-1}y_i\); `sampleVariance` is
  \(v(y)=\sum_i(y_i-\bar y)^2/( (n:\mathbb R)-1)\); and `sampleSD` is
  \(s(y)=\sqrt{v(y)}\). The subtraction in the denominator is real subtraction.
* The population `variance Y μ` is Mathlib's
  \((\int^-\omega\,\|Y(\omega)-\int Y\,d\mu\|_e^2\,d\mu).\mathrm{toReal}\).
  For the bounded measurable binary variables below this is exactly the usual
  second central moment. `binaryPopulationVariance p` is the polynomial
  \(p(1-p)\). `binaryStudySE` is the fixed positive rational
  \(s_* =154987506828555/10^{16}=0.0154987506828555\).
* `caliperCutoff` is \(c=49/25\). For any real function \(f\) and real \(h\),
  `caliperAbove` is the oriented Lebesgue interval integral
  \(A_f(h)=\int_c^{c+h} f(x)\,dx\), `caliperBelow` is
  \(B_f(h)=\int_{c-h}^c f(x)\,dx\), and `caliperProbability` is
  \(p_f(h)=A_f(h)/(A_f(h)+B_f(h))\).
* `binomialTail n k p` is the finite real sum
  \(Q(n,k,p)=\sum_{j\in\{k,\ldots,n\}}{n\choose j}p^j(1-p)^{n-j}\).
  The index set is Mathlib's natural-number `Finset.Icc k n`, the exponent
  \(n-j\) is natural subtraction, and the binomial coefficient is cast to reals.
* `caliperDataLaw M f` is the finite product measure on
  \(\mathbb R^{\mathrm{Fin}(M)}\) whose marginal measures are
  \(\lambda_f=\mathrm{volume.withDensity}(x\mapsto\mathrm{ENNReal.ofReal}(f(x)))\).
  Thus the coordinates are independent and identically distributed whenever
  \(\lambda_f\) is a probability measure; it is not a law allowing dependent
  repeated draws. For an array \(X\), `caliperCount h X` is the number \(N_h(X)\)
  of indices with \(X_i\in[c-h,c+h]\), and `caliperSuccesses h X` is the number
  \(K_h(X)\) with \(X_i\in[c,c+h]\). Both are natural numbers.
* `linearCaliperDensity` is \(f_1(x)=x/8\) on the closed interval \([0,4]\),
  and zero outside it. `powerCaliperDensity m` is
  \(f_m(x)=(m+1)x^m/4^{m+1}\) on that interval, zero elsewhere, for natural \(m\).
* `foldedNormalCDF θ x` is \(F_\theta(x)=\Phi(x-\theta)-\Phi(-x-\theta)\).
  `foldedCaliperProbability θ h` is
  \(p^G_\theta(h)=[F_\theta(c+h)-F_\theta(c)]/
  [F_\theta(c+h)-F_\theta(c-h)]\).
  `intervalCoverage μ T θ H` is the real-valued measure
  \(\mu\{\omega:\theta\in[T(\omega)-H,T(\omega)+H]\}\).
* `clusterCountRatio L R` is
  \(\rho(L,R)=|L\cup R|/(|L|+|R|)\), with all cardinalities cast to reals.
  `funnelPoint β se s₀` is the pair \((|\beta|/s_0,\mathrm{se}/s_0)\).

## SAP.P033.T6

Location: `SAP/P033/Challenge/Part1.lean:54–56`; its entire statement is
`T6Statement`, `SAP/P033/Defs/Part3.lean:44–80`. Its docstring describes binary
standard-deviation bounds, power for the stored SE, roots, sample-size bounds,
table arithmetic, and cancellation of a common standardization.

There are no outer hypotheses: the theorem is a conjunction of the following
claims, with each displayed universal quantifier local to its clause.

1. For every type \(\Omega\), measurable-space structure, probability measure
   \(\mu\), real function \(Y\), and real \(p\), in that order, if \(Y\) is
   measurable, \(Y\in\{0,1\}\) almost surely, and
   \(\mu\{Y=1\}=p\), then
   \(\operatorname{Var}_\mu Y=p(1-p)=1/4-(p-1/2)^2\),
   \(\operatorname{Var}_\mu Y\leq1/4\), and
   \(\sqrt{\operatorname{Var}_\mu Y}\leq1/2\). The probability identity implies
   \(p\in[0,1]\), although this is not separately assumed.
2. For every natural \(N\geq2\), then every binary real array of length \(N\),
   \(v(Y)=N\bar Y(1-\bar Y)/(N-1)\),
   \(v(Y)\leq N/[4(N-1)]\), and
   \(s(Y)/10\leq\sqrt{N/(N-1)}/20\).
3. For every real \(p\in[0,1]\), \(\sqrt{p(1-p)}/10\leq1/20\).
   Separately, for every two real probabilities \(p,q\in[0,1]\),
   \(|p-q|\leq1\).
4. \(1<1229/500\), and \(P(0)=1/20\). For every real \(a>0\),
   \(P\) has derivative \(\phi(a-z)-\phi(a+z)>0\) at \(a\), and
   \(P(a)<\Phi(a-z)+1/40\). Also \(P\) is strictly increasing on \([0,\infty)\).
5. For every real \(\tau\) with \(|\tau|\leq1/20\),
   \(P(|\tau|/s_*)\leq P(1/(20s_*))\), and \(P(|\tau|/s_*)<19/20\).
   The maximum displayed power is strictly between \(8972619/10^7\) and
   \(8972620/10^7\).
6. There exist three real numbers \(\sigma_{60},\sigma_{80},\sigma_{95}\)
   simultaneously such that \(P(\sigma_{60}/(10s_*))=3/5\),
   \(P(\sigma_{80}/(10s_*))=4/5\), and
   \(P(\sigma_{95}/(10s_*))=19/20\). Their respective strict intervals are
   \((3430295,3430296)/10^7\), \((4342101,4342102)/10^7\), and
   \((5587016,5587017)/10^7\); additionally \(\sigma_{95}>1/2\).
7. For every natural \(N\geq31731\),
   \(\sqrt{N/(N-1)}/2\leq5000079/10^7\), and
   \(P(\sqrt{N/(N-1)}/(20s_*))\leq8972711/10^7<19/20\), where the
   last strict inequality in the source is directly asserted of the power.
8. \(((15/4)-1)/36=11/144\), \(((11/4)-1)/10=7/40\). For every real
   \(\beta,\mathrm{se},\sigma\), with \(\sigma>0\) and \(\mathrm{se}>0\),
   \((|\beta|/\sigma)/(\mathrm{se}/\sigma)=|\beta|/\mathrm{se}\).

Junk-value audit: real division defines \(x/0=0\); the stored SE is nonzero,
all fixed rational denominators are nonzero, \(N\geq2\) or \(N\geq31731\)
protects every variable sample denominator, and positivity protects the final
ratio. `sampleMean` and `sampleVariance` at lengths zero or one would give zero,
but these lengths are excluded. `Real.sqrt` returns zero at negative arguments;
all arguments used here are nonnegative. Population expectation and variance
could otherwise use the nonintegrable-integral value zero and `toReal ∞ = 0`;
bounded measurable binary variables under a probability measure have finite
moments, so neither fallback can apply. The normal quantile uses conditional
real completeness: empty or unbounded-below sets have infimum zero. Its only
input here is 39/40, whose Gaussian superlevel set is nonempty and bounded below.
No logarithms, real powers, partial functions, or asymptotic limsup/liminf occur.
An empty probability-space type cannot support an `IsProbabilityMeasure`.

## SAP.P033.T7

Location: `SAP/P033/Challenge/Part1.lean:58–60`; its statement is
`T7CoreStatement` (`Defs/Part3.lean:83–133`) conjoined with
`T7Statement`'s additional clauses (`Defs/Part4.lean:159–165`). The docstring calls
the populations selection-free and describes their unequal caliper sides and
rejection tails. The theorem has no outer hypotheses.

1. \(\int_0^4x/8\,dx=1\). For every real
   \(r\in\{1/10,3/20,1/5\}\), let \(h=cr\). Then \(0<h<c\), \(f_1\) is
   strictly positive at every point of \([c-h,c+h]\), and is infinitely
   differentiable on \((c-h,c+h)\). Moreover
   \(A_{f_1}(h)=(2ch+h^2)/16\), \(B_{f_1}(h)=(2ch-h^2)/16\), and
   \(p_{f_1}(h)=1/2+r/4\). Infinite differentiability is Mathlib's
   `ContDiffOn ℝ ⊤` on that open interval.
2. The three side probabilities are respectively \(21/40,43/80,11/20\).
   At \(h=c/5\), the upper and lower masses are \(26411/250000\) and
   \(21609/250000\). The three caliper endpoint pairs are
   \((441/250,539/250)\), \((833/500,1127/500)\), and
   \((196/125,294/125)\), respectively.
3. For every natural \(k\leq19\), \(Q(19,k,1/2)\leq1/20\) iff \(14\leq k\).
   For every natural \(M\geq19\), set \(\mu=\lambda_{f_1}^{\otimes M}\).
   If \(\mu\{N_{c/5}=19\}>0\), then
   \[\frac{\mu(\{N_{c/5}=19\}\cap
   \{Q(19,K_{c/5},1/2)\leq1/20\})}{\mu\{N_{c/5}=19\}}
   =Q(19,14,11/20)>1/20.\]
   The strict inequality is also a separate unconditional conjunct.
4. The exact tail values, each separately asserted, are
   \(Q(12,9,1/2)=299/4096\),
   \(Q(12,9,21/40)=336637329302285487/3355443200000000000\),
   \(Q(15,11,1/2)=1941/32768\),
   \(Q(15,11,43/80)=3589476431322242287677900507/
   35184372088832000000000000000\),
   \(Q(19,14,1/2)=2083/65536\), and
   \(Q(19,14,11/20)=50930691593528557166389/655360000000000000000000\).
5. For every natural \(m\geq1\),
   \(\int_0^4(m+1)x^m/4^{m+1}\,dx=1\). For each real \(0<h<c\), \(f_m\)
   is strictly positive on the closed caliper, infinitely differentiable on its
   interior, and
   \[p_{f_m}(h)=\frac{(c+h)^{m+1}-c^{m+1}}
                        {(c+h)^{m+1}-(c-h)^{m+1}}.\]
   Separately, for every real \(0<h<c\), the sequence \(p_{f_m}(h)\) tends
   to 1 as the natural number \(m\) tends to infinity. Its \(m=0\) term is
   included in the sequence but has no effect on the limit.
   \(p_{f_9}(49/125)=4609141/5401600\).
6. For all real \(\theta,x\), with \(x\geq0\),
   \(G_\theta\{t:|t|\leq x\}=F_\theta(x)\). For every real \(\theta\),
   \(G_\theta\{t:\theta\in[t-z,t+z]\}=19/20\).
   At \(\theta=7/2,h=49/125\), \(p^G_\theta(h)\) is in the closed interval
   \([644747758104,644747758105]/10^{12}\); its
   \(Q(19,14,\cdot)\) value is in
   \([280413461677,280413461678]/10^{12}\).
   At \(\theta=0\), the corresponding side probability is in
   \([318944499071,318944499072]/10^{12}\).
7. Additional wrapper clauses:
   \(Q(19,13,1/2)=10949/131072>1/20\),
   \(Q(19,14,1/2)<1/20\), and
   \(\lambda_{f_1}^{\otimes19}\{N_{c/5}=19\}>0\).

Junk-value audit: interval integrals use zero when the real integrand is not
integrable, but all displayed compactly supported polynomial densities and
bounded intervals are integrable. All used widths are positive and their
intervals lie strictly inside \((0,4)\), so oriented-integral signs cause no
problem. `ofReal` would truncate negative densities to zero; these densities are
nonnegative on their support. Product measures are finite probability measures,
so `μ.real` cannot turn infinite mass into zero. The conditional ratio explicitly
requires a positive conditioning probability and its wrapper supplies an actual
case. Upper/lower side ratios have strictly positive total mass; the polynomial
formula denominator is positive for \(0<h<c\), and the used folded-Gaussian
denominators are positive. `foldedNormalCDF` outside \(x\geq0\) is an algebraic
difference rather than the CDF of \(|T|\), but the CDF assertion restricts
\(x\geq0\) and the numerical windows stay positive. `Finset.Icc k n` is empty
when \(k>n\), giving tail zero; every relevant enumerated sum uses \(k\leq n\).
Within those sums natural \(n-j\) never truncates. An empty product, if \(M=0\),
is excluded in the conditional assertion. Gaussian quantile conventions are as
in T6; the only quantile input is 39/40. No unbounded infimum/supremum, limsup,
logarithm, real power, square-root problem, or partial-function fallback is used.

## SAP.P033.T8

Location: `SAP/P033/Challenge/Part1.lean:62–64`; `T8CoreStatement` is at
`Defs/Part3.lean:136–175` and `T8Statement` at `Defs/Part4.lean:168–171`.
The docstring describes conditional binomial laws, mass conditions, monotonicity,
finite-window bounds, and small-window limits for normalized densities.

The core first universally quantifies a real function \(f\), then proofs that
\(f(x)\geq0\) everywhere, \(f(x)=0\) for every \(x<0\), \(f\) is Bochner
integrable on the real line with respect to Lebesgue measure, and
\(\int_{\mathbb R} f=1\). For each such \(f\), it asserts all of the following.

1. For every real \(h\), assuming in order \(0<h\), \(h<c\), and
   \(A_f(h)+B_f(h)>0\), the following conjunction holds.
   * For every natural \(M,n\), if
     \(\mu=\lambda_f^{\otimes M}\) gives positive probability to
     \(E=\{N_h=n\}\), then for every natural \(j\leq n\),
     \(\mu(E\cap\{K_h=j\})/\mu(E)={n\choose j}p_f(h)^j
     (1-p_f(h))^{n-j}\), and for every natural \(k\leq n\),
     \(\mu(E\cap\{K_h\geq k\})/\mu(E)=Q(n,k,p_f(h))\).
   * \(p_f(h)=1/2\) iff \(A_f(h)=B_f(h)\).
   * If for every real \(0<u<h\), \(f(c+u)=f(c-u)\), then the two masses
     agree. No symmetry at endpoints is required.
   * If \(f\) is antitone on \([c-h,c+h]\), then \(A_f(h)\leq B_f(h)\),
     \(p_f(h)\leq1/2\), and for every natural \(n,k\) with \(k\leq n\),
     \(Q(n,k,p_f(h))\leq Q(n,k,1/2)\).
   * If \(f\) is monotone on that interval, the two mass, probability, and
     tail inequalities reverse.
   * For every real \(a,L\), if \(a>0\), \(f(x)\geq a\) on the entire
     closed caliper, and \(|f(x)-f(y)|\leq L|x-y|\) for every pair of
     points in it, then
     \(|A_f(h)-B_f(h)|\leq Lh^2\),
     \(A_f(h)+B_f(h)\geq2ha\),
     \(|p_f(h)-1/2|=|A_f(h)-B_f(h)|/[2(A_f(h)+B_f(h))]\), and
     \(|p_f(h)-1/2|\leq Lh/(4a)\).
2. For every natural \(n,k\), if \(k\leq n\), the real function
   \(p\mapsto Q(n,k,p)\) is monotone on \([0,1]\).
3. If \(f\) is continuous at \(c\) and \(f(c)>0\), then
   \(p_f(h)\to1/2\) as \(h\to0\) through positive reals. The limit uses
   Mathlib's right-neighborhood filter `𝓝[>] 0`.
4. For every real \(f'\), if \(f\) has derivative \(f'\) at \(c\) and
   \(f(c)>0\), then
   \(p_f(h)-1/2-hf'/(4f(c))=o(h)\) along that same filter.
   Here `IsLittleO` means that for every real \(\varepsilon>0\), eventually
   the norm of the expression is at most \(\varepsilon|h|\).
5. \(Q(12,9,1/2)=299/4096\), \(Q(15,11,1/2)=1941/32768\), and
   \(Q(19,14,1/2)=2083/65536\).

Outside the quantifier over \(f\), the wrapper adds: for every natural \(M\),
every real \(h\geq0\), and every array \(X:\mathrm{Fin}(M)\to\mathbb R\),
\(K_h(X)\leq N_h(X)\).

Junk-value audit: the integrability, positivity, and normalization hypotheses
rule out nonintegrable-integral zero, negative-density truncation, and infinite
mass. They are genuine density conditions, not the asserted binomial law.
The density is allowed to be only almost-everywhere measurable, as provided by
`Integrable`, which suffices for its absolutely continuous measure and integrals.
Conditional divisions exclude null conditioning events; \(A+B>0\) protects
\(p_f(h)\), and \(a>0\) protects the Lipschitz denominator. No explicit
\(L\geq0\) is needed: the Lipschitz condition on a nondegenerate interval
implies it. The limits do not evaluate the ratio only at \(h=0\): positivity and
continuity/differentiability imply positive masses for all sufficiently small
positive \(h\), so the definition's value \(p_f(0)=0\) is immaterial.
An empty array \(M=0\) is legitimate: \(N=K=0\), its product space is a
singleton, and only \(n=0\) has positive probability. In the binomial expression
\(0^0=1\) is the usual empty-product convention and correctly handles \(n=0\)
and \(p=0,1\). For \(n>M\) the positive-probability premise is impossible, as
expected. Tail sums use \(j\leq n\), so natural subtraction does not truncate.
Interval endpoints may both count \(c\), but absolute continuity makes equality
to \(c\) a null event; the unconditional count inequality also holds pointwise.
No square root, real power, logarithm, extremum, limsup/liminf, or partial
function occurs in this closure.

## SAP.P033.T9

Location: `SAP/P033/Challenge/Part1.lean:66–68`; `T9CoreStatement` is at
`Defs/Part3.lean:178–199`, with added wrapper arithmetic at
`Defs/Part4.lean:174–181`. Its docstring describes Gaussian power, improvement
under a cluster-count SE factor, and explicit arithmetic corrections.
There are no outer hypotheses.

1. For every type \(\Omega\), measurable-space structure, probability measure
   \(\mu\), function \(T:\Omega\to\mathbb R\), and real \(\tau,s\), in that
   order, if \(s>0\) and `HasLaw T (gaussianReal (τ/s) 1) μ`, then
   \(\mu\{|T|>z\}=P(|\tau|/s)\). `HasLaw` means both almost-everywhere
   measurability of \(T\) and the pushforward identity
   \(\mu\circ T^{-1}=G_{\tau/s}\); the hypothesis is not merely an
   unguarded measure-map equality.
2. \(P(0)=1/20\). For every real \(a>0\), \(P\) has derivative
   \(\phi(a-z)-\phi(a+z)>0\) at \(a\), and \(P\) is strictly increasing on
   \([0,\infty)\). For every real \(a,b\geq0\), if
   \(1/20<P(a)<1\) and \(P(a)=P(b)\), then \(a=b\).
3. For every type \(\alpha\) with decidable equality, and finite subsets
   \(L,R\), in that order, if both subsets are nonempty, then
   \(|L|+|R|=|L\cup R|+|L\cap R|\),
   \(1/2\leq\rho(L,R)\leq1\), and
   \(\rho(L,R)<1\) iff \(L\cap R\ne\varnothing\).
4. For every real \(\tau,s,\rho\), assuming in order \(\tau\ne0\),
   \(s>0\), \(\rho>0\), and \(\rho<1\),
   \(P(|\tau|/s)<P(|\tau|/(s\sqrt\rho))\).
   This asserts an implication about a proposed SE scaling, not a theorem that
   an arbitrary variance estimator actually has this scaling.
5. The four ratios are
   \(57/(23+46)=19/23\), \(185/(98+101)=185/199\),
   \(278/(202+226)=139/214\), \(204/(133+130)=204/263\).
   The six differences asserted in order are
   \(31/48-1/36=89/144\), \(113/144-1/36=109/144\),
   \(31/48-1/36=89/144\) again, \(61/104-1/26=57/104\),
   \(81/104-1/26=77/104\), and \(61/104-1/26=57/104\) again.
6. The wrapper adds the natural-number identities
   \((23+46)-57=12\), \((98+101)-185=14\),
   \((202+226)-278=150\), \((133+130)-204=59\), and states that
   each of the four ratios in item 5 is strictly between zero and one.

Junk-value audit: `HasLaw` includes the needed measurability and the Gaussian
law and probability-space hypothesis make every event probability finite.
The nonempty finite-set hypotheses ensure a positive count denominator. Real
division and square roots are protected by \(s>0,\rho>0\); the new denominator
is strictly positive. If \(\tau=0\), strict improvement would fail, and that
case is expressly excluded. The four natural subtractions in the wrapper are
truncated in Lean, but each actual minuend is larger than its subtrahend, so
the displayed values are the ordinary differences. All rational casts are
exact; no integer rounding or natural-number division occurs in the ratios.
The normal quantile's input is again the interior probability 39/40 and avoids
empty or unbounded infimum defaults. No nonintegrable expectation, logarithm,
real power, limsup/liminf, or partial-function default affects the statement.

## SAP.P033.T10

Location: `SAP/P033/Challenge/Part1.lean:70–72`; `T10CoreStatement` is at
`Defs/Part3.lean:202–212`, and the wrapper is at `Defs/Part4.lean:184–186`.
The docstring interprets the arithmetic as a funnel-line counterexample and a
variance-versus-SD coordinate distinction. There are no hypotheses or quantified
free parameters; the entire theorem is a closed conjunction of these facts:

* \(0\leq1/2\), \(1/2\leq2\), \(1/2\leq4/5\).
* \((1/2)/(1/2)=1<49/25\).
* \((1/2)/(49/25)=25/98<1/2\).
* For the three-entry real array \((0,2,4)\),
  \(\bar y=2\), \(v(y)=4\), \(s(y)=2\).
* \((|1|/2,(1/2)/2)=(1/2,1/4)\) and
  \((|1|/4,(1/2)/4)=(1/4,1/8)\); these two pairs are unequal.
* \((1/2)/(1/4)=2\) and \((1/4)/(1/8)=2\).
* The wrapper adds \((25/49)(1/2)=25/98<1/2\).

Thus the point \((x,y)=(1/2,1/2)\) meets the printed-line numerical test
\(y\leq(49/25)x=49/50\) and also \(y\leq4/5\), while \(x/y=1\)
is below \(49/25\). The correct reciprocal-slope height at this \(x\)
is \(25/98\), which is strictly below \(y\). The source states elementary
inequalities from which these observations follow, rather than defining a
predicate for a drawn plot.

Junk-value audit: every denominator is a fixed positive real; the sample length
is three and its divisor is the real number two. `sampleSD` takes the square
root of four. The variance and SD standardizers are both positive and unequal,
and the resulting y coordinates are positive. All finite sums have nonempty
index types. Consequently no zero-division, negative-root, or empty-sum fallback
is active. This closure has no measures, integrals, infima/suprema, logarithms,
real powers, asymptotic operators, casts with truncation, or partial functions.
