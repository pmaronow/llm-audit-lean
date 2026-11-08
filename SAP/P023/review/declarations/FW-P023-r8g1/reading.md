# Blind reading

This file was written and saved before opening `claims.json` or `record.json`.
I read the five Challenge docstrings, every entry of `closure.json`, and the
source of every substantive declaration in those closures. I also compiled
`scratch/ClosureChecks.lean` and read the types of all 160 distinct generated
`_proof_` declarations (`scratch/closure-checks.log`). Those auxiliary facts
provide numeral instances (`AtLeastTwo`, `NeZero`), valid `Fin` indices,
nonempty coefficient/polynomial types, and ordinary measure/scalar instances;
none is a statistical assumption or an encoded conclusion.

## Common expansion of the finite-data definitions

All scalars below are real numbers. A finite observation type is a Lean `Type`
with `Fintype`; where images or equality tests are used it also has
`DecidableEq`. Vectors are functions on these types, not lists with missing
entries. `dot u v` is the Mathlib finite sum \(\sum_i u_i v_i\).
`predict X c i` is \(\sum_j X_{ij}c_j\).

`IsOLS X y c` means precisely the normal equations
\(\sum_i X_{ij}(y_i-\sum_lX_{il}c_l)=0\) for every regressor index \(j\).
`FullRank X` means that, for every real coefficient vector \(c\), if
\(\sum_jX_{ij}c_j=0\) at every observation, then \(c\) is the zero function.
`olsCoefficients X y` is `Classical.epsilon` applied to these normal equations.
`polynomialDesign J x d` has `Fin (J+2)` columns, in order
\(1,d,x,x^2,\ldots,x^J\); `polynomialOLS J x d y` selects column 1's
coefficient (zero-based indexing) from that epsilon choice. `smoothDesign J x`
has columns \(1,x,\ldots,x^J\). Thus
\(r_i=d_i-\sum_{j=0}^J x_i^j\widehat a_j\), where \(\widehat a\) is the
chosen normal-equation solution for regressing \(d\) on those smooth columns,
expands `finiteResidual`; `finiteWeight` is
\(w_i=r_i/\sum_l r_l^2\).

`TwoParty x d` means, for every observation, \(-1\leq x_i\leq1\),
\(d_i\in\{0,1\}\), \(x_i>0\Rightarrow d_i=1\), and
\(x_i<0\Rightarrow d_i=0\). At a zero margin either binary value is allowed.
`Condition1 k x` is the existence of an observation in each of \((0,k)\) and
\((-k,0)\). `close k x` is the finite subset
\(C=\{i:-k<x_i\leq k\}\). With \(n_1=\sum_{i\in C}d_i\) and
\(n_0=\sum_{i\in C}(1-d_i)\),
\[
 R_k(y)=\frac{\sum_{i\in C}d_i y_i}{n_1}
       -\frac{\sum_{i\in C}(1-d_i)y_i}{n_0}
\]
expands `rd`. The `coarsenedWeight` is zero off \(C\), and on \(C\) is
\(d_i/n_1-(1-d_i)/n_0\). `Localized k x est` is
\(\forall y,y',\ [\forall i\in C,y_i=y'_i]\Rightarrow est(y)=est(y')\).

For the bins, put \(n=2\lceil(1-k)/(2k)\rceil_{\mathbb N}\).
`binLabel k t` is the `Fin (n+1)` value with natural-number value
\(\min(n,\lceil(t/k+n-1)/2\rceil_{\mathbb N})\).
`inBin k 0 t` means \(-n-1\leq t/k\leq-n+1\); for \(j\ne0\), it means
\(2j-n-1<t/k\leq2j-n+1\). `binIndicator` is its real 0/1 indicator.
`coarsenedDesign` has columns \(1,d\) followed by the indicators with bin
indices \(1,\ldots,n\), leaving bin 0 as the reference. For any finite label
type, `IsBinOLS B d y a b` means
\[
 \forall j,\ \sum_{i:B_i=j}(y_i-a_{B_i}-b d_i)=0,
 \qquad \sum_i d_i(y_i-a_{B_i}-b d_i)=0.
\]
`CoarsenedOLS k x d y b` asserts existence of all the bin intercepts \(a\)
satisfying these equations for \(B_i=\text{binLabel}(k,x_i)\).

## Common expansion of the population and sampling definitions

The underlying real and product spaces have their Borel measurable spaces.
`expectation μ f` is the real Bochner integral \(\int f\,d\mu\).
`ProbabilityLaw μ` is \(\mu(\mathrm{univ})=1\).
`MarginSupport μ` is \(\mu([-1,1]^c)=0\).
`party t` is \(D(t)=1_{[0,\infty)}(t)\).
`marginLaw ν` is the pushforward of \(\nu\) by the first coordinate.

`IsProjection μ J q` means \(q\in\mathbb R[X]\),
\(\operatorname{natDegree}q\leq J\), and, for every natural \(j\leq J\),
\(\int(D(x)-q(x))x^j\,d\mu=0\). `projection μ J` is an epsilon choice
of such a polynomial. Write \(q_J\) for this choice,
\(r_J(x)=D(x)-q_J(x)\), and \(v_J=\int r_J^2\,d\mu\); these expand
`popResidual` and `residualVariance`. `biasFunctional μ J h` is
\(\int r_Jh\,d\mu/v_J\).

`MomentPositiveDefinite μ J` means
\(\forall c\in\mathbb R^{J+2},c\ne0\Rightarrow
\int(c_0+c_1D(x)+\sum_{j=1}^Jc_{j+1}x^j)^2\,d\mu>0\).
`PopNormal μ J m c` is the normal equation against every column of
\((1,D,x,\ldots,x^J)\) for residual \(m-\operatorname{predict}(c)\).
`populationCoefficient μ J m` is coefficient 1 of an epsilon choice satisfying
those equations; write it as \(b_{\mu,J}(m)\).

`uniformMargins` is \(\mu_U=\tfrac12\lambda|_{[-1,1]}\).
`populationRD μ m k` is
\[
 \mathcal R_{\mu,m}(k)=
 \frac{\int_{(0,k]}m\,d\mu}{\operatorname{toReal}(\mu(0,k])}
 -\frac{\int_{(-k,0)}m\,d\mu}{\operatorname{toReal}(\mu(-k,0))}.
\]
In particular it excludes zero on both sides. `ConditionalMean ν m` means
that \(Y\) and \(m(X)\) are integrable and, for every measurable
\(t:\mathbb R\to\mathbb R\) admitting a finite global absolute bound,
\(\int t(X)Y\,d\nu=\int t(X)m(X)\,d\nu\).

`noiseLaw` assigns mass 1/2 to each of \(-1/10,1/10\).
`witnessLaw μ h` is the pushforward of the product \(\mu\otimes
\text{noiseLaw}\) by \((x,e)\mapsto(x,1/2+h(x)+e)\). Thus noise is
independent of the margin in this construction. Real `predictionRisk ν f` is
\(L_\nu(f)=\int(Y-f(X))^2\,d\nu\). `extendedPredictionRisk` is instead
\(L_\nu^+(f)=\int^-\operatorname{ofReal}((Y-f(X))^2)\,d\nu\in[0,\infty]\).
`fittedRisk ν J` is the real `sInf` of all
\(L_\nu(c_0+c_1D+\sum_{j=1}^Jc_{j+1}x^j)\), over every real coefficient
vector. Write this infimum as \(F_{\nu,J}\).

`ConvergesInProbability P Z z` means
\(\forall\epsilon>0,\ P\{|Z_N-z|>\epsilon\}\to0\), with measures and
the limit in Mathlib's extended-nonnegative-real topology. `IIDSample P ν s`
means \(P\) has total mass 1, every \(s_i\) is measurable, every pushforward
\((s_i)_*P=\nu\), and the countable family is independent in the sense of
`ProbabilityTheory.iIndepFun`. `samplePolynomial s N J` applies the finite
coefficient definition to the first `Fin N` sample pairs, with \(d_i=D(X_i)\).
`sampleRD s k N` applies \(R_{k_N}\) to the same observations.

## SAP.P023.T1

There are no outer variables or hypotheses. The theorem is the conjunction
`T1Statement`, which includes every clause of `LinearWitness`.
All vectors have type `Fin 6 → ℝ`, with indices 0 through 5:
\[
 x=(-3/4,-1/4,-1/400,1/400,1/4,3/4),\quad d=(0,0,0,1,1,1),
\]
\[
 y=(37/80,39/80,3999/8000,4801/8000,49/80,51/80),
\quad y'=y+(1/100)e_5.
\]
The coefficient vector `linearExact : Fin 3 → ℝ` is \((1/2,1/10,1/20)\),
and
\[
 w=(20299/139202,-59901/139202,-49800/69601,
       49800/69601,59901/139202,-20299/139202).
\]
At \(k=1/200\) it asserts all of the following:

1. The two-party conditions and Condition 1 hold, the three-column design
   \((1,d,x)\) is injective, and \(y_i=1/2+d_i/10+x_i/20\) at every index.
2. For every outcome vector \(z:\mathrm{Fin}\,6\to\mathbb R\), the selected
   coefficient equals \(\sum_iw_i z_i\).
3. Its values on \(y,y'\) are \(1/10\) and \(1371721/13920200\), with
   difference \(-20299/13920200\ne0\).
4. \(y,y'\) agree on every close observation, differ exactly by \(1/100\)
   at index 5, and both RD values equal \(401/4000\).
5. The bin count is 200 and the six labels are
   \((25,75,100,100,125,175)\). Each of \(y,y'\) has bin normal-equation
   intercepts with party coefficient \(401/4000\). Separately for each outcome
   vector, every real coefficient satisfying those equations equals this value.
6. Every entry of both outcome vectors lies strictly between 0 and 1.
   Polynomial OLS is not localized (there exist outcome vectors agreeing on the
   close subset but giving different coefficients).
7. The close set is exactly \(\{2,3\}\), its RD value for \(y\) is
   \(y_3-y_2\), and for every pair of real outcome vectors agreeing on this
   set the two RD estimates agree.
8. For all outcome vectors \(z,z'\), then all real coefficients \(b,b'\),
   agreement on the close set followed by bin-normal-equation validity for each
   coefficient implies \(b=b'\).

Junk conventions: all displayed rational denominators are positive real
numerals. The RD denominators are 1 and 1, and both groups are witnessed
strictly inside the window. Epsilon cannot select a non-solution here: finite
real least squares has a normal-equation solution, and injectivity gives
uniqueness. The coarsened nuisance coefficients need not be unique in empty
bins, but their party coefficient is explicitly unique. The natural ceiling
clips negative inputs to zero, and `min` clips the upper end; all listed margins
are in the stated range with positive \(k\), so this is endpoint binning.
The natural subtraction in polynomial column exponents is used only in its
\(j\geq2\) branch. Empty sum conventions and `Fin` bounds introduce no
missing observation or regressor. No integral, supremum, logarithm, square root,
real power, or limit appears in this closure.

## SAP.P023.T2

There are again no outer variables or hypotheses. Every clause of
`DegreeSevenWitness` is asserted, followed by two close-set clauses.
The vectors have type `Fin 16 → ℝ`. Their margins, in increasing order, are
\((-1,-7/8,-3/4,-5/8,-1/2,-3/8,-1/4,-1/8,
1/8,1/4,3/8,1/2,5/8,3/4,7/8,1)\). The first eight party values are 0 and
the last eight are 1. At every index the supplied outcome equals
\(y_i=1/2+d_i/10+x_i/20+x_i^7/100\); this specifies exactly the rational
vector `degree7Y` read in Part1. The perturbed vector is
\(y'=y+(1/100)e_{15}\) (its final entry is \(67/100\), instead of
\(33/50\)). The exact coefficient vector has type `Fin 9 → ℝ` and entries
\((1/2,1/10,1/20,0,0,0,0,0,1/100)\).

At \(k=1/5\), the two-party conditions and strict-interior witnesses hold;
the nine-column design is injective and has the exact outcome model just
given. For every real outcome vector \(z\), polynomial OLS is \(\sum_iw_i z_i\)
where
\[
 1607w=(-175,725,-685,-643,554,1289,239,-2911,
          2911,-239,-1289,-554,643,685,-725,175).
\]
Every one of these 16 weights is nonzero. The original and perturbed
coefficients are \(1/10\) and \(3249/32140\), and their difference is
\(7/6428\ne0\). The vectors agree at every close election, with only the
stated final-coordinate perturbation. Both RD values are
\(11796481/104857600\). The bin count is 4 and the labels are
\((0,0,0,0,1,1,1,2,2,3,3,3,4,4,4,4)\).
Both outcomes admit bin-normal-equation coefficients equal to that RD value;
for each outcome every valid party coefficient equals it. Every outcome and
perturbed outcome lies strictly between 0 and 1. Polynomial OLS is not
localized. Finally the close subset is exactly \(\{7,8\}\), and the original
RD value is \(y_8-y_7\).

Junk conventions are checked for this declaration independently: all rational
denominators are nonzero, both RD counts are 1, the explicitly full-rank finite
normal equations select a unique solution, and the fixed positive bandwidth
makes natural-ceiling clipping ordinary boundary binning. The 16 observation
and 9 coefficient indices are inhabited, bounded, and not defaults. Polynomial
exponent subtraction is guarded. There are no Bochner integrals, infinities,
suprema/infima, square roots/logarithms/real powers, or asymptotic sequence
conventions in this closure.

## SAP.P023.T3

There are no outer hypotheses. `T3WholeStatement` is a conjunction of nine
universally quantified propositions. Using the fully expanded notation above:

1. For every finite observation type, every real \(k\) with \(0<k<1\),
   then every \(x,d,y\) satisfying the two-party conditions, and every real
   \(b\), bin-normal-equation validity is equivalent to existence of a
   `Fin (binCount k+2)` coefficient vector satisfying the ordinary normal
   equations of the printed indicator design and having party coefficient
   \(b\). No nonempty-bin condition is imposed.
2. For the same universal data, now with both close-group sums \(n_1,n_0>0\),
   every real \(b\) satisfying the bin equations equals both
   \(\sum_i w_i^C y_i\) and \(R_k(y)\). Every off-window weight is zero;
   every close winner weight is \(1/n_1\), and every close loser weight is
   \(-1/n_0\).
3. For all finite two-party data and bandwidths as in item 2, all pairs of
   outcomes agreeing on the close subset, and all valid bin-equation party
   coefficients \(b,b'\), one has \(b=b'\).
4. For every finite type with decidable equality, natural degree \(J\geq1\),
   then two-party \(x,d\) with injective polynomial design, put \(r,w\)
   equal to the finite residual and its normalization. Then
   \(\sum r_i d_i=\sum r_i^2>0\); \(\sum r_i x_i^j=0\) for every
   natural \(j\leq J\); and for every outcome vector \(y\),
   \(\widehat b_J(y)=\sum r_i y_i/\sum r_i^2=\sum w_i y_i\).
   Furthermore \(\sum w_i=0\), \(\sum w_i x_i^j=0\) for
   \(1\leq j\leq J\), \(\sum w_i d_i=1\), and, for every \(y\),
   every index \(i\), and every real \(\delta\), changing only \(y_i\)
   by \(\delta\) changes the coefficient by \(w_i\delta\).
5. For every such finite type and \(J\geq1\), every \(0<k<1\), every
   full-rank two-party design having at least one observation of each party,
   at most \(J\) distinct negative margins have zero polynomial weight, and
   at most \(J\) distinct positive margins have zero polynomial weight.
   If there are more than \(2J\) distinct nonzero margins outside the close
   subset, there exist an off-window index \(i\) and two outcome vectors
   equal at every other index and throughout the close subset, whose
   polynomial coefficients differ. If additionally both close-group sums
   are positive, their RD values agree and every pair of valid coarsened
   party coefficients agrees. The count assumptions are inside this last
   implication, not hypotheses on polynomial nonlocality.
6. For every finite observation type, every measurable probability space
   \((\Omega,P)\), every \(J\geq1\), every full-rank two-party design,
   every real \(\alpha,\beta\), every function \(h:\mathbb R\to\mathbb R\),
   and then every collection \(Y_i:\Omega\to\mathbb R\) of integrable
   variables with \(E Y_i=\alpha+\beta d_i+h(x_i)\),
   \[
   E\widehat b_J(Y)-\beta=\frac{\sum r_i h(x_i)}{\sum r_i^2}.
   \]
   For each polynomial \(p\) of natural degree at most \(J\), agreement
   \(h(x_i)=p(x_i)\) at every observation implies \(E\widehat b_J=\beta\).
   Set \(u_i=Y_i-(\alpha+\beta d_i+h(x_i))\). If all \(u_i^2\) are
   integrable and \(E(u_i u_l)=0\) for all distinct indices, then
   \(E(\widehat b_J-E\widehat b_J)^2=\sum_iw_i^2 E u_i^2\).
   Finally for every index and real \(\sigma^2\), nonzero \(w_i\) and
   \(\sigma^2>0\) imply \(w_i^2\sigma^2>0\).
7. For the fixed uniform law the chosen projections satisfy, at every real
   \(x\),
   \[
   q_1(x)=1/2+3x/4,\quad
   q_7(x)=1/2+(11025x-40425x^3+63063x^5-32175x^7)/4096.
   \]
   The residual variances are \(1/16\) and \(1225/65536\).
   The normalized residuals at \(9/10\) are \(-14/5\) and
   \(-20283449/6125000\). The fractions of residual squared mass on
   \(\{|x|\geq1/2\}\), divided by their total residual variances, are
   \(1/8\) and \(572158921/10276044800\).
   For \(m_1=1/2+D/10+x/20\) and
   \(m_7=1/2+D/10+x/20+x^7/100\), respectively, the matching-degree
   population coefficients are \(1/10\). For every \(0<k\leq1\) the RD
   values are \(1/10+k/20\) and \(1/10+k/20+k^7/400\), respectively;
   each tends to \(1/10\) as \(k\downarrow0\).
8. For every natural \(J\geq1\), uniform-law regressor moments are positive
   definite, the chosen polynomial actually satisfies its projection equations,
   and its residual variance is strictly positive.
9. For every measurable space \(\Omega\), **any** measure \(P\) on it, every
   two real-valued sequences \(A,B:\mathbb N\to\Omega\to\mathbb R\), and
   every real \(\beta\), first for every natural \(N\) and real
   \(\epsilon>0\),
   \[
   P(|A_N-B_N|>\epsilon)\leq
   P(|A_N-\beta|>\epsilon/2)+P(|B_N-\beta|>\epsilon/2).
   \]
   Next convergence in probability of each sequence to \(\beta\) implies
   convergence of their difference to zero. This clause has no IID,
   probability-mass, sample-rank, or window-count premise.

Junk conventions: finite divisions in items 2 and 3 are guarded by positive
counts; in item 5 count guards occur only on the RD/coarsened comparison.
Full column rank ensures a unique finite OLS coefficient, a unique smooth
projection, and a strictly positive residual sum of squares. Injectivity for
\(J\geq1\) rules out empty observation types; no existential nonlocality
witness comes from an empty type. Bin ceilings are clipped at the boundary,
with \(0<k<1\) and supported margins; natural exponent subtraction is guarded.
The population projections and coefficients use epsilon, but bounded uniform
moments and positive definiteness ensure the required solutions and uniqueness.
The uniform RD windows have finite positive mass at every stated positive
bandwidth. `toReal ∞ = 0` is therefore irrelevant there. All fixed population
integrands are bounded on the support, and all stochastic integrals have the
stated integrability/second-moment guards; cross products are integrable by
Cauchy--Schwarz. Measures in item 9 are evaluated on sets via the Mathlib outer
measure even absent measurability, but the set inclusion and subadditivity
remain valid; no undefined subtraction of infinities occurs. There are no
`sInf`/`sSup`, `liminf`/`limsup`, logarithms, square roots, or real powers in
this declaration's closure. `nhdsWithin 0 (Ioi 0)` is the nontrivial right-hand
limit, not a limit along an empty filter.

## SAP.P023.T4

There are no outer hypotheses. The statement conjoins population, risk,
sampling, symmetry, and approximation assertions. Here
\(h_{a,\eta}(x)=a\max(-1,\min(1,x/\eta))\), which expands `sigmoid`.
For each real \(a>0\), then \(0<\eta\leq1\), put
\(m=1/2+h_{a,\eta}\) and \(\nu=\text{witnessLaw}(\mu_U,h_{a,\eta})\):

1. \(h\) is continuous on all reals, \(h(0)=0\), \(h(-x)=-h(x)\) for
   every real \(x\), and for every real \(x,x'\),
   \(|h(x)-h(x')|\leq(a/\eta)|x-x'|\). The defined conditional-mean
   identities hold for \(m\). For every \(0<k\leq\eta\),
   \(\mathcal R_{\mu_U,m}(k)=ak/\eta\), and its right cutoff limit is zero.
2. For every natural \(J\geq1\),
   \[
   b_{U,J}(m)=2a-\frac{a}{v_J}\int_{[0,\eta]}r_J(x)(1-x/\eta)\,d\lambda(x).
   \]
   The integral here is **Lebesgue volume**, not the uniform probability
   measure. The degree-one coefficient is \(2a(1-\eta)^2\).
   Also \(\int(h-a(2D-1))^2\,d\mu_U=a^2\eta/3\). For every
   \(J\geq1\), the real infimum of squared errors approximating \(m\)
   by \(c_0+c_1D+\sum_{j=1}^Jc_{j+1}x^j\) lies in \([0,a^2\eta/3]\).
3. \(\nu\) is a probability law with margin \(\mu_U\), and
   \(L_\nu(m)=1/100\). For every \(J\geq1\),
   \(1/100\leq F_{\nu,J}\leq1/100+a^2\eta/3\). For every measurable
   predictor \(f:\mathbb R\to\mathbb R\) whose squared loss is integrable,
   \(F_{\nu,J}-L_\nu(f)\leq a^2\eta/3\), and
   \((F_{\nu,J}-1/100)/F_{\nu,J}\leq100a^2\eta/3\).
   If \(a=1/20\), its degree-seven coefficient is
   \[
    1/10-(4096/6125)\eta+(6/5)\eta^2-(33/25)\eta^4
            +(858/875)\eta^6-(143/490)\eta^8.
   \]
4. Every family law has integrable \(Y^2\), continuous \(m\), and
   \(m(0)=1/2\). For every natural \(J\), including zero, and every real
   vector \(c:\mathrm{Fin}(J+2)\to\mathbb R\), the associated regression
   loss is integrable. For every \(J\geq1\),
   \(b_{U,J}(m)=\int r_Jm\,d\mu_U/v_J\). Then, for every measurable
   probability sample space \((\Omega,P)\) and sample \(s\), if `IIDSample`
   holds for this \(\nu\), for every fixed \(J\geq1\) the first-\(N\)
   polynomial coefficient converges in probability to \(b_{U,J}(m)\).
5. For every member and every \(J\geq1\), then **every** measurable
   \(f:\mathbb R\to\mathbb R\), with no finite-risk premise,
   \[
   \operatorname{ofReal}(1/100)\leq L_\nu^+(f),\quad
   \operatorname{ofReal}(F_{\nu,J})\leq
       L_\nu^+(f)+\operatorname{ofReal}(a^2\eta/3).
   \]
6. For every fixed natural \(J\geq1\) and real \(a>0\),
   \(b_{U,J}(1/2+h_{a,\eta})\to2a\) as \(\eta\downarrow0\).
   For every real \(a\), \(a^2\eta/3\to0\) in the same limit.
   For every real \(a\) and every natural \(J\), there exists a coefficient
   vector representing \(1/2+a(2D-1)\) at every real \(x\).

The numerical member is \(a=1/20,\eta=1/10000\). Its degree-one coefficient
is \(99980001/1000000000\); its degree-seven coefficient is
\(4896723787999993532000048047999857/
49000000000000000000000000000000000\). Almost surely its outcomes are
between \(7/20\) and \(13/20\). The absolute fit-error bound equals
\(1/12000000\), and for every \(J\geq1\) the relative bound is
\((F_{\nu,J}-1/100)/F_{\nu,J}\leq1/120000\).
For every measurable sample space, measure \(P\), and sample \(s\) IID from
this numerical member, then every real bandwidth sequence \(k_N\) with
\(k_N>0\) for all \(N\), \(k_N\to0\), and \(Nk_N\to+\infty\), the
degree-one and degree-seven sample coefficients converge in probability to
those displayed constants and the window RD converges to zero. There is no
separate rank or nonempty-window probability hypothesis.

The statement also asserts, for every \(J\geq1\), uniform positive-definite
moments, valid chosen projections and \(v_J>0\); for every real \(x\ne0\),
\(r_J(-x)=-r_J(x)\). For every \(x>0\),
\(r_1(x)=1/2-3x/4\) and
\(r_7(x)=1/2-(11025x-40425x^3+63063x^5-32175x^7)/4096\).
The residual variances are \(1/16\) and \(1225/65536\).

Junk conventions: \(\eta>0\) protects every division in the clipped function
and Lipschitz constant; \(v_J>0\) protects the residual ratios; the risk
denominator is at least \(1/100\). The real infima have a nonempty coefficient
set and are bounded below by zero; all candidates' Bochner losses are
integrable, explicitly for regression risk and also by boundedness for the
mean-error infimum. `ENNReal.ofReal` clips negative inputs to zero, but every
input used for risk is nonnegative; infinite competitor risks are retained as
infinity and not sent through `toReal`. Population cutoff windows have finite
positive masses. Epsilon projection choices are legitimate and unique by
uniform positive definiteness. In samples, zero observations at \(N=0\),
empty winner/loser windows, or singular designs can occur. `rd` then uses real
division by zero (=0), and epsilon may choose among multiple normal-equation
solutions. These conventions need not describe identified estimators at those
sample outcomes; the limits require their probabilities to vanish under IID
sampling and the bandwidth assumptions. They are not assumptions of the
statement and do not themselves supply the convergence conclusion. The
countable IID family is a real independence condition, not repeated use of
one draw. No logarithm, square root, noninteger power, or sequence
limsup/liminf is used. Polynomial exponent subtraction and finite-index bounds
are guarded as above. The zero polynomial's natural degree is not used here.

## SAP.P023.T5

There are no outer hypotheses. For every real \(d\) with \(0<d\leq1/2\),
define the triangular bump
\(T_{c,w}(x)=\max(w-|x-c|,0)/w^2\), with \(w=d/2\), and
\[
 \rho_d(x)=d^4/2+(1-d^4)(T_{1/2,d/2}(x)+T_{-1/2,d/2}(x))/2.
\]
`clusteredMargins d` is \(\mu_d=(\lambda|_{[-1,1]})\) with density
\(\operatorname{ofReal}(\rho_d)\). The positive-side piecewise-linear
function is
\[
 g_d(x)=\begin{cases}
 0&x<1/2-d,\\
 1/2-d-x&1/2-d\leq x\leq1/2-d/2,\\
 x-1/2&1/2-d/2<x\leq1/2+d/2,\\
 1/2+d-x&1/2+d/2<x\leq1/2+d,\\
 0&x>1/2+d.
 \end{cases}
\]
`clusterSmooth d x` is \(h_d(x)=-g_d(-x)\) for \(x<0\) and \(g_d(x)\)
otherwise. Put \(m_d=1/2+h_d\) and \(\nu_d=\text{witnessLaw}(\mu_d,h_d)\).
`T5WholeStatement` asserts all of the following:

1. \(\mu_d\) is a probability supported on \([-1,1]\), has zero mass at
   zero, and assigns positive mass to every interval \((a,b)\) with
   \(-1\leq a<b\leq1\). The density is continuous on the reals and at least
   \(d^4/2\) on \([-1,1]\).
2. \(h_d\) is continuous, equals zero at zero and everywhere
   \(|x|\leq1/2-d\), is odd for every real argument, and satisfies
   \(|h_d(x)-h_d(x')|\leq|x-x'|\) for all real \(x,x'\). Globally
   \(|h_d|\leq d/2\), and
   \(\sup_{x\in[-1,1]}|h_d(x)|=d/2\). It supplies the conditional mean
   \(m_d\) under \(\nu_d\).
3. The exact moments are
   \[
   E_{\mu_d}X=E_{\mu_d}h_d=E_{\mu_d}[(D-1/2)h_d]=0,
   \quad E_{\mu_d}(XD)=1/4,
   \]
   \[
   E X^2=(1-d^4)(1/4+(d/2)^2/6)+d^4/3,
   \quad E(Xh_d)=(1-d^4)(d/2)^2/6+2d^4(d/2)^3.
   \]
   The degree-one coefficient is
   \(b_{\mu_d,1}(m_d)=-(1-d^4+6d^5)/(1-d^4+2d^2)\).
   For every \(0<k<1/2-d\), \(\mathcal R_{\mu_d,m_d}(k)=0\).
   Also \(E h_d^2\leq(d/2)^2\).
4. \(\nu_d\) is a probability with margin \(\mu_d\),
   \(L_{\nu_d}(m_d)=1/100\), and
   \(L_{\nu_d}(1/2)=1/100+E h_d^2\). Every measurable finite-squared-risk
   predictor \(f\) satisfies
   \(L_{\nu_d}(1/2)-L_{\nu_d}(f)\leq(d/2)^2\). For every \(J\geq1\),
   \(F_{\nu_d,J}\leq L_{\nu_d}(1/2)\) and, for every such \(f\),
   \(F_{\nu_d,J}-L_{\nu_d}(f)\leq(d/2)^2\).
5. For **every** measurable predictor \(f\), with infinite risks permitted,
   \(\operatorname{ofReal}(1/100)\leq L_{\nu_d}^+(f)\),
   \(L_{\nu_d}^+(1/2)\leq L_{\nu_d}^+(f)+\operatorname{ofReal}((d/2)^2)\),
   and, for every \(J\geq1\),
   \(\operatorname{ofReal}(F_{\nu_d,J})\leq
       L_{\nu_d}^+(f)+\operatorname{ofReal}((d/2)^2)\).
   Every regressor squared loss, for all natural \(J\) and all vectors
   \(c:\mathrm{Fin}(J+2)\to\mathbb R\), is integrable under \(\nu_d\).
6. For every natural \(J\), the zero polynomial has natural degree at most
   \(J\), and at every \(x\in[-1,1]\),
   \(|h_d(x)-0(x)|\leq d/2\). Also
   \[
   A_d=(1-d^4)(d/2)^2/6+d^4/12>0,
   \quad b_{\mu_d,1}(m_d)=
    -\frac{(1-d^4)(d/2)^2/6+2d^4(d/2)^3}{A_d}.
   \]

Separately, at \(d=1/1000\), the coefficient is
\(-499999999999503/500000999999500\), the outcomes lie almost surely in
\([799/2000,1201/2000]\), and for every natural \(J\) the zero polynomial
has degree at most \(J\) and uniform error at most \(1/2000\).
As \(d\downarrow0\), the degree-one coefficient tends to \(-1\), while
\(d/2\to0\). There does not exist a real \(C\) such that for **every**
\(0<d\leq1/2\), \(|b_{\mu_d,1}(m_d)|\leq C(d/2)\).

Junk conventions: \(w=d/2>0\), so the triangular normalization never divides
by zero. The background density is positive and the triangular factors
nonnegative, so `ofReal` never alters the intended density on the support.
The displayed denominator \(A_d\) is explicitly positive; the other simplified
denominator is positive too. Compact support and bounded \(h_d\) and noise
ensure all stated Bochner moments and all regressor losses exist. Competing
real risks are guarded by integrability, and the unguarded comparisons use
the extended nonnegative integral, preserving infinite risk. The fitted-risk
set is nonempty and bounded below. The supremum defining the uniform error
is over the nonempty compact interval and a bounded continuous function;
thus it is an ordinary real supremum. The zero polynomial has `natDegree 0`
in Mathlib; that convention correctly includes it among degree-at-most-\(J\)
approximants for every natural \(J\). When \(d=1/2\), the special exact-zero
RD range \(0<k<1/2-d\) is empty, but the rest of the family assertion is
not: continuity, the zero value at cutoff, and positive density still describe
a zero cutoff jump. For \(d<1/2\) the exact-zero RD range is nonempty, with
finite positive mass on both sides, so `toReal` and division by zero do not
create those equalities. The epsilon population coefficient is well-defined
by finite bounded moments and the positive continuous margin density on
both sides, which give positive-definite moments at every finite degree;
no arbitrary default can produce the coefficient formula. The filter
\(d\downarrow0\) is nontrivial. There is no logarithm, square root,
noninteger power, empty index type, or sequence limsup/liminf in this closure.
