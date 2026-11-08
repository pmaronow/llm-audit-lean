# Blind reading

This file was written and saved before opening `claims.json` or `record.json`.
It describes the statements, without assessing their agreement with either file.
Sources read: `closure.json`, `Challenge/Part1.lean`, `Defs/Part1.lean` through
`Defs/Part5.lean`, and `Defs/WholeW1.lean`, as well as the aggregate imports.
All source paths below are relative to `SAP/P053/`.
`scratch/ClosureCheck.lean` was compiled to read every auxiliary declaration in
the supplied closures and to inspect the structures and projections. The
auxiliary declarations are numeral-instance certificates and, in one case, a
finite-cardinality equality; none adds a mathematical hypothesis.

## SAP.P053.T1

The theorem has an implicit, arbitrary type `S`, with no structure or
nonemptiness assumption. Its conclusion is the following universal proposition.
First choose natural numbers `n1,n0`, with hypotheses `0<n1` and `0<n0`, then
choose any Boolean vector `y` indexed by `Fin (n1+n0)`. Put `N=n1+n0`, let
`U={0,...,N-1}`, and let `D` be the finite set of all subsets of `U` of
cardinality `n1`. Thus `support n1` is literally `univ.powersetCard n1`.
For a subset `s`, let

* `a_y(s)=|{i in s : y(i)=true}|`, the cardinality of a filtered finite set;
* `M_y=a_y(U)`;
* `C(a)=(a,n1-a,M_y-a,n0-M_y+a)`, with **all four entries integers**;
* `t_y(s)=a_y(s)/n1-(M_y-a_y(s))/n0`, a real number;
* `r_M(t)=(n1*n0*t+n1*M)/(n1+n0)` in the reals.

All natural counts in real or integer expressions are embedded by the usual
casts. With these definitions, the conclusion is a conjunction of six groups:

1. For every `s in D`,
   `t_y(s)=(N*a_y(s)-n1*M_y)/(n1*n0)` and
   `r_(M_y)(t_y(s))=a_y(s)`.
2. For every `s in D`, then every `t in D`,
   `t_y(s)=t_y(t)` iff `a_y(s)=a_y(t)`, and
   `a_y(s)=a_y(t)` iff `C(a_y(s))=C(a_y(t))`.
3. For every function `h : Z^4 -> S`, there exists `g : R -> S` such that
   `g` is exactly the following prescribed total function:
   `g(t)=h(b,n1-b,M_y-b,n0-M_y+b)` where
   `b=floor(r_(M_y)(t))` is an integer. For **every** other Boolean outcome
   vector `yy` on the same carrier whose total successes equal `M_y`, and
   every `s in D`,
   `h(C(a_yy(s)))=g(t_yy(s))`. The factor is chosen before `yy` and is
   uniform over all vectors with that same total.
4. For every function
   `F : (Fin n1 -> Bool) -> (Fin n0 -> Bool) -> S`, assume that for all
   sample vectors `x1,x0` and all permutations `p1,p0` of their respective
   finite index sets, `F(x1 o p1,x0 o p0)=F(x1,x0)`. There then exists
   `g : R -> S` such that for every subset `s` and proof `s in D`, there
   exist certificates `ht:|s|=n1`, `hc:|U\s|=n0`, and both equalities
   
   `F(y on s in increasing unit-label order, y on U\s in increasing order)`
   `=F(canonical(n1,a_y(s)),canonical(n0,M_y-a_y(s)))`
   `=g(t_y(s))`.
   
   Here `canonical(n,k)(j)` is the Boolean proposition `j<k`, converted to
   `Bool`. The ordered samples are obtained by the increasing order embedding
   `s.orderEmbOfFin ht : Fin n1 -> Fin N` and its complement analogue.
   The function `g` is chosen after `F,y,n1,n0`, before `s`.
5. For every `h:Z^4 -> S`, every pair of Boolean vectors `x1,x0` of lengths
   `n1,n0`, and every pair of permutations `p1,p0`, applying `h` to
   `(number of ones in x1 o p1,n1 minus that count,
   number of ones in x0 o p0,n0 minus that count)` gives the same result
   as applying `h` to the unpermuted counts. Subtractions here are integers.
6. For every statistic `T` on the subtype of subsets `s` with `|s|=n1`,
   there exists a total `g:R->S` with `T(s)=g(t_y(s))` for every such `s`
   **iff** for every two such subsets `s,t`, equality of their four-entry
   tables implies `T(s)=T(t)`.

The docstring describes fixed binary sharp-null outcomes, table identification,
the explicit common factor, symmetry of the arm samples, and the exact
table-constancy criterion. There is no separate stochastic or sharp-null
hypothesis: the same fixed `y` supplies the outcomes in both arms.

Junk-value/domain audit:

* Real division is total in Lean, with `x/0=0`. The hypotheses make `n1`,
  `n0`, `n1+n0`, and `n1*n0` strictly positive wherever used here.
* The inverse uses the ordinary integer floor of a real. On attainable
  statistics the reconstructed real is precisely the integer count, so floor
  changes nothing. Off the attainable set the function can return arbitrary,
  even negative, integer tables; no assertion gives those values a statistical
  interpretation, and `h` was explicitly defined on all integer quadruples.
* The subtraction `M_y-a_y(s)` in the canonical control sample is natural
  truncated subtraction. As `s` is a subset of the full carrier,
  `a_y(s)<=M_y`, so no truncation affects the claimed value. All table
  subtractions are in the integers, not truncated naturals.
* `canonical(n,k)` would saturate at all-true for `k>=n`. In its asserted uses,
  treated and control counts lie within their respective arm sizes.
* The order embeddings are total maps requiring exact cardinality proofs,
  with no default lookup value. The existential proofs do not restrict
  `s` beyond its already assumed membership in `D`.
* Both arms and `D` are nonempty. Although `S` may be empty, the quantified
  statistic functions then do not exist; the theorem does not assume a
  nonexistent statistic or obtain its substantive content from that case.
* There are no integrals, `toReal`, logarithms, square roots, real powers,
  extrema, partial functions, or limsup/liminf in this closure.

## SAP.P053.T2

This theorem has no external parameters or hypotheses. It asserts an explicit
finite example, its repetition at every positive block count, exact moments,
and a regular sequence of those same populations.

The basic design is the six two-element subsets `D4` of `Fin 4`; each has
uniform mass `1/6`. Put

`y=(true,true,false,false)`, `x=(true,false,true,false)`,
`A={0,2}`, `B={1,2}`, and `L(s)=1` if `0 in s`, `0` otherwise.

For any Boolean vector `b` on a finite carrier, let `a_b(s)` count its true
entries in `s`, `M_b` count them in the whole carrier, and put
`t_b(s)=a_b(s)/n1-(M_b-a_b(s))/n0`. The table is the integer quadruple
`(a_b(s),n1-a_b(s),M_b-a_b(s),n0-M_b+a_b(s))`.
The covariate statistic is `t_(x AND y)`, with Boolean AND, so its binary
outcome is exactly the real product of the zero-one covariate and outcome.
The asserted finite facts are:

* `|D4|=6`, `A,B in D4`;
* `t_y(A)=t_y(B)=0` and both tables are `(1,1,1,1)`;
* `L(A)=1`, `L(B)=0`;
* `t_(x AND y)(A)=1/2`, `t_(x AND y)(B)=-1/2`;
* there does not exist `g:R->R` expressing `L(s)=g(t_y(s))` for every
  `s in D4`, and separately there does not exist such a `g` for
  `t_(x AND y)(s)`.

Next, for every natural `m` and every proof `hm:0<m`, use the carrier
`Fin m x Fin 4`, the design `Dm` of all subsets of cardinality `2m`, and
repeat the two vectors blockwise: `y_m(j,i)=y(i)`, `x_m(j,i)=x(i)`.
Put `A_m=Fin m x A`, `B_m=Fin m x B`, and
`L_m(s)=1_{(0,0) in s}`; the first zero in this expression is constructed
as an element of `Fin m` using `hm`. Then:

* `A_m,B_m in Dm`, both `t_(y_m)` values are zero, and both tables are
  `(m,m,m,m)`;
* `L_m(A_m)=1`, `L_m(B_m)=0`;
* the difference of means for `x_m AND y_m` is `1/2` on `A_m` and `-1/2`
  on `B_m`;
* `2m/(4m)=1/2`, `M_(y_m)/(4m)=1/2`;
* neither `L_m` nor the covariate statistic factors as a real function of
  `t_(y_m)` on **all** of `Dm`.

Here, repetition is repetition of fixed population blocks, not a random
replicate sampling scheme. Every design still consists of all subsets of the
specified size.

There is also the conjunction of these four scaling statements, with index
`k` ranging over all naturals and real-valued ratios:

1. `4(k+1) -> infinity` in the natural-number `atTop` filter.
2. `2(k+1)/(4(k+1)) -> 1/2`.
3. `M_(y_(k+1))/(4(k+1)) -> 1/2`.
4. For every `k`, the sum over `Fin (k+1) x Fin 4` of twice the fourth
   power of the real zero-one outcome, divided by `4(k+1)`, is at most `2`.

To express moments on the population carrier, for each `m` choose a bijection
`e_m : Fin (2m+2m) <-> Fin m x Fin 4` using equality of the finite
cardinalities. It is not an explicitly prescribed ordering. Define `P_m` by
`n1=n0=2m` and both real potential outcomes
`Y1(i)=Y0(i)=1_{y_m(e_m(i))=true}`. The theorem asserts, for every `m>0`,

* `Y1(i)=Y0(i)` for every unit;
* both population means are `1/2`;
* both population variances are `m/(4m-1)`;
* the population variance of `i -> Y1(i)-Y0(i)` is zero, and the difference
  of the two population means is zero;
* `(sum_i (Y1(i)^4+Y0(i)^4))/(4m)=1`.

Here a finite-sample mean is `sum_{i in s} f(i)/|s|`; its centered sum of
squares is `sum_{i in s}(f(i)-mean_s(f))^2`; its variance divides that sum
by the **real** number `|s|-1`. A population mean/variance is that same
operation on the entire finite carrier. Thus the variance formula is the
finite-population variance with divisor `4m-1`, not divisor `4m`.

Finally the fixed family `E(k)=P_(k+1)` has a `Regularity` certificate with
parameters `(p,v1,v0,vt,tauInf)=(1/2,1/4,1/4,0,0)`. Unfolded, this means
all of the following, without further hypotheses:

* `N_k=n1_k+n0_k -> infinity`;
* eventually `n1_k>=2` and `n0_k>=2`;
* `0<p<1`;
* `n1_k/N_k -> p`;
* the full-population variances of `Y1_k`, `Y0_k`, and `Y1_k-Y0_k` tend
  to `v1,v0,vt`, respectively;
* `mean(Y1_k)-mean(Y0_k) -> tauInf`;
* there is a real `B>=0` such that for every `k`,
  `sum_i(Y1_k(i)^4+Y0_k(i)^4)/N_k <= B`.

The docstring says that these witnesses refute the unrestricted reading
allowing labelled and fixed-covariate statistics, and describes the masses,
moments, and regularity certificate. It also says usual measure-theoretic
conditions hold automatically. The Lean proposition is an explicit
nonfactorization assertion; it contains no separate proposition formalizing
the paper sentence or any test-inference comparison.

Junk-value/domain audit:

* All support sets in the asserted examples are nonempty (six assignments
  at four units, and `binomial(4m,2m)>0` for `m>0`). The uniform-mass
  function is `1/|D|` on `D` and zero elsewhere. Although a generic empty
  support would have `1/0=0` internally, no example uses one.
* Every arm has at least two units, every population has at least four, and
  every denominator `2m`, `4m`, `4m-1` used under `m>0` is positive.
  The fixed sequence starts at `m=k+1`, avoiding `m=0`.
* `RepeatedMomentsW1` can be formed at `m=0`, where means and moments are
  totalized and its claimed mean equalities would fail. The theorem asserts
  it only under `0<m`; its standalone definition is not an unconditional
  theorem about zero blocks.
* For a generic empty finite set, mean is `0/0=0`; for a singleton,
  sample variance is `0/0=0`. These cases do not occur in the witnesses or
  the regularity family here. In `Regularity` generally the arm condition
  holds only eventually, but in this particular family it holds always.
* The bijection is a classical choice of a genuine equivalence, not a
  partial map or a default-valued relabeling. All quantities asserted of
  the relabeled population are invariant under that choice.
* Natural arithmetic in the sizes and cardinalities is nonnegative and
  exact; count-table subtraction occurs in the integers. Nonfactorization
  quantifies over total real functions, with no integrability premise
  needed on these finite domains.
* Limits are ordinary `Filter.Tendsto` limits, not real-valued limsup of an
  unbounded sequence. There are no integrals, `toReal`, extrema, logs,
  square roots, or noninteger powers in the statement closure.

## SAP.P053.T3

There are no external parameters or hypotheses. The first part fixes the
six-unit Boolean outcome vector `y6=(1,1,1,0,0,0)` and considers every
three-element subset `D6` of the six units. For any fixed binary vector,
the statistic is
`t_y(s)=a_y(s)/n1-(M_y-a_y(s))/n0`, where `a_y(s)` and `M_y` are filtered
finite-set success counts. For `y6`, the statement asserts the counts
`|{s in D6:a_y6(s)=a}|=(1,9,9,1)` for `a=0,1,2,3` and
`t_y6(s)=(2a_y6(s)-3)/3` for every `s in D6`.

For a finite index type and integer treatment size `k`, the inclusive upper
tail is the exact finite-count ratio

`p_T(z)=|{w in D_k : T(z)<=T(w)}|/|D_k|`,

where `D_k` is the set of all `k`-element subsets of the carrier. At
`z6={0,1,2}`, the theorem asserts

* `|D6|=20`, `z6 in D6`, `t_y6(z6)=1`;
* `p_t(z6)=1/20`, `p_abs(t)(z6)=1/10`;
* `p_t(z6)<=1/20`, and it is not the case that
  `p_abs(t)(z6)<=1/20`.

The four-unit part fixes `y4=(1,1,0,0)`, the six two-element subsets `D4`,
`z_top={0,1}`, and `z_bottom={2,3}`. It asserts

* `|D4|=6`, both specified subsets belong to `D4`,
  `t_y4(z_top)=1`, and `t_y4(z_bottom)=-1`;
* at `z_top`, `p_t=1/6`, `p_abs(t)=1/3`;
* at `z_bottom`, `p_t=1`, `p_abs(t)=1/3`;
* for every `z in D4` with `z!=z_top` and `z!=z_bottom`,
  `t_y4(z)=0`, `p_t(z)=5/6`, and `p_abs(t)(z)=1`.

The last conjunct is universal. Choose natural `n1,n0`, assume `n1>0` and
`n0>0`, then choose an arbitrary real vector
`y:Fin(n1+n0)->R` and an arbitrary total function `g:R->R`. For subsets
`z` put `T(z)=mean_z(y)-mean_(z complement)(y)`, where
`mean_s(y)=sum_{i in s} y(i)/|s|`. Assume `g` is strictly increasing on
the finite set `{T(z):z in D_n1}`: for any two elements of that image,
`a<b` implies `g(a)<g(b)`. Then for every `z in D_n1`, the exact
inclusive upper-tail ratios satisfy `p_(g o T)(z)=p_T(z)`.

The docstring describes the absolute/signed difference examples and the
preservation of their inclusive upper tails under strictly increasing
transformations. The statement says nothing about equality of the tails
under arbitrary, nonmonotone transformations.

Junk-value/domain audit:

* Real division by zero would yield zero. Every design in an asserted
  p-value has a positive number of assignments, and every mean actually
  used by the universal conclusion has a positive arm cardinality.
* In the definition of `T`, values on arbitrary empty or full subsets
  would use the empty mean `0/0=0`; only the positive-size supported arms
  and their complements enter either the hypothesis image or conclusion.
* The observed sets in the examples are explicitly supported. In the
  universal part `z` is explicitly supported. No assertion relies on
  interpreting an unsupported observed assignment.
* Absolute value is the usual real absolute value; it has no undefined
  case. Strict monotonicity is required only on the attainable image,
  and ties in the upper-tail test are included on both sides.
* Finite vector indices have positive modulus (4 and 6). All auxiliary
  proofs in the closure just certify their numeral instances and
  rational denominators. There are no natural subtractions in these
  definitions, integrals, `toReal`, extrema, logs, square roots, real
  powers, partial functions, limsup, or liminf.

## SAP.P053.T4

Choose real `p,S1,S0`, in that order, and assume in sequence
`0<p`, `p<1`, `0<=S1`, `0<=S0`. The conclusion is the conjunction

`(S0^2/p+S1^2/(1-p))-(S1^2/p+S0^2/(1-p))`
`=((S1^2-S0^2)*(2p-1))/(p*(1-p))`

and

`S1^2/p+S0^2/(1-p) < S0^2/p+S1^2/(1-p)`
iff
`(1/2<p and S0<S1) or (p<1/2 and S1<S0)`.

These are statements solely about real scalars, not about separately
quantified populations, variances, estimators, or limits. The parameters
`S1,S0` have the mathematical domain of nonnegative standard deviations;
the docstring interprets the two expressions as variance-limit coefficients.
No SAP definition beyond `T4Statement` remains after the displayed formula.
The shared auxiliary declaration in its closure only supplies the
`AtLeastTwo` numeral instance for division by two.

Junk-value/domain audit: `p`, `1-p`, and `p*(1-p)` are strictly positive.
Real division by zero is therefore excluded. Zero standard deviations and
`p=1/2` are allowed and yield genuine equality cases. Squares are natural
powers in the reals. There are no casts, index types, truncated subtraction,
integrals, extrema, logarithms, roots, real powers, or limit operators.

## SAP.P053.T5

Quantifier order: choose an arbitrary sequence `E:N->Population`, then
real parameters `p,v1,v0,vt,tauInf`; assume `Regularity E p v1 v0 vt
tauInf`; conclude five asymptotic assertions.

A `Population` consists exactly of natural numbers `n1,n0` and two fixed
real functions `Y1,Y0:Fin(n1+n0)->R`. Its size is `N=n1+n0`. At each
index `k`, the complete design `D_k` consists of all `n1_k`-element
subsets of `U_k=Fin N_k`. For any event `A` of assignments its probability
is the real number

`Pr_k(A)=|{z in D_k : A(z)}|/|D_k|`.

For a finite subset `s` and real vector `f`, set
`m_s(f)=sum_{i in s}f(i)/|s|`,
`SS_s(f)=sum_{i in s}(f(i)-m_s(f))^2`, and
`V_s(f)=SS_s(f)/(|s|-1)`, with the subtraction in the reals.
Population mean and variance are `m_U` and `V_U`. Put

* `tau_k=m_U(Y1_k)-m_U(Y0_k)`;
* `d_k(i)=Y1_k(i)-Y0_k(i)`;
* `S1k2=V_U(Y1_k)`, `S0k2=V_U(Y0_k)`;
* `Yobs_z(i)=Y1_k(i)` if `i in z`, else `Y0_k(i)`;
* `RSS_k(z)=SS_z(Yobs_z)+SS_(U\z)(Yobs_z)`;
* `VF_k(z)=N_k*V_U(Yobs_z)/(n1_k*n0_k)`;
* `VO_k(z)=RSS_k(z)/(N_k-2)*(1/n1_k+1/n0_k)`.

All sums are literal finite sums, all displayed ratios and variances are
real, and `U\z` is finite-set complement in `Fin N_k`.

The assumed `Regularity` structure is exactly the simultaneous list:

1. `N_k -> infinity` in the natural `atTop` filter.
2. Eventually, both `n1_k>=2` and `n0_k>=2`.
3. `0<p` and `p<1`.
4. `n1_k/N_k -> p` as a real sequence.
5. `S1k2 -> v1`, `S0k2 -> v0`, `V_U(d_k) -> vt`.
6. `tau_k -> tauInf`.
7. There exists a real `B>=0` such that for every natural `k`,
   `sum_{i in U_k}(Y1_k(i)^4+Y0_k(i)^4)/N_k <= B`.

There are no assumed estimator limits, independence conditions beyond the
uniform complete design, positive variance limits, or positive estimated
variances. The real limits are finite by their types.

For a varying real assignment statistic `X_k(z)`, the notation
`InProbability E X c` means exactly: for every real `epsilon>0`, the
sequence `Pr_k(epsilon<|X_k(z)-c|)` tends to zero.
`LittleOInvSize E X` means this same statement for `N_k*X_k(z)` and
`c=0`. Thus it is `X=o_P(1/N_k)` under the uniform designs, allowing a
different finite assignment space at every `k`.

With `L=v1/(1-p)+v0/p`, the five conclusions, in order, are:

1. `VF_k(z)-(S1k2/n0_k+S0k2/n1_k+tau_k^2/N_k)=o_P(1/N_k)`.
2. `VO_k(z)-(S1k2/n0_k+S0k2/n1_k)=o_P(1/N_k)`.
3. `N_k*(VF_k(z)-VO_k(z))-tau_k^2 -> 0` in probability.
4. `N_k*VF_k(z) -> L+tauInf^2` in probability.
5. `N_k*VO_k(z) -> L` in probability.

The parameter `vt` is used in the hypotheses but deliberately absent from
these limiting coefficients. The docstring calls `Regularity` S5 and
describes the first three assertions as three first-order expansions,
followed by two scaled probability limits.

Junk-value/domain audit:

* Lean's field division uses `a/0=0`. A generic population may have empty
  arms or `N<=2`. `Regularity` excludes all such cases eventually, so the
  asserted limits use genuine positive denominators `n1,n0,N,N-1,N-2`
  after finitely many indices. `0<p<1` also makes `p` and `1-p` positive.
* Before that eventual range, empty means are `0/0=0`, singleton variances
  are `0/0=0`, and zero residual divisors or arm sizes are totalized. Empty
  sums are zero. These affect at most a finite prefix and hence no
  `Tendsto` conclusion. The all-index fourth-moment bound is also
  totalized at `N=0`; an empty population contributes zero there.
* The assignment support is nonempty for **every** population, even
  degenerate ones: `n1<=n1+n0` ensures a subset of the required size exists.
  In particular, at `N=0` the support is the singleton containing the
  empty assignment. Its probability denominator is never zero.
* Subtraction in `N-1`, `N-2`, centered residuals, and probability errors
  is real subtraction, with no natural truncation. Natural counts and
  sizes are cast exactly to the reals. All vector indexing is total on
  the dependent finite carrier.
* There are no Bochner integrals, means over nonintegrable functions,
  `ENNReal.toReal`, empty or unbounded extrema, logarithms, square roots,
  noninteger powers, limsup, liminf, or partial-function defaults in this
  closure. In particular this theorem does not divide by an estimated
  variance and needs no positivity assumption on it.

