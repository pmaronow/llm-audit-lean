# Blind reading

This file was written and saved before opening `claims.json` or `record.json`.
I read `closure.json`, both Challenge files, `Defs.lean`, and all five Defs
parts. Each closure entry was read in its source. The source-less generated
entries, the SurveyModel constructor, and the stratum decidability instance
were also printed by `scratch/BlindPrint.lean` (successful compilation).
The generated entries are ordinary positive-numeral/finite-index instances,
one scalar-tower instance, and an exhaustive Option eliminator. They introduce
no mathematical hypotheses or extra axioms.

## SAP.P034.T1

Location: `SAP/P034/Challenge/Part1.lean:6-14`.
This is a closed conjunction about two fixed, explicitly defined finite
probability distributions and a fixed frequency table. It has no hypotheses.

### Objects and definitions unfolded

`SurveyModel Ω K k` is a record of four completely arbitrary functions:
`T : Ω → Bool`, `Y : Bool → Ω → K`, `R : Bool → Ω → Bool`, and
`X : Ω → (Fin k → K)`. Its constructor and four projections just package
these functions. The realized outcome is `Y (T ω) ω` and the realized
completion is `R (T ω) ω`. In this section numerical values are rational
unless explicitly declared real. Identify Bool false/true with 0/1; the
function `bitQ` is precisely this identification.

For a finite type Ω and a rational weight function w, the definitions mean

* `P_w(E) = ∑_{ω∈Ω} if E(ω) then w(ω) else 0`;
* `E_w[f] = ∑_{ω∈Ω} w(ω)f(ω)`;
* `P_w(E | F) = P_w(E∩F)/P_w(F)`;
* `E_w[f | E] = (∑_{ω∈Ω} if E(ω) then w(ω)f(ω) else 0)/P_w(E)`.

These definitions do not themselves require normalized or nonnegative
weights. Independence of f and g means, for every value a of f's codomain
and every value b of g's codomain,
`P_w(f=a,g=b)=P_w(f=a)P_w(g=b)`. Conditional independence given E means
the same factorization with each probability conditioned on E. Their
codomains in this statement are finite Boolean products, so singleton-cell
factorization is the usual full independence condition.

World A is the 32-element type `Fin 5 → Bool`. Write its coordinates as
`(u,r₀,r₁,x,t)`. Put `p_s(u)=37/50` if s=u, and `13/50` otherwise, and
`B(p,r)=p` if r=true, `1-p` otherwise. Its point mass is
`w_A=(1/8)B(p_0(u),r₀)B(p_1(u),r₁)`. Its model is
`T=t`, `Y(0)=Y(1)=u` in rational coding, `R(0)=r₀`, `R(1)=r₁`, and
the sole covariate `X(0)=x` in rational coding. Its potential-variable
bundle is the Boolean tuple `(u,u,r₀,r₁,x)`. Its effect is
`τ_A=E_A[Y(1)-Y(0)]`. Its respondent arm mean is
`m_t=E_A[Y(T) | T=t,R(T)=true]`.

For each Boolean triple (t,x,y), its stratum is
`{T=t, X(0)=bitQ(x), Y(T)=bitQ(y)}`. The explicit decidability instance
only decides these rational and Boolean equalities.

The three design coordinates in A are `Z=(1,bitQ(T),X(0))`.
The matrix and vector called worldAGram and worldARhs are respectively
`G_A(i,j)=E_A[Z_i Z_j | R(T)=true]` and
`h_A(i)=E_A[Z_i Y(T) | R(T)=true]`, i,j in Fin 3.
The fixed comparison data are

```
G* = [[1,   1/2, 1/2],
      [1/2, 1/2, 1/4],
      [1/2, 1/4, 1/2]],
h* = (1/2,37/100,1/4),    β* = (13/50,12/25,0).
```

An observed cell is an element of `Bool × Bool × Option Bool`, written
`(t,x,o)`. In A it is `(t,x,some u)` when `R(T)=true` and `(t,x,none)`
otherwise. Thus the completion indicator is recoverable from whether the
Option is present. Define the integer multiplicity n(t,x,o) as 50 for
`o=none`, 37 for `o=some y` with t=y, and 13 for `o=some y` with t≠y.
The sample's rational count `N(t,r)` sums these multiplicities over cells
with treatment t and with `o.isSome=r`. Its expected count is
`e(t,r)=(∑_s N(t,s))(∑_s N(s,r))/(∑_c n(c))`.
Its Pearson statistic is `S=∑_t∑_r (N(t,r)-e(t,r))²/e(t,r)`.
For any real s, the specified chi-square-one tail probability is
`Q(s)=(gaussianReal 0 1)({z:ℝ | s≤z²}).toReal`. Mathlib's Gaussian
parameter 1 is its variance, so this is the square of a standard normal.

The sample design is `z(c)=(1,bitQ(t),bitQ(x))`. The sample matrix is
`G_s(i,j)=∑_{c with o.isSome} n(c)z_i(c)z_j(c)` and its right-hand side
is `h_s(i)=∑_{c=(t,x,some y)} n(c)z_i(c)bitQ(y)`. Missing records
contribute zero to both; no default outcome is substituted. The real
versions of G*, h*, β*, G_s, and h_s are entrywise rational-to-real casts.
Matrix multiplication by a vector means the usual finite sum over its
three coordinates.

World B is the 64-element type `Fin 6 → Bool`, with coordinates
`(y₀,y₁,r₀,r₁,x,t)` and masses
`w_B=B(13/50,y₀)B(37/50,y₁)/16`. Its model is
`T=t`, `Y(s)=bitQ(y_s)`, `R(s)=r_s`, and `X(0)=bitQ(x)`.
Its observed cell is `(t,x,some y_t)` on completion and `(t,x,none)`
otherwise.

### Entire conjunction and quantifier order

1. A's masses sum to 1 and every mass is strictly positive. Treatment is
   independent of `(u,u,r₀,r₁,x)` and `P_A(T=true)=1/2`. At every point
   `Y(1)-Y(0)=0`, and `τ_A=0`.
2. For every Boolean t, `P_A(R(T)=true | T=t)=1/2`. For every Boolean
   t,x,y, the (t,x,y) stratum has positive mass, and the probability of
   completion conditioned on it is exactly p_t(y).
3. For every Boolean t,x, `R(T)` and u fail conditional independence given
   `{T=t,x=x}`. Also R(0) and u fail unconditional independence.
4. Each event `{T=t,R(T)=true}` has positive mass. The arm means are
   `m_0=13/50`, `m_1=37/50`, their difference is `12/25`, and this
   difference is unequal to τ_A.
5. `G_A=G*`, `h_A=h*`, `det(G*)=1/16`, and `G*β*=h*`.
   The treatment coordinate β*_1 is `12/25` and is unequal to τ_A.
6. For every real vector β indexed by Fin 3,
   `G*_{ℝ}β=h*_{ℝ} ↔ β=β*_{ℝ}`. This gives existence and uniqueness
   over all real coefficients, not just rational ones.
7. The sum of all sample multiplicities is 400 and the sum for present
   outcomes is 200. For every t,x the missing count is 50. For every x,
   the counts `(0,x,some 1)`, `(0,x,some 0)`, `(1,x,some 1)`,
   `(1,x,some 0)` are respectively 13,37,37,13. Every observed cell has
   positive A probability. For every Boolean t,r, `N(t,r)=e(t,r)=100`.
   `S=0`, `G_s=200G*`, and `h_s=200h*`.
8. `Q((S:ℝ))=1` and it is not less than the real number 5/100.
   For every real vector β indexed by Fin 3,
   `G_{s,ℝ}β=h_{s,ℝ} ↔ β=β*_{ℝ}`.
9. B's masses sum to 1 and all are positive. Treatment is independent of
   `(y₀,y₁,r₀,r₁,x)`, with `P_B(T=true)=1/2`. The completion pair
   `(r₀,r₁)` is independent of `(y₀,y₁,x,t)`. The B effect is `12/25`.
   For every observed cell c its probability in A equals its probability
   in B. For every t,x the missing cell has A probability 1/8. For each
   x the four present cells in the order above have A probabilities
   13/400,37/400,37/400,13/400.

The sample is encoded by frequencies, not an ordered list or an explicit
product-measure event. Full support of A's observed-cell law means that an
ordered independent 400-draw realization having these frequencies does have
positive probability; this inference is not itself a conjunct.

### Junk-value audit

Rational and real division are total, with inverse zero equal to zero.
Although the generic finite conditional functions would return zero on
zero-mass conditioning events, all events used here have positive mass:
the treatment events and (t,x) events have mass 1/2 and 1/4, the (t,x,y)
strata have mass 1/8, completed arms have mass 1/4, and overall completion
has mass 1/2. Some of these positive numbers follow directly from the
specified law rather than appearing as separate conjuncts. The sample
total is 400 and all its Pearson expected counts are 100. No division
here uses a zero denominator. All subtractions in the statistics, effects,
and Bernoulli masses are in ℚ or ℝ, not truncated natural subtraction.

`toReal` sends infinite extended nonnegative values to zero in general,
but the Gaussian is a probability measure, so the tail mass is finite.
Its variance is strictly positive; no degenerate Gaussian branch is used.
All rational-to-real and natural-to-rational casts are exact. Fin indices
are bounded, all Option cases are explicit, and no empty index type occurs
in these finite calculations. No logarithm, square root, real power,
Bochner integral, supremum/infimum, limit superior/inferior, or partial
function default appears in this statement. The finite probability
definitions are used with genuine positive normalized weights, rather
than arbitrary signed weights.

## SAP.P034.T2

Location: `SAP/P034/Challenge/Part1.lean:16-22`.
This theorem is universally quantified first over a type Ω and its
measurable-space structure. Its expanded proposition then quantifies over
`k:ℕ`, a measure μ on Ω, a proof that μ is a probability measure, and a
model M with `T:Ω→Bool`, `Y_t:Ω→ℝ`, `R_t:Ω→Bool`, and
`X:Ω→(Fin k→ℝ)`. The finite vector has the usual finite-dimensional
function norm and product Borel measurable structure. The intercept and
treatment index set is `Fin 2 ⊕ Fin k`; its two left indices are the
intercept (0) and treatment (1). No finite sample-space assumption is made.

### Hypotheses, in order

1. T is measurable.
2. For every Boolean t, Y_t is measurable.
3. For every Boolean t, R_t is measurable.
4. X is measurable.
5. For every Boolean t, `MemLp Y_t 2 μ`.
6. `MemLp X 2 μ`. These L² conditions mean almost-everywhere strong
   measurability and finite second moment of the absolute value/norm.
7. T is independent of the full vector `(Y_0,Y_1,R_0,R_1,X)` under μ.
   Mathlib's `IndepFun` is independence of the two generated sigma
   algebras; for these measurable functions it is factorization of
   probabilities of inverse images of arbitrary measurable sets.
8. `0 < μ.real({T=true}) < 1`.
9. For every Boolean t, R_t is independent of `(Y_0,Y_1,X)` under μ,
   and `μ.real({R_t=true})>0`. No independence of R_0 and R_1 from one
   another is assumed.

All these premises precede a conclusion containing both the identification
conjunction and a fixed, parameter-independent finite counterexample.

### Definitions and complete identification conclusion

Write `Y=Y_T`, `R=R_T`, `C={R=true}`, `C_t={T=t,R=true}`,
`P(E)=(μ(E)).toReal`, and `E[f]=∫_Ω f dμ` (real Bochner integral).
For an event E the conditional measure is exactly
`μ_E=(μ(E))⁻¹ • (μ.restrict E)`, where inverse and scalar multiplication
are over the extended nonnegative reals. Conditional means and
probabilities are explicitly `E[f|E]=(∫_E f dμ)/P(E)` and
`P(A|E)=P(A∩E)/P(E)`, with division in ℝ. Define
`τ=∫(Y_1-Y_0)dμ`, `p=P(T=true | C)`, and
`Z=(1,bitR(T),X)`, where bitR maps false/true to real 0/1.
Define `G(i,j)=E[Z_i Z_j|C]` and `h(i)=E[Z_i Y|C]`.

The conclusion asserts all of the following, in this order:

1. For every Boolean t,
   `P(C_t)=P(T=t)P(R_t=true)` and `P(C_t)>0`.
2. `0<p<1`.
3. For every Boolean t, `E[Y|C_t]=∫Y_t dμ`.
4. `E[Y|C_true]-E[Y|C_false]=τ`.
5. For every Boolean t, the pushforward measure of X under μ_{C_t}
   equals its pushforward under μ. This is equality of full covariate
   distributions, not just equality of means.
6. For every j in Fin k, `E[(bitR(T)-p)X_j|C]=0`.
7. For every real coefficient vector β indexed by `Fin 2 ⊕ Fin k`, if
   `Gβ=h`, then its treatment coordinate `β(Sum.inl 1)=τ`.
8. If `IsUnit(det G)`, equivalently det G≠0 in ℝ, there exists exactly
   one such real coefficient vector solving `Gβ=h`.

Matrix-vector multiplication in the last two clauses is a finite sum
over all k+2 coordinates. These clauses concern normal equations; no
minimization operator or inverse of a possibly singular matrix is used.

### Entire fixed counterexample conjunct unfolded independently

There is additionally a fixed 32-point rational model, independently of
Ω, μ, k, and M. Its points are `(u,r₀,r₁,x,t)∈{false,true}^5`, with
weight `(1/8)B(p_0(u),r₀)B(p_1(u),r₁)`, where
`p_s(u)=37/50` when s=u, `13/50` otherwise, and `B(p,r)` is p or 1-p
according as r is true or false. Its assignments are `T=t`,
`Y_0=Y_1=bitQ(u)`, `R_0=r₀`, `R_1=r₁`, and `X_0=bitQ(x)`;
bitQ has rational values 0/1. For this finite model, probabilities are
sums of weights, expectations are sums of weight times value, event
conditioning divides joint weighted sums by the conditioning-event mass,
and independence means factorization of every pair of singleton cells.

The fixed conjunct asserts treatment's independence of `(u,u,r₀,r₁,x)`;
for every Boolean t the conditional completion rate given T=t is 1/2;
R_0 is not independent of u; R_0 is not independent of `(u,u,x)`;
`τ_A=∑w_A(Y_1-Y_0)=0`; and `G_Aβ*=h_A`, where
`G_A(i,j)=E_A[Z_iZ_j|R_T=true]`,
`h_A(i)=E_A[Z_iY_T|R_T=true]`, `Z=(1,bitQ(T),bitQ(x))`, and
`β*=(13/50,12/25,0)`. Finally `β*_1=12/25` and `β*_1≠τ_A`.
These are concrete failures of the independence premise and unbiased
coefficient inference, not assumptions that the general model is this
finite example. The counterexample is conjoined after all general-model
hypotheses; it is not a separately unconditional top-level conjunct.

### Junk-value audit

`μ.real E` means `(μ E).toReal`; its infinite-value convention cannot
intervene because μ is a probability measure. Event conditional means
and probabilities would be zero for zero denominators. Both completed
arms are proved positive, hence their union C is positive; the primitive
treatment and potential-completion events are positive by the premises
and probability-one total mass. Thus every conditioned event in the
identification conclusions has positive finite mass. Normalizing a
zero-mass event by extended-real inverse would not yield its intended
probability measure (in particular ∞ times zero remains zero), but this
case is excluded here.

Mathlib's real Bochner integral returns zero for nonintegrable functions.
The L² hypotheses on both potential outcomes and the finite-dimensional
covariate vector imply L¹ integrability on this probability space, on
measurable restrictions, and for all products appearing in G and h by
Cauchy–Schwarz. The realized Y is a measurable two-piece combination of
the L² outcomes. Treatment is bounded. Consequently this convention
does not produce the claimed conclusions. The covariate maps and events
are measurable, so map/restrict also have their ordinary meanings rather
than a default for a nonmeasurable input.

The finite counterexample has positive normalized weights by its explicit
formula. Its treatment events have probability 1/2 and overall completion
has probability 1/2; these are nonzero denominators independently of the
general model. All finite subtractions are rational. The case k=0 is
allowed: X is then the unique empty vector, the covariate orthogonality
clause is empty, and the regression still has its two intercept/treatment
coordinates. If Ω were empty there could be no probability measure;
this does not make the universal theorem vacuous on nonempty Ω.
There are no logs, roots, out-of-domain powers, extrema, sequence
limits, truncated subtraction, or partial-function defaults.

## SAP.P034.T3

Location: `SAP/P034/Challenge/Part1.lean:24-28`.
This is a closed conjunction, with no premises or data parameters.
In general the fitted function is the polynomial
`m(w,v,z)=a+bw+cv+dwv+∑_{j∈Fin k}γ_jz_j`, with real coefficients,
real w,v, and two finite real vectors γ,z. In this statement k=0 and
both vectors are zero, so its finite sum is exactly the empty sum 0.
The cell function on Boolean pairs is `f(w,v)=2` if both are true and
0 otherwise; its four entries are (0,0,0,2).

First, for every real a,b,c,d, fitting
`a+b bit(w)+c bit(v)+d bit(w)bit(v)=f(w,v)` for every Boolean w and
then every Boolean v is equivalent to
`a=0 ∧ b=0 ∧ c=0 ∧ d=2`. (The Boolean-to-real coding is an explicit
if-then-else 0/1.) This biconditional states existence as well as
uniqueness of the interpolating coefficients. It is followed by

* `f(1,0)-f(0,0)=0`;
* `(1/2)(f(1,0)-f(0,0))+(1/2)(f(1,1)-f(0,1))=1`;
* `f(0,1)-f(0,0)=0`;
* `(1/2)(f(0,1)-f(0,0))+(1/2)(f(1,1)-f(1,0))=1`;
* the real inequality `0≠1`.

Thus both main coefficients/reference contrasts vanish, whereas both
equally weighted contrasts are 1. The statement concerns a constructed
interpolation example, without a probability model or empirical outcome
claim. Its docstring describes separation from a reading of printed row
labels rather than an unconditional falsification of the printed text.

Junk values: division occurs only by the nonzero real number 2. All
subtraction is real. Fin 0 is intentional and its empty sum is zero,
which correctly removes the covariate term. The Boolean cell definition
and its generated positive-numeral instance are total. There are no
integrals, infinite casts, logs, roots, real powers, extrema, limits,
other empty domains, or partial-function defaults.

## SAP.P034.T4

Location: `SAP/P034/Challenge/Part1.lean:30-34`.
For every natural k, every real a,b,c,d, and every pair of vectors
γ,z indexed by Fin k with real entries, define the fully specified real
polynomial `m(w,v,z)=a+bw+cv+dwv+∑_{j∈Fin k}γ_jz_j`.
The theorem asserts the following conjunction after those quantifiers;
there are no assumptions on any coefficient or vector:

1. For every real v, `m(1,v,z)-m(0,v,z)=b+dv`.
2. `m(1,0,z)-m(0,0,z)=b`.
3. `m(1,1,z)-m(0,1,z)=b+d`.
4. For every real w, `m(w,1,z)-m(w,0,z)=c+dw`.
5. `m(0,1,z)-m(0,0,z)=c`.
6. `m(1,1,z)-m(1,0,z)=c+d`.
7. For every real q,
   `(1-q)[m(1,0,z)-m(0,0,z)]+q[m(1,1,z)-m(0,1,z)]=b+qd`.
8. For every real p,
   `(1-p)[m(0,1,z)-m(0,0,z)]+p[m(1,1,z)-m(1,0,z)]=c+pd`.
9. For every real q, `b+qd=b ↔ qd=0`.
10. For every real p, `c+pd=c ↔ pd=0`.
11. For every real q, if q>0, `b+qd=b ↔ d=0`.
12. For every real p, if p>0, `c+pd=c ↔ d=0`.

All comparisons hold at the same covariate vector z. In particular q,p
range over all reals in the weighted identities and only have a positive
lower bound in the final implications; there is no p≤1 or q≤1 premise.
These are algebraic identities, including the special case of genuine
probability weights. No data-generating or causal interpretation is
assumed by the actual proposition.

Junk values: all sums are finite and all subtraction/multiplication is
real. With k=0 the sum is 0 and the same identities hold. No division,
nonintegrable mean, infinite-to-real cast, log/root/power domain,
extremum, sequence limit, or partial-function convention is involved.

## SAP.P034.T5

Location: `SAP/P034/Challenge/Part1.lean:36-40`.
This is a closed conjunction of exact arithmetic facts and universal
checks over bounded finite row/column indices. Its definitions contain
these explicit natural-number arrays; rows are numbered 0 through 12,
columns 0 through 2:

```
counts                         tenths of reported percent
(818,777,1595)                  (282,270,276)
(477,475,952)                   (165,165,165)
(281,309,590)                   ( 97,107,102)
(266,268,534)                   ( 92, 93, 92)
(259,240,499)                   ( 89, 83, 86)
(258,240,498)                   ( 89, 83, 86)
(224,252,476)                   ( 77, 88, 82)
(219,214,433)                   ( 76, 74, 75)
(49,19,68)                     ( 17,  7, 12)
(24,25,49)                     (  8,  9,  8)
(9,39,48)                      (  3, 14,  8)
(9,15,24)                      (  3,  5,  4)
(5,4,9)                        (  2,  1,  2)
column totals: (2898,2877,5775)
```

Write c_ij for the first array, n_j for the column totals, and t_ij for
the second array. The exact percentage is the rational
`P_ij=100(c_ij:ℚ)/(n_j:ℚ)`. The rounding predicate for a rational x and
a natural integer h is precisely
`(h:ℚ)/10-1/20 ≤ x ∧ x < (h:ℚ)/10+1/20`.
Thus it rounds to h/10 using a closed lower endpoint and open upper
endpoint, all in rational arithmetic.

The theorem asserts, in order:

1. The natural equalities `266+268=534`, `24+25=49`,
   and `2898+2877=5775`.
2. `P_(3,2)=712/77`; `915/100≤712/77<925/100`;
   this percentage rounds to 92/10 but does not round to 93/10.
3. `P_(9,2)=28/33`; `75/100≤28/33<85/100`;
   this percentage rounds to 8/10 but does not round to 9/10.
4. For every i in Fin 13 and then j in Fin 3, P_ij rounds to t_ij/10.
5. For every i in Fin 13, `c_i0+c_i1=c_i2`.
6. For every j in Fin 3, `∑_{i∈Fin 13}c_ij=n_j`.
7. The natural equality `5775=3*1925`.

The definitions call row 3 character evaluation and row 9 other policies.
They identify columns as no information, information, total, and say the
two Total-column percentages have been corrected. The theorem alone
checks a literal table; source transcription is a separate fidelity
question to be considered after this blind stage.

Junk values: all three percentage denominators are strictly positive
natural numbers (2898,2877,5775) and remain positive under rational casts.
All other rational denominators are explicit positive numerals. The
subtraction in rounding bounds is rational, not truncated natural
subtraction; natural arithmetic is used only for sums and products.
Fin indices keep all array accesses within the displayed tables, with no
fallback/default entry. The index types are nonempty. There are no
integrals, infinities, logs, roots, real powers, extrema, sequence limits,
or partial functions.
