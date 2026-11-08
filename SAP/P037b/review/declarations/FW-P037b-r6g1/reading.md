# Blind reading

This file was written before opening `claims.json` or `record.json`. It records
the elaborated assertions, not an inference about what the paper intended.
Sources read: `closure.json`, both relevant definition modules, the five
docstrings in `Challenge/Part1.lean`, and `scratch/ClosurePrint.log` (compiled
`#print`s of every line-0 closure entry). No canonical claim or architect record
has been consulted at this stage.

All finite matrices below have real entries. Matrix multiplication is finite
summation, `(MN)jl = Σi Mji Nil`; `Mv` and `vᵀw` likewise mean finite sums.
`Fin n` means the integers from 0 through n−1, and `1` for square matrices is
the identity matrix. All scalar divisions are real divisions.

## SAP.P037b.T18

Location: `Challenge/Part1.lean:8–12`; statement:
`Defs/Part1.lean:223–254`. This is a conjunction of four independently
universally quantified assertions. Define, only as notation for the following
fully specified Mathlib operations,

* `A = (XᵀX)⁻¹ Xᵀ` (`olsMap`, line 12),
* `H = XA` (`hatMatrix`, line 15),
* `r(y) = y − XAy` (`olsResidual`, line 18),
* `W(y) = A diag(r(y)i²) Aᵀ` (`hc0Covariance`, line 22),
* `m(v)j = ∫ vj dμ` (`vectorMean`, line 27),
* `Cov(v)jl = ∫(vj−m(v)j)(vl−m(v)l)dμ`
  (`vectorCovariance`, line 31).

1. For every type Ω with a measurable space, every probability measure μ on Ω,
   natural numbers n,k, real n-by-k matrix X, real n-vector y, proof that the
   map `v ↦ Xv` is injective, and function `v : Ω → ℝⁿ`, assume each coordinate
   vi and every product vi vj are μ-integrable, `m(v)=0`, and
   `∫vi vj dμ = 1` if i=j and 0 otherwise. Set `b=Ay` and
   `b*(ω)=A(Xb + (r(y)i vi(ω))i)`. Then for every ω,
   `b*(ω)=b+A(r(y)i vi(ω))i`; its mean is b and its covariance is W(y).
   Independence of the coordinates of v is not assumed; the exact first and
   second moments are assumed. The same X and fixed y are used in the refit.
2. For every n,k,X with `X.mulVec` injective and n>0: H is symmetric and
   idempotent, each diagonal entry lies in [0,1], `Σi Hii=k`, and
   `(Σi Hii)/n=k/n`. No intercept is required.
3. For every measurable Ω, probability μ, n,k,X of full column rank, coefficient
   vector β, real σ²≥0, and `u : Ω → ℝⁿ`, assume each ui and ui uj is
   integrable, `m(u)=0`, and `∫ui uj=σ²` for i=j and 0 otherwise.
   Define `y(ω)=Xβ+u(ω)`, `V=Cov(Ay)`, and
   `EVjl=∫W(y(ω))jl dμ`. Conclude:
   * for every ω, `r(y(ω))=(I−H)u(ω)`;
   * for every i, `∫r(y)i²=σ²(1−Hii)`;
   * `V=σ² AAᵀ=σ²(XᵀX)⁻¹`;
   * `EV=σ² A diag(1−Hii) Aᵀ`;
   * `V−EV=σ² A diag(Hii) Aᵀ`;
   * for every real k-vector t, `tᵀ(V−EV)t≥0`.
   This concerns the expectation of HC0, not a pointwise ordering for every
   sample, and assumes uncorrelated homoskedastic errors, not independence.
4. For every n and real n-vectors a,h, assuming `0≤hi≤1` for every i and
   `Σi ai²>0`, put `R=Σi ai²(1−hi)/Σi ai²`. Then
   `R=1−Σi ai²hi/Σi ai²`, `R≤1`, and
   `R=1 ↔ ∀i, ai≠0 → hi=0`. There is no assertion connecting these arbitrary
   a,h to a particular row of A or to V and EV.

The docstring describes residual multiplier refits, leverage and the positive
semidefinite homoskedastic shortfall. It explicitly drops the connection to R,
an additional sandwich expression, coefficient SE/Wald formulae, and the
interpretation of R as an expected-to-true variance ratio.

Conventions and boundary cases: Mathlib's square-matrix inverse is zero when
the determinant is not a unit (over ℝ, when singular). Here injectivity of X
implies invertibility of XᵀX wherever the inverse is used. A real Bochner
integral is zero for a non-integrable function; the explicit coordinate and
product integrability assumptions, probability normalization, and finite sums
ensure integrability of all the derived coordinates, covariances, squared
residuals and expected HC0 entries. No result depends on the undefined-integral
convention. The fourth denominator is positive and the second denominator is
positive. The other n,k can be zero: empty sums and vectors have their usual
finite-dimensional meanings; full column rank forces k=0 if n=0. The fourth
block has no instance at n=0 because its positive-sum hypothesis fails, but has
ordinary instances for n>0. σ²=0 is allowed. Natural casts are exact. No log,
sqrt, nonintegral power, ENNReal-toReal, infimum, supremum, limsup, liminf,
truncated subtraction or partial function occurs.

## SAP.P037b.T23

Location: `Challenge/Part1.lean:14–18`; statement:
`Defs/Part2.lean:118–139`. This is a closed numerical certificate, with no
premises and no free data. Every sum over i is over `Fin 6`, and every
coefficient/matrix index is in `Fin 3`.

Its data (`Defs/Part1.lean:40–83`) are the real six-vectors

```
s = (14,14,7,7,7,7)                [bandSizes]
t = (0,0,1,1,1,1)                 [bandTreatments]
c = (0,0,0,0,1/5,1/5)             [bandCompositions]
y = (0,1/5,1/10,3/10,2/5,3/5)     [bandOutcomes]
x_i = (1,t_i,t_i c_i)             [bandDesignRow]
b = (1/10,1/10,3/2)               [bandFit]
Ginv = [[1/28,-1/28,0],[-1/28,3/28,-5/14],[0,-5/14,25/7]]
V = [[1/2800,-1/2800,0],[-1/2800,3/2800,-1/280],
     [0,-1/280,1/28]]             [bandHC0]
G_jl = Σi s_i x_ij x_il           [bandDesignGram]
q_j = Σi s_i x_ij y_i             [bandNormalRhs]
M_jl = Σi s_i (y_i−Σj x_ij b_j)² x_ij x_il [bandSandwichMeat]
xc_i = (1,t_i,t_i(c_i−1/10))      [centeredBandRow]
bc = (1/10,1/4,3/2)               [centeredBandFit]
Gcinv = [[1/28,-1/28,0],[-1/28,1/14,0],[0,0,25/7]]
Gc_jl = Σi s_i xc_ij xc_il        [centeredBandGram]
Mc_jl = Σi s_i (y_i−Σj xc_ij bc_j)² xc_ij xc_il [centeredBandMeat]
```

Here Ginv and Gcinv are literal matrices named `bandGramInverse` and
`centeredBandGramInverse`; their inverse property is a conclusion to be
checked, not a definition by assertion. Likewise b and V are candidate values
whose normal equations and sandwich identities are conclusions.

The assertions, in order, are:

1. `Σs=56`, `Σs_i t_i=28`, `Ginv G=I`, `Gb=q`,
   `|y_i−x_iᵀb|=1/10` for every i, and `Ginv M Ginvᵀ=V`.
2. `(1,0,0)ᵀb=1/10`, `(1,1,1/10)ᵀb=7/20`.
   The helper `linearPredictionVariance V l` is exactly `lᵀVl`.
   At `l0=(1,0,0)` and `l1=(1,1,1/10)` these forms both equal 1/2800;
   at `d=(0,1,1/10)` it equals 1/1400.
   The cross form `l0ᵀVd=−1/2800`.
   The arithmetic expression `((28/100)/27)/56=1/5400`;
   `1/1400>1/2800`, `1/5400<1/2800`,
   `(1/5400)/(1/2800)=14/27`, and `((28/100)/27)/28≠1/2800`.
   No separate assertion defines 28/100 as a residual sum of squares or proves
   the residual-control sample mean/sample variance.
3. `Gcinv Gc=I`, `Gc bc=(Σi s_i xc_ij y_i)j`, and
   `xc_iᵀbc=x_iᵀb` for every i. The (1,1) entry of
   `Gcinv Mc Gcinvᵀ` equals 1/1400 (indices start at 0).

The docstring describes the exact 56-school fit and these named variances. Its
restriction drops explicit rank, difference/decomposition equations, separate
residual-control mean/sample-variance certificates, sqrt interval widths and
identification of plotting code.

Conventions and boundary cases: all vector/matrix dimensions are fixed and
positive, all denominators are fixed nonzero positive integers, and all sums
are finite. The hard-coded inverse candidates are justified by product
identities; no singular-inverse convention is used. Group sizes are real
numbers rather than natural multiplicities, but these particular values are
positive integers. Matrix/vector literal indexing is over the correct `Fin`
type; no out-of-bounds/default lookup occurs. There are no integrals, roots,
logs, real powers, infinities, extrema, asymptotic extrema or partial functions.

## SAP.P037b.T24

Location: `Challenge/Part1.lean:20–24`; statement:
`Defs/Part2.lean:142–172`. There are three independent universal assertions.

1. For every natural p, real vector zbar indexed by `Fin p`, real coefficient
   vector b indexed by the disjoint union `Fin 3 ⊕ Fin p`, and real c, define
   `l0=(1,0,0;zbar)` and `l1=(1,1,c;zbar)`; the semicolon denotes the
   `Sum.elim` function with the displayed values on the two summands.
   Then `l0ᵀb=b_inl0+Σj zbar_j b_inrj`,
   `l1ᵀb=b_inl0+b_inl1+c b_inl2+Σj zbar_j b_inrj`, and
   `l1ᵀb−l0ᵀb=b_inl1+c b_inl2`.
2. For every natural k, real k-by-k matrix V satisfying `Vᵀ=V`, and real
   k-vectors l0,d: `(l0+d)ᵀV(l0+d)=l0ᵀVl0+dᵀVd+2 l0ᵀVd` and
   `(l0+d)ᵀV(l0+d)=dᵀVd ↔ l0ᵀVl0+2 l0ᵀVd=0`.
   Symmetry alone is required; positive semidefiniteness is not a premise.
3. For every natural n,p, real n-vectors T,C,y, real n-by-p covariate matrix z,
   and real c, build n-by-(3+p) matrices with rows
   `X_i=(1,T_i,T_i C_i,z_i)` and
   `Xc_i=(1,T_i,T_i(C_i−c),z_i)`.
   Their implementation uses columns 0,1,2, and column `j−3` of z for j≥3.
   Set `b=(XᵀX)⁻¹Xᵀy`, `bc=(XcᵀXc)⁻¹Xcᵀy`,
   `r=y−Xb`, `rc=y−Xc bc`, and
   `V=(XᵀX)⁻¹Xᵀ diag(r_i²) X((XᵀX)⁻¹)ᵀ`.
   Assuming `v ↦ Xv` injective, conclude
   `Xc bc=Xb`, `rc=r`, `bc_1=b_1+c b_2`, and
   `HC0(Xc,y)_11=V_11+2c V_12+c² V_22`, where HC0 is exactly
   the same matrix product with Xc and rc. These are coefficients, residuals
   and HC0 matrices computed from the same fixed sample.

The docstring describes prediction rows, a contrast and its variance,
symmetry-based decomposition/equality, and full-rank same-sample recentering.
It drops interval endpoints, realized variance-ordering examples,
residual-control failures/certificate, explicit centered-variance prediction
form identification and plotting-routine verification.

Conventions and boundary cases: the first two blocks allow p=0 or k=0;
empty sums are zero and the formulas have their standard meanings. In the
third block, 3+p is at least three; n=0 is incompatible with its full-rank
premise. X has full column rank and recentering is an invertible change of
columns, so both Gram inverses are genuine. The natural subtraction j−3 is
truncated in Lean, but is evaluated as a covariate index only after j≠0,1,2,
which implies j≥3. Bounds are proved by the generated `_proof_4`; `_proof_5`
and `_proof_6` certify that coefficient indices 1 and 2 are valid. There is no
unchecked/default lookup. No integrals, scalar division, real powers, roots,
logs, infinities or order-extremum convention occurs in this statement beyond
the matrix inverse described above. T is any real vector, not restricted to
Boolean treatment; the reparameterization identities do not require Boolean T.

## SAP.P037b.T19

Location: `Challenge/Part1.lean:26–30`; statement:
`Defs/Part2.lean:14–35`. Its concrete four-unit model uses
`i : Fin 4`, `z : Fin 6`, and these definitions (`Defs/Part1.lean:97–124`):

* the outcome screen is `Y>1/50`;
* treated sets R_z, in order, are `{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}`;
* `Y_i(t)=3 i/100 + (3/100 if t=true, else 0)`;
* observed `Y_i(z)=Y_i(i∈R_z)`, with membership converted to a Bool;
* `K_z={i∈{0,1,2,3}:Y_i(z)>1/50}`;
* `KT_z=K_z∩R_z`, `KC_z=K_z\R_z`;
* `δ_z=Σi∈KT_z Y_i(z)/|KT_z|−Σi∈KC_z Y_i(z)/|KC_z|`;
* `w_z=|KT_z||KC_z|/(|KT_z|+|KC_z|)`;
* for natural B and any `z : Fin B → Fin 6`,
  `b_B(z)=Σb w_(z_b) δ_(z_b)/Σb w_(z_b)`.

The theorem is a conjunction of:

1. For every i, `Y_i(true)−Y_i(false)=3/100`; for every z,i,
   `i∈K_z ↔ i≠0 or 0∈R_z`; for each z, `|KT_z|=2` and the vector
   of `|KC_z|` is `(2,2,2,1,1,1)`. The δ vector is
   `(-3/100,0,3/100,-3/200,3/100,3/40)` and w is
   `(1,1,1,2/3,2/3,2/3)`. Their uniform-six-state moments satisfy
   `Σδ/6=3/200≠3/100`, `Σw/6=5/6`, `Σwδ/6=1/100`,
   `(1/100)/(5/6)=3/250≠3/100`.
2. For every real ε>0, as natural B tends to infinity,
   `Σ(z∈{0,…,5}^B) (1/6)^B 1{|b_B(z)−3/250|>ε}` tends to zero.
   The sum uses all `Fin B → Fin 6`, so it is precisely the probability
   under B independent uniform assignments. There is no arbitrary dependent
   replicate sequence here. Convergence is a filter limit of real numbers.
3. For all real nT,nC,yT,yC, with nT>0 and nC>0,
   `nT(1−nT/(nT+nC))²+nC(nT/(nT+nC))²=nT nC/(nT+nC)`, and
   `(1−nT/(nT+nC))yT−(nT/(nT+nC))yC`
   `=(nT nC/(nT+nC))(yT/nT−yC/nC)`.
4. For every nonempty finite subset S of `Fin 4`,
   `Σi∈S(Y_i(true)−Y_i(false))/|S|=3/100`.

The docstring describes selection changing the expectation and block-ratio
probability limit despite constant effects, and explicitly omits identifying
the ratio with an OLS coefficient in a general block-indicator regression.

Conventions and boundary cases: real division gives zero when its denominator
is zero. The six-state treated/control sizes prove that δ and w use positive
denominators. For B>0 each weight is positive and Σw>0. At B=0 there is one
empty assignment, both block sums are zero, and b_0=0 by the 0/0 convention;
this single term cannot affect the limit at infinity. In the profiling
identities nT,nC,nT+nC are positive. The subset average is guarded by
nonemptiness, so its cardinal is positive. All finite cardinal and index
casts into ℝ are exact; powers have natural exponents (including `(1/6)^0=1`).
Empty universal quantification on a particular empty S is guarded, not the
entire claim. No integral, root, log, nonintegral power, infinity conversion,
infimum/supremum, limsup/liminf, truncated subtraction or partial function is
used. The asymptotic expression is `Tendsto` to 0, not a totalized limsup.

## SAP.P037b.T20

Location: `Challenge/Part1.lean:32–36`; statement:
`Defs/Part2.lean:38–59`. The structure `ProbabilityDesign Ω`
(`Defs/Part1.lean:85–88`, including its constructor and mass projection) has
finite Ω, real mass p_z strictly positive at every z, and `Σz p_z=1`.
For an event E, `eventProbability P E=Σz p_z 1_E(z)` (line 90), and
`finiteExpectation P Y=Σz p_z Y_z` (line 94). These are finite sums, not
integrals with missing measurability conditions.

The first block quantifies, in order, over arbitrary types Ω,I,K, finite Ω
and I, decidable equality on K, a `ProbabilityDesign Ω`, an exposure function
`D : Ω → I → K`, a varying Boolean inclusion function `A : Ω → I → Bool`,
fixed real potential-outcome values `y : I → K → ℝ`, and a fixed inclusion
function `a : I → Bool`. Let `π_i(d)=Σz p_z 1{D(z,i)=d}` and
`S={i:a_i=true}`. It concludes all three assertions:

1. For every d,i with π_i(d)>0,
   `Σz p_z [1{a_i} 1{D(z,i)=d} y_i(d)/π_i(d)]`
   `= y_i(d)` if a_i=true, and 0 otherwise.
2. For every d, if π_i(d)>0 for every i∈S and |S|>0,
   `Σz p_z [(Σi 1{a_i} 1{D(z,i)=d} y_i(d)/π_i(d))/|S|]`
   `=Σi∈S y_i(d)/|S|`.
3. For every d,i with π_i(d)>0,
   `Σz p_z [1{A(z,i)} 1{D(z,i)=d} y_i(d)/π_i(d)]`
   `= y_i(d) [Σz p_z 1{A(z,i)=true and D(z,i)=d}/π_i(d)]`.
   The ratio on the right is a conditional inclusion probability, expressed
   as a joint/marginal ratio rather than a separate conditional-law object.

The second block independently quantifies over arbitrary types Ω,I and
`Y : Ω → I → ℝ`. If for every i either `∀z, Y(z,i)>1/50` or
`∀z, Y(z,i)≤1/50`, then for every z,z',i,
`Y(z,i)>1/50 ↔ Y(z',i)>1/50`. There are no finiteness requirements here.

The docstring describes fixed-inclusion identification and varying-inclusion
factors. Its restriction describes the finite identities and same-side
sufficiency, and says it omits the sharp-null specialization, the T19 example,
conditional inclusion probabilities in (d), and empirical/script assertions.
The theorem itself already contains the joint/marginal ratio in assertion 3;
whether the clause reference (d) concerns something else cannot be known
during blind reading.

Conventions and boundary cases: an empty Ω cannot carry this design because
its mass sum would be 0=1. I can be empty, in which case some universal clauses
are empty and the population identity has an impossible positive-cardinal
premise; nonempty I is also allowed. K can be empty only if D's domain is
empty. For a retained i, the relevant probability is explicitly positive.
For an excluded i in the population sum π_i(d) may be zero; its numerator
has the exact zero multiplier 1{a_i}=0, so Lean's 0/0=0 discards that
unretained term. A conventional mathematical rendering should sum directly
over S or define the term by a guarded conditional. The final population
division is guarded by |S|>0. Finite sums are always defined, no totalized
integral is used, and all casts of finite cardinalities are exact. The
same-side condition has the intended strict/weak split at equality to 1/50.
No root/log, real power, infinity conversion, extrema, truncated subtraction
or partial lookup occurs.

## Closure auxiliary declarations

Every line-0 entry in `closure.json` was printed and read in
`scratch/ClosurePrint.log`. They add no statistical premises. For explicit
coverage, the numeral/index certificates are:

* `T19Statement._proof_1,2,4,5,6,7,8,9`: `AtLeastTwo` for
  3,100,200,40,2,6,2,250 respectively; `_proof_3`: `NeZero 4`.
* `T23Statement._proof_1,2,3,4,5,6,7,8,9,10`: `AtLeastTwo` for
  56,28,10,7,20,2800,1400,27,5400,14 respectively;
  `_proof_11`: `NeZero 3`.
* `bandCompositions._proof_1`: `AtLeastTwo 5`;
  `bandGramInverse._proof_1,2`: `AtLeastTwo 28,25`;
  `bandHC0._proof_1,2`: `AtLeastTwo 2800,280`;
  `bandOutcomes._proof_1,2,3`: `AtLeastTwo 10,3,2`;
  `bandSizes._proof_1,2`: `AtLeastTwo 14,7`;
  `centeredBandFit._proof_1`: `AtLeastTwo 4`.
* `passesConflictThreshold._proof_1`: `AtLeastTwo 50`;
  `potentialOutcome4._proof_1`: `AtLeastTwo 100`;
  `treatmentPair._proof_1`: `NeZero 4`;
  `T20Statement._proof_1`: `AtLeastTwo 50`.
* `T24Statement._proof_4`: if `j : Fin(3+p)` and its value is not 0,1,2,
  then `j.val−3<p`; `_proof_5`: `1<3+p`; `_proof_6`: `2<3+p`.

The remaining closure entries are the definitions/structure, mass projection
and constructor unfolded in the five sections above. Proof-valued generated
entries are ordinary arithmetic/index certificates, not assumptions about a
regression or a probability law.
