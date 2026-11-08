# Blind reading

This file was written after reading only `SAP/P004b/Defs.lean`, its eight
parts, `SAP/P004b/Challenge.lean`, its one part, and the Mathlib definitions
identified below. Neither `claims.json` nor `record.json` has been read.
Challenge theorem bodies are stubs; this reading concerns their propositions.

## Common objects and exact conventions

All node indices are in `{0,...,N-1}`. An assignment is a function from this
set to `{false,true}`, written below as `z_i` in `{0,1}`. For a vector `p`,
`w_p(z)=product_i p_i^(z_i)(1-p_i)^(1-z_i)` means exactly the product of
`p_i` when `z_i=true` and `1-p_i` otherwise. `E_p X=sum_z w_p(z) X(z)`;
`P_p(A)=E_p 1_A`; `Cov_p(X,Y)=E_p(XY)-E_p(X)E_p(Y)` and
`Var_p X=Cov_p(X,X)`. They are finite sums, not measure integrals. They are
probabilities and expectations when the supplied probabilities are in `[0,1]`.
Every theorem here that uses them probabilistically supplies interior
probabilities or fixes them to `1/2`.

A table `R` is any real function `R_i(z)`. Write

* `m_i(a)=E_p[1_{z_i=a} R_i]/q_i(a)`, where `q_i(1)=p_i`,
  `q_i(0)=1-p_i`;
* `m_ij[X;a,b]=E_p[1_{z_i=a,z_j=b}X]/(q_i(a)q_j(b))`;
* `tau_i=m_i(1)-m_i(0)`, `tau=N^-1 sum_i tau_i`,
  `mu_a=N^-1 sum_i m_i(a)`;
* `n_a(z)=sum_i 1_{z_i=a}`, `hatmu_a(z)=sum_i 1_{z_i=a}R_i(z)/n_a(z)`,
  `H(z)=hatmu_1(z)-hatmu_0(z)`;
* `HT=N^-1 sum_i[z_i R_i/p_i-(1-z_i)R_i/(1-p_i)]`;
* for deterministic real fits `g_i(a)`,
  `C_i^g=z_i(R_i-g_i(1))/p_i-(1-z_i)(R_i-g_i(0))/(1-p_i)`,
  `delta_i^g=tau_i-(g_i(1)-g_i(0))`,
  `A_g=N^-1 sum_i[g_i(1)-g_i(0)+C_i^g]`;
* `L=A_g` with `g_i(a)=mu_a` (the definition `linearHajek`);
* `linearFormula=tau+N^-1 sum_i C_i^mu`;
* observed residuals `e_i(z)=R_i(z)-hatmu_{z_i}(z)`.

The pair marginal is an ordinary joint conditional mean for **distinct**
indices with interior probabilities. Its definition does not special-case
equal indices; all uses in `secondMomentBound` exclude the diagonal.

`I_R(i,j)` means either `i=j`, or there are two assignments differing at
most at coordinate `j` with different values of `R_i`. Thus self influence
is included even for a constant table. `S_R(i,j)` means there is an `l`
with `I_R(i,l)` and `I_R(j,l)`. For any real distance array `D`,
`B_D(i,r)={j:D_ij<=r}` includes its boundary. `LocalAt(R,D,h)` means
`D_ij>h` implies not `S_R(i,j)`, for all ordered pairs. `maxDegree` is the
maximum cardinality of the supplied finite neighborhoods (zero at `N=0`).

A spatial population consists of a metric space `X`, an independently
specified measurable space on `X` (no Borel-compatibility assumption),
nonempty node sets `A_i`, a measure `zeta`, an arbitrary outcome function
`Y(x,z)`, and arbitrary sets of radii `bands(d)`. Define

`rho_i(x)=inf_{y in A_i} dist(x,y)`,
`D_ij=inf_{x in A_i,y in A_j} dist(x,y)`,
`S_i(d)={x:rho_i(x) in bands(d)}`,
`R_i(d,z)=integral_{S_i(d)}Y(x,z) dzeta / zeta(S_i(d)).toReal`.

`WellDefined(P,d)` requires, for **every** node, a measurable `S_i(d)`,
strictly positive and finite measure, and integrability of `Y(.,z)` on it
for **every** assignment. `FiniteSourceRange(P,dbar)` requires, for every
source `l`, point `x`, and assignments `z,z'` equal off `l`, that
`rho_l(x)>dbar` implies `Y(x,z)=Y(x,z')`. `Polygonal(A)` means that `A`
is a finite union of convex hulls of triples of points in Euclidean `R^2`;
degenerate triangles are allowed. `rectangle(a,b,c,d)=[a,b] x [c,d]`.

The following asymptotic definitions are literal:

* `InProb(p,U)`: for each real `epsilon>0`,
  `P_{p_N}(|U_N|>epsilon)` tends to zero as natural `N` tends to infinity.
* `BigOp(p,U,r)`: for each `epsilon>0` there exists **one** `C>0` such
  that eventually `P_{p_N}(|U_N|>C|r_N|)<epsilon`.
* `LittleOp(p,U,r)=InProb(p,U/r)`; this definition is not used in the
  exported statements.
* `Phi(x)=(gaussianReal(0,1)((-infinity,x])).toReal`, the standard normal
  CDF; `q(a)=inf{x:a<=Phi(x)}`. `FiniteQuantile(a)` explicitly requires
  this set to be nonempty and bounded below.
* `NormalLimit(p,U)`: for **every** real `x`, `P(U_N<=x)->Phi(x)`.
* `Nondegenerate(V)`: there exists `v>0` such that eventually `v<=N V_N`.
* `LiminfAtLeast(u,a)`: for every `epsilon>0`, eventually `a-epsilon<=u_N`.
  `Conservative(c,alpha)` is this property with `a=1-alpha`.
  `PrintedCoverage` instead asserts existence of a limit at least
  `1-alpha`; it is not used in these theorems.
* `ValidArms(z)` means `n_1(z)>0` and `n_0(z)>0`.
  `armRestricted(U)(z)=U(z)` there, and is **zero** elsewhere. It is not
  a conditional distribution.

For neighborhoods `B_i`, define the following deterministic or random
quantities, with every double sum ordered:

`M_g=N^-2 [sum_i {E[(R_i-g_i(1))^2|z_i=1]/p_i
 +E[(R_i-g_i(0))^2|z_i=0]/(1-p_i)}
 +sum_i sum_{j in B_i, j!=i} sum_{a,b in {0,1}}
 (2a-1)(2b-1) E[(R_i-g_i(a))(R_j-g_j(b))|z_i=a,z_j=b]]`;

`Q_g=N^-1 sum_i sum_{j in B_i} delta_i^g delta_j^g`;
`O_g(z)=N^-2 sum_i sum_{j in B_i} C_i^g(z) C_j^g(z)`;

`SAH_g=N^-2 sum_i |B_i| {E[(R_i-g_i(1))^2|z_i=1]/p_i
 +E[(R_i-g_i(0))^2|z_i=0]/(1-p_i)}`.

These are respectively `secondMomentBound`, `homophilyQ`, `oracleHAC`, and
`sahLimit` in the files. For estimated probabilities `phat_i`,
`weightedEpsilon_i=(n_1/N) z_i(R_i-g_i(1))/phat_i
+(n_0/N)(1-z_i)(R_i-g_i(0))/(1-phat_i)`.

For regression, `X` has columns `1` and `z`, `G=(X^T X)^-1`,
`M=I-X G X^T` (`residualMaker`), and
`lambda_i=z_i/n_1-(1-z_i)/n_0`.
`sandwich(z,e,Q)=G X^T [e_i e_j Q_ij] X G`;
`kernelVariance(z,e,Q)=sum_ij lambda_i lambda_j e_i e_j Q_ij`.
The treatment entry has index `(1,1)` in the zero-based two-column matrix.

`DependencyGraph(mu,V,B)` asserts self membership, symmetry of neighborhood
membership, and, for **all** finite index sets `I,J` with no cross edge,
independence of the entire vectors `(V_i)_{i in I}` and `(V_j)_{j in J}`
under `mu`. `FiniteDependencyGraph` replaces this Mathlib measurable-vector
independence by the equality `P(A and C)=P(A)P(C)` for **all** predicates
on the two finite vectors. Neither is merely pairwise independence.

For sequences of populations (`PopulationSequence`), abbreviations are:

* `MetricNodeDistances`: at **every** `N`, `D` is nonnegative, symmetric,
  `D_ij=0 iff i=j`, and satisfies the triangle inequality.
* `BoundedOutcomes`: there exists `b>0` such that eventually, for every
  point and assignment, `|Y_N(x,z)|<b`.
* `SpatialLocalConditions`: this outcome bound; existence of a function
  `h(d)>=0` for `d>=0` such that for each such fixed `d`, eventually
  `LocalAt(R_N(d),D_N,h(d))`; and existence of `c(r)` such that for each
  fixed `r>=0`, eventually **all** `|B_D(i,r)|<=c(r)`. No metric-array,
  geometric-dimension, or uniform-in-radius-in-`N` condition is implicit.
* `QuadraticSpacing`: there is `Cb>0` and an eventual `N` threshold after
  which **all** nodes and **all** `s>=0` satisfy
  `|B_D(i,s)|<=Cb(1+s^2)`.
* `conditionOn(p,J,U)(z)=E_p[1_{z'_J=z_J}U(z')]/product_{j in J}q_j(z_j)`;
  `l2Norm(p,U)=sqrt(E_p U^2)`.
* `NEDConditions(P,p,d)`: there exist real functions `psi`, positive
  numbers `g_Ni`, and a real `G`, in this order, such that `psi>=0` on
  `[0,infinity)`, is nonincreasing there and tends to zero at infinity;
  there exist `exponent>4`, `C`, and `S>0` such that
  `psi(s)<=C s^(-exponent)` for `s>=S`; `0<g_Ni<=G` for **all** `N,i`;
  and for **all** `N,i,s>=0`,
  `||R_Ni-E[R_Ni|z_{B_D(i,s)}]||_2<=g_Ni psi(s)`.
* `KernelConditions(K)`: `K(0)=1`; `K(t)=0` for `t>1`; there exists real
  `Kmax` with `|K(t)|<Kmax` for all `t>=0`; and there exist
  `0<epsilon<1`, `C>0` with `|K(t)-1|<=C|t|` for `0<=t<epsilon`.
  Neither positivity nor positive semidefiniteness is required.
* `uniformKernel=1_[0,1]`, `distanceKernel(D,K,b)_ij=K(D_ij/b)`.
* `F_N=kernelHomophily=N^-1 sum_ij K(D_ij/b_N)(tau_i-tau)(tau_j-tau)`.
* `epsilon_i(c1,c0)=C_i^{(c1,c0)}/N` (`nedEpsilon`);
  `v_i(c1,c0)=sum_{j in B_D(i,b)}epsilon_i epsilon_j K(D_ij/b)`
  (`nedVRow`); `V1=sum_i v_i(hatmu_1,hatmu_0)`;
  `V2=sum_i v_i(mu_1,mu_0)`.
* `tailEnvelope(P,phi,r)_N=sup_{i in Fin N}
  sum_{j:D_ij>r_N} phi(D_ij)`. For positive `N` this is the supremum of a
  nonempty finite real set, hence a maximum. Its value at `N=0` is not
  needed by any eventual conclusion.

## T16

There are no theorem hypotheses: four concrete assertions are conjoined.

1. Set `A0=[0,1]x[0,1]`, `A1=[10,11]x[0,1]`,
   `A2=[0,11]x[2,3]`, use planar volume, outcome `z_2` on `A0 union A1`
   and zero elsewhere, and `bands(d)={d}` (`rectangleWitness`). At `d=0`
   the averages are well defined, the finite source range is `2`,
   `|Y|<2` everywhere, and for every assignment `(R0,R1,R2)=(z2,z2,0)`.
   Nodes 0 and 1 share a source, `D01=9>4`, and their covariance under
   independent fair coins is `1/4`.
2. For every real `h>=0` there exist `L>=2` with `L>h+1` and the
   population replacing `10` by `L`, top rectangle by
   `[0,L+1]x[2,3]`, and bands by `[0,d]` (`polygonRangeFamily`). At
   `d=0` it is well defined, has range `2`, and `|Y|<2`; its three nodes
   are polygonal and pairwise disjoint; `D01=L-1>h`; nodes 0 and 1 share
   a source and have fair-coin covariance `1/4`.
3. For every natural `n>0`, the `n+1` sets `thinPolygon(n,i)` are pairwise
   disjoint, each has area one, and each has set separation strictly
   less than `2` from node zero. They are `A0=[0,1]^2` and, for `i>0`,
   `[2,2+n] x [2(i-1)/n,(2(i-1)+1)/n]`. Also for every real `C` there
   exists a natural `n>0` with `n+1>C`.
4. For every `n>0`, exactly `n+1` of these indices have separation at
   most `2` from node zero.

## T17

Four general/concrete parts are conjoined, without an outer hypothesis.

1. For every natural `N`, metric measurable space `A`, spatial population
   `P` with **compact** nodes, and reals `d,dbar,D>=0`, assume
   `bands(d) subset [0,d]`, `WellDefined(P,d)`, finite source range
   `dbar`, and within-node point distances at most `D`. Then every
   distinct pair sharing a source has separation at most
   `2*dbar+2*d+D`; also `LocalAt` holds at that cutoff for all pairs.
2. The complete `NoRangeCutoff` assertion in T16(2).
3. For every planar spatial population, reals `a>0`, `D,r>=0`, assume
   all nodes polygonal, pairwise disjoint **interiors**, area at least
   `a`, and within-node point distances at most `D`. For every node,
   `|B_D(i,r)|<=pi*(r+2D)^2/a` (here the subscript distance is the node
   separation, while the scalar `D` is the diameter bound).
4. Both area/crowding assertions in T16(3)-(4).

## T18

For every sequence of metric measurable spaces, population sequence `P`,
and real `p,d`, assume `0<p<1`, `d>=0`, `SpatialLocalConditions(P)`, and
eventually `WellDefined(P_N,d)`. Set `R_N=circleAverage(P_N,d)` and
constant probability `p` at every node. Then
`armRestricted(sqrt(N)(L_N-H_N))->0` in probability and
`armRestricted(H_N-L_N)=O_p(1/N)`. Both errors are zero, by definition,
on every assignment with either arm empty.

## T19

No theorem hypotheses. Let `V_Ni(z)=2z_i-1` when `i=0`, zero otherwise,
with independent fair coins. For **every** `N>0`, all summands have
absolute value at most one, zero expectation, and fourth moment at most
one; singleton neighborhoods form a `FiniteDependencyGraph` and all have
cardinality one; the sum has variance exactly one and CDF at `-1/2`
exactly `1/2`. Also `1/N->0`, `Phi(-1/2)<1/2`, and the sum divided by its
own standard deviation does **not** satisfy `NormalLimit`.

## T20

For every sequence of measurable spaces `Omega_N`, measures `mu_N` that
are probability measures for **every** `N`, real arrays `V_Ni`, and
neighborhood arrays `B_Ni`, assume, in this order: all variables are
measurable; all integrals of individual variables are zero; there exists
one real `M` bounding every variable's absolute value almost surely;
every row has a `DependencyGraph`; there exists one natural `D` bounding
every neighborhood cardinality; and there exists `v>0` such that
eventually `E[(sum_i V_Ni)^2]>=vN`. Then for **every** real `x`, the
probability that `sum_i V_Ni/sqrt(E[(sum_i V_Ni)^2])<=x` tends to `Phi(x)`.
The bound and probability assumptions ensure integrability; the variance
lower bound is on the **sum**, not the individual summands.

## T21

For every natural `N`, real `p`, table `R`, and neighborhoods `B`, assume
`N>0`, `0<p<1`, self membership, symmetric membership, and that every
excluded ordered pair has no shared source. With constant probabilities
`p` and `g_i(a)=mu_a`, for every node
`Var(C_i^g)=E[(R_i-mu_1)^2|z_i=1]/p
+E[(R_i-mu_0)^2|z_i=0]/(1-p)-(delta_i^g)^2`.
In addition, `Var(L)<=SAH_g`.

## T22

For every natural `N`, probability vector `p`, table `R`, neighborhoods
`B`, and deterministic fits `g`, assume `N>0`, all `0<p_i<1`, self
membership, and no shared source for any excluded ordered pair.
**No symmetry hypothesis on B** is present. Then
`Var(A_g)=M_g-Q_g/N`; furthermore, if `Q_g>=0` then `Var(A_g)<=M_g`.

## T23

For every natural `N`, real vector `phat`, table `R`, neighborhoods `B`,
deterministic fits `g`, and assignment `z`, assume `N>0`, both arm counts
positive, and all `0<phat_i<1`. For every node,
`lambda_i weightedEpsilon_i=C_i^g/N` (using `phat` in `C`). Moreover the
`(1,1)` entry of `sandwich(z,weightedEpsilon,Q_B)`, where
`(Q_B)_ij=1_{j in B_i}`, equals `O_g(z)`. There are no stochastic,
neighborhood-symmetry, fitting-consistency, or coverage assumptions or
conclusions.

## T24

For every natural `N` and assignment `z` with both arm counts positive,
and then for **every** real vector `e` and real `N`-square matrix `Q`,
the residual maker is symmetric and idempotent and annihilates `X`;
the treatment row of `G X^T` is `lambda`; `G_11=N/(n1*n0)`;
`sum_i lambda_i^2=N/(n1*n0)`; and
`sandwich(z,e,Q)_11=kernelVariance(z,e,Q)`.

## T25

For every natural `N`, probability vector `p`, table `R`, and real
`mu1,mu0`, assume `N>0` and all `0<p_i<1`. Let
`U_i=[mu1-mu0+C_i^{(mu1,mu0)}-tau_i]/N` (`centeredSummand`).
Then for every `i`, `E U_i=0`; for every assignment,
`sum_i U_i=A_(mu1,mu0)-tau`; and for every `i`,
`E[U_i+(1/N-1)tau_i]=(1/N-1)tau_i`. The last random variable is exactly
`[mu1-mu0+C_i^{(mu1,mu0)}]/N-tau_i`.

## T26

For every sequence of metric measurable spaces, population sequence `P`,
reals `p,d`, real functions `K,phi`, and real bandwidth sequence `b_N`,
assume, in order: `0<p<1`; bounded outcomes; well-defined averages at
**all** `N`; metric node distances at all `N`; quadratic spacing;
kernel conditions; `b_N->infinity`; all `b_N>0`; `phi(s)>=0` for
`s>=0`; eventually, for **all** node pairs,
`|tau_i-tau| |tau_j-tau|<=phi(D_ij)`; and for **every** real sequence
`r_N->infinity`, `tailEnvelope(P,phi,r)_N->0`. Then `F_N->0`.
There is no explicit `d>=0`, NED, or upper bandwidth-rate hypothesis.

## T27

There are no theorem hypotheses. For each `N`, put singleton nodes at
`x_i=(((i+1)N^2),0)` in Euclidean `R^2`, let `zeta=sum_i dirac(x_i)`,
`R^*_Ni(z)=1/4+3z_i/4` when `i=0` and zero otherwise, let
`Y(x,z)=sum_i 1_{x=x_i} R^*_Ni(z)`, and set `bands(d)=[0,d]`
(`sparsePopulation`). Use `p=1/2`, `d=1`, `K=1_[0,1]`, and
`b_N=floor(N^(1/12))`, where the floor is a natural floor coerced to a
real. All the following are asserted together:

* bounded outcomes, quadratic spacing, NED conditions, and kernel
  conditions; `b_N->infinity`, `b_N=o(N^(1/6))`; well-defined averages
  for every `N>=3`; and `LiminfAtLeast(F,0)`;
* `N Var(L_N)->0`;
* with `Good_N={2N/5<=n1<=3N/5}`, `P(Good_N^c)->0`;
* for every `N>=10` and assignment in `Good_N`, the interval is valid
  (both arms nonempty and `Vhac=kernelVariance(z,e,Q)>0`), and
  `-2 <= (H-tau)/sqrt(Vhac) <= 2` iff `z_0=true`;
* for every `N>0`, `P(z_0=true)=1/2`;
* `alpha*=2(1-Phi(2))` is strictly between zero and one and
  `1-alpha*>=3/4`.

The interval equivalence is expressed using `GuardedInterval`; its
antecedent is expressly supplied by `ValidInterval` on `Good_N`.

## T28

For every sequence of metric measurable spaces, population sequence `P`,
reals `p,d`, kernel `K`, and bandwidth `b_N`, assume `0<p<1`, `d>=0`,
bounded outcomes, well-defined averages at **all** `N`, NED conditions,
metric node distances, quadratic spacing, kernel conditions,
`b_N>0` for all `N`, `b_N->infinity`, `b_N=o(N^(1/6))`, and
`LiminfAtLeast(F,0)`. Then the following conjunction holds:

1. Each of `armRestricted(N(Vhac-V1))`,
   `armRestricted(N(V1-V2))`, and
   `armRestricted(N(V2-E V2))` tends to zero in probability.
2. `LiminfAtLeast(N(E V2-Var(L)),0)`.
3. **If** `Nondegenerate(Var(L))`, then for **every** real `alpha` with
   `0<alpha<1` and `FiniteQuantile(alpha/2)` and
   `FiniteQuantile(1-alpha/2)`, the probabilities of the events
   `ValidInterval => q(alpha/2)<=(H-tau)/sqrt(Vhac)<=q(1-alpha/2)`
   have `LiminfAtLeast` equal to `1-alpha`.

The event in (3) counts every invalid interval as a success. It is an
implication, not the conjunction of validity and inclusion. The
nondegeneracy condition applies only to (3).

## T29

Four universally quantified assertions are conjoined.

1. For every population sequence on metric measurable spaces, real
   `p,d`, functions `K,psi`, and bandwidth `b_N`, assume `0<p<1`, bounded
   outcomes, metric node distances, quadratic spacing, kernel
   conditions, nonnegative nonincreasing `psi` on `[0,infinity)`,
   existence of one real `G` bounding **all** the conditional
   approximation errors by `G psi(s)` at all `N,i,s>=0`, well-defined
   averages at all `N`, and `b_N>=1` for all `N`. Then there exists one
   real `C` such that eventually, for **all** pairs with `D_ij>3b_N`,

   `|Cov(v_i(mu1,mu0),v_j(mu1,mu0))| <= C b_N^2/N^4 * max`
   `(sum_{k:D_ik<=b_N} psi(D_ij/3-D_ik),`
   ` sum_{l:D_jl<=b_N} psi(D_ij/3-D_jl))`.

   This does not require `psi` to tend to zero or have a power rate,
   nor the bandwidth to diverge. `C` is not explicitly required positive.
2. For every `N,R`, real distance array `D`, real function `K`, reals
   `b,p`, and assignment `z`, assume `b>0`, kernel conditions,
   `D_ij=D_ji`, `D_ii=0`, `D_ij>=0`, and both arms positive. Then, with
   `e_i=R_i-hatmu_{z_i}`, `Vhac` equals these five terms:
   `sum_i z_i e_i^2/n1^2 + sum_i (1-z_i)e_i^2/n0^2`
   `+sum_{i!=j}z_i z_j e_i e_j K(D_ij/b)/n1^2`
   `-2sum_{i!=j}(1-z_i)z_j e_i e_j K(D_ij/b)/(n1*n0)`
   `+sum_{i!=j}(1-z_i)(1-z_j)e_i e_j K(D_ij/b)/n0^2`.
   The extra quantified real `p` is unused.
3. For every pair of Booleans `z,w`, and real
   `N,p,yi,yj,h1,h0,b1,b0` with `N!=0`, `p!=0`, and `1-p!=0`, let
   `E(a,y,c1,c0)=a(y-c1)/(Np)-(1-a)(y-c0)/(N(1-p))`.
   The product difference `E(z,yi,h1,h0)E(w,yj,h1,h0)` minus the
   analogous product with centers `b1,b0` equals the sum of:
   `zw/(N^2 p^2)*[-(yi+yj)(h1-b1)+h1^2-b1^2]`,
   `(1-z)(1-w)/(N^2(1-p)^2)*[-(yi+yj)(h0-b0)+h0^2-b0^2]`,
   `-(1-z)w/(N^2 p(1-p))*[-yi(h1-b1)-yj(h0-b0)+h0h1-b0b1]`,
   `-z(1-w)/(N^2 p(1-p))*[-yi(h0-b0)-yj(h1-b1)+h0h1-b0b1]`.
4. For every `N>0`, `0<p<1`, table `R`, and arbitrary real matrix `Q`,
   put `epsilon_i=C_i^mu/N`. Then `E epsilon_i=(tau_i-tau)/N` for
   every node, and
   `sum_ij Q_ij(E[epsilon_i epsilon_j]-Cov(epsilon_i,epsilon_j))`
   `=N^-2 sum_ij Q_ij(tau_i-tau)(tau_j-tau)`.

## T30

Three assertions are conjoined:

1. For every natural `N,n1` with `1<=n1<=N-1`, node `i`, and Boolean
   `a`, assume explicitly that both the complete-randomization
   conditioning support and the remainder support have positive
   cardinality. Then for **every** Boolean assignment `u` on the nodes
   other than `i`, the fraction of assignments with total treated count
   `n1`, `z_i=a`, and remainder `u`, divided by the number with total
   count `n1` and `z_i=a`, is `1/|remainderSupport|` when `u` has treated
   count `n1-1` for `a=true` or `n1` for `a=false`, and zero otherwise.
   Both `N-1` and the remainder count subtraction are natural-number
   subtraction; the hypotheses put them in their ordinary range.
2. For every natural `N`, vector `p` with all `0<p_j<1`, table `R`,
   node `i`, and Boolean `a`,
   `m_i(a)=E_p[R_i(update(z,i,a))]`.
3. For every natural `N>0`, `0<p<1`, and table `R`, `L(z)` equals
   `linearFormula(z)` for every assignment; `L=A_mu` as functions; and
   for every assignment,
   `A_g(z)-L(z)=(mu1-mu0)(n0/(N(1-p))-1)` when both fitted centers of
   `g` are `mu1`.

## Mathlib endpoints and totalization checks

The finite sums/products and matrices above use `Finset.univ`, ordinary
finite sums, ordinary matrix multiplication/transposition, and real
arithmetic. `EuclideanSpace R (Fin 2)` is the `L2` norm on coordinate
functions (`Mathlib/Analysis/InnerProductSpace/PiL2.lean:114`), so volume
is Euclidean area. `convexHull`, `interior`, `IsCompact`, `Pairwise`,
`Disjoint` and `MeasurableSet` carry their ordinary set/topological meanings.

`Metric.infDist` is `ENNReal.toReal(infEDist)`
(`Topology/MetricSpace/HausdorffDistance.lean:463`); nonempty nodes
exclude its empty-set convention. Node separation is a real `sInf` of a
nonempty set bounded below by zero, so is an actual infimum. Integrals
are Bochner integrals with the measure restricted to the region;
`IntegrableOn` is exactly integrability for that restriction
(`MeasureTheory/Integral/IntegrableOn.lean:92`). Bochner integration
returns zero for a nonintegrable function
(`MeasureTheory/Integral/Bochner/Basic.lean:158`). `WellDefined` excludes
that branch wherever assumed. It also excludes zero/infinite denominator
mass (`ENNReal.toReal` totalizes infinity to zero). Some finite initial
sample sizes in T18/T27 are deliberately outside the well-definedness
assumptions and do not affect their limits.

Real division and square root are total (`x/0=0`, `sqrt(x)=0` for `x<=0`).
The printed finite identities require positive arm counts where they
matter; T18/T28 explicitly replace the errors on empty-arm assignments;
`GuardedInterval` makes an assertion only if both arms and its variance
are strictly positive. Matrix inversion is Mathlib's nonsingular inverse,
zero for a singular real matrix
(`LinearAlgebra/Matrix/NonsingularInverse.lean:169`); the positive-arm
hypotheses make `det(X^T X)=n1*n0>0` in T23/T24.

The Gaussian is the probability measure with mean zero and variance one
(`Probability/Distributions/Gaussian/Real.lean:222`);
`IsProbabilityMeasure` means total mass one
(`MeasureTheory/Measure/Typeclasses/Probability.lean:64`).
`IndepFun` means independence of the sigma-algebras pulled back by the
two functions (`Probability/Independence/Basic.lean:144` and
`Probability/Independence/Kernel/IndepFun.lean:55`), specialized through
constant kernels to ordinary independence. The measurable vector
codomains have their finite product Borel structures.

`Tendsto` is filter convergence, `atTop` is the eventual-large-index
filter, and `nhds` is the usual neighborhood filter. Mathlib's
`Asymptotics.IsLittleO` means: for every `c>0`, eventually
`|f_N|<=c|g_N|` (`Analysis/Asymptotics/Defs.lean:169`), rather than
totalized division by `g_N`. All real suprema in eventual tail assertions
are finite maxima; the normal inverse CDF is protected by
`FiniteQuantile` wherever used in a theorem conclusion. No exported
statement uses a real-valued `Filter.limsup`.
