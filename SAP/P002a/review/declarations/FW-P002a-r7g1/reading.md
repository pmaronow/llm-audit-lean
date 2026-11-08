# Blind reading

This file was written before opening `claims.json` or `record.json`. I read all
entries of `closure.json`, the five Challenge docstrings and statements, and all
source definitions reached by their statements. I also printed every generated
line-0 declaration in the closures: `scratch/Generated.lean` and
`scratch/Generated.log`. Those auxiliary declarations are proofs that explicit
natural numerals are at least two, proofs that `Fin 1` has a nonzero bound, and
the `Option` case splitter for the augmented vector. They add no assumptions.
The structure constructors/projections are precisely the fields described below.

The shared dictionary below is part of each of the five readings. All symbols
introduced here are explicit finite sums, real arithmetic, finite sets, ordinary
matrices, or Mathlib order/topological notions; no SAP probabilistic notion is
left implicit.

## Shared unfolded dictionary

* A population of size `n : Nat` consists of functions
  `y : Fin n → Bool → Real`, `d : Fin n → Bool → Bool`, and `n1 : Nat`.
  A covariate population additionally has `x : Fin n → Fin k → Real`.
  Write `I = Fin n`, `t = n1`, `u = n-t` in the reals, and `p=t/n`.
  Validity means `2 ≤ n`, `0 < t`, and `t < n`. Receipt monotonicity is
  `∀ i, d(i,false)=true → d(i,true)=true`. Let
  `C={i : d(i,false)=false and d(i,true)=true}`. Booleans cast to reals by
  `b(false)=0`, `b(true)=1`. All sums below are finite.
* `M(q)=Σ_i q_i/n`; `M_D(q)=Σ_{i∈D}q_i/|D|`.
  `L=M_C(y(·,true)-y(·,false))`.
  `V(q)=Σ_i(q_i-M(q))²/(n-1)` and
  `Cov(q,h)=Σ_i(q_i-M(q))(h_i-M(h))/(n-1)`.
  The corresponding group covariance is the sum with group means and denominator
  `|D|-1` if `|D|≥2`, and is explicitly zero otherwise. Denote it `Cov_D` and
  its diagonal `V_D`. `F(q)=sqrt(sqrt(M(q⁴)))`.
* `w_a(β)_i=y(i,d(i,a))-β b(d(i,a))`,
  `v_a(β)=w_a(β)-M(w_a(β))`.
  The class `Theta(P,δ,r,A)` means: valid design, monotone receipt, `C≠∅`,
  `rn≤t≤(1-r)n`,
  `Cov_C(w_true(L),w_false(L)) ≥ -δ sqrt(V_C(w_true(L)))sqrt(V_C(w_false(L)))`,
  and `∀ a : Bool, F(v_a(L))≤A sqrt(V(w_a(L)))`.
* `D(P)` is the finite set of all subsets of `I` having cardinality `t`.
  `E_P f=Σ_{S∈D(P)}f(S)/|D(P)|`;
  `Var_P f=E_P[(f-E_P f)²]`;
  `Pr_P E=|{S∈D(P):E(S)}|/|D(P)|`.
  These are the exact uniform complete-randomization distribution, not an
  arbitrary coupling or sampling scheme.
  For any subset `S`, `q_β(S)_i=y(i,d(i,1_{i∈S}))-β b(d(i,1_{i∈S}))`.
  `R(q,S)=Σ_i q_i(1_{i∈S}-p)/n`, and `tau(P,β,S)=R(q_β(S),S)`.
  `S_a²(β)=p²(1-p)² V(w_a(β))` and
  `S_diff²(β)=p²(1-p)² Σ_i(v_true(β)_i-v_false(β)_i)²/(n-1)`.
* Let `z_i=(1,x_i)` indexed by `Option(Fin k)`, where `none` is the intercept.
  For a subset `D`, `G_D=Σ_{i∈D}z_i z_i^T/|D|` and
  `h_D(q)=Σ_{i∈D}z_i q_i/|D|`; `RSS_D(q,c)=Σ_{i∈D}(q_i-z_i·c)²`.
  `OLS_D(q)` is `G_D^{-1}h_D(q)` if `det G_D ≠ 0`, otherwise a fixed
  classically chosen global minimizer of `RSS_D(q,·)` if one exists, otherwise
  the zero vector. All dot products are sums over the indicated finite indices.
  `psi_a(β)=OLS_I(w_a(β))`, `e_a(β)_i=w_a(β)_i-z_i·psi_a(β)`.
  For coefficient vectors `c1,c0`,
  `H(q,S,c1,c0)=M_S(q_i-Σ_j x_ij c1_j)-M_(Sᶜ)(q_i-Σ_j x_ij c0_j)`;
  only slope coordinates occur in these subtractions.
  `oracleTau(P,β,S)=H(q_β(S),S,psi_true(β),psi_false(β))`.
  `fit_a(q,S)=OLS_(S if a else Sᶜ)(q)`;
  `adjustedTau(q,S)=H(q,S,fit_true(q,S),fit_false(q,S))`.
* `Xi(P,δ,e,A,B,r)` means valid design, monotone receipt, nonempty `C`, the
  same balance bounds,
  `Cov(e_true(L),e_false(L))≥-δ sqrt(V(e_true(L)))sqrt(V(e_false(L)))`,
  `∀a, F(e_a(L))≤B sqrt(V(e_a(L)))`, `∀j, Σ_i x_ij=0`,
  `∀j, M(x_·j⁴)≤A`, and
  `∀b : Fin k → Real, e Σ_j b_j²≤M((Σ_j x_ij b_j)²)`.
  There is no variance-positivity requirement in either class.
* The raw variance estimate is
  `s²(q,S)=p²(1-p)²[Σ_{i∈S}(q_i-M_S q)²/t² +
  Σ_{i∈Sᶜ}(q_i-M_(Sᶜ) q)²/u²]`.
  The adjusted estimate is
  `s_adj²(q,S)=RSS_S(q,fit_true)/t²+RSS_(Sᶜ)(q,fit_false)/u²`.
  `J(t,s²)` takes values in Mathlib `ENNReal = [0,∞]`: it is zero at `(0,0)`,
  infinity at `s²=0,t≠0`, and `ofReal(|t|/sqrt(s²))` otherwise.
  Raw/adjusted AR statistics are `J(R,s²)` / `J(adjustedTau,s_adj²)`.
* For an `ENNReal` statistic `g` on assignments, its quantile is the smallest
  member of its finite image for which `Pr_P(g≤value)≥1-α`, or infinity if
  there is no such value. Raw acceptance at `(β,α,S)` compares the raw AR
  statistic of the fixed observed vector `q_β(S)` at `S` to the quantile of
  `T ↦ rawAR(q_β(S),T)`. Adjusted acceptance does the same with adjusted AR.
  Coverage is the finite uniform probability of acceptance in `S`.
* `I_Theta(n,δ,r,A,α)` is the `ENNReal` infimum first over all real `β`,
  then over the subtype of populations with `Theta(P,δ,r,A)` and `L=β`, of
  `ofReal(coverage(P,β,α))`. `I_Xi` is the analogous infimum over covariate
  populations and adjusted coverage. Thus these are infima over all admissible
  models at their own LATE; β is not fixed before taking the final infimum.
  `N_Theta={n:∃P,Theta(P,δ,r,A)}` and `N_Xi={n:∃P,Xi(P,δ,e,A,B,r)}`.
  The size filters in T5 are `atTop ⊓ principal(N_class)`, and all limits are
  Mathlib `Filter.Tendsto` or `Filter.liminf` with the displayed topology/order.

### Shared totalizations

Real division by zero is zero. Thus empty population/group/assignment means
are zero outside the guards, and a one-unit population variance is zero.
`n-1`, `n-t`, and `|C|-1` in the displayed variance/balance formulas are real
subtractions, not truncated natural subtraction. The special group covariance
branch makes both empty and singleton group covariances/variances zero.
Validity and nonempty compliers protect population denominators and LATE;
the singleton convention still affects admissible models. `Fin 0` is empty;
`k=0` would leave only the intercept, but adjusted universal claims require
`k>0` and the explicit adjusted witnesses all have `k=1`.

`Real.sqrt` is zero on nonpositive inputs. Every use here on an admissible
model is a square root of a nonnegative sum/variance, so no negative-domain
artifact is needed. There are no logarithms, nonintegral powers, Bochner
integrals, or `ENNReal.toReal` in these five closures. The moments/expectations
are finite sums, always integrable on their finite probability spaces.

Matrix inverse is totalized by Mathlib, but OLS only uses it when the Gram
determinant is nonzero. Finite-dimensional least squares has a minimizer even
on a singular or empty design, so the last zero fallback is mathematically
unreachable. A chosen minimizer need not have unique coefficients; adjusted
statistics can depend on this choice on singular arms. T4 expressly quantifies
over even arbitrary coefficients there, subject to agreement on nonsingular
arms. This is a real completion convention to check, not a hidden full-rank
hypothesis.

`ofReal` truncates negative reals to zero; the probabilities, standard errors,
coverage, and nominal level used here are nonnegative. `J(0,0)=0` and
`J(nonzero,0)=∞` materially govern degenerate models. Quantile infinity is
an explicit fallback, and is also a legitimate quantile when image values
include infinity. For a valid finite design and `0<α<1`, the maximum image
value qualifies, so the empty-qualifying-set fallback is not used.

The empty `ENNReal` infimum is infinity, so an empty β fiber cannot lower a
nonempty model-class infimum; an entirely empty class has infimum infinity.
`ENNReal` is a complete lattice; no unbounded-real liminf default is involved.
The liminf over the bottom filter is infinity. In T5 the size filter is bottom
if admissible sizes are bounded, so its lower bound is automatic in that case.
This has substantive interpretive relevance and is explicitly described in
the definition docstring. Casts of natural numbers are ordinary exact real
casts. Natural division `n/2` used in explicit witnesses is floor division.

## SAP.P002a.T1

The theorem has no external parameters or hypotheses. It is the conjunction
`T1Statement ∧ W2T1Details`, expanded as follows.

Define `P_m` on `n=12m` units by `t=2m`, all units complying (`d(i,a)=a`),
`y(i,a)=-1` for even `i.val`, and `+1` for odd `i.val`, independently of `a`.
There is one covariate, `x_i=-1` if `i.val mod 4<2`, otherwise `+1`.

For `P_1` it asserts membership in
`Theta(δ=-1/2,r=1/6,A=2)` and `Xi(δ=-1/2,e=1/2,A=2,B=2,r=1/6)`;
`L=0`; `|D|=66`; both `S_a²(0)=25/1188`;
`Var(tau(0))=5/396`; `Var(oracleTau(0))=36/55`;
and each of the following claimed lower bounds strictly exceeds its variance:

`(3/2)[u/(12·2) S_true²(0) + 2/(12u) S_false²(0)]`,

`(3/2)[u/(12·2) V(e_true(0)) + 2/(12u) V(e_false(0))]`.

For every natural `m≥1` (the data depend only on `m`, not the proof of the
inequality), it asserts membership in those same two classes and `L=0`,
`Var(tau(0))=5/[36(12m-1)]`,
`Var(oracleTau(0))=36/(60m-5)`, and each printed lower-bound expression with
`n=12m,t=2m,δ=-1/2` is exactly `13/12` of its corresponding actual variance.

The arithmetic conjuncts say
`12/11+12/11+2(-1/2)(12/11)=12/11`,
`12/11+12/11+(-1/2)5(12/11)+(-1/2)(1/5)(12/11)=-36/55`,
and `¬(12/11≤-36/55)`. Finally both population coefficient vectors
`psi_a(0)` for `P_1` are zero.

The extra finite details assert, for both arms, `w_a(0)=y(·,false)`, its mean
zero and fourth norm one; complier covariance and both complier variances
`12/11`; `1≤2 sqrt(12/11)`; `Σx=Σy=Σxy=0`, `Σx²=12`, `M(x⁴)=1`;
and `sInf{M((x·b)²):Σb²=1}=1` (the smallest Rayleigh quotient).
Both residual arrays equal `y(·,false)`, their covariance and each variance
are `12/11`, and their fourth norms are one. Both the scaled contrast
variance `S_diff²` and `V(e_true-e_false)` are zero.
The two offending right sides are exactly `65/4752` and `39/55`.
For every `S∈D`, `Pr(T=S)=1/66`, and the oracle statistic is
`(1/2)Σ_{i∈S}y_i-(1/10)Σ_{i∈Sᶜ}y_i`.

All witness denominators are strictly positive. The only real `sInf` here,
the Rayleigh quotient, is of a nonempty bounded-below set (`k=1`, norm-one
vectors exist). Although its general definition would totalize an empty
set (for example at `k=0`), that convention does not affect this statement.
Modulo by 2/4 has positive divisor; `m=0` is expressly excluded in the family.
The docstring calls this a refutation of a printed claim, with the exact
finite and repeated-block failures above; what printed claim is meant remains
to be checked at the next stage.

## SAP.P002a.T2

This is a conjunction of universal claims, with no external hypotheses.
In the raw bound, quantify in order over `n`, a population `P` of size `n`,
then real `δ,r,A`, then assume `δ<1`, `0<r≤1/2`, `A>0`, and
`Theta(P,δ,r,A)`. Put `dplus=max(δ,0)`. The conclusion is

`(1-dplus)[u/(nt) S_true²(L)+t/(nu) S_false²(L)]≤Var_P(tau(P,L))`.

For the adjusted bound quantify over `n,k`, a covariate population, then
real `δ,e,A,B,r`; assume `k>0`, `δ<1`, `e,A,B>0`, `0<r≤1/2` and Xi.
The conclusion is

`(1-dplus)[u/(nt) V(e_true(L))+t/(nu) V(e_false(L))]≤Var_P(oracleTau(P,L))`.

For the raw chain, under the same raw hypotheses and additionally `|C|≥2`,
let `V1=V_C(w_true(L))`, `V0=V_C(w_false(L))`,
`C10=Cov_C(w_true(L),w_false(L))`,
`Q=Σ_{i∈C}(v_true(L)_i-v_false(L)_i)²/(|C|-1)`,
`b1=1+dplus·u/t`, `b0=1+dplus·t/u`.
The conjunction is

`Q=V1+V0-2C10`,
`Q≤V1+V0+2dplus sqrt(V1)sqrt(V0)`,
`V1+V0+2dplus sqrt(V1)sqrt(V0)≤b1 V1+b0 V0`,
`b1 V1+b0 V0≤[b1 Σ_C v_true(L)²+b0 Σ_C v_false(L)²]/(|C|-1)`.

For every raw admissible model (without `|C|≥2`) it also asserts
`S_diff²(L)≤p²(1-p)²/(n-1)[b1 Σ_I v_true(L)²+b0 Σ_I v_false(L)²]`.
For every adjusted admissible model it asserts
`Σ_I(e_true(L)-e_false(L))²≤b1 Σ_I e_true(L)²+b0 Σ_I e_false(L)²`.

For arbitrary sizes, models and real constants, `δ<0` and Theta imply
Theta at `δ=0` with all other constants unchanged; likewise for Xi.
These inclusion claims impose no separate positivity/balance assumptions.
Finally both variance bounds are also stated with `1-δ` under the additional
assumption `0≤δ` and the respective admissibility conditions.

The full variance conclusions include zero variances and singleton compliers.
The group chain alone excludes singleton compliers because of its `|C|-1`
denominator. Validity protects `n,t,u,n-1`; nonnegative group and population
variances protect square roots. There is no stochastic subsequence quantified
in this theorem: its pointwise universal bounds can be specialized to every
term. The docstring describes precisely that pointwise consequence.

## SAP.P002a.T3

This closed proposition is `¬PrintedLemma5 ∧ ¬PrintedE10`. The first negated
proposition universally quantifies `n`, `P : Population n`, and reals `δ,r,A`;
if `δ<1`, `0<r≤1/2`, `A>0`, and Theta hold, it claims

`(1-δ)[u/(nt) S_true²(L)+t/(nu) S_false²(L)]≤Var_P(tau(P,L))`.

The second universally quantifies `n,k`, `P : CovPopulation n k`, and reals
`δ,e,A,B,r`; under `k>0`, `δ<1`, `e,A,B>0`, `0<r≤1/2`, and Xi,
it claims

`(1-δ)[u/(nt) V(e_true(L))+t/(nu) V(e_false(L))]≤Var_P(oracleTau(P,L))`.

Thus the theorem requires a counterexample to each universal, possibly two
different models and parameter values. The theorem does not itself name a
witness or specify which hypothesis a counterexample should exploit.
Both definitions allow negative δ with no lower bound. They have no explicit
positive-variance assumption. The validity/class hypotheses do protect all
ordinary denominators in the variance bounds; singleton complier covariance
uses the shared zero convention. OLS can be singular on arbitrary admissible
arms but population OLS is nonsingular under the adjusted positive-e condition
and centering. The docstring says both printed universal lower bounds are
false; whether these are the canonical printed assertions is a stage-2 check.

## SAP.P002a.T4

This is a closed conjunction of the following statements.

1. For every size `n`, real array `q : Fin n → Real`, and proof `n≥2`, if
   `F(q)≤(1/2)sqrt(Σ_i q_i²/(n-1))`, then `∀i,q_i=0`.
2. For every raw `P` in `Theta(P,0,1/4,1/2)`, there exists one real `c` such
   that `∀a,i,w_a(L)_i=c`. (The existential follows the population quantifier;
   `c` is common to both arms and all units.)
3. For each `α∈(0,1)`, every `n≥2` and real `β` has the witness
   `D_nβ` with `y(i,false)=0`, `y(i,true)=β`, `d(i,a)=a`, `t=floor(n/2)`.
   It belongs to the preceding Theta class and has `L=β`. Every population in
   that class has coverage one. Consequently `I_Theta=1` for every `n≥2`,
   it tends to one, and does not tend to `ofReal(1-α)`.
4. For each `α∈(0,1)`, every `n≥2,β` also has the one-covariate witness
   `D_nβ` with `x_i=(2(i.val+1)-n-1)/n`. It belongs to
   `Xi(0,1/4,4,1/2,1/4)` and has LATE β. Every member of that Xi class has
   adjusted coverage at least `max(0,1-1548/(n-1))`. Its class infimum tends
   to one and does not tend to nominal coverage.
5. In the raw class, for each α in that interval there is a common `c` as in
   item 2, such that for every original assignment O the observed adjusted
   response is constant c, the observed tau and variance estimate and AR
   statistic are zero, every reassignment T has raw statistic, estimate and AR
   zero, the quantile is zero, and O is accepted.
6. In the adjusted class, every population residual is zero and the two
   population intercepts agree. For every original assignment O whose two arm
   Grams have nonzero determinant, both fitted coefficient vectors equal their
   respective population vectors, every observed residual from its own arm
   fit is zero, and the observed adjusted statistic, estimate and AR are zero.
   For **every** fit rule F from `(q,S,a)` to a coefficient vector that agrees
   with the defined fit whenever that arm Gram is nonsingular, and every real
   α (no α bound in this clause), its resulting coverage is at least
   `max(0,1-1548/(n-1))`. This resulting coverage is obtained by the same
   observed/reassigned quantile test, with numerator H using F and denominator
   `RSS_S(q,F_true)/t²+RSS_(Sᶜ)(q,F_false)/u²`.
7. In that adjusted class, treatment rank-loss probability is at most
   `258u/[t(n-1)]`, control rank-loss at most `258t/[u(n-1)]`, each of these
   two upper bounds is at most `774/(n-1)`, and probability that either arm
   loses rank is at most `1548/(n-1)`.
8. For every `n≥2` the grid has sum zero, second moment
   `(n²-1)/(3n²)≥1/4`, and fourth moment strictly below one.
9. The fixed six-unit model with this grid, all units complying, `t=3`,
   `y(i,false)=x_i`, `y(i,true)=7/3+2x_i`, belongs to that same Xi class,
   has LATE `7/3`, and has two units with unequal treatment effects.
   There are 20 assignments. Every original assignment has observed adjusted
   AR zero and is accepted for every `α∈(0,1)`. Exactly 312 of its 400
   ordered original/reassignment pairs have nonzero reassigned adjusted AR.
10. For every `α∈(0,1),n≥2`, the adjusted class infimum is bounded below by
    `ofReal(max(0,1-1548/(n-1)))` and above by one.

The docstring calls the collapsed nonempty classes a refutation and describes
the finite rank constants and the six-unit illustration. The formal count is
for nonzero **absolute** studentized statistics (`ENNReal` AR), whereas the
docstring says squared statistics. Their zero/nonzero support is the same
under this convention, but the formal quantity is not literally a square.

The half-moment conditions include zero arrays; they are not assertions of
positive variances. The raw conclusion uses `J(0,0)=0` essentially. The
adjusted fits can be singular; the arbitrary-completion bound addresses that
issue explicitly. All explicit classes have models for every `n≥2` and every
β, so their β fibers and their size limits do not exploit empty infima.
`floor(n/2)` is between 1 and n-1 when n≥2. Small-n lower rank bounds can
be negative before applying `max 0`, which is an intentional vacuous finite
lower bound, not an unsigned subtraction error. No infinity-to-real map or
unbounded-real limit occurs.

## SAP.P002a.T5

This closed proposition is the conjunction of two uniform lower bounds,
one raw sharpness statement, two necessary-witness statements, and the full
raw/adjusted degenerate-class statements numbered 3 and 4 under T4.

* For every real `δ,r,A,α`, under `δ<1`, `0<r≤1/2`, `A>0`, `0<α<1`,
  `ofReal(1-α) ≤ liminf_(n→atTop restricted to N_Theta) I_Theta(n,δ,r,A,α)`.
  There is **no** assumption that the size filter is nonbottom or that sizes
  are cofinal. For every natural `k` and reals `δ,e,A,B,r,α`, under
  `k>0,δ<1,e,A,B>0,0<r≤1/2,0<α<1`, the identical assertion holds for
  `I_Xi` on `N_Xi`.
* Quantify first over `sizes : Nat → Nat`, then a proof that it is strictly
  increasing, then a family `P_j : Population(sizes(j))`, then reals
  `δ,r,A,α`. Under the preceding raw constant bounds, assume
  `∀j,Theta(P_j,δ,r,A)`, `∀j,∃β_j,∀i,y_j(i,true)=y_j(i,false)+β_j`, and
  `∀j,V(y_j(·,false))>0`. Then the coverage of this sequence tends to
  `ofReal(1-α)`, and the liminf class infimum on nonempty sizes equals it.
  There is no analogous sufficient adjusted-sequence statement in T5.
* For each fixed admissible raw tuple of constants, if that class infimum
  liminf equals nominal, then there **exists** a strictly increasing size
  sequence and populations in the **same** class, with constant additive
  effects at each size, positive baseline variance at every size, **and**
  coverage tending to nominal. The existential includes convergence rather
  than making it an additional premise on the class.
* For each fixed admissible adjusted tuple (including k>0), equality of the
  corresponding class infimum liminf to nominal implies existence of a
  strictly increasing sequence of covariate populations in that same class,
  with constant additive effects at each size, positive population OLS
  residual variance `V(e_false(L))` at each size, and adjusted coverage
  tending to nominal.
* For every α in (0,1), raw and adjusted collapsed classes have all the
  explicit models, pointwise coverage/lower-bound facts, and limits to one
  and failure of convergence to nominal stated under T4 items 3–4 above.

Strictly increasing natural sizes tend to infinity and provide cofinal
nonempty sizes in the sharpness/witness clauses. Without such a sequence,
the universal lower bounds allow the bottom size filter; its liminf is
infinity. The equality-to-finite-nominal premise of the necessary-witness
clauses rules that case out. Empty β fibers have infimum infinity, and the
explicit degenerate examples make their fixed classes nonempty for every
n≥2. The standard errors and AR convention at zero, the singular-fit rule,
and ordinary exact casts are as in the shared dictionary. No undefined
expectation or `toReal(∞)` enters any part of this theorem.
