# Blind mathematical reading

Saved before reading either `claims.json` or `record.json`. This reading uses only
the Defs, Challenge, and the Mathlib definitions they invoke. Challenge docstrings
are annotations; the propositions below come from the Lean types.

## Common objects and conventions

Every universally quantified study has an arbitrary **finite** type Ω (in the
universe `Type`, not all universes), a Fintype enumeration, and atom masses
pω ∈ ℝ satisfying pω ≥ 0 and Σω pω = 1. Zero-mass atoms are allowed. The existence
of such a law rules out an empty Ω. There is no arbitrary probability space or
infinite-support law in these statements. Each study has W,V : Ω → ℕ and
X,Y,Z : Ω → {false,true}. Thus the list responses are nonnegative integer counts;
there is no fixed bound J in the type. On a finite Ω all these variables are
bounded. Write X,Y,Z numerically as their 0–1 indicators where used in formulas.

For a real function f and event D, the SAP definitions expand to

* E[f] = Σω pω f(ω), P(D) = Σω pω 1D(ω).
* E[f | D] = Σω pω 1D(ω)f(ω) / P(D).
* Var(f) = E[f²] − E[f]² and Var(f | D) = E[f² | D] − E[f | D]².

These are finite real sums, not generalized integrals. Conditional means are
defined as zero at P(D)=0 by real division by zero, but positive conditioning
probabilities are explicit or implied wherever the conclusions need population
conditional moments. Denote the event {Z=z,Y=y} by Dzy.

The named study assumptions are exactly:

1. `monotone`: at every positive-mass atom, Y=1 implies X=1. It places no
   restriction on zero-mass atoms.
2. `noLiarsDesign`: at every positive-mass atom, V = W + XZ, as an equality in ℝ.
3. `treatmentIndependent`: for every f : ℕ → Bool → Bool → ℝ and each z ∈ Bool,
   E[1{Z=z} f(W,X,Y)] = P(Z=z) E[f(W,X,Y)]. On a finite law this is joint
   independence of Z and (W,X,Y), including zero-mass possibilities.
4. `nondegenerate`: for **each** z,y ∈ Bool, P(Dzy)>0 **and** Var(V | Dzy)>0;
   also Var(Z)>0 and Var(Y)>0. The latter two are explicitly included even
   though positivity of all four cells implies them for binary variables.

`standing` is the conjunction of all four. `tripleIndependent(P,W,R,Q,Z)` is
the same factorization as item 3 with R,Q in place of X,Y.

The population quantities are

* μ=P(X=1), q=`truthRate`=E[Y | X=1], γ=P(Z=1).
* mzy=E[V | Dzy] (`listMean`).
* C=`combined`=E[Y]+E[1−Y](m10−m00).
* β=m11−m01.
* δ=E[Y | Z=1]−E[Y | Z=0].

Subscripts in this reading always put z first and y second. In particular m10
conditions on treatment and Y=0. Under `standing`, μ>0, 0<E[Y]<1,
0<γ<1 and all of these conditional distributions exist.

For n ∈ ℕ, the sample is an ordered map s : Fin n → Ω. Its mass is
Πi p(s(i)), so its law is the **unconditioned IID product law**, with random arm
and cell sizes. No assignment or nonempty-cell conditioning is built into this
law. For n=0 the product is 1 on the unique empty sample. Define

* ȳ=n⁻¹Σi Yi, with ȳ=0 at n=0.
* Nzy=Σi 1{Zi=z,Yi=y}; Nz=Σi 1{Zi=z}.
* v̄zy(c)=Σi 1Dzy(i)Vi/Nzy if Nzy>0, and c otherwise.
* v̄z(c)=Σi 1{Zi=z}Vi/Nz if Nz>0, and c otherwise.
* ŷz(c)=Σi 1{Zi=z}Yi/Nz if Nz>0, and c otherwise.
* μ̂(c1,c0)=ȳ+(1−ȳ)(v̄10(c1)−v̄00(c0)).
* μ̂std(d1,d0)=v̄1(d1)−v̄0(d0).
* γ̂=N1/n, with value zero at n=0.
* β̂(c1,c0)=v̄11(c1)−v̄01(c0).
* δ̂(c1,c0)=ŷ1(c1)−ŷ0(c0).

The sample cell variance s²zy is zero if Nzy<2, and otherwise
Σi 1Dzy(i)(Vi−v̄zy(0))²/(Nzy−1). The arm variance of direct responses t²z
is zero if Nz<2, and otherwise Σi 1{Zi=z}(Yi−ŷz(0))²/(Nz−1).
The subtractions in these denominators are in ℝ, not truncated ℕ subtraction.

The population asymptotic variances are exactly

σ² = ((1−μ)²/(1−μq)) μq
     + (1−μq){Var(V | D10)/γ + Var(V | D00)/(1−γ)},

σ²std = Var(V | Z=1)/γ + Var(V | Z=0)/(1−γ).

The estimated variance v̂μ(c1,c0,cV) is

{ ((1−μ̂)²/(1−ȳ))ȳ
  + (1−ȳ)[s²10/γ̂ + s²00/(1−γ̂)] } / n

when N10≥2, N00≥2, ȳ<1 and 0<γ̂<1, and is cV otherwise. The estimated
variance v̂β(cV) is s²11/N11+s²01/N01 when both cell counts are at least two,
and is cV otherwise. Similarly v̂δ(cV)=t²1/N1+t²0/N0 when both arm counts
are at least two, and cV otherwise. All completion constants in the theorems
are arbitrary **fixed real numbers**, independent of n and of the sample.

`gaussianReal a v` is Mathlib's Borel Gaussian probability measure with mean a
and **variance** v ∈ ℝ≥0 (not standard deviation); v=0 gives a Dirac measure.
`normalCDF(t)` is its ordinary real probability Φ(t)=P(G≤t) for G∼N(0,1).
The `.toReal` operation on an extended nonnegative real sends infinity to zero,
but these are probabilities under a probability measure and hence finite.
`normalQuantile(u)` is inf{x∈ℝ : u≤Φ(x)}; the statements only use
u=1−α/2 with 0<α<1, where the set is nonempty and bounded below and this is
the usual quantile. Mathlib's `Real.sqrt(v)` is zero when v≤0. Real division
by zero is zero. `v.toNNReal` is max(v,0), regarded as a nonnegative real.

`WeakLimit(P,T,Q)` means: for **every** continuous f : E → ℝ that has a
global real bound |f(x)|≤B for some B, E_{P^n}[f(Tn)] tends to ∫f dQ as
n→∞ through ℕ. Here all actual E are ℝ with their usual topology and Borel
measurable structure, and Q is a Gaussian probability measure. These bounded
continuous functions are integrable, so Mathlib's convention assigning zero to
a nonintegrable Bochner integral has no effect. `ProbabilityLimit(P,T,a)`
means that for every ε>0, P_{P^n}(|Tn−a|>ε)→0. `Tendsto ... atTop (nhds a)`
is the usual sequential limit as n→∞, with its full ε–N quantifiers.

`normalPValue(e,h,v)` = 2Φ(−|e−h|/√v). If v≤0 this is 2Φ(0)=1 by the
preceding totalized arithmetic. It is the ordinary two-sided Gaussian p-value
on samples with positive v.

## SAP.P019b.T12

For every finite Ω and every study S, first assume monotonicity, the no-liars
design, and treatment independence, then assume P(D01)>0 and P(D11)>0.
The conclusion is β=1, i.e. E[V | Z=1,Y=1]−E[V | Z=0,Y=1]=1.
It imposes neither all of `nondegenerate` nor any sampling hypotheses or
sampling conclusion.

## SAP.P019b.T13

This is a closed conjunction about one explicit twelve-atom study. Write
ω=4k+r, with k∈{0,1,2} and r∈{0,1,2,3}. Each atom has mass 1/16 for
k=0,1 and 1/8 for k=2. Put U=r mod 2, Z=⌊r/2⌋, W=1+U,
X=1{k<2}, Y=1{k=0}, V=W+XZ. `fairBit ω j` is the Boolean assertion
(⌊ω/2^j⌋ mod 2)=1; thus these formulas exactly expand the study.

For a Boolean world b define Qb (`cnnWatching`) to mean
k=0 or (b=true and k=1), and Rb (`cnnReading`) to mean b=false and k=1.
The asserted conjunction, in order, is:

1. This single study satisfies all four standing assumptions.
2. For every b and every ω, X(ω)=Rb(ω)∨Qb(ω), pointwise, including all atoms.
3. P(Qfalse=1)=1/4 and P(Qtrue=1)=1/2.
4. P(Y≠Qfalse)=0 and P(Y≠Qtrue)=1/4.
5. C=1/2, μ=1/2, β=1 and δ=0.

There are two different latent labelings of exactly the same probability law
and W,X,Y,Z,V; there is no quantifier over other models, no universal
identification impossibility theorem, and no atom/cell table in the conclusion.

## SAP.P019b.T14

For every finite Ω, study S, and two Boolean functions R,Q, assume, in order:

1. For every ω, Y(ω)=Q(ω).
2. For every ω, X(ω)=R(ω)∨Q(ω).
3. The no-liars design.
4. Z is independent of the whole triple (W,R,Q), in the full test-function
   factorization sense above.
5. 0<P(Z=1)<1 and 0<P(Q=1)<1.

Set b=P(Q=1), a=P(R=1,Q=0), and L=E[V | Z=1]−E[V | Z=0].
The conclusion is the following single conjunction:

* Monotonicity, the no-liars design, and independence of Z from (W,X,Y).
* m10−m00=E[X | Y=0]=a/(1−b).
* C=b+a, μ=b+a, and L=b+a.
* E[Y]=b; C−b=a and L−b=a.
* C=b if and only if a=0; L=b if and only if a=0.
* β=1 and δ=0.

No positivity of conditional V variances is required. The universal
pointwise latent identities imply monotonicity; it is a conclusion, not
an additional hypothesis. R and Q need not be independent or disjoint.

## SAP.P019b.T15

Write S=p1(1−p1)+p2(1−p2), V=(p1+p2)(1−(p1+p2)/2), d=|p1−p2|.
For arbitrary **real** n,p1,p2,α, in that order, assume n>0, 0≤p1≤1,
0≤p2≤1, S>0 and 0<α<1; let c=Φ⁻¹(1−α/2). Define

F=Φ((√n d−c√V)/√S), O=Φ((−√n d−c√V)/√S),
P2=P_{G∼N(0,1)}(c√(V/n)<|d+√(S/n)G|).

The first half states the conjunction:

* c>0.
* V−S=(p1−p2)²/2 and V−S≥0.
* P2=F+O.
* O=1−Φ((√n d+c√V)/√S).
* 0<O≤α/2.
* O=α/2 if and only if p1=p2.
* P2−F=O.

The second half has no free parameters: for α=1/20, c=Φ⁻¹(39/40),
n=50 and p1=p2=1/2, it asserts S=V=1/2, d=0, F=Φ(−c),
Φ(−c)=1/40, O=1/40, and P2=1/20. Here n is the scale parameter in
the displayed Gaussian planning event; the formal proposition itself has
no variable for total sample size 100 or binomial experiment.

## SAP.P019b.T16

There is a fixed finite baseline on w∈{0,1,2,3,4}, with probabilities
(81,216,216,96,16)/625, i.e. Binomial(4,2/5). The unaffected treated response
is w+1; the affected treated response is min(w+1,4). For **every** real ρ,
if 0≤ρ≤1, then

E[(1−ρ)(W+1)+ρ min(W+1,4)]−E[W] = 1−(16/625)ρ.

The expectation is with respect to the fixed baseline law only. The mixture
is expressed directly as a convex combination of responses, equivalently
the expectation under an affected indicator independent of W with share ρ.
There is no sample, test, p-value, rejection probability or power assertion.

## SAP.P019b.T17

For every finite Ω and study S, a conjunction of two implications is asserted:

1. If all four standing assumptions hold, μ=C.
2. If the no-liars design, treatment independence and nondegeneracy hold,
   and additionally aF=P(X=0,Y=1)>0, then C=μ+aF and μ<C.

The second implication does not assume monotonicity. It assumes positive
false-confession mass directly and does not assert E[X | Y=1]<1.

## SAP.P019b.T18

For every finite Ω and study S, assume all four standing assumptions.
Then for every pair of fixed real constants c1,c0,

lim_{n→∞} n Var_{P^n}(μ̂(c1,c0)) = σ².

This is the actual finite-sample variance under the unconditional ordered IID
product law, including empty cells and their chosen values, followed by a
scaled limit. It is not merely the variance of a limiting normal law.

## SAP.P019b.T19

For every finite Ω and study S, first assume all four standing assumptions,
then for every fixed c1,c0,cV ∈ ℝ assert the conjunction:

1. σ²>0.
2. For every ε>0 there exist M>0 and N∈ℕ such that, for every n≥N,
   P_{P^n}(|√n(μ̂(c1,c0)−μ)|>M)<ε (`RootNTight`). Thus √n error is
   eventually tight, or μ̂−μ=Op(n^−1/2).
3. √n(μ̂(c1,c0)−μ) converges weakly to N(0,σ²), in the bounded-continuous
   test-function sense stated above.
4. n v̂μ(c1,c0,cV) converges in probability to σ²: for every ε>0 the
   probability of |n v̂μ−σ²|>ε tends to zero.
5. For every α∈ℝ with 0<α<1,
   P_{P^n}(|μ̂−μ|≤Φ⁻¹(1−α/2)√v̂μ)→1−α.

The Wald event uses a non-strict inequality. A negative or zero completed
variance gives a zero radius. All assertions concern n→∞; no finite-n
coverage guarantee is present.

## SAP.P019b.T20

For every finite Ω and study S, first assume all four standing assumptions,
then for every fixed c1,c0,d1,d0 ∈ ℝ assert the conjunction:

* n Var_{P^n}(μ̂(c1,c0))→σ².
* n Var_{P^n}(μ̂std(d1,d0))→σ²std.
* σ²<σ²std, strictly.

The two actual-variance limits and their strict comparison are population
claims; there is no finite-n variance inequality.

## SAP.P019b.T21

For every finite Ω and study S, first assume all four standing assumptions,
then for every fixed c1,c0,cV ∈ ℝ assert the conjunction:

* β=1.
* (β̂(c1,c0)−1)/√v̂β(cV) converges weakly to N(0,1).
* For every real u with 0<u<1,
  P_{P^n}(2Φ(−|β̂(c1,c0)−1|/√v̂β(cV))≤u)→u.

Thus the completed two-sided p-value has a limiting Uniform[0,1] CDF on
the interior. On samples with nonpositive v̂β the statistic is zero and
the p-value is one; all deficient cells use cV as specified above.

## SAP.P019b.T22

For every finite Ω and study S, assert the conjunction of:

1. If treatment independence holds, P(Z=0)>0 and P(Z=1)>0, then δ=0.
2. If treatment independence and nondegeneracy hold, then for every fixed
   c1,c0,cV ∈ ℝ, the following conjunction holds:
   δ=0; δ̂(c1,c0)/√v̂δ(cV) converges weakly to N(0,1); and for every
   real u with 0<u<1,
   P_{P^n}(2Φ(−|δ̂(c1,c0)|/√v̂δ(cV))≤u)→u.

Neither implication needs monotonicity or the no-liars design. The second
does require all four positive V-cell variances from `nondegenerate`, as
well as Var(Y)>0 and Var(Z)>0. This is a restriction on S even though the
studentized statistic itself uses only Y,Z. Nonpositive completed estimated
variances give statistic zero and p-value one. No causal or survey-order
assertion appears in the formal conclusion.

## Mathlib definition tracing

The source checks behind this reading include:

* `Mathlib/Probability/Distributions/Gaussian/Real.lean`, especially
  `gaussianPDFReal`, `gaussianReal`, its probability-measure instance and
  `variance_fun_id_gaussianReal` (the second argument really is variance).
* `Mathlib/Analysis/Real/Sqrt.lean`, `Real.sqrt` and
  `Real.sqrt_eq_zero_of_nonpos` (square root is totalized by zero).
* `Mathlib/Basic/ENNReal/Basic.lean`, `ENNReal.toNNReal` and
  `ENNReal.toReal` (finite Gaussian probabilities avoid the infinity convention).
* `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`, `integral`
  (the integrability branch is satisfied for the bounded continuous Gaussian
  tests here).
* `Mathlib/Order/Filter/Defs.lean`, `Filter.Tendsto`;
  `Mathlib/Order/Filter/AtTopBot/Defs.lean`, `atTop`; and
  `Mathlib/Topology/Defs/Filter.lean`, `nhds` (ordinary sequential limits).

All remaining SAP operations above reduce to finite sums/products, natural
integer arithmetic, real field operations, ordinary order/absolute value,
Boolean logic and real infimum. No limsup, improper integral or empty index
type is being used to obtain the stated conclusions.
