# Blind reading

This file was written before opening `claims.json` or `record.json`. Indices in
this reading are zero based. I read every entry in `closure.json`, every source
declaration listed there, and printed all 102 distinct generated `_proof_`
declarations in `scratch/ClosurePrint.lean` (output in
`scratch/closure-print.log`). The generated declarations prove numeral
instances, nonzero finite-index moduli, the positive phase count used in the
six-row family, the three rational facts in the eight-unit design, or scalar
tower instances. None is an extra statistical assumption. Structure constructor
and projections have their ordinary record meanings.

The notation below is fully expanded here so later formulas use no uninterpreted
SAP statistical notions. A design consists of finite types U and Ω, real weights
w(ω), and Boolean membership s(ω,k). Its validity means w(ω)≥0 for every ω and
Σω w(ω)=1. Write Iωk=1 when s(ω,k)=true and 0 otherwise, E[f]=Σω w(ω)f(ω),
πk=Σω w(ω)Iωk, πkl=Σω w(ω)Iωk Iωl, and
Var(f)=Σω w(ω)(f(ω)−Ση w(η)f(η))². Positivity means πk>0 for every k.

For real outcomes y:U→ℝ, the total and mean statistics are
T_y(ω)=Σk Iωk yk/πk and T_y(ω)/|U|. The uncorrected variance estimate is

H_y(ω)=ΣkΣl [πkl>0] Iωk Iωl (πkl−πkπl)/πkl · (yk/πk)(yl/πl),

where a false bracket means that the entire term is 0. Let
Z={(k,l):k≠l and πkl=0}, an **ordered** pair set. Then

* A(y)=Σ(k,l)∈Z yk yl;
* Q_y(ω)=Σ(k,l)∈Z (Iωk yk²/(2πk)+Iωl yl²/(2πl));
* C_y(ω)=H_y(ω)+Q_y(ω);
* A*(y)=Σ(k,l)∈Z (yk²+yl²)/2;
* R(y)=Σ(k,l)∈Z (yk+yl)²/2.

All these expressions denote finite Mathlib sums in ℝ. Whenever used below,
the C2 bias is B_C(y)=E[C_y]−Var(T_y), not a relative bias. For an outcome
probability measure μ, E_y f means the real Bochner integral ∫ξ f(ξ)dμ.

## SAP.P027a.T1

There are no outside hypotheses: this is a conjunction of concrete facts and
universally quantified family facts.

The concrete population is U=Fin 8, with sizes xk=2 for even k and 10 for odd k,
and outcomes zk=−1 for even k and 1 for odd k. Ω=Fin 4. The atom g selects
exactly the two k with k mod 4=g and has weight 1/12 for even g, 5/12 for odd g.
The underlying general four-phase constructor accepts nonnegative real low and
high weights with 2low+2high=1; T1 uses the displayed rational arguments.

The concrete assertions are all of the following:

* This design is valid and positive; πk is 1/12 or 5/12 according to k's parity;
  πkl=πk if k mod 4=l mod 4 and 0 otherwise. There are 48 ordered zero pairs.
* Σk xk=48. The cumulative left endpoints Σa<k xa are
  (0,2,12,14,24,26,36,38). πk=2xk/(Σa xa).
* The four start cells have left endpoints (0,2,12,14) and lengths
  (2,10,2,10). For every g and real u in its half-open cell, a unit k is selected
  exactly when some j∈Fin 2 satisfies left(k)≤u+j(Σa xa)/2<left(k)+xk,
  and this agrees with the two-unit atom g.
* L=24>0, and ν=(ofReal L)⁻¹·(Lebesgue measure restricted to [0,L)) is a
  probability measure. Every u∈[0,L) belongs to exactly one cell; its ν-mass is
  the atom weight. For every function F:(Fin 8→Bool)→ℝ, u↦F(sample(u)) is
  ν-integrable and its integral equals Σg w(g)F(s(g,·)).
* Σk zk=0 and zk=xk/4−(Σl xl/4)/8. The selected outcome sums in phase order
  are (−2,2,−2,2). A(z)=−16=−Σg(selected outcome sum in g)² and A*(z)=48.
* For every g, the following table gives the samplewise values (the two columns
  are even and odd g):

  | quantity | even | odd |
  | --- | ---: | ---: |
  | T_z/8 | −3 | 3/5 |
  | H_z/64 | 33/4 | 21/100 |
  | C_z/64 | 21/2 | 33/50 |
  | WR | 0 | 0 |

  Here WR is exactly
  Σk I_gk (zk/(πk/2)−T_z(g))² / (8²·2·(2−1)). It is further asserted that
  every selected k satisfies zk/(πk/2)=T_z(g).
* E[T_z/8]=0; Var(T_z/8)=9/5; Var(T_z)=576/5; E[H_z]=496/5;
  E[H_z]=Var(T_z)+A(z); E[H_z/64]=31/20; E[C_z/64]=23/10;
  E[H_z/64]−Var(T_z/8)=−1/4=A(z)/64. This difference divided by
  Var(T_z/8) is −5/36, and Var(T_z/8)≤E[C_z/64].

For the family, quantifiers are ∀r,m∈ℕ, ∀hr:0<r, then (0<m)→ assertions,
except for the inclusion-law component, which allows m=0. Put q=2r, N=mq,
G=Fin r×Fin 2, K=Σg∈G Fin m. For g=(i,b), pg=1/(6r) if b=0 and
5/(6r) otherwise. Atom g has weight pg and selects all (g,j), j∈Fin m, and
no other units. Sizes are 2 if b=0 and 10 if b=1. The ordinary list index
is 2i+b+2rj. The grouped one-draw design has the same atom and group types,
weight pg, and selects exactly g. Its lift repeats that membership m times.

For every r>0 and every m (including 0), the original design is valid and
positive, π(g,j)=pg, π((g,j),(h,l))=pg if g=h and 0 otherwise, selected membership
is decidable equality of group labels, and two units have identical membership
on every atom iff their group labels agree.

For every r,m>0, L=12r; the cumulative left endpoint obtained by summing sizes
with smaller list index is 12i+(0 if b=0 else 2)+Lj. The normalized restricted
Lebesgue law on [0,L) is a probability law. Its cells are
[12i+(0 if b=0 else 2),12i+(0 if b=0 else 2)+(2 if b=0 else 10)). They uniquely
partition [0,L). At every u in cell g, selection by the inequalities
left(k)≤u+j'L<left(k)+xk for some j'∈Fin m equals the finite design's atom g.
The mass of each cell is ofReal pg. For every real-valued function of the
Boolean sampled subset, the continuous-start statistic is integrable and its
integral equals its finite-design weighted sum.

Also Σk xk=6N, (Σk xk)/N=6, Σk(xk−6)²=16N,
Σk(xk−6)²/(N−1)=16N/(N−1), and πk=m xk/(Σl xl).

For the alternating outcomes z(g,j)=−1 if b=0, 1 otherwise, Σk zk=0 and
Yg=Σj z(g,j)=−m or m according to b. The assertions are
A(z)=−q m²=−N²/q, A(z)/N²=−1/q, Var(T_z/N)=9/5, and
E[H_z/N²]−Var(T_z/N)=A(z)/N²=−1/q.

There is a separate ∀row∈Fin 6 specialization: the (N,m) arrays are
((8,2),(40,2),(120,30),(600,30),(240,60),(1200,60)); r=2 for even row and
10 for odd row. The asserted N=m(2r) and actual mean-scale bias is −1/4 for
even row and −1/20 for odd row. Finally, ∀r>0, defining A_j to be this
family's A with m=j+1, neither A_j nor A_j/(((j:ℝ)+1)·2r)² tends to 0
as j→∞ (Mathlib `Tendsto` along `atTop` to the neighborhood filter of 0).

Junk conventions: real division by 0 is 0, but all statistical denominators
used here are positive (r,m>0, q≥2, N≥2, N−1≥1, πk>0, and the positive
constants in the eight-unit case). The underlying WR definition permits m=0
or 1 and then uses division by 0; T1 uses only m=2. Its `m−1` is **real**
subtraction after casting m, not truncated natural subtraction. `Fin` remainders
use positive moduli 2 and 4. The inclusion-law clause with m=0 has an empty
unit type, so its unit quantifiers are vacuous, but the atom distribution
still has mass 1; all population-mean claims require m>0. The sequences use
m=j+1. The ENNReal inverse in the uniform law would have exceptional values
at L≤0; every use has finite L>0. The integrals are explicitly integrable for
every F because only finitely many sampled subsets occur. No logs, square
roots, real powers, `toReal`, infima, suprema, limsups, or partial-function
defaults occur in this closure. Finite-index numerals denote actual in-range
indices, and natural-to-real casts are injective and exact.

## SAP.P027a.T2

Again there are no outside hypotheses. The statement conjoins the same family
start law, inclusion law and size identities from T1 with the following
universally quantified assertions. The design, K,G,r,m,q,N,pg and the finite
sum definitions E,Var,T,H,A are exactly the expanded ones above.

First ∀r,m∈ℕ, ∀hr:0<r, ∀hm:0<m, ∀z:K→ℝ, (Σk zk=0)→ the following.
Set Yg=Σj z(g,j), S=Σg Yg², V=Var(T_z), and
B=E[H_z/N²]−Var(T_z/N). Then:

* Σg Yg=0;
  A(z)=ΣgΣh [g≠h]YgYh=(ΣgYg)²−S=−S≤0;
  S≥0; S=0 iff every Yg=0; A(z)=0 iff every Yg=0.
* E[T_z]=0; V=Σg Yg²/pg;
  H_z(g)=(1−pg)Yg²/pg²;
  E[H_z]=V−S=Σg(1/pg−1)Yg².
* (E[H_z]−V)/N²=−S/N²;
  B=A(z)/N²=−S/N²≤0; B=0 iff every Yg=0.
* If V>0, then −5/(3q)≤A(z)/V≤−1/(3q).

The outcome-model quantifiers are, in order: for every type Ξ with a measurable
space, every measure μ on Ξ with `IsProbabilityMeasure μ`, every r,m and proofs
0<r,0<m, every β,σ²∈ℝ, assume 0≤σ²; for every
ε:K→Ξ→ℝ, assume that each εk is μ-integrable with ∫εk=0, and each
εk εl is integrable with integral σ² if k=l and 0 otherwise. These are the
entire error hypotheses: equal diagonal variances and zero off-diagonal
moments; independence and Gaussian laws are not imposed.

Define raw yk(ξ)=βxk+εk(ξ), zk(ξ)=yk(ξ)−Σl yl(ξ)/N,
Yg(ξ)=Σj z(g,j)(ξ), M=16m²β²+mσ²(1−1/q),
V(ξ)=Var(T_z(ξ)), H(ξ)=E[H_z(ξ)],
Vm(ξ)=Var(T_z(ξ)/N), Hm(ξ)=E[H_z(ξ)/N²]. Conclusions:

* For all ξ,k, zk(ξ)=β(xk−6)+εk(ξ)−Σεl(ξ)/N.
  For all ξ,g, Yg(ξ)=mβ(−4 if b=0 else 4)+Σj ε(g,j)(ξ)−mΣεl(ξ)/N.
* Each Yg² is integrable and E_y[Yg²]=M; V,H,A(z),Vm,Hm are integrable.
* E_y[A(z)]=−qM, E_y[V]=(9/5)q²M,
  E_y[H]=E_y[V]−qM, and E_y[H−V]=−qM.
* E_y[A(z)/N²]=−16β²/q−σ²(1−1/q)/N.
* If M>0 then (E_y[H]−E_y[V])/E_y[V]=−5/(9q),
  E_y[V]>0, E_y[Vm]>0,
  E_y[H−V]/E_y[V]=−5/(9q), and
  E_y[Hm−Vm]/E_y[Vm]=−5/(9q).

The calibration component separately quantifies over every measurable Ξ,
probability μ, r,m>0, ρ∈ℝ with |ρ|≤1, and every error family satisfying the
same integrability/moment conditions with σ²=900(1−ρ²). Let
sx=sqrt(Σk(xk−6)²/(N−1)), β=ρ(30/sx). It concludes sx>0,
β²=900ρ²(N−1)/(16N), and

E_y[A(z)/N²]=b(q,ρ,N):=−900ρ²(N−1)/(qN)−900(1−ρ²)(q−1)/(qN).

If ρ≠0, b(q,ρ,N)≤−450ρ²/q<0.

The limit component says ∀r∈ℕ with 0<r, ∀ρ∈ℝ (no |ρ| bound here),
b(2r,ρ,m·2r)→−900ρ²/(2r) as natural m→∞. It also asserts the exact rational
identities −5/(9·4)=−5/36, −5/(9·20)=−1/36, and
−900(99/100)²/4=−220.5225.

Junk conventions: those of the common finite sums and family apply. N≥2 makes
N−1>0, Σ(xk−6)²=16N>0, hence the sqrt argument and sx are strictly positive;
Mathlib's sqrt of a nonpositive input being 0 has no role. The Bochner integral
would be 0 for a nonintegrable integrand; the moment assumptions and explicit
integrability conclusions remove that possibility here. Real divisions in
relative biases are guarded by V>0 or M>0 with positive expected variances
asserted. The rational function b is evaluated at N=0 in the initial m=0
term of the **limit sequence**, where real division by 0 makes it 0. This is
one initial value of a sequence eventually having N>0, and has no effect on
its limit. There are no sample-mean assertions for m=0. As in T1, the inclusion
component allows an empty unit type; the other components do not. `q−1`,
`N−1`, and `1−ρ²` are real subtraction. There is no hidden limsup, log, rpow,
`toReal`, empty extremum, or choice-based default.

## SAP.P027a.T3

This is an unconditional conjunction about two concrete finite distributions
and two pairs of outcome vectors. The original population is Fin 3. With
probability 1/2 atom 0 selects {0,1}; with probability 1/2 atom 1 selects {2}.
The grouped population is Fin 2, with atom g of probability 1/2 selecting {g}.
All πk=1/2; in the original design πkl=1/2 iff k,l are both <2 or both
not <2, and otherwise 0. In the grouped design πgh=1/2 iff g=h and otherwise 0.
Both designs are valid and positive. Original units 0 and 1 have equal
Boolean membership on every atom, equal numeric indicators, and zero expected
disagreement. Original membership factors through k↦(0 if k<2 else 1).
The original ordered zero-pair set is {(0,2),(2,0),(1,2),(2,1)} (cardinality 4),
and the grouped set is {(0,1),(1,0)} (cardinality 2).

For y=(1,1,1), the grouped values are Y=(2,1), explicitly the within-group
sums. Original and grouped T_y agree samplewise. For every atom g, the explicit
table is:

| quantity | atom 0 | atom 1 |
| --- | ---: | ---: |
| original T | 4 | 2 |
| grouped T | 4 | 2 |
| original H | 8 | 2 |
| grouped H | 8 | 2 |
| original Q | 4 | 4 |
| grouped Q | 8 | 2 |
| original C | 12 | 6 |
| grouped C | 16 | 4 |

Both E[T] are 3; both Var(T) are 1; both E[H] are 5; both A are 4.
Original A*=4, grouped A*=5; original E[C]=9, grouped E[C]=10;
original B_C=8, grouped B_C=9.

For y=(1,1,−1/4), the grouped values are Y=(2,−1/4), again explicitly the
within-group sums. Both Var(T)=81/16, both A=−1;
original A*=17/8, grouped A*=65/16;
original E[C]=99/16, grouped E[C]=65/8;
original B_C=9/8, grouped B_C=49/16. The conjunction also explicitly states
0≤8,0≤9,0≤9/8,0≤49/16,8<9,9/8<49/16.

The statement has no explicit samplewise mixed-outcome table: its mixed-outcome
component states the aggregate moments listed above. This matters when reading
the docstring's words "full ... before/after estimator values for the two ...
witnesses." There is no extra unknown witness to choose or antecedent to make
the concrete facts vacuous.

Junk conventions: all inclusion probabilities equal 1/2; only positive joint
probabilities are divided by in H, and zero-joint terms are deliberately
omitted. Population sizes and all fixed rational denominators are nonzero.
All sums and moments are finite; there is no improper integral. Finite literals
are in range. No natural subtraction, empty type, sqrt, log, rpow, `toReal`,
supremum/infimum, limit, or partial-function default is used.

## SAP.P027a.T4

This is a conjunction of a general almost-sure aggregation theorem, a finite
squared-difference identity, and concrete examples. The main quantifiers are:
for all finite types G and Ω, all n:G→ℕ and proofs hn:∀g,0<n(g), and all
designs on U=Σg Fin(n(g)) with atom type Ω, assume validity, positivity, and
the following cluster condition: for every g and every i,j∈Fin(n(g)),
Σω w(ω)[s(ω,(g,i))≠s(ω,(g,j))]=0. Then for every y:U→ℝ the conclusions hold.
No full-support condition on Ω or maximality of the groups is assumed.

The grouped design retains w and uses the genuine representative (g,0):
sc(ω,g)=s(ω,(g,0)). Put Yg=Σi y(g,i), Sg=Σi y(g,i)²,
Δ=B_C(original y)−B_C(grouped Y). For group-design ordered zero pairs
Zc={(g,h):g≠h and πcgh=0}, write e(f)=Σ(g,h)∈Zc f(g,h)/2.
The conclusions are:

* The grouped design is valid and positive. For every g,i the original π(g,i)
  equals grouped πg. For every g,h,i,j the original joint equals grouped
  πgh, and grouped πgg=πg.
* For every ω, **if w(ω)>0**, original and grouped T and H agree at ω.
  Their design variances agree.
* A(original y)=Σ(g,h)∈Zc YgYh=A(grouped Y).
  A*(original y)=e(nh Sg+ng Sh), and A*(grouped Y)=e(Yg²+Yh²).
* B_C(original y)=A(original y)+A*(original y), and the corresponding grouped
  formula also holds.
* Δ=e(nh Sg+ng Sh−Yg²−Yh²), and original B_C<grouped B_C iff Δ<0.
* For every real v, if all y(g,i)=v, then
  Δ=−v²e((ng−nh)²)≤0. If additionally v≠0 and some (g,h)∈Zc has ng≠nh,
  then Δ<0. If all pairs in Zc have equal group sizes, then Δ=0 for these
  constant outcomes.
* If all pairs in Zc have equal group sizes, 0≤Δ for arbitrary outcomes.
* Define dg=|{h:g≠h and πcgh=0}| and
  Lg=Σh [g≠h and πcgh=0](nh:ℝ). Then Σg(Lg−dg ng)Sg≤Δ.
* B_C(grouped Y)=e((Yg+Yh)²), B_C(original y)=R(original y), and both
  biases are nonnegative.

Separately, ∀n∈ℕ, ∀y:Fin n→ℝ,
nΣi yi²−(Σi yi)²=ΣiΣj [i<j](yi−yj)² and the left side is ≥0.
This includes n=0.

The reduction example has Ω=Fin 2, each atom weight 1/2, G=Fin 2 with the
one-draw design from T3, and two members in each group. Outcomes in sigma
coordinates are (1,−1) in group 0 and (2,−2) in group 1. The lifted design
is valid and positive; both Yg=0; its B_C=20, the grouped B_C=0.
The final conjunction repeats the T3 concrete bias increases (8→9 and
9/8→49/16) and the positive-witness grouped variance 1.

Junk conventions: `hn` ensures that selecting representative 0 never invokes
an empty-index or default choice. All π are positive, and positive-joint
guards prevent division by zero in H. The /2 in e is essential because the
sum is ordered, not a zero denominator. Group sizes and neighbor counts are
cast to ℝ **before** the signed differences; no truncated subtraction is used.
G may be empty, so U may be empty and positivity then is vacuous, but the
theorem remains the valid empty-sum identity with no division by |U|. Ω cannot
be empty under validity. Empty zero-pair sets give sum 0 as mathematically
appropriate. Samplewise equalities are guarded by positive atom weight and
do not claim equality at null atoms. No Bochner integral, sqrt, log, rpow,
extremum, limit, `toReal`, or partial-function junk value enters the statement.

## SAP.P027a.T5

This is an unconditional conjunction of a robust rounded-number inequality
and a concrete 120-unit moment calculation. For every row∈Fin 4, and every
V,G∈ℝ, assume |V−vrow|≤0.005 and |G−grow|≤0.005, where the row arrays are

| row | vrow | grow | qrow |
| --- | ---: | ---: | ---: |
| 0 | 42.55 | 653.92 | 4 |
| 1 | 56.35 | 891.43 | 20 |
| 2 | 23.14 | 622.28 | 4 |
| 3 | 28.58 | 861.11 | 20 |

Then V>0 and it is false that G≤(1+5(qrow−2)/(3qrow))V.
The decimals are exact rational reals, not floating-point computations.

The concrete population has G=Fin 2×Fin 2, 30 members per group, U=Σg Fin 30,
Ω=G, phase probabilities 1/12 for b=0 and 5/12 for b=1, and a sampled phase
selects all its members. Its grouped counterpart selects exactly that phase.
Outcomes are y((i,b),j)=(−4 if b=0 else 4)+2j−29. Let Yg=Σj y(g,j).
The asserted values are:

* Σk yk=0, Σg Yg²=57600, Σk yk²=37880;
* V=Var(original T)=414720;
* E[original H]=357120;
* E[original C]=3766320;
* E[grouped C]=529920;
* V/14400=144/5; E[original H]/14400=124/5;
  E[original C]/14400=5231/20; E[grouped C]/14400=184/5;
* (E[original C]−V)/V=4655/576;
  (E[grouped C]−V)/V=5/18.

The statement contains no universal population inequality, no averaging over
collections of populations, no stronger rowwise relative-bias thresholds, and
no formal identification of the row numbers with the displayed scalar witness
or with grouped design expectations. The sample size is still 30 and the mean
normalization is 120², including after grouping. The docstring explicitly
labels the omissions as a restriction and says no implementation or grouped
design-average identification is asserted.

Junk conventions: qrow is 4 or 20 and V in the rounded-row statement is forced
positive by a nonempty interval about a positive rational. The concrete V is
414720; all other inclusion probabilities and the fixed denominator 14400
are positive. Thus every relative ratio is meaningful. The `qrow−2` operation
is real subtraction. The concrete index types are nonempty, and all functions
are total. There are no integrals beyond finite weighted sums and no log,
sqrt, rpow, `toReal`, empty/unbounded extrema, limits, or partial-function
defaults. The four rounding hypotheses are satisfiable at V=vrow,G=grow.
