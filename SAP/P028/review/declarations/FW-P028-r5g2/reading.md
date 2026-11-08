# Blind reading

This file was saved at step 1, before opening `claims.json` or `record.json`.
I read all four Challenge statements and docstrings, every source definition in
their `closure.json` entries, the fields and constructors of their structures,
and printed all six generated auxiliary declarations appearing in the closures.
The auxiliary declarations prove only `NeZero 3` or the numeral-base facts
`AtLeastTwo 2`, `AtLeastTwo 3`, `AtLeastTwo 4`; they add no statistical assumptions.
Below, 0/1 subscripts stand for Bool false/true. Probabilities written as real
numbers mean `(μ E).toReal`, and integrals are Mathlib Bochner integrals.

## SAP.P028.T7

Sources: `Challenge/Part1.lean:51–55`, `Defs/Part9.lean:12–44`,
`Defs/Part3.lean:12–21,40–46,178–183`, `Defs/Part1.lean:12–24`.

There are no hypotheses or unspecified model parameters. A latent atom is a
record of six Bools `(d0,d1,y0,y1,r0,r1)`. Fix
`a=(false,true,false,true,true,true)`. On the sample space Bool, give each point
weight 1/2 in the rational numbers. For any predicate E on Bool and any
rational-valued function f, define

* P(E) = sum over b=false,true of `if E(b) then 1/2 else 0`;
* m(f,E) = [sum over b of `if E(b) then f(b)/2 else 0`] / P(E).

Thus these are explicit finite rational sums, not a Measure or a supplied model
with proof assumptions. The rational bit map sends false to 0 and true to 1.
For an atom v, treatment D(v,z) is v.d1 if z is true, v.d0 otherwise;
outcome O(v,z) is v.y1 if D(v,z) is true, v.y0 otherwise; C(v) is the
proposition `v.d0=false and v.d1=true`. The sample's latent record is the constant
a and its assignment is the sample point b itself.

The theorem asserts all of the following conjunctions:

1. P(True)=1; P(b=false)=P(b=true)=1/2.
2. bit(a.d0)≤bit(a.d1), and each bit(a.y0), bit(a.y1) is in [0,1].
3. The sum over the two b of `(bit(a.d1)-bit(a.d0))/2` is 1, and P(C(a))=1.
4. m(b↦bit(O(a,b)), b=false)=0 and the analogous mean on b=true is 1.
5. m(b↦bit(a.y0), C(a))=0 and m(b↦bit(a.y1), C(a))=1.
6. P(a.d1=a.d0)=0; 1−P(C(a))=0; 1−P(C(a))*1=0.
7. P(D(a,b)=true and b=false)=0, and P(D(a,b)=false and b=true)=0.
8. For every real n, `1*0+(1−1)*n=0` and `1*1+(1−1)*n=1`.
9. For every pair of real a',n, `0*a'+0*n=0`.
10. For every predicate E on latent records, and then every Bool z,
    P(E(a) and b=z)=P(E(a))*P(b=z). This explicitly verifies independence of
    the fixed full latent record and assignment.
11. For every Bool z, D(a,z)=z and O(a,z)=z.
12. Set rational q=P(D(a,b)=true and b=false)/P(b=false), and
    r=P(D(a,b)=false and b=true)/P(b=true). Then q=0, r=0, q+r=0;
    for every rational a',n, q*a'+r*n=0.
13. Evaluating the following four real expressions at (p,e0,e1)=(1,0,1)
    gives respectively 0,0,1,1:
    L0=max(max(0,−(e1−e0)/p),1−(1−e0)/p),
    U0=min(min(1,1−(e1−e0)/p),e0/p),
    L1=max(max(0,(e1−e0)/p),1−(1−e1)/p),
    U1=min(min(1,1+(e1−e0)/p),e1/p).

The docstring calls this a randomized full-compliance law, notes null
noncomplier and pure-cell events and zero proof denominators/numerators,
describes an undetermined noncomplier mean, and claims singleton intervals.
The actual quantified n's above are free mixture parameters, not evaluations
of a conditional expectation on the null noncomplier event.

Junk values: rational and real division are total and x/0=0. The finite mean
definition would therefore assign zero on any null event. Every finite mean
actually evaluated here has denominator 1 or 1/2. q and r also have denominator
1/2. All four bounds have denominator 1. The theorem exposes the null-event
obstruction using masses and free mixture parameters; it does not equate an
undefined ordinary noncomplier mean to the finite-mean default zero. The two
indices and record fields are inhabited and finite. No truncated subtraction,
logarithm, square root, real power, infinity conversion, extremum of an empty
set, limit operation or partial function occurs. The `max`/`min` here are binary
real operations. All subtractions are real or rational.

## SAP.P028.T8

Sources: `Challenge/Part1.lean:57–61`, `Defs/Part9.lean:46–60`,
`Defs/Part8.lean:28–33`, `Defs/Part2.lean:12–30,36,44–59,67–68`,
`Defs/Part1.lean:12–24`.

First universally quantify a type Ω in any universe and a measurable space on
it. A model M then consists of:

* a probability measure μ on Ω;
* measurable S:Ω→Fin 3, measurable Y0,Y1:Ω→R, and measurable Z:Ω→Bool;
* both Y0,Y1 Bochner integrable under μ;
* the random vector (S,Y0,Y1) independent of Z under μ;
* μ.real{Z=z}>0 for each z=false,true;
* the integral of `bit(D1)−bit(D0)` under μ is nonzero, where
  `Dz=true` for S=0, `Dz=false` for S=1, and `Dz=z` for S=2.

Here Fin 3 has precisely the elements 0,1,2, so these are always-takers,
never-takers, compliers, with no defiers. The real bit function is the indicator
of true. Observed D is D_Z and observed Y is Y_D. This encodes binary
monotonicity and absence of a direct assignment argument in the outcomes.
Write C={S=2}, A_z={Z=z}, p=(μ C).toReal,
e_z=(integral over A_z of observed Y)/(μ A_z).toReal, and
x_d=(integral over C of Y_d)/(μ C).toReal.

Define δ=(e1−e0)/p and the real endpoints
L0=max(max(0,−δ),1−(1−e0)/p),
U0=min(min(1,1−δ),e0/p),
L1=max(max(0,δ),1−(1−e1)/p),
U1=min(min(1,1+δ),e1/p).

The statement is the conjunction of these two independently quantified parts:

1. For every model M on the supplied Ω, if for every d and every ω,
   0≤Y_d(ω)≤1, then p>0, L0≤x0≤U0, L1≤x1≤U1, and x1=x0+δ.
2. For every real p,e0,e1, if 0<p≤1, 0≤e0≤1, 0≤e1≤1, and
   |e1−e0|≤p, then L0≤U0 and L1≤U1, and both of these hold:
   * For every real x1 in [L1,U1], there exists a model on Bool×Bool
     (with the standard discrete product measurable space), satisfying every
     model requirement above and pointwise bounded outcomes, whose p,e0,e1
     equal the specified numbers and whose two complier means are
     (x1−δ,x1).
   * For every real x0 in [L0,U0], there exists such a model on Bool×Bool
     with the specified p,e0,e1 and complier means (x0,x0+δ).

The existential models depend on the triple and selected coordinate; neither
they nor the second part's sample space must equal the first part's Ω.
Full compliance p=1 is permitted in both parts. This is marginal and joint-line
attainability, not an assertion that the two interval coordinates can vary
independently. The docstring states interval validity, nonemptiness and
attainment for all compatible triples.

Junk values: `eventMean` is the totalized real Bochner integral divided by
`(μ E).toReal`; it is zero on a null event, and the integral is zero by
convention when not integrable. Model integrability supplies the potential and
observed integrals. Arm denominators are positive by a structure field;
the first-stage integrand is precisely 1_C, so nonzero first stage and a
probability measure force p>0. The numeric-triple part explicitly requires
p>0. Thus no mean or displayed bound uses division by zero. `toReal ∞=0`
cannot intervene because μ is a probability measure. Fin 3 and Bool×Bool
are nonempty; an empty arbitrary Ω cannot carry a probability measure, so the
first universal implication has no model there, but the second part still
asserts real attainment. Fin numerals 0,1,2 are genuine distinct indices,
not truncating arithmetic. No other domain-sensitive operation from the
requested checklist occurs; subtractions and binary max/min are in R.

## SAP.P028.T9

Sources: `Challenge/Part1.lean:63–74`, `Defs/WholeW2.lean:16–141`,
`Defs/Part2.lean:12–15,50–51`.

For each type Ω in a fixed arbitrary universe with a measurable space, a model
consists of a probability measure μ, measurable S:Ω→Fin 3, measurable
Y0,Y1:Ω→R, and measurable Z:Ω→Bool. It requires independence of
(S,Y0,Y1) and Z; both assignment arms have positive real μ mass; and
integral(bit(D1)−bit(D0)) is nonzero. Treatment is exactly true for S=0,
false for S=1, and z for S=2. Observed D=D_Z, observed Y=Y_D. There is
no model-level outcome moment assumption.

Let C={S=2}, A={S=0}, N={S=1}, NC=C-complement, A_z={Z=z},
and E_dz={D=d and Z=z}. For any measurable E and real-valued f, put
m(f,E)=(integral over E of f)/(μ E).toReal. Define
p=(μ C).toReal, e_z=m(observed Y,A_z), x_d=m(Y_d,C),
n=m(observed Y,NC), π_dz=(μ E_dz).toReal/(μ A_z).toReal,
and m_dz=m(observed Y,E_dz).
The additional finite-cells hypothesis is: for every d and z, E_dz has
strictly positive real μ mass and observed Y is Bochner integrable on E_dz.

Set e'_z=sum over d=false,true of π_dz*m_dz,
p'=π_11−π_10, and
F_d(π,m)=(e'_d−π_10*m_10−π_01*m_01)/p'.
The theorem is a conjunction:

1. For every Ω, its measurable space, and model M, finite-cells implies all
   these conclusions together:
   * observed Y is integrable on Ω; each Y_d is integrable on C; Y1 is
     integrable on A; Y0 is integrable on N; observed Y is integrable on NC;
   * p>0, μ.real A>0, μ.real N>0, μ.real NC>0, and π_10+π_01>0;
   * for both z, e_z=e'_z;
   * π_10=μ.real A, π_01=μ.real N,
     p=1−π_10−π_01, μ.real NC=π_10+π_01, and p=p';
   * m_10=m(Y1,A) and m_01=m(Y0,N);
   * n=(π_10*m_10+π_01*m_01)/(π_10+π_01);
   * for both z, p*x_z+(1−p)*n=e_z;
   * x0=(e0−π_10*m_10−π_01*m_01)/p;
   * x1=x0+(e1−e0)/p;
   * x1=(e1−π_10*m_10−π_01*m_01)/p;
   * for both d, x_d=F_d(π,m).
2. For every pair of types Ω,Ξ in the universe, their measurable spaces,
   and models M,N, if M has finite cells, N has finite cells, all four π
   values agree, and all four m values agree, then both complier means agree.

Neither potential outcomes nor their means are bounded here. No integrability
is imposed on the unused Y0 of always-takers or Y1 of never-takers. The structure
of conclusions is a conjunction of results, not a hypothesis requiring the
claim in advance. The docstrings describe eight ordinary observed summaries,
the printed formulas, and identification, and call positive conditioning
events the existence condition for the ordinary means in the premise.

Junk values: all event means are totalized integral/mass. A probability measure
prevents `toReal ∞`. The finite-cells hypothesis guards all four cell means and
supplies their integrability. Positive arms guard conditional probabilities
and arm means; finite cells imply the latter integrable. The positive first
stage and encoded monotonicity imply p>0. Pure-cell positivity and independence
give positive A,N,NC and π_10+π_01. The conclusions explicitly provide the
integrability needed for all other means used. There is therefore no
zero-denominator or nonintegrable-integral interpretation in either theorem
part under its hypotheses. In particular the assertion does not cover models
with a null pure cell or full compliance. An arbitrary empty Ω cannot carry a
model. Fin 3 numerals are legitimate distinct indices. All sums are over the
two inhabited Bool indices. There is no truncated subtraction, logarithm,
square root, real power, set extremum, limit operation or partial function.

## SAP.P028.T10

Sources: `Challenge/Part1.lean:76–83`, `Defs/WholeW1.lean:13–108`,
`Defs/Part9.lean:100–107`, `Defs/Part2.lean:12–30,36,44–59,64–68`.

The statement is the conjunction of a universal population assertion, a
universal sample assertion, and a pair of concrete-model existentials.

Population part: for every small type Ω (`Type`, not a particular Ω),
measurable space, and causal data M, take a probability measure μ, measurable
S:Ω→Fin 3, Y0,Y1:Ω→R, Z:Ω→Bool, with (S,Y0,Y1) independent of Z,
both Z arms of positive real mass, and nonzero integral(bit(D1)−bit(D0)).
Here D_z is true for S=0, false for S=1, and z for S=2, observed D=D_Z,
observed Y=Y_D. Let C={S=2}, A_z={Z=z},
p=(μ C).toReal,
e_z=(integral over A_z of observed Y)/(μ A_z).toReal,
c_d=(integral over C of Y_d)/(μ C).toReal,
τ=(integral over C of (Y1−Y0))/(μ C).toReal, and
s=[(integral over A_1 of bit(D))/(μ A_1).toReal]
 −[(integral over A_0 of bit(D))/(μ A_0).toReal].
The unconditional integral of bit(D1)−bit(D0) equals p; s=p; 0<p≤1.
If, further, observed Y is Bochner integrable on each A_z, then Y0,Y1 and
their difference are integrable on C; τ=c1−c0; e1−e0=p*τ;
τ=(e1−e0)/p; and τ=(e1−e0)/s. No unused-potential integrability is assumed.

Sample part: for every natural n, the sample space is
R^(Fin n) × Bool^(Fin n) × Bool^(Fin n), with the product measurable space.
Write a sample as (y,d,Z). For each z define real count
N_z=sum_i 1{Z_i=z}; mean(v,z)=sum_i 1{Z_i=z}v_i/N_z;
E_z=mean(y,z); P=mean(bit(d),1)−mean(bit(d),0);
W=(E_1−E_0)/P. Define the unnormalized centered cross product
K(Z,v)=sum_i (bit(Z_i)−sum_j bit(Z_j)/(n:R))
                 *(v_i−sum_j v_j/(n:R)).
The theorem says:

* for both z, the map sample↦E_z is measurable; sample↦P and sample↦W
  are measurable;
* for every sample, if N_0>0, N_1>0, and P≠0 (in that order), then
  K(Z,bit(d))≠0 and W=K(Z,y)/K(Z,bit(d));
* for every pair of samples s,t with the same n, if E_0(s)=E_0(t),
  E_1(s)=E_1(t), and P(s)=P(t), then W(s)=W(t).

This is a measurable, totalized finite-sample statistic with the ordinary IV
identity on valid samples. It asserts no distribution, independence of draws,
consistency, unbiasedness, or asymptotic assertion. The associated docstring
explicitly says no sampling law or convergence assertion is supplied.

Existential part: there exist two models M0,M1 on Bool×Bool, each carrying
the full probability, measurability, random-assignment, positive-arm and
nonzero-first-stage requirements just described, and additionally both
Y0,Y1 integrable globally. Both models have outcomes in [0,1] for every d,ω;
p=1/2; e0=e1=3/4; τ=0. M0 has c0=c1=1/2, while M1 has c0=c1=1.
The models need not agree on the full observed law or the separate treatment
cell summaries: only the listed triple and CACE agree. This is not a
counterexample to the population LATE identity.

Junk values: eventMean is totalized Bochner integral divided by real event
mass. Probability finiteness guards `toReal`, positive arms guard arm means,
and nonzero first stage plus monotonicity guard the complier denominator.
The outcome identities are all conditional on observed-arm integrability,
which yields the complier moments in their conclusions; outside this
hypothesis no outcome-ratio identity is asserted. The existential models
have integrable bounded potentials.

On arbitrary samples, absent arms have mean 0 via 0/0=0, and zero first stage
gives W=0 via division by zero. For n=0, all sums are empty and (n:R)=0, so
the centered sums also use totalized division; their final sums are zero.
Measurability and equality from equal summaries include these totalized
values. The ordinary IV assertion is guarded by two strictly positive arm
counts and a nonzero P; these imply n>0 and nonzero cross-product denominator,
so no junk value enters that assertion. Natural-number n is cast to a real
in K, without truncated subtraction or loss of information. Fin n can be
empty, as just accounted for. Bool and Fin 3 are not empty. The finite
existential sample space has four points. No logarithms, square roots,
real powers, infinities, set extrema, limit operations or partial functions
occur. All subtraction outside the index type is in R.
