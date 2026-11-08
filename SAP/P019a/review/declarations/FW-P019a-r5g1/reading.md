# Blind reading of SAP.P019a.T1–T5

This document was written and saved before opening `claims.json` or `record.json`.
Only the Challenge statements/docstrings, their closure definitions, and relevant
Mathlib conventions have been used. The descriptions below do not import any
assertions from the later claims or record.

## Common notation, fully reduced to sums and integrals

A finite law on a finite type Ω is a function p : Ω → ℝ with p(ω) ≥ 0 for
every ω and Σω p(ω) = 1. Its constructor and projection add no other data.
For this law, write E f = Σω p(ω) f(ω), P(D) = E 1_D, and
E(f | D) = E(f 1_D)/P(D). Write Var(f) = E(f²) − (Ef)²,
Var(f | D) = E(f² | D) − E(f | D)²,
Cov(f,g) = E(fg) − Ef Eg, and
Cov(f,g | D) = E(fg | D) − E(f | D)E(g | D).
Indicators are real 0 or 1. These are precisely the finite-law definitions,
not symbolic assumptions about expectations.

A finite study consists of such a law and functions W,V : Ω → ℕ and
X,Y,Z : Ω → Bool. Identify false/true with 0/1 in formulas.
Its cell C_zy is {ω : Z(ω)=z and Y(ω)=y}; its cell list mean is
m_zy = E(V | C_zy). Its prevalence is μ=P(X=1), truth rate is
p=E(Y | X=1), assignment probability is γ=P(Z=1), and β=m_11−m_01.
Here every occurrence of V and W in a real formula means its natural-to-real cast.

The predicate called `standing` is the conjunction of these four predicates:

1. On every atom with p(ω)>0, Y(ω)=1 implies X(ω)=1.
2. On every atom with p(ω)>0, V(ω)=W(ω)+X(ω)Z(ω), as a real equality.
3. For every function f : ℕ → Bool → Bool → ℝ and every z : Bool,
   E[1_{Z=z} f(W,X,Y)] = P(Z=z) E[f(W,X,Y)]. This is independence
   of assignment from the entire triple, not just pairwise independence.
4. For all z,y : Bool, P(C_zy)>0 and Var(V | C_zy)>0;
   also Var(Z)>0 and Var(Y)>0.

An ordered sample of size n is a function s : Fin n → Ω, where Fin n is
{0,…,n−1}. Its iid law gives it mass Πi p(s(i)). For each sample define
N_zy=Σi 1_{C_zy}(s(i)), N_z=Σi 1_{Z=z}(s(i)), and
Ybar=(Σi Y(s(i)))/n. Define
M_zy(c)=c if N_zy=0, otherwise (Σi 1_{C_zy}(s(i))V(s(i)))/N_zy.
The occupied event D is {N_10>0 and N_00>0}. Write
K=N_10+N_00, A=1−Ybar,
B=M_10(c1)−M_00(c0)−1,
μhat=Ybar+(1−Ybar)(M_10(c1)−M_00(c0)), and γhat=N_1/n.
These formulas expand all finite-study sample definitions used below.
A pattern fibre F_s consists of samples t with Y(t(i))=Y(s(i)) and
Z(t(i))=Z(s(i)) for every i. The finite and measure versions use the same formulas.

`uniformFin(n,hn)` is the law giving each element of Fin n mass 1/n,
with an explicit proof hn : 0<n. `fairBit(ω,k)` is the Boolean assertion
((ω.val / 2^k) mod 2 = 1), using natural-number quotient and remainder.
`bitVal` maps false to real 0 and true to real 1.

All 169 distinct unit declarations appearing in the union of the five closures
were inspected in their source or generated signature. The 59 line-zero
auxiliaries are displayed in `scratch/ClosureChecks.log`: numeral `AtLeastTwo`
and `NeZero` proofs, normalization/nonnegativity proofs for finite laws,
positivity of 8 and 16, and the generated pattern matcher for the explicit mass
table. The structure constructors/projections merely supply the fields described
above and below. No auxiliary adds a mathematical hypothesis.

## SAP.P019a.T1

Source: `SAP/P019a/Challenge/Part1.lean:10–15`,
`SAP/P019a/Defs/Part5.lean:13–26`, and the finite-law/ceiling definitions
in `Defs/Part1.lean` and `Defs/Part3.lean`.

This is a closed conjunction: it has no input objects, hypotheses, or outer
existential quantifiers. The underlying five-element population is w : Fin 5.
Its masses, in order w=0,1,2,3,4, are
(81,216,216,96,16)/625. Let E denote the weighted sum with these masses.
The three real response functions are
r_print(w)=min(w+1,4), r_code(w)=min(w+1,4)+1, and r_unaff(w)=w+1.
For any real ρ and response r, define the deterministic quantity
b(r,ρ)=Σw P(w)[(1−ρ)(w+1)+ρr(w)]−Σw P(w)w.
No affected-status random variable, assignment variable, or conditional observed
response is constructed.

The conjunction asserts, in order:

- For every w : Fin 5, P(w)=choose(4,w)(2/5)^w(3/5)^(4−w).
- Ew=8/5 and E(w²)−(Ew)²=24/25.
- For every w : Fin 5, the printed, coded, and unaffected response functions
  have respective vectors (1,2,3,4,4), (2,3,4,5,5), and (1,2,3,4,5).
- b(r_print,1/5)=3109/3125 and b(r_code,1/5)=3734/3125.
- b(r_print,1/5)−1=−16/3125 and b(r_code,1/5)−1=609/3125.
- b(r_code,1/5)−b(r_print,1/5)=1/5.

The docstring calls this the discrepancy between printed and coded mechanisms.
It expressly restricts the theorem to the deterministic mixture with affected
status integrated out, omits a joint random-variable model and identification
with observable conditional means, and promises no numerical power guarantee.

Junk-value audit: all real divisions have positive, fixed denominators. The
subtraction 4−w is natural truncated subtraction, but w≤4, so it is ordinary
subtraction here. Every vector index is in Fin 5; the numeral 4 denotes its valid
last element. Exponents are natural, including the ordinary x^0=1 convention.
The law is nonempty and normalized. There are no conditionals on null events,
nonintegrable means, partial inverses, square roots, logs, real powers,
extended-real conversions, extrema, or limits. This theorem does not depend on
a junk value.

## SAP.P019a.T2

Source: `Challenge/Part1.lean:17–22`, `Defs/Part5.lean:28–43`, and the
same finite-law/ceiling definitions as T1.

Use exactly the explicit population, response functions, and weighted-sum
quantity b(r,ρ) just expanded under T1. Quantifier order is: for every real ρ,
if 0≤ρ and then ρ≤1, the following conjunction holds. Thus every assertion
in the conjunction, including the pointwise response equalities and the
numerical evaluations at 1/5, lies inside these two implications.

- For every w : Fin 5, r_code(w)=w+2 when w<4 and 5 otherwise.
- For every w : Fin 5 and every affected : Bool, the response selected as
  r_code(w) when affected and w+1 otherwise has increment over w equal to
  1+1_{affected=true and w<4}. In the same quantifiers, selecting r_print(w)
  when affected and w+1 otherwise gives increment 1−1_{affected=true and w=4}.
- b(r_code,ρ)=1+ρ(1−P(4))=1+(609/625)ρ, stated as two equalities.
- b(r_print,ρ)=1−ρP(4)=1−(16/625)ρ, also stated as two equalities.
- b(r_code,ρ)−b(r_print,ρ)=ρ.
- If additionally ρ>0, then b(r_code,ρ)>1.
- b(r_code,1/5)=3734/3125 and b(r_print,1/5)=3109/3125.

The affected Boolean is universally quantified pointwise. The mixture uses the
same coefficient ρ for every w; there is no joint probability model for that
Boolean. The docstring discloses omission of the claim of roughly 80% power
with 800 affirmative respondents and 20% affected, and omission of the joint
population and observable-mean identification.

Junk-value audit: the only divisions have fixed positive denominators. Fin 5
and its last-element numeral are valid. No subtraction in the increment
formulas is natural subtraction: the response and w are already real.
`min(w+1,4)` uses natural values before a real cast. The baseline law's
nonnegativity/normalization proofs are genuine. There is no null-event mean,
nonintegrability, extended-real operation, or limit. The outer hypotheses are
satisfiable, for instance at ρ=1/5 (and at both endpoints).

## SAP.P019a.T3

Source: `Challenge/Part1.lean:24–30`, `Defs/Part5.lean:45–78`,
`Defs/WholeW1.lean:14–17,25–44,60–125`, and the finite definitions in
`Defs/Part1.lean`, `Part2.lean`, `Part3.lean`.

This is a closed conjunction about a specified population, not an implication
from a user-supplied study. Let Ω=Fin 16 with uniform mass 1/16. Write
X=bit_0, C=bit_1, W=bit_2, Z=bit_3 (W is the natural 0/1 count),
Y=X AND C, and V=W+(X AND Z). The four bits are asserted to have their full
joint fair law: for every function a : Fin 4 → Bool,
P(∀i,bit_i=a(i))=(1/2)^4. The theorem also asserts all four `standing`
conditions expanded in the common notation.

The population conjunction specifies every cell's probability, conditional
mean and conditional variance, each conditional probability being positive:

| z | y | P(C_zy) | E(V given C_zy) | Var(V given C_zy) |
|---|---|---------|-----------------|------------------|
| 0 | 0 | 3/8 | 1/2 | 1/4 |
| 0 | 1 | 1/8 | 1/2 | 1/4 |
| 1 | 0 | 3/8 | 5/6 | 17/36 |
| 1 | 1 | 1/8 | 3/2 | 1/4 |

Also Var(Y)=3/16, Var(Z)=1/4, μ=1/2, p=1/2, γ=1/2,
and P(Y=1)=μp=1/4. For every y,z : Bool and v : ℕ, the full observable
mass P(Y=y,Z=z,V=v) equals this table, and is zero at all unlisted triples:

| y | z | v | mass |
|---|---|---|------|
| 0 | 0 | 0 | 3/16 |
| 0 | 0 | 1 | 3/16 |
| 0 | 1 | 0 | 1/8 |
| 0 | 1 | 1 | 3/16 |
| 0 | 1 | 2 | 1/16 |
| 1 | 0 | 0 | 1/16 |
| 1 | 0 | 1 | 1/16 |
| 1 | 1 | 1 | 1/16 |
| 1 | 1 | 2 | 1/16 |

For every n : ℕ and z : Bool, under the ordered product law P_n,
P_n(N_z0=0)=(5/8)^n>0. At one observation, the zero-completed mean is
M_z(ω)=V(ω)1_{C_z0}(ω). The population covariances are
Cov(1−Y,M_1)=5/64 and Cov(1−Y,M_0)=3/64.
Also P(Y=0)>0, E(1_{Z=1} | Y=0)=1/2,
E(M_1 | Y=0)=5/12, and E(V | C_10)=5/6.
Under the actual one-observation product law the theorem separately gives
EA=3/4, EM_10(0)=5/16, E[A M_10(0)]=5/16,
EM_00(0)=3/16, and E[A M_00(0)]=3/16.

The four explicit numerical missing-mass factors 1−(1−1/2)^k at
k=0,1,2,4 are respectively 0,1/2,3/4,15/16.
More generally, for every n,k : ℕ with k≤n, under P_n the event {K=k}
has positive probability; then for every z : Bool and every i : ℕ with i≤k,
P_n(N_z0=i | K=k)=choose(k,i)(1/2)^k.
For every such z the sum of these probabilities over integers i in [1,k]
is 1−(1/2)^k, and that value is strictly below 1. These assertions include
n=0 and k=0.

For n=4 let A=1−Ybar, B=M_10(0)−M_00(0)−1, and D={N_10>0,N_00>0}.
The theorem asserts:

- P_4(D)=1431/2048>0.
- Cov(A,B | D)=0 and Cov(M_10(0),M_00(0) | D)=0.
- Var(μhat | D)=141205/404496.
- E(A | D)² Var(B | D)+Var(A | D)E(B | D)²+
  Var(A | D)Var(B | D)=75809/202248.
- Subtracting that expression from Var(μhat | D) gives −1157/44944.
- The six moments are E(A | D)=43/53, E(A² | D)=73/106,
  E(B | D)=−2/3, E(B² | D)=1849/1908,
  E(AB | D)=−86/159, and E(A²B² | D)=4897/7632.
- Var(μhat | D)=Var(AB | D).
- 4γ=2, P_4(N_1=2)=3/8, and P_4(N_1=0)=1/16.

Thus the asserted numerical product comparison is explicitly conditional on
both negative-response cells being occupied. The unconditional n=1
covariance comparison instead uses a zero completion. The docstring describes
these exact choices and calls the occupied n=4 comparison a refutation of the
exact product-variance formula.

Junk-value audit: finite support makes all real sums integrable. The product
law at n=0 is the unit mass on the unique empty function; its empty product
is 1 and all cell counts are 0. Ybar then equals real 0/0=0 and A=1.
These are explicit totalizations; the count law at n=0 conditions on K=0,
a probability-one event. Each unoccupied cell mean is explicitly 0, not an
undisclosed quotient; the n=1 covariances depend on that completion and do
not describe an unspecified incomplete statistic. D at n=4 is strictly
positive and its denominators are positive; every other conditional mean
actually asserted has a positive conditioning probability. The general
formula uses natural binomial coefficients and the sum [1,k], which is empty
at k=0 and then equals 0. The half-power with exponent 0 is 1. All
natural subtraction used in binomial probabilities has its range guarded.
In bit extraction 2^k>0; all actual bit indices are in range, and uniform
population denominators are explicitly nonzero. No log, sqrt, real exponent,
extended-real conversion, infimum/supremum, or limit occurs in this theorem.

## SAP.P019a.T4

Source: `Challenge/Part1.lean:32–40`, `Defs/WholeW1.lean:319–441,
458–472,595–704`, and `bitVal` from `Defs/Part1.lean:40`.

Outer quantifier order: for every type E in the theorem's universe, every
measurable-space structure on E, and every tuple S consisting of a measure ν
on E and functions W,V : E→ℕ and X,Y,Z : E→Bool, assume in order:

1. ν is a probability measure (ν(E)=1).
2. All five functions are measurable.
3. There exists M : ℕ such that V≤M ν-almost everywhere.
4. The four standing assumptions hold, with the first two interpreted ν-almost
   everywhere, and independence and nondegeneracy expressed by the formulas
   in the common notation with E f = the real Bochner integral ∫f dν.

The independence quantifier still ranges over every f : ℕ→Bool→Bool→ℝ and
z : Bool. Nondegeneracy still includes positive probability and positive V
variance for every one of the four cells, and positive Y and Z variance.
The generic `WholeMeasureLaw` structure alone is only a measure; the explicit
probability premise is essential. The conclusion is the conjunction of three
families, expanded below. For all these families P_n is the actual product
measure Πi∈Fin n ν on E^(Fin n), `prob` is ∫1_D dP_n, and conditional
moments are ratios of the integrals of their indicators as above.

Set q=μp, m_z=E(V | C_z0), σ_z²=Var(V | C_z0),
b=m_1−m_0−1, and h(s)=σ_1²/N_10(s)+σ_0²/N_00(s), with real divisions.
Use A,B,D,K,μhat,γhat and pattern F_s from the common notation.

The first family (`wholeT4MeasureCore`) says:

- For every n : ℕ and z : Bool,
  P_n(N_z0=0)=(1−P(C_z0))^n>0.
- For every n : ℕ with 2≤n and every c1,c0 : ℝ, P_n(D)>0 and all
  the following assertions hold with those completions:
  - For every k : ℕ with k≤n and P_n(K=k)≠0, and every i : ℕ with i≤k,
    P_n(N_10=i | K=k)=choose(k,i)γ^i(1−γ)^(k−i).
    Also P_n(N_10>0 | K=k)=1−(1−γ)^k and
    P_n(N_00>0 | K=k)=1−γ^k.
  - For every sample s in D whose pattern fibre has nonzero probability,
    for each z : Bool,
    E[M_z0(c_z) | F_s]=m_z and
    Var(M_z0(c_z) | F_s)=σ_z²/N_z0(s), where c_true=c1,c_false=c0.
    The two means have conditional covariance 0 given F_s;
    E(B | F_s)=b and Var(B | F_s)=h(s).
  - For every a : ℝ such that P_n(D and A=a)≠0 and every z : Bool,
    E[M_z0(c_z) | D and A=a]=m_z.
  - For every z : Bool, Cov(M_z0(c_z),A | D)=0. Also
    Cov(M_10(c1),M_00(c0) | D)=0.
  - Var(μhat | D)=b² Var(A | D)+E(A²h | D), and the same right-hand
    side equals Var(AB | D), each stated separately.
  - The product expression
    T=E(A | D)² Var(B | D)+Var(A | D)E(B | D)²+
      Var(A | D)Var(B | D)
    equals b² Var(A | D)+E(A² | D)E(h | D).
  - Var(AB | D)−T=Cov(A²,h | D).
- Put R_shift(n)=Cov_{P_(n+2)}(A²,h | D), for n : ℕ.
  This sequence is O((1/(n+2))²) at the natural-number filter atTop, and
  (n+2)² R_shift(n) tends in ℝ to
  −2q(σ_1²/γ+σ_0²/(1−γ)). Here Big O means that for some real C,
  eventually |R_shift(n)|≤C|(1/(n+2))²|; convergence has its usual
  eventual-neighbourhood/filter meaning.
- For every positive n : ℕ, E_{P_n} N_1=nγ, and for every sample s,
  N_1(s)=n γhat(s). No equality N_1=nγ is asserted for each realization.

The second family (`wholeT4MeasureCounts`) says: for every n,k : ℕ with
k≤n, P_n(K=k)>0; for every i : ℕ with i≤k the same treated binomial
probability holds; and the sums over i∈{1,…,k} of P_n(N_10=i | K=k)
and P_n(N_00=i | K=k) equal 1−(1−γ)^k and 1−γ^k respectively.
This family includes n=0 and n=1 without a lower bound.

The third family (`wholeT4MeasureExtras`) says:

- For every n : ℕ and every sample s, K(s)=nA(s), and for every
  c1,c0 : ℝ, μhat(s)=1+A(s)B(s).
- P(Y=1)=μp, μ>0, 0<γ<1, and 1−μp>0.
- For every positive n : ℕ, E_{P_n} A=1−μp and
  Var_{P_n}(A)=μp(1−μp)/n.
- m_1−m_0=(1−p)μ/(1−μp), and b=−(1−μ)/(1−μp).
- Put R(n)=Cov_{P_n}(A²,h | D). Then R(n)=O((1/n)²) atTop and
  n²R(n) tends to −2q(σ_1²/γ+σ_0²/(1−γ)).

The docstring describes the bounded count-valued iid setting, all-size count
laws, occupied-cell corrected identities, second-order discrepancy, direct
response moments, population contrasts, and expectation-versus-realized count.
It says conditional moments are asserted only on positive-probability events.

Junk-value audit: the Bochner integral is defined as 0 for a nonintegrable
integrand. Here probability, measurability and the almost-sure bound on V
ensure genuine moments for V and all fixed-size sample functions. Moreover
V=W+XZ almost everywhere with nonnegative counts implies 0≤W≤V almost
everywhere. Thus W is also essentially bounded; any function of (W,X,Y)
is almost surely finite-range and integrable. The all-functions independence
premise does not obtain its meaning through nonintegrable integrals.

Conditional ratios would give 0 on null events, and conditional variances and
covariances would also give 0 there. Every substantive conditional formula
has either a positive-probability theorem (D for n≥2 and K=k for k≤n), an
explicit nonzero probability guard, or a positive population-cell premise.
The asymptotic sequence R(n) also evaluates conditional covariance at n=0,1,
where D is empty; those two values are 0 by the totalized ratio. They do
not affect Big O or a limit atTop. The shifted sequence avoids these cases.
The function h is totalized by real division at zero cell counts, but is used
inside integrals restricted to D, where both counts are positive.
At n=0, Ybar=0/0=0, γhat=0/0=0, A=1 and K=0; the all-size algebra
K=nA remains true. The identity for μhat is algebraic for every completion,
including this case. Population denominators γ, 1−γ and 1−μp are positive.
The reciprocal sequence 1/n at n=0 equals 0, which has no effect on its
asymptotic assertions. All occurrences k−i in natural exponents have i≤k.
The sum over [1,0] is empty. Empty products at n=0 define a one-point
probability space. No `ENNReal.toReal` of infinity is used: probabilities
are real integrals of indicators. No log, sqrt, real rpow, infimum,
supremum, limsup/liminf, or default partial-function choice is present.

## SAP.P019a.T5

Source: `Challenge/Part1.lean:42–47`, `Defs/Part5.lean:80–85`,
`Defs/WholeW1.lean:14–17,25–30,127–165`, and the finite-study and
eight-atom witness definitions in `Defs/Part1.lean`, `Defs/Part3.lean`.

This is a closed conjunction about Ω=Fin 8 with uniform mass 1/8. Let
X=bit_0, W=bit_1, Z=bit_2, Y=X and V=W+(X AND Z), with W,V natural
counts. The full joint bit law is asserted: for every a : Fin 3→Bool,
P(∀i,bit_i=a(i))=(1/2)^3. Every atom satisfies Y=X. The theorem asserts
all four `standing` conditions, expanded in the common notation.
For every z,y : Bool, P(C_zy)=1/4>0, Var(V | C_zy)=1/4,
and E(V | C_zy)=3/2 if z=y=1 and 1/2 otherwise.
Also Var(Y)=Var(Z)=1/4, μ=1/2, p=1 and β=1.

For every t : ℝ the conditional point probabilities are given in full:

- P(V=t | C_01)=(1/2)1_{t=0}+(1/2)1_{t=1}.
- P(V=t | C_11)=(1/2)1_{t=1}+(1/2)1_{t=2}.
- P(V+1=t | C_11)=(1/2)1_{t=2}+(1/2)1_{t=3}.
- P(V−1=t | C_11)=(1/2)1_{t=0}+(1/2)1_{t=1}.

In particular, P(V=0 | C_01)=1/2, P(V+1=0 | C_11)=0,
and P(V−1=0 | C_11)=1/2 are asserted separately. The sets
{0,1} and {2,3} in ℝ are disjoint (their intersection is empty).
There exists a real t where the conditional point probabilities of control V
and treated V+1 differ. Following that existential assertion, for every real t
(the universal quantifier is outside its witness) the theorem asserts all of:

- P(V=t | C_01)=P(V−1=t | C_11).
- P(V=t | C_01)=P(V=t+1 | C_11).
- P(V≤t | C_01)=P(V−1≤t | C_11).

The docstring describes a sign-error counterexample to a final distribution
comparison, together with satisfaction of a preceding displayed identity.
The correction of the comparison is asserted for this fixed witness, not for
all populations in this theorem.

Junk-value audit: every conditioning cell has probability 1/4, X=1 has
probability 1/2, and all finite sums exist. The uniform-law denominator 8 is
positive. V−1 is real subtraction after casting V, never natural truncated
subtraction; hence the formula really shifts the distribution down by 1.
The sets have ordinary real numeral elements. No undefined event conditioning,
nonintegrable mean, invalid division, empty population, logarithm, square
root, real power, extended-real conversion, extremum, or limit is involved.
The existential point-probability discrepancy has the explicit genuine
candidate t=0 in the preceding conjuncts.
