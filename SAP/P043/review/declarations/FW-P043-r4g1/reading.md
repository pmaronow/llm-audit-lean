# Blind reading

Saved before opening `claims.json` or `record.json`. This reading uses only
`closure.json`, the listed Challenge/Defs sources, their elaborated `#print`
output, and relevant Mathlib definitions. All 174 distinct declarations in the
five closures were inspected. `scratch/Closure.lean` prints them; its compilation
log is `scratch/closure-print.log`. Generated `_proof_*` declarations supply
ordinary numeral instances, nonemptiness, the measure interface, or proofs of
nonnegative normalized masses. Structure constructors and projections have
their usual meanings; none supplies an additional statistical assumption.

## SAP.P043.T1

This is a closed conjunction, with no parameters or hypotheses. It asserts facts
about two completely specified finite probability models.

Here is the full expansion of the finite-law notation used in this section and
below. A population on a finite type Ω is a function w : Ω → ℝ satisfying
w(i) ≥ 0 for every i and Σ_i w(i) = 1. Its expectation is E_w f = Σ_i w(i)f(i).
Write 1_A(i) for the real number 1 when A(i) holds and 0 otherwise. Event
probabilities are P_w(A) = Σ_i w(i)1_A(i), and event means are
Σ_i w(i)1_A(i)f(i) / P_w(A). Assignment is a Boolean z, represented numerically
by z = 0 or 1. For a real p, a_p(1) = p and a_p(0) = 1-p; joint masses are
a_p(z)w(i). The arm mean of f is

    A_z(f) = [Σ_i a_p(z)w(i) f(z,i)] / a_p(z).

The contrast is A_1(f)-A_0(f). The design expectation is
(1-p)E_w f(0,·)+p E_w f(1,·). Covariance is the design expectation of fg minus
the product of the design expectations; variance is covariance of f with itself.
The assignment regression slope is Cov(z,f)/Var(z). Uniform populations put
mass 1/|Ω| on each point of a nonempty finite type; product populations multiply
the two masses.

A mediation model consists of arbitrary functions K : Bool → Ω → ℝ and
S : Bool → ℝ → Ω → ℝ. Observed support is Y(z,i)=S(z,K(z,i),i). Its reduced form
τ is the contrast in Y. The two other quantities are

    M = Σ_i w(i)[S(0,K(1,i),i)-S(0,K(0,i),i)],
    D = Σ_i w(i)[S(1,K(1,i),i)-S(0,K(1,i),i)].

The generic linear mediation functions mentioned in the statement are
K(z,i)=α+a z+u₁(i) and S(z,k,i)=σ+b k+c z+u₂(i).

For the first fixed model, Ω=Bool×Bool with each point of mass 1/4. Let
u₁(r,s)=1/5 if r=true and -1/5 otherwise, and u₂(r,s)=1/10 if s=true and -1/10
otherwise. Set p=1/2 and

    K(z,i)=8+(6/5)z+u₁(i),
    S(z,k,i)=23/10+(k-8)/20-(3/50)z+u₂(i).

The conjunction asserts all of the following:

- Every (z,i) has joint mass 1/8. For every Boolean r,s the event with both
  coordinates equal to r,s has probability 1/4. For each Boolean r, each
  individual coordinate equals r with probability 1/2.
- For every latent point i, K(1,i)-K(0,i)=6/5>0. For every Boolean z, real k,h,
  and point i, if h>0 then S(z,k+h,i)-S(z,k,i)=h/20>0.
- The knowledge contrast is 6/5, M=3/50, D=-3/50, and τ=0. Var(z)=1/4,
  Cov(z,Y)=0, Cov(z,K)=3/10, the assignment slope for Y is 0, and that for K
  is 6/5. The real-number identities (6/5)(1/20)=3/50 and
  (6/5)(1/20)-3/50=0 hold.
- For every arm z and real y, the arm expectation of 1_{Y=y} is 1/4 if
  y∈{219/100,221/100,239/100,241/100}, and 0 otherwise.
- τ<M and M>0.
- For every z,i, Y(z,i)=23/10+u₁(i)/20+u₂(i). The entire model equals the
  generic linear model with parameters (α,a,σ,b,c)=(8,6/5,19/10,1/20,-3/50)
  and the above disturbances.

For the second fixed model, Ω=Fin 5×Fin 100. Equivalently let W∈{1,…,5} and
V∈{1,…,100} independently uniform, where W=i.1.val+1 and V=i.2.val+1. Each
latent point has mass 1/500, and p=1/2. Define

    K(z,W,V)=8+z(1+1_{W=5}),
    S(z,k,W,V)=2+1_{V ≤ 36+5(k-8)-6z},
    G(z,W,V)=2.

The conjunction asserts:

- Every joint (z,W,V) has mass 1/1000. For every z,i, K(z,i)∈{8,9,10},
  Y(z,i)∈{2,3}, and G(z,i)=2.
- For every Boolean z and real k, if k=8 or k=9, every pointwise one-unit
  increment S(z,k+1,i)-S(z,k,i) belongs to {0,1}, and its population mean is
  1/20. This is not a statement about all real k.
- A_0(K)=8, A_1(K)=46/5, and E_w[K(1)-K(0)]=6/5.
  E_w S(0,K(0),·)=59/25; E_w S(0,K(1),·)=121/50;
  E_w S(1,K(1),·)=59/25. Consequently M=3/50, D=-3/50, and τ=0 are asserted
  explicitly as well.
- For every arm z and real y, the arm probability of Y=y is 16/25 at y=2,
  9/25 at y=3, and 0 elsewhere. Each support arm mean is 59/25.
- For every i, K(0,i)=8, K(1,i)=10 when i.1.val=4 and 9 otherwise.
  The further implications W≤4 ⇒ K(1,i)=9 and W=5 ⇒ K(1,i)=10 are explicit.
- For every z,i, 0≤K(z,i)≤15, 0≤Y(z,i)≤3, and 0≤G(z,i)≤5.
- τ<M and M>0.

For each of the two populations separately, the conjunction also asserts that
both assignment arms have probability 1/2, every joint mass is nonnegative,
the total joint mass is 1, and each arm mass is 1/2. For every predicate
A : Ω → Prop and each z,

    Σ_i a_{1/2}(z)w(i)1_A(i) = a_{1/2}(z) P_w(A).

Thus independence is of the entire latent type, not merely of a selected
variable. The statement repeats the numerical values τ=0, M=3/50, D=-3/50,
and concludes for each model that D<0, ¬(τ≥M), and ¬(τ=0 ⇒ M≤0).
It does not assert a counterexample with D≥0. The docstring explicitly limits
the refuted reading to the unconditional comparison.

Junk-value audit: all finite means exist. All divisions used here have fixed
nonzero denominators: 2, cardinalities 2, 5, 100 and their products, the
displayed rational constants, and the assignment variance 1/4. Although the
general arm-mean/slope definitions return 0 for a zero denominator in ℝ, these
applications do not use that convention. All subtraction involving outcomes,
knowledge or the threshold is real subtraction. The only natural addition is
the exact relabelling of `Fin` values by +1; casts into ℝ are exact. `Fin`
indices are bounded and total. There is no log, sqrt, rpow, infinite sum,
Bochner integral, toReal, extremum, limit, or partial-function default here.
The finite populations are explicitly nonempty.

## SAP.P043.T2

This is a conjunction of a universally quantified law theorem and facts about
the fixed first model of T1. The universal quantifier order is: any type Ω in
universe u, any measurable space on Ω, any probability measure μ on it, any
p∈[0,1], then the hypothesis 0<p<1, then any mediation functions K,S, then five
integrability hypotheses. There is no finiteness or atomicity hypothesis.

The five integrable functions under μ are K(0,·), K(1,·),
S(0,K(0,·),·), S(0,K(1,·),·), and S(1,K(1,·),·). `Integrable` is Mathlib's
Bochner-integrability predicate, including almost-everywhere strong
measurability and finite integral of the norm. The model fields themselves
are ordinary real-valued functions as in T1.

The randomized measure is μ×(p δ_true+(1-p)δ_false), with Bernoulli weights
understood as nonnegative extended-real scalars. This explicitly makes the
Boolean assignment independent of all latent variables. For a function f,
its arm mean is

    A_z(f) = [∫_{Ω×{z}} f(t,i) d(μ×Bernoulli(p))]
              / [(μ×Bernoulli(p))(Ω×{z})].toReal.

Here the integrand on Ω×Bool is f(second coordinate, first coordinate), so
there is no reversal of the assignment probability. Define τ=A_1(Y)-A_0(Y),
Y(z,i)=S(z,K(z,i),i), and

    M=∫[S(0,K(1,i),i)-S(0,K(0,i),i)]dμ,
    D=∫[S(1,K(1,i),i)-S(0,K(1,i),i)]dμ.

The conclusion asserts, in this order:

- τ=∫S(1,K(1,i),i)dμ-∫S(0,K(0,i),i)dμ; τ=M+D;
  (τ≥M ↔ D≥0); (τ>M ↔ D>0); D≥0 ⇒ τ≥M;
  D≥0 ⇒ τ≤0 ⇒ M≤0; and D≥0 ⇒ τ=0 ⇒ M≤0.
- For every i, the pointwise total difference equals the sum of the
  assignment difference at K(1,i) and the knowledge difference with assignment
  held at 0. All subtractions are real.
- Next, for every α,a,σ,b,c∈ℝ and every u₁,u₂ : Ω→ℝ, if u₁ and u₂ are
  μ-integrable, the linear model K=α+a z+u₁ and S=σ+b k+c z+u₂ satisfies:
  its knowledge contrast is a, its M is ab, its D is c, its τ is ab+c,
  and τ≥M iff c≥0. For every natural n and d : Fin n→ℝ, if c=Σ_j d(j), then
  the same comparison holds iff Σ_j d(j)≥0.
- For those same linear parameters and disturbances, if a>0 then
  τ/a=b+c/a, and τ/a≥b iff c≥0. No ratio conclusion is imposed at a=0.
- For every natural n and d : Fin n→ℝ, (∀j, d(j)≥0) ⇒ Σ_j d(j)≥0.
  There also exists d : Fin 2→ℝ with Σ_j d(j)≥0 but not all d(j)≥0.
  These last channel assertions are quantified as arithmetic assertions; the
  link to the linear comparison is the preceding condition c=Σ_j d(j).

The final top-level conjunct uses the finite first model spelled out in T1
and says τ=0, M=3/50, D=-3/50, M>0. Its finite-law definitions are precisely
the weighted sums, product masses, arm differences and nested differences
already expanded in T1. There are no hypotheses on this fixed witness.

Junk-value audit: Mathlib's real Bochner integral is total and returns zero
for nonintegrable integrands. The five explicit integrability hypotheses
cover the nested functions and their differences; integrable u₁,u₂ cover the
linear specializations. Product-measure arm integrands are integrable under
the finite Bernoulli mixture. Probability measures are finite and σ-finite.
`ENNReal.toReal` maps ∞ to 0, but both arm masses are finite, equal to p and
1-p, and strictly positive here. Thus neither the integral default nor a
zero arm denominator supplies the asserted conclusions. The ratio formula
is guarded by a>0. The finite witness has p=1/2 and no undefined expectation.
An empty Ω admits no probability measure, so does not yield an inhabited
premise; there are many nonempty instances. n=0 is allowed for channel sums
and gives the usual empty sum 0, while the existential uses Fin 2 and is
nonempty. No truncated subtraction, log, sqrt, rpow, extremum, limit or
partial-function default occurs.

## SAP.P043.T4

This is a closed conjunction with no external hypotheses, about three
specified IV models. All finite probability/expectation/covariance definitions
are the sums expanded in T1, with p=1/2 throughout. An IV model is functions
K : Bool→Ω→ℕ and R : ℕ→Ω→ℝ. Potential support at any assignment z and dose k
is exactly R(k,i); the definition ignores z. Observed knowledge is the real
cast of K(z,i), and observed outcome is Y(z,i)=R(K(z,i),i). Thus exclusion and
consistency hold by construction, and their equalities are also conjuncts.
The first stage F is the knowledge arm contrast, the reduced form T is the
outcome arm contrast, and IV=T/F. An increaser is a point with K(0,i)<K(1,i).
Its conditional effect is

    E_w[1_{K0<K1}(R(K1,i)-R(K0,i))] / P_w(K0<K1).

The per-unit version replaces the inner effect, on increasers only, by
[R(K1,i)-R(K0,i)]/[cast(K1)-cast(K0)]; it uses 0 on other points before taking
the same conditional mean.

Let h(k)=1 if 9≤k, and 0 otherwise. The first population is Ω=Bool with
w(true)=2/3 and w(false)=1/3. At the true type, (K0,K1)=(8,9) and R(k)=3+h(k).
At the false type, (K0,K1)=(9,8) and R(k)=2+2h(k). The assertions are:

- A_0(K)=25/3, A_1(K)=26/3, F=1/3>0;
  A_0(Y)=A_1(Y)=10/3, T=0, IV=0.
  Cov(z,K)=1/12, Cov(z,Y)=0, and Cov(z,Y)/Cov(z,K)=0.
- The increaser probability is 2/3, its conditional effect is 1, and the
  arithmetic cancellation (2/3)·1+(1/3)·(-2)=0 holds.
- For every i, increaser(i) iff i=true; if it is an increaser then K0=8,
  K1=9, and R(9,i)-R(8,i)=1. For every assignment K∈{8,9} and K≤18.
  For every natural k, R(k,i)∈{2,3,4}, 0≤R(k,i)≤7, and R(·,i) is
  nondecreasing on ℕ.
- For every pair x=(i,j)∈Bool×ℕ with i an increaser and K0(i)<j≤K1(i),
  j=9 and R(j,i)-R(j-1,i)=1.
- For every natural n, sequence x : Fin n→Bool×ℕ, and weights
  w' : Fin n→ℝ, in that quantifier order, if all w'≥0, all x(a) satisfy the
  preceding increaser-crossing condition, and Σ_a w'(a)=1, then
  Σ_a w'(a)[R(j_a,i_a)-R(j_a-1,i_a)]=1 and this sum differs from IV.
- For every probability measure ν on Bool×ℕ, if ν-almost every x satisfies
  that increaser-crossing condition, then the increment function is
  ν-integrable, its Bochner integral is 1, and its integral differs from IV.
  Integrability is concluded, not assumed. The qualifying set is the singleton
  {(true,9)}, so this quantifier is inhabited, for example by its Dirac measure.

The other population is uniform on Fin 5, with each type of mass 1/5. The two
models are given by the following ordered lists, with indices 0,…,4:

    A: K0=(8,8,9,8,9), K1=(9,9,8,8,9),
       R(k)=(3+h(k),3+h(k),2+2h(k),2,4).
    B: K0=(8,8,9,8,9), K1=(9,9,8,9,8),
       R(k)=(3+h(k),3+h(k),2+2h(k),2+2h(k),2+2h(k)).

For each model separately, A_0(K)=42/5, A_1(K)=43/5, F=1/5>0,
A_0(Y)=A_1(Y)=16/5, T=0, and IV=0. For every type and assignment,
K∈{8,9} with K≤18. For every natural k, 0≤R(k,i)≤7, R(·,i) is
nondecreasing, and any increaser goes from 8 to 9.

The conditional observable point mass at (z,k,y) is
Σ_i w(i)1_{K(z,i)=k ∧ Y(z,i)=y}. For all Boolean z, natural k and real y,
each model's conditional law equals

    z=1: (2/5)1_{k=8,y=2}+(3/5)1_{k=9,y=4};
    z=0: (1/5)1_{k=8,y=2}+(2/5)1_{k=8,y=3}+(2/5)1_{k=9,y=4}.

The joint observable point mass at x=(z,(k,y)) is a_{1/2}(z) times that
conditional mass. The complete joint point-mass functions of A and B are
asserted equal. The increaser conditional effects are 1 for A and 4/3 for B;
the probabilities are nonzero and, more precisely, 2/5 and 3/5 respectively.
The per-unit effects are 1 for the first model, 1 for A and 4/3 for B.

There does not exist any function

    G : ((Bool×(ℕ×ℝ)→ℝ)→ℝ)

whose value on A's joint observable mass function equals A's conditional
effect and whose value on B's equals B's conditional effect. This forbids
recovery even by arbitrary functions of these finite laws; it does not rely
on restricting the recovery function to a statistical subclass.

Finally, the fair-product-assignment conjunction expanded in T1 holds for
both the two-type population and the uniform five-type population, and the
exclusion/consistency equalities expanded above hold for all three models.

Junk-value audit: every finite arm denominator is 1/2; all first stages and
the covariance ratio denominator are positive (1/3, 1/5, 1/12). All conditional
increaser probabilities are explicitly positive. Real per-unit denominators
are used only for increasers and equal 1 in these models; the conditional
branch avoids division elsewhere. `doseIncrement` uses natural j-1, truncated
at 0 in general, but every tested crossed margin is 9. Every unrestricted
increment under a measure is 1 almost everywhere, and integrability is an
explicit conclusion, so the nonintegrable-Bochner default cannot produce
the claimed integral 1. The measure domain is nonempty and supports a
qualifying Dirac law. Fin 0 is allowed in the finite weighted-average
quantifier, but Σw'=1 then cannot hold; n=1 gives a nonvacuous instance.
The five-element vectors use bounded Fin indices with no out-of-range
default. Point masses describe complete laws here because support is finite.
No other listed junk-value operation occurs.

## SAP.P043.T5

This theorem is universal, with quantifiers and hypotheses ordered as follows:
any type Ω in universe u, a finite enumeration of Ω, a population weight
function w≥0 with Σw=1, any p∈ℝ, then 0<p<1, then any IV functions
K : Bool→Ω→ℕ and R : ℕ→Ω→ℝ, any natural bound J, then

    (∀i, K0(i)≤J and K1(i)≤J),
    (∀i, K0(i)≤K1(i)),
    Σ_i w(i)[cast(K1(i))-cast(K0(i))]>0.

The law is independent Bernoulli assignment with joint masses a_p(z)w(i),
the arm means and covariances are exactly the finite formulas expanded in
T1, and observed Y(z,i)=R(K(z,i),i). Exclusion is built into the model, as
expanded in T4. Denote the first stage by F, outcome contrast by T, and IV=T/F.
Define, for every natural j and point i,

    Δ_j(i)=R(j,i)-R(j-1,i),
    C_j(i)=1_{K0(i)<j≤K1(i)},
    H_j(i)=1_{j≤K1(i)}-1_{j≤K0(i)},
    q_j=Σ_i w(i)C_j(i), v_j=q_j/F,
    e_j=[Σ_i w(i)C_j(i)Δ_j(i)]/q_j.

Every sum over r∈range J below has r=0,…,J-1 and uses margin j=r+1, so
equivalently it sums over j=1,…,J. The conclusion is the following conjunction:

- F=Σ_i w(i)[cast(K1(i))-cast(K0(i))], and
  T=Σ_i w(i)[R(K1(i),i)-R(K0(i),i)].
- Cov(z,K)=p(1-p)F and Cov(z,Y)=p(1-p)T. If F≠0, then
  Cov(z,Y)/Cov(z,K)=IV.
- For every i, R(K1(i),i)-R(K0(i),i)=Σ_{j=1}^J C_j(i)Δ_j(i), and
  cast(K1(i))-cast(K0(i))=Σ_{j=1}^J C_j(i).
- T=Σ_{j=1}^J Σ_i w(i)C_j(i)Δ_j(i), and F=Σ_{j=1}^J q_j.
- For every natural j, v_j≥0; Σ_{j=1}^J v_j=1; and
  IV=Σ_{1≤j≤J, q_j>0} v_j e_j.
- For every other IV model K',R' on the same Ω, every natural J', and
  every i, if K'0(i)≤J' and K'1(i)≤J', then
  R'(K'1(i),i)-R'(K'0(i),i)=Σ_{j=1}^{J'} H'_j(i)Δ'_j(i) and
  cast(K'1(i))-cast(K'0(i))=Σ_{j=1}^{J'} H'_j(i).
  These further models need not satisfy monotonicity, but this whole
  conclusion remains inside the outer hypotheses for the original model.
- For every i,j, if ¬(K0(i)<K1(i)) then C_j(i)=0.
- For every i,j, H_j(i)∈{-1,0,1}, and H_j(i)=C_j(i). This is stated for
  the original monotone model, not for every K',R'.
- For every other IV model on Ω, every i,j, if K'1(i)<j≤K'0(i), then
  H'_j(i)=-1.

The docstring discloses the finite-type restriction with arbitrary normalized
nonnegative masses, the confinement of identification/covariance conclusions
to the outer monotonicity and positive-stage hypotheses, and omissions of
general nonmonotone signed-crossing set membership, a particular down-type
response value, and separate nonidentification. No assertion about nonatomic
laws is present. No sign or monotonicity assumption on the response R is
required.

Junk-value audit: arm denominators p and 1-p are positive. The first population
identity plus the positive mean hypothesis makes F>0; covariance denominator
p(1-p)F is therefore positive. q_j may vanish, and the definition of e_j then
uses ℝ division by zero, returning 0. Such terms are deliberately excluded
from the IV formula by the strict filter q_j>0. Hence that convention has no
effect on any claimed conditional effect. `j-1` is natural truncated
subtraction, but telescoping sums use j=r+1≥1. At j=0, Δ_0=R(0)-R(0)=0
and both crossing functions are 0; no negative dose is asserted.
The knowledge difference in the stage and signed identities is subtraction
after casting to ℝ, so downward changes remain negative. Finite sums are
always defined. J=0 is allowed syntactically but inconsistent with the
positive mean hypothesis under the bounds; J=1 and a one-point population
give a nonvacuous instance. An empty Ω cannot carry normalized weights.
Zero-weight types are allowed and still subject to pointwise bounds and
monotonicity. There is no integral, toReal, log, sqrt, rpow, extremum, limit,
or partial-function default in this closure.

## SAP.P043.T6

The quantifier order is any naturals n,q, any stratum assignment
s : Fin n→Fin(q+1), then any γ : Fin q→ℝ. Strata 0,…,q-1 have coefficients
γ(0),…,γ(q-1), and stratum q is the reference. For each observation i and
nonreference stratum k define

    d(i,k)=1 if s(i)=k (embedded from Fin q into Fin(q+1)), else 0,
    g(i)=Σ_{k∈Fin q} γ(k)d(i,k),
    c(r)=γ(r) for r<q and c(q)=0.

These are the full expansions of the indicator, stratum effect, and
`Fin.lastCases` coefficient definition. The statement is a conjunction of:

- For every i∈Fin n and k∈Fin q, if s(i)=k then g(i)=γ(k).
- For every i∈Fin n, if s(i)=q then g(i)=0.
- For every i∈Fin n, Σ_{k∈Fin q} d(i,k)=1-1_{s(i)=q}, with subtraction in ℝ.
- Next, for every X : Fin n→Fin 2, u,Y : Fin n→ℝ and β₀,β₁∈ℝ,

      (∀i, Y(i)=β₀+β₁ cast((X(i)).val)+g(i)+u(i))
        ↔
      (∀i, Y(i)=(β₀+c(s(i)))+β₁ cast((X(i)).val)+u(i)).

Thus the treatment is binary, γ and β are arbitrary real coefficients, and
there is no estimation, residual orthogonality, randomization or identification
claim. The corrected regression right side is precisely the first expression
inside the equivalence; it is not another hypothesis in the theorem.

Junk-value audit: q=0 is a meaningful single reference stratum, with unique
s(i)∈Fin 1, empty nonreference sum 0, and c=0. n=0 has no observations, so
the observation-wise assertions are vacuous for that instance, but positive n
is also covered. `Fin.lastCases` has an explicit reference value 0 and is a
total case split, not an unspecified default. Both embeddings and treatment
casts preserve their exact natural values. All subtraction is real. There
are no divisions, integrals, toReal, logs, roots, rpow, infinite operations,
extrema, limits, or partial-function defaults. The docstring describes only
these algebraic/indexing identities.
