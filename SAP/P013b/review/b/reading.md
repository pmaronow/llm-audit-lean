# Blind statement reading

Saved before opening `claims.json` or `record.json`. Sources read: all ten
`SAP/P013b/Defs/Part*.lean` files, the Defs aggregator, and both Challenge
files. There are twelve theorems, each asserting the corresponding
`TxxStatement`. The following notation expands those definitions; it is part
of each reading, rather than an additional assumption.

## Common finite probability and estimator definitions

`Fin N` is the set of integers from 0 through N−1. Unless a clause says
otherwise, N and K are arbitrary natural numbers and Ω is an arbitrary finite
type. A design P is a function p:Ω→ℝ with p(z)>0 for every z and
Σ_z p(z)=1. Thus Ω cannot be empty. E[X]=Σ_z p(z)X(z),
Pr(A)=Σ_{z:A(z)}p(z), Cov(X,Y)=E[XY]−E[X]E[Y], and Var(X)=Cov(X,X).
There are no measurability or integrability qualifications to these finite sums.

A population F consists of arbitrary maps D:Ω×Fin N→Fin K and
y:Fin N×Fin K→ℝ. Its observed outcome is Y_i(z)=y_i(D_i(z)); exposure-specific
potential outcomes and consistency are consequently built into the objects.
Write I_id(z)=1 if D_i(z)=d and 0 otherwise,
π_id=E[I_id], and π_ij,de=E[I_id I_je].
`Positivity F d` means **both** 0<π_id and π_id<1 for every i.
T_d=Σ_i y_id, μ_d=T_d/N, τ_de=μ_d−μ_e,
H_d(z)=Σ_i I_id(z)y_id/π_id, and C_d(z)=Σ_i I_id(z)/π_id.
`htMean` is H_d/N and `htEffect` is (H_d−H_e)/N.

For i,j,d,e define

    B_ij,de(z) = I_id(z) I_je(z)
      · (π_ij,de − π_id π_je)/π_ij,de · (y_id/π_id) · (y_je/π_je).

All double sums below are ordered sums, and i≠j means precisely the
`univ.erase i` index used in the source. Define

    V_d = Σ_i I_id(1−π_id)(y_id/π_id)^2 + Σ_{i≠j} B_ij,dd;
    A2_d = Σ_{i≠j:π_ij,dd=0}
              [I_id y_id^2/(2π_id) + I_jd y_jd^2/(2π_jd)];
    C_HT,de = Σ_{i≠j} B_ij,de
              − Σ_i [I_id y_id^2/(2π_id) + I_ie y_ie^2/(2π_ie)];
    C_A,de = Σ_{i≠j:π_ij,de>0} B_ij,de
              − Σ_{i,j:π_ij,de=0}
                    [I_id y_id^2/(2π_id) + I_je y_je^2/(2π_je)];
    V_effect,de = (V_d + A2_d + V_e + A2_e − 2 C_A,de)/N^2.

`differenceTotal F d g` is
Δ_d(g)=H_d−Σ_i I_id g_i/π_id+Σ_i g_i. Predictions g are deterministic
functions of i. The corresponding `differenceEffect` is
δ_de(g,k)=(Δ_d(g)−Δ_e(k))/N. `hajek` is H_d/C_d.
All divisions are Lean real division: x/0=0, including 0/0=0. In particular,
zero joint probabilities contribute zero to B. An individual clause's positive
denominator hypotheses must be checked separately.

A shifted population y^c has the same D and outcomes y_id+c for **all** i,d.
Its π are therefore unchanged. Put w_id(z)=I_id(z)/π_id and
L_d(h,c,z)=Σ_i(1−w_id(z))(h_i−c); this is `translationError`.

A recording R is a fixed Boolean function of (i,d), not of the realized
assignment except through d. The recorded population has the same D and
G_id=y_id if R_id=true and G_id=0 otherwise. Its data at (z,i) are
(D_i(z),G_i,D_i(z),R_i,D_i(z)). Define lost mean
ℓ_d=N^−1 Σ_{i:R_id=false} y_id.

For a fixed exposure vector D_i, weights w_i, scores G_i and finite set T,
write A_d(T)=Σ_{i∈T:D_i=d}w_iG_i and B_d(T)=Σ_{i∈T:D_i=d}w_i.
These are the recorded numerator and denominator; they do not themselves
impose a randomization or inverse probability interpretation on w.

## Mathlib endpoints and limiting definitions

`Fintype.piFinset` is the finite set of functions whose value at each index
belongs to its specified finite set (`Mathlib/Data/Fintype/Pi.lean:32`, with
`mem_piFinset`). `univ.powersetCard r` is exactly the set of r-element
subsets (`Mathlib/Data/Finset/Powerset.lean:198`, with `mem_powersetCard`).
Thus the school supports below are literal subsets, without ordered-subset
or multiplicity conventions.

`normalCDF x` is the CDF of `gaussianReal 0 1`: the mean-zero,
variance-one Gaussian probability measure, with Lebesgue density the
ordinary Gaussian density (`Mathlib/Probability/Distributions/Gaussian/Real.lean:222`).
Mathlib's `cdf_eq_real` identifies this CDF with Pr((−∞,x])
(`Mathlib/Probability/CDF.lean:57,83`). For 0<α<1,
q_α=`normalCritical α` is inf{x∈ℝ:Φ(x)≥1−α/2}, the usual positive
normal critical value; this set is nonempty and bounded below.
`Real.sqrt` is the nonnegative real square root on nonnegative inputs and
zero on negative inputs. `Tendsto ... atTop (𝓝 a)` for a real sequence is
ordinary convergence as the natural index tends to infinity.
`Filter.liminf` on ℝ is the supremum of eventual lower bounds
(`Mathlib/Order/LiminfLimsup.lean:50–67`, the dual of `limsSup`/`limsup`).
Here coverage probabilities lie in [0,1], so this is the usual real liminf,
without an unbounded-set convention contributing to the result.

## SAP.P013b.T15

For every finite Ω, every natural N,K, every design P and population F:
if N>0, then for every d,e∈Fin K, if d≠e, `Positivity F d`, and
`Positivity F e`, the following four assertions hold together:

1. If π_ij,de>0 for every distinct i,j, E[C_HT,de]≤Cov(H_d,H_e).
2. If those same off-diagonal cross joints are positive **and** y_id=y_ie
   for every i, E[C_HT,de]=Cov(H_d,H_e).
3. Without any cross-joint positivity assumption, E[C_A,de]≤Cov(H_d,H_e).
4. Var((H_d−H_e)/N)≤E[V_effect,de].

The first estimator's bound is a lower bound on covariance, while the
effect variance bound is an upper bound. No sign restriction is imposed
on outcomes. The cross-joint assumptions are local to clauses 1 and 2.

## SAP.P013b.T16

For every finite Ω, natural N,K, design P and population F, if N>0,
then for every d with 0<π_id<1 for all i, and then every deterministic
g:Fin N→ℝ, all of the following hold:

1. E[Δ_d(g)]=T_d.
2. For every assignment z,
   Δ_d(g,z)=Σ_i I_id(z)(Y_i(z)−g_i)/π_id+Σ_i g_i.
3. E[C_d]=N.
4. |E[H_d/C_d]−μ_d|≤sqrt(Var(C_d/N) Var(H_d/C_d)).

The ratio is specifically zero when C_d=0. There is no assumption that
each assignment exposes any unit to d, and g may be any real-valued
fixed prediction.

## SAP.P013b.T17

For every finite Ω, natural N,K, design P, population F, and N>0,
then every randomization-indexed outcome array r:Fin N×Ω→ℝ and every
d,e∈Fin K: assume d≠e, assume there exist i,z,z′ with
D_i(z)=D_i(z′) but r_i(z)≠r_i(z′), and assume 0<π_id,π_ie<1 for every i.
Define

    H^r_d(z)=Σ_i I_id(z) r_i(z)/π_id,
    ω_i(z)=p(z)/π_i,D_i(z),
    T^r_d=Σ_i Σ_{z:D_i(z)=d} ω_i(z) r_i(z).

Then E[H^r_d]=T^r_d and
E[(H^r_d−H^r_e)/N]=(T^r_d−T^r_e)/N.
The array r is distinct from F's fixed y. No relationship between those
two arrays is required. The existence assumption explicitly requires a
failure of exposure sufficiency somewhere; it does not require it for
each unit or exposure.

## Sequence objects shared by T18 and T19

An experiment of size N has natural support size s and exposure count K,
a design on Fin s and a population of N units and K exposures.
An experiment sequence S supplies such an experiment with N=n+1 for
every natural n, chosen labels d_n≠e_n, and 0<π_i,d_n,π_i,e_n<1
for every n,i. Write τ_n, τhat_n, v_n and vhat_n for its causal effect,
HT effect, true variance and `V_effect` estimator.

`NestedPopulationSetup` says there exist, in this order, injections
λ_n:Fin K_n↪ℕ, fixed distinct natural labels d,e, and a fixed array
y:ℕ×ℕ→ℝ such that λ_n(d_n)=d, λ_n(e_n)=e and the potential outcome
of unit i and label a in experiment n equals y(i.val,λ_n(a)). There is
no cross-n compatibility requirement on assignment laws or exposures.
`StandingPositivity` further requires 0<π_ia<1 for every n,i,a,
including labels other than d_n,e_n.

`Condition3`: there exist fixed real c1≥0 and c2>0 such that for every
n,i,a, |y_ia|≤c1 and |1/π_ia|≤c2.

`PairIndependent(i,j)`: π_ij,ab=π_iaπ_jb for every exposure pair a,b.
`Condition4`: there exists a Boolean array g_n(i,j) for every n such
that whenever g_n(i,j)=false, PairIndependent(i,j) holds, and
(Σ_iΣ_j 1{g_n(i,j)=true})/(n+1)^2→0. No symmetry is required.

`VectorIndependent(A,B)` requires, for **every** pair of label vectors
a,b:Fin N→Fin K,

    Pr(∀i∈A,D_i=a_i and ∀j∈B,D_j=b_j)
      = Pr(∀i∈A,D_i=a_i) Pr(∀j∈B,D_j=b_j).

For a Boolean array h, `PrintedNoEdge(h,A,B)` is **exactly** that there
do not exist i,j with h(i,j)=true and at least one of

    (i∈A and j∉B), (j∈A and i∉B),
    (i∉A and j∈B), (j∉A and i∈B).

`PrintedDependency` requires VectorIndependent(A,B) for every A,B
that are disjoint and satisfy this particular `PrintedNoEdge` predicate.
`Condition5Printed`: there exist one natural m and Boolean arrays h_n
such that for every n, PrintedDependency holds and every row of h_n
contains at most m true entries. There is no zero-diagonal, symmetry,
or ordinary no-edge-between-A-and-B requirement in this definition.

`Condition6`: there exists a real c>0 with (n+1)v_n→c.
Coverage at n and level α is

    c_n(α)=Pr(vhat_n≥0 and |τhat_n−τ_n|≤q_α sqrt(vhat_n)).

A negative variance estimate is explicitly excluded from the event.
Convergence in probability of X_n to a means: for every real ε>0,
Pr(|X_n−a|>ε)→0. Its laws are allowed to vary with n.

## SAP.P013b.T18

The theorem negates this universal statement: for every sequence S,
if nestedness, standing positivity, Condition 3, printed Condition 5,
and Condition 6 hold, then for every real α with 0<α<1,
1−α≤liminf_n c_n(α).

Equivalently in ordinary classical mathematics, **there exist** S and
α satisfying every one of those hypotheses and 0<α<1 for which
liminf_n c_n(α)<1−α. It asserts failure of the coverage claim with this
exact printed graph predicate. It does not itself give a named sequence,
a value of α, or a claim about a corrected dependency condition.

## SAP.P013b.T19

For every sequence S, nestedness, standing positivity, Condition 3 and
Condition 4 imply that τhat_n−τ_n converges in probability to zero.
Explicitly: for every real ε>0,
Pr(|τhat_n−τ_n|>ε)→0 as n→∞. The bounds and graph arrays in those
conditions are existentially quantified before the convergence conclusion.
There is no Condition 5, Condition 6, variance lower bound, or normality
assumption in this theorem.

## SAP.P013b.T21

This is a conjunction of unconditional facts about a specified example,
not a universal statement about arbitrary populations. The three
assignments z=0,1,2 have probabilities 1/4,1/4,1/2. There are three
units and two labels. Exactly unit z receives label 1, all others label
0. Predictions are g=(2,3,5), and y_id=g_i for both labels. The shift
adds 1 to every potential outcome and initially holds g fixed.

For every unit, π_i1=p(i), π_i0=1−p(i), and every exposure is strictly
between zero and one. For every i,d, y_id=g_i, and
Cov(g_i,I_i1)=0. Every assignment has exactly one label-1 unit and
two label-0 units. Both unshifted potential totals are 10 and both
shifted totals are 13; the true effect is zero before and after the
shift. For every assignment and label, unshifted Δ_d(g)=10 and the
unshifted difference effect is zero.

The assignment-specific assertions are the following (the first column
applies separately to z=0 and z=1):

| Quantity | z=0 or 1 | z=2 |
|---|---:|---:|
| C_1 | 4 | 2 |
| C_0 | 10/3 | 8/3 |
| shifted Δ_1(g) | 14 | 12 |
| shifted Δ_0(g) | 40/3 | 38/3 |
| shifted δ_10(g,g) | 2/9 | −2/9 |
| shifted Δ_1−old Δ_1−3 | 1 | −1 |
| shifted Δ_0−old Δ_0−3 | 1/3 | −1/3 |

Thus for **every** assignment neither shifted total equals its old
value plus 3, and the shifted effect differs from its old value even
though the true effect is unchanged. The source repeats the positivity,
zero covariance and fixed realized-count facts in this refutation clause.
Both shifted totals have expectation 13 and the shifted difference
effect has expectation zero. All three unshifted estimator variances
are zero; their shifted variances are respectively 1,1/9,4/81.
For every z, jointly shifting g to g+1 makes both difference totals
exactly 13 and the difference effect zero. For every z,i, the original
residual is 0, the shifted-outcome/fixed-prediction residual is 1, and
the jointly shifted residual is 0. Finally the theorem repeats and
identifies the errors as shifted Δ_d=10+C_d and
shifted δ_10−old δ_10=(C_1−C_0)/3, with the values in the table.

## SAP.P013b.T22

This theorem is a conjunction of twelve separately universally
quantified clauses and one fixed example. In clauses involving an
arbitrary population, Ω is finite, P is a design and F is a population;
all functions and constants below are deterministic. Quantifier and
hypothesis scopes are as follows.

1. For every F,d,g,h,c,z, then N>0 and π_id>0 for all i:
   Δ^c_d(g+h,z)−Δ_d(g,z)=c C_d(z)+Σ_i(1−w_id(z))h_i.
2. With the identical quantifiers and hypotheses, subtracting cN
   from that difference gives L_d(h,c,z).
3. With the identical quantifiers and hypotheses,
   Δ^c_d(g+h,z)=Δ_d(g,z)+cN iff L_d(h,c,z)=0.
4. For every F,d,g,c,z, then N>0 and all π_id>0,
   Δ^c_d(g+c,z)=Δ_d(g,z)+cN.
5. For every F, N>0, d,e,g,k,c,z, then positive marginals for d,e
   and d≠e: the jointly shifted totals divided by N equal the
   original divided totals plus c; on units exposed to the appropriate
   label the jointly shifted residual equals the old residual; the
   jointly shifted δ_de equals the old δ_de; T^c_d=T_d+cN,
   T^c_e=T_e+cN, and τ^c_de=τ_de.
6. For every F, N>0, d,e,g,k,h,l,c,z, then positive marginals for
   d,e and d≠e: δ^c_de(g+h,k+l)−δ_de(g,k)
   =(L_d(h,c,z)−L_e(l,c,z))/N. The two effects are equal iff
   L_d(h,c,z)=L_e(l,c,z).
7. For every F, N>0, d,e,g,k,c,z, then positive marginals for d,e
   and d≠e: with predictions held fixed, Δ^c_d(g)−Δ_d(g)=cC_d;
   its error relative to cN is c(C_d−N); and
   δ^c_de−δ_de=c(C_d−C_e)/N. If c≠0, the total is equivariant
   iff C_d=N and the effect is invariant iff C_d=C_e.
8. For every F,d,i, if π_id>0, E[w_id]=1. This clause imposes
   no N>0 separately; an index i already requires a unit to exist.
9. For every F, N>0, d,e,c,z, then positive marginals for d,e and
   d≠e: zero predictions give Δ_d=H_d and δ_de=HT effect;
   H^c_d−H_d=cC_d and HT^c_de−HT_de=c(C_d−C_e)/N.
10. For every F,d,g,h,c, if all π_id>0: E[L_d(h,c)]=0,
    E[Δ^c_d(g+h)]=E[Δ_d(g)]+cN=T_d+cN, and E[C_d]=N.
    No N>0 or upper bound π_id<1 is required in this clause.
11. For every F,d,e,c, positive d,e marginals, N>0 and d≠e:
    E[c(C_d−N)]=0 and E[c(C_d−C_e)/N]=0.
12. For every F, N>0, d, natural m≥1, assume for every z that
    Σ_i I_id(z)=m and for every i that π_id=m/N. Then for every
    g,c and every z, C_d(z)=N and
    Δ^c_d(g,z)=Δ_d(g,z)+cN. No π_id<1 assumption is added.
13. The fair two-assignment, two-unit design assigns label 1 exactly
    to the unit whose index equals z, with all potential outcomes zero.
    For every label its marginals are strictly between 0 and 1;
    for every z, C_1=2 and shifting all outcomes by 1 while retaining
    zero predictions raises Δ_1 by 2.

There are twelve universal clauses above and the thirteenth is the
fixed calibration example (the count here follows the top-level
conjuncts in the Lean definition).

## SAP.P013b.T23

The design consists of two independent fair labels z=(z_1,z_2)∈{0,1}²
with probability 1/4 for each pair. Unit 0 receives z_1 and unit 1
receives z_2. In each of three worlds unit 0 has potentials (0,1).
Unit 1 has potentials (0,0) in world 0, (0,1) in world 1, and (1,0)
in world 2. Recording is true for unit 0 and false for unit 1 at both
labels. All assertions below are unconditional, quantified over every
world and, where a realized quantity occurs, every assignment (and
every unit or exposure where indicated).

Every potential outcome is 0 or 1; every unit/exposure probability is
1/2 and strictly between zero and one. The recorded outcome equals
Σ_d I_id G_id. The full data map is identical across all worlds, and
explicitly records (z_1,z_1,true) at unit 0 and (z_2,0,false) at unit 1.
The recorded HT effect is z_1; its expectation, variance and recorded
target are respectively 1/2,1/4,1/2.

| World | wearing τ_10 | lost ℓ_0 | lost ℓ_1 | E[recorded HT]−wearing τ |
|---|---:|---:|---:|---:|
| 0 | 1/2 | 0 | 0 | 0 |
| 1 | 1 | 0 | 1/2 | −1/2 |
| 2 | 0 | 1/2 | 0 | 1/2 |

There is no real-valued function of the **entire assignment-indexed
recorded-data map** that equals the wearing causal effect in all three
worlds. The bias equals ℓ_0−ℓ_1 in every world.
The respondent-only population contains just unit 0 with the same
assignment law and potentials (0,1). Its HT effect is 2z_1 and its
expectation is 1. In every world and assignment the all-unit recorded
HT is half the respondent HT. Respondent HT bias against the full
wearing target is 1/2,0,1 in worlds 0,1,2 respectively. The difference
of the two estimators' expectations is 1/2 in every world.

## SAP.P013b.T24

Six top-level conjuncts assert the following.

1. For every finite Ω, natural N,K, design P, population F and
   Boolean recording R, then N>0, d,e, d≠e and positive d,e
   marginals (no upper bounds): the recorded HT mean at d and
   effect d−e are unbiased for their recorded targets. For every
   exposure a, μ^G_a=μ^y_a−ℓ_a. The recorded effect is
   τ^y_de−ℓ_d+ℓ_e, and recorded HT bias for τ^y_de is ℓ_e−ℓ_d.
   Unbiasedness for that wearing effect holds iff ℓ_d=ℓ_e;
   unbiasedness of its d mean for μ^y_d holds iff ℓ_d=0.
   For every a, if all y_ia≥0, then ℓ_a≥0 and ℓ_a=0 iff
   every unrecorded y_ia is zero.
2. For every F,R,N>0,d,e,d≠e and positive d,e marginals, then
   nonnegative potentials at d,e and zero potentials at each
   unrecorded (i,d) and (i,e): the recorded HT effect is unbiased
   for the wearing effect.
3. For every natural N,K, exposure vector D, arbitrary real w,G,
   sets S and SR⊆S with |S|,|SR|>0, positive w_i on S, and
   every nonzero score in S belonging to SR, then every d,e:
   for all a, A_a(SR)=A_a(S);
   A_d(S)/|S|=(|SR|/|S|)(A_d(SR)/|SR|);
   (A_d(S)−A_e(S))/|S|=(|SR|/|S|)(A_d(SR)−A_e(SR))/|SR|.
   If B_d(SR)>0, additionally
   A_d(S)/B_d(S)=[B_d(SR)/B_d(S)] A_d(SR)/B_d(SR).
4. For every N,K,D,w,G,S,item,survey, assume item⊆S,
   survey⊆S, |S|=2050, |item|=1708, |survey|=1899,
   positive weights on S, and every nonzero score in S belongs
   to **both** item and survey. For every d,e the full-set
   difference of numerators divided by 2050 equals respectively
   (854/1025) times the item-set contrast divided by 1708 and
   (1899/2050) times the survey-set contrast divided by 1899.
   No subset relation between item and survey is assumed, and
   no assertion identifies these hypothetical sets with real data.
5. In the fixed example N=3,K=2, D=(1,1,0), w=(2,2,2),
   G=(1,0,1), S={0,1,2}, SR={0,2}: all nonzero scores are
   retained, the denominator ratios for d=1 and d=0 are 1/2
   and 1, and there exists **no** real c making the full-set
   Hájek contrast equal c times the retained-set Hájek contrast.
   Here those contrasts are −1/2 and 0 respectively.
6. Exact arithmetic: 2050−342=1708 and 2050−151=1899 in ℕ,
   1708/2050=854/1025, 342/2050=171/1025, and
   1899/2050+151/2050=1 in ℝ.

## School definitions shared by T25 and T26

The 56 schools are pairs (block,position)∈Fin 14×Fin 4.
B is the set of functions choosing an unordered pair of positions in
each block, and H_B(z) consists of those chosen schools. C is the set
of all 28-element subsets of the 56 schools. Uniform mean on a set S
is Σ_{z∈S}X(z)/|S|; uniform event probability is its event count/|S|;
uniform variance is mean(X²)−mean(X)². These definitions totalize
empty S by real division by zero, but the named B,C are nonempty.
`schoolBadHosts` H* consists of every school in blocks 0 through 6.

For distinct schools a,b, put x_i=1 if i=a or i=b and zero otherwise.
Its potential outcomes are y_i(true)=x_i and y_i(false)=0.
For any Boolean hosting map H on any type α, write J_i(z)=1{H(z,i)}.
The example's observed outcome is J_i x_i,
T(z)=Σ_i J_i(z)x_i/(1/2), and

    V_q(z)=Σ_i J_i(z)(1−1/2)(x_i/(1/2))²
      + Σ_{i≠j} J_i(z)J_j(z) (q−1/4)/q
                     · (x_i/(1/2)) · (x_j/(1/2)).

The B and C hosting maps are membership of the corresponding host sets.

For student formulas, a separate finite type Ξ has weights Q_x≥0
with Σ_x Q_x=1, school membership s:Fin N→School and arbitrary
codes k:Ξ×Fin N→Fin 4. Independently draw school assignment
uniformly from B or C and x according to Q. Student exposure is
0 if the school is not hosting and k_i(x)+1 otherwise.
`schoolStudentJoint` is exactly the double weighted sum of the two
exposure indicators under that product law; its same-student,
same-exposure version is `schoolStudentMarginal`.

## SAP.P013b.T25

The conjunction contains these assertions:

1. H* has size 28, belongs to C, differs from H_B(z) for every
   z∈B, has C probability 1/7648690600760440>0 and B
   probability zero.
2. For every distinct a,b, all school potentials are binary,
   their hosting total is 2 and their nonhosting potentials are
   zero; for every type α, Boolean hosting map H, z and i,
   the observed example outcome is J_i(z)x_i.
3. For every type α,H, distinct a,b and z,
   T(z)=2(J_a(z)+J_b(z)) and Σ_i x_i=2.
4. For every type α,H, distinct a,b, real q and z, if q>0,
   V_q(z)=2(J_a+J_b)+8J_aJ_b(q−1/4)/q.
5. For every type α, finite S⊆α, hosting map H, distinct a,b,
   and real p,q, assume each of a,b hosts with uniform S
   probability 1/2 and their joint hosting probability is p.
   If q>0, then E_S[T]=2, Var_S(T)=8p, and
   E_S[V_q]=2+8p(q−1/4)/q. S need not separately be assumed
   nonempty, because its marginal probability hypotheses force it.
6. With the same S,H,a,b and marginals and joint p>0,
   E_S[V_p]=Var_S(T).
7. For B and a=(0,0),b=(0,1), E[T]=2, Var(T)=4/3 and
   E[V_(27/110)]=160/81. For B and a=(0,0),b=(1,0),
   Var(T)=2 and E[V_(27/110)]=53/27<2. For C and the
   first pair, Var(T)=E[V_(27/110)]=108/55.
8. The two B variance-estimator biases just listed are exactly
   52/81 and −1/27.
9. For every school a, both laws give hosting and nonhosting
   probabilities 1/2. The displayed same-block B, different-block B,
   and C joint hosting probabilities are 1/6,1/4,27/110.
10. 1/(56 choose 28)=1/7648690600760440.

The arbitrary α clauses do not assume a finite type; their explicit
S is a finite set. The named-law assertions are unconditional.

## SAP.P013b.T26

The conjunction asserts:

1. |B|=6^14=78364164096 and |C|=(56 choose 28)=7648690600760440.
2. For every z∈B, H_B(z)∈C.
3. Every school has B hosting marginal 1/2, and every school
   has C hosting marginal 1/2.
4. For every distinct a,b, the B joint hosting probability is
   p=1/6 if their blocks agree and 1/4 otherwise; the C joint
   hosting probability is 27/110.
5. 27/110−1/6=13/165 and 27/110−1/4=−1/220.
6. For every distinct a,b, the B probabilities of
   (nonhost,nonhost), (nonhost,host), (host,nonhost), (host,host)
   are (p,1/2−p,1/2−p,p). The corresponding C probabilities
   are (27/110,14/55,14/55,27/110).
7. For every finite Ξ, natural N>0, nonnegative normalized Q,
   school function s and code function k: all student exposure
   marginals agree between the two product laws; for all i,j,d,e,
   if s(i)=s(j), their joint exposure probabilities also agree.
8. For every Boolean host and code∈Fin 4, the hosted-exposure
   function is 0 iff host=false.
9. For every finite Ξ, natural N (zero is allowed), nonnegative
   normalized Q, school function and codes: exposure-0 marginal
   probabilities are 1/2 under either law; for every i,j in
   distinct schools, their joint exposure-0 probabilities are
   (1/6 if the schools share a block, else 1/4) under B and
   27/110 under C.
10. H* belongs to C but to no image H_B(z) of an element of B.
11. The explicit counts and ratios used above hold:
    (4 choose 2)=6; its fourteenth power is 6^14;
    3·6^13/6^14=1/2;
    (55 choose 27)/(56 choose 28)=28/56=1/2;
    6^13/6^14=1/6; 3²·6^12/6^14=1/4;
    (54 choose 26)/(56 choose 28)=(28·27)/(56·55)=27/110.
12. For every distinct a,b the C-minus-B hosting joint
    probability is 13/165 for the same block and −1/220 for
    different blocks, and is nonzero in either case.

Together the image inclusion and H* witness give strict support
inclusion after identifying a block choice with its host subset.

## SAP.P013b.T27

For every finite Ω, natural N,M, design P, then N>0, an injective
map a:Fin N→Fin M of analysed students, school membership
s:Fin M→Fin 56, arbitrary assignment-dependent host indicators
H:Ω×Fin 56→Bool, own-treatment indicators A:Ω×Fin M→Bool,
neighbor sets B_i⊆Fin M, and y:Fin N×Fin 5→ℝ:
assume every y_id is 0 or 1; no student neighbors itself; neighborhood
membership is symmetric; neighbors share a school; and **every**
analysed unit has strictly positive probability for **every** one of
the five exposures. These hypotheses precede the conclusions below.
No upper bound π_id<1 is stated separately (positivity of all five
mutually exclusive labels implies it).

For analysed unit i define exposure 0 if its school is not hosting.
If hosting, assign exposure 1 for (own=false,no treated neighbor),
2 for (own=false,some treated neighbor), 3 for (own=true,no treated
neighbor), and 4 for (own=true,some treated neighbor). Some treated
neighbor means that filtering its finite neighbor set by A(z,j)=true
leaves a nonempty set. Observed outcomes are y at this exposure.

For every z,i the observed outcome equals Σ_d I_id(z)y_id.
For every exposure d∈Fin 5 with d≠0,

    τ_d0 = (Σ_i y_id)/N − (Σ_i y_i0)/N,
    E[(H_d−H_0)/N] = τ_d0.

Because the potentials are binary these are differences of finite
population proportions. The theorem supplies no recorded-data model,
school support, numerical Table 2 estimate, or wearing/recording
identification assumption beyond the exposure-specific binary y.
