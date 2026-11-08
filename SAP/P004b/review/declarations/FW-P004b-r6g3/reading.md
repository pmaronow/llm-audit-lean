# Blind reading

This file was written before opening `claims.json`, `record.json`, `earlier.json`, or
`architect-report.md`. I read the five Challenge docstrings and statements, all
declarations listed for each in `closure.json`, their source definitions, and the
31 generated proof declarations (printed in `scratch/ClosurePrint.lean`). The latter
prove numeral `AtLeastTwo` instances, singleton nonemptiness, or validity of the
first index under `10 ≤ N`; they add no mathematical assumptions. The field
projections and constructor of the population structure have their ordinary meaning.

## Mathematical notation used below (fully expanded common definitions)

For a natural number N, write I_N={0,...,N-1} and Ω_N={0,1}^{I_N}. Bool true is
1 and false is 0. For real propensities π_i, put

    w_π(z)=∏_{i∈I_N} [π_i if z_i=1, otherwise 1-π_i],
    E_π f=∑_{z∈Ω_N} w_π(z)f(z),   P_π(A)=E_π 1_A,
    Cov_π(f,g)=E_π(fg)-(E_π f)(E_π g),   Var_π f=Cov_π(f,f).

These are finite sums, not Bochner integrals. They are genuine independent
Bernoulli expectations when all π_i lie in [0,1]. A subscript p means all π_i=p.
For any array R_i(z) of real numbers, define

    m_i(a)=E_π[1_{z_i=a}R_i(z)]/[π_i if a=1, otherwise 1-π_i],
    τ_i=m_i(1)-m_i(0), τ=N^{-1}∑_i τ_i, μ_a=N^{-1}∑_i m_i(a),
    n_a(z)=∑_i 1_{z_i=a}, h_a(z)=∑_i 1_{z_i=a}R_i(z)/n_a(z),
    H(z)=h_1(z)-h_0(z), e_i(z)=R_i(z)-h_{z_i}(z),
    A_g(z)=N^{-1}∑_i[g_i(1)-g_i(0)+z_i(R_i(z)-g_i(1))/π_i
                              -(1-z_i)(R_i(z)-g_i(0))/(1-π_i)],
    L(z)=A_g(z) with g_i(a)=μ_a,
    HT(z)=N^{-1}∑_i[z_i R_i(z)/π_i-(1-z_i)R_i(z)/(1-π_i)].

For constants c_1,c_0 and common p also put

    ε_i(c_1,c_0;z)=N^{-1}[z_i(R_i(z)-c_1)/p
                                      -(1-z_i)(R_i(z)-c_0)/(1-p)].

A population of size N consists of a metric space X_N with a measurable-space
structure, nonempty subsets A_{Ni}⊆X_N, a measure ζ_N, an arbitrary real function
Y_N(x,z), and a band selector B_N:ℝ→Set ℝ. Neither compactness nor measurability
is built into the structure itself. Write

    δ_{Ni}(x)=inf_{y∈A_{Ni}} dist(x,y),
    D_N(i,j)=inf{dist(x,y):x∈A_{Ni},y∈A_{Nj}},
    C_{Ni}(d)={x:δ_{Ni}(x)∈B_N(d)},
    R_{Ni}(z)=[∫_{C_{Ni}(d)} Y_N(x,z) dζ_N]/ζ_N(C_{Ni}(d)).toReal,
    B_D(i,s)={j∈I_N:D_N(i,j)≤s}.

The integrals here are Mathlib set-restricted real Bochner integrals.
"Well-defined averages" means, for every i, C_{Ni}(d) is measurable, its ζ_N
measure is strictly positive and finite, and every Y_N(·,z) is integrable on it.
"Metric node distances" means at every N that D is nonnegative, symmetric,
D(i,j)=0 iff i=j, and D(i,k)≤D(i,j)+D(j,k).
"Bounded outcomes" means ∃M>0, eventually in N, ∀x,z, |Y_N(x,z)|<M.
"Quadratic spacing" means ∃C_b>0, eventually in N, simultaneously ∀i and
∀s≥0, #B_D(i,s)≤C_b(1+s²).
The kernel conditions mean K(0)=1, K(t)=0 for t>1, ∃M_K with
∀t≥0, |K(t)|<M_K, and ∃η∈(0,1), C>0 with
∀0≤t<η, |K(t)-1|≤C|t|. No nonnegativity or positive definiteness is assumed.

For J⊆I_N, the conditional function used is

    E_π[f | z_J](z)=E_π[1_{∀j∈J,z'_j=z_j}f(z')]/∏_{j∈J}coin(π_j,z_j),
    ||f||_{2,π}=sqrt(E_π f²).

The NED condition at fixed p,d is existence of ψ:ℝ→ℝ, positive coefficients
g_{Ni}, and G∈ℝ such that ψ≥0 on [0,∞), ψ is antitone there, ψ(s)→0,
∃q>4,C,S>0 with ψ(s)≤C s^{-q} for s≥S (C itself need not be positive),
0<g_{Ni}≤G for every N,i, and for every N,i,s≥0,

    ||R_{Ni}-E_p[R_{Ni}|z_{B_D(i,s)}]||_2 ≤ g_{Ni}ψ(s).

For Q_{ij}=K(D(i,j)/b), set

    λ_i(z)=z_i/n_1(z)-(1-z_i)/n_0(z),
    V_HAC(z)=∑_{i,j}λ_iλ_j e_i e_j Q_{ij},
    v_i(c_1,c_0;z)=∑_{j∈B_D(i,b)} ε_i(c_1,c_0;z)ε_j(c_1,c_0;z)Q_{ij},
    V_row(z)=∑_i v_i(h_1(z),h_0(z);z),
    V_2(z)=∑_i v_i(μ_1,μ_0;z),
    Q_hom(N)=N^{-1}∑_{i,j}Q_{ij}(τ_i-τ)(τ_j-τ).

For any e,Q,A,B define the independent five-term expression

    F(z,e,Q,A,B)=∑_i z_i e_i²/A² + ∑_i(1-z_i)e_i²/B²
       + ∑_{i≠j}z_i z_j e_i e_j Q_ij/A²
       - 2∑_{i≠j}(1-z_i)z_j e_i e_j Q_ij/(AB)
       + ∑_{i≠j}(1-z_i)(1-z_j)e_i e_j Q_ij/B²,
    V_1(z)=F(z,e(z),Q,Np,N(1-p)).

Here all off-diagonal sums are ordered. Valid arms mean n_1>0 and n_0>0;
a valid interval additionally requires V_HAC>0. Its standardized statistic is
T=(H-τ)/sqrt(V_HAC). "Covered(lo,hi)" means a valid interval AND lo≤T≤hi.
"Guarded(lo,hi)" means valid interval IMPLIES lo≤T≤hi, so invalid intervals
are counted as successes in the latter event only.
The normal CDF is Φ(x)=(gaussianReal(0,1)((-∞,x])).toReal and
q(a)=inf{x:a≤Φ(x)}. A finite quantile means this set is nonempty and bounded
below. "liminf at least a" is explicitly ∀ε>0, eventually a-ε≤u_N;
"conservative at α" uses a=1-α. This formulation does not use a totalized
liminf. U_N=o_p(1) means ∀ε>0, P_p(|U_N|>ε)→0. U_N=O_p(r_N)
means ∀ε>0, ∃C>0, eventually P_p(|U_N|>C|r_N|)<ε.
All limits are along natural N→∞, unless s→∞ is specified.

## SAP.P004b.T26

The theorem asserts the following conjunction, in the order below.

1. For every real sequence b_N tending to +∞, r_N=b_N^(1/6) tends to +∞ and
   r_N³/b_N→0. No sign hypothesis is imposed on the finite prefix of b.
2. For every sequence of metric/measurable spaces and populations, then every
   p,d∈ℝ, functions K,φ:ℝ→ℝ, and sequence b:ℕ→ℝ, assume, in order:
   0≤p≤1; d≥0; bounded outcomes; eventually well-defined averages; metric
   node distances at every N; quadratic spacing; the kernel conditions;
   b_N→+∞; φ(s)≥0 for every s≥0. Instead of the conditional m_i at endpoints,
   use the forced means

       m*_i(a)=∑_z w_p(z)R_i(z with coordinate i replaced by a),
       τ*_i=m*_i(1)-m*_i(0), τ*=N^{-1}∑_i τ*_i, a_{Ni}=τ*_i-τ*.

   Assume additionally that eventually, simultaneously for every i,j,
   |a_{Ni}||a_{Nj}|≤φ(D_N(i,j)). For a finite row f, its maximum is
   sup(range f) when N>0 and explicitly zero when N=0. Define

       E_out(N,r)=max_i ∑_{j:D_N(i,j)>r_N} φ(D_N(i,j)),
       E_in(N)=max_i ∑_{j:D_N(i,j)≤b_N} φ(D_N(i,j)),
       S(N)=max_i a_{Ni}²,
       A(N)=N^{-1}∑_{i,j}K(D_N(i,j)/b_N)a_{Ni}a_{Nj}.

   The conclusions are two separate implications with the same preceding data:
   (a) if for EVERY real sequence r_N→+∞, E_out(N,r)→0, then A(N)→0,
   Mathlib's real Filter.liminf A atTop equals 0, and ∀ε>0 eventually A(N)≥-ε;
   (b) if E_in(N)→0, then φ(0)=0, eventually all a_{Ni}=0,
   eventually S(N)≤E_in(N), S(N)→0, and, for EVERY L∈ℝ uniformly bounding
   |K(t)| strictly for t≥0, eventually |A(N)|≤L E_in(N); also all three
   conclusions in (a) hold. φ is a single function, not an N-indexed family.
3. For EVERY N, propensity array π, and real table R, if 0<π_i<1 for every i,
   then all forced means equal the conditional m_i, their average effect equals
   τ, and each forced centered effect equals τ_i-τ.

Junk conventions: real division and inversion at zero give zero, so averages and
kernel forms at N=0 are totalized; the empty row maximum is explicitly zero.
Empty I_0 has one assignment, empty sums zero and empty products one. Node sets
are nonempty, so their point/set and set/set distance infima are over nonempty
sets bounded below by zero, and are genuine infima. Well-defined averages
exclude zero/infinite mass and nonintegrable Bochner branches eventually;
ENNReal.toReal(∞)=0 and a nonintegrable real Bochner integral is zero outside
that region of use. Arbitrary early bad averages cannot affect these limits.
Forced means avoid division by a zero-probability own arm at p=0 or 1; the
conditional means appear only under strict propensity positivity. Real rpow is
exp(log x·y) for x>0, is zero at x=0 for nonzero exponent, and for x<0 is
exp(log x·y)cos(πy), with log x=log|x|. b_N→∞ makes these nonpositive-base
branches and b_N=0 irrelevant eventually. The negative-argument extensions of
K and φ are not used eventually because D≥0 and b>0. The only real liminf
appears beside convergence to zero, which guarantees eventual boundedness and
prevents any empty/unbounded order-infimum convention from deciding its value.
No square roots, conditional laws on zero mass, partial functions, or truncated
subtractions enter this statement. Nat-to-real casts preserve N exactly.

## SAP.P004b.T27

This is a conjunction about ONE explicitly fixed population sequence, with no
external hypotheses. In the Euclidean plane, put x_{Ni}=((i+1)N²,0),
A_{Ni}={x_{Ni}}, ζ_N=∑_i δ_{x_{Ni}}, B_N(d)=[0,d], and
Y_N(x,z)=∑_i 1_{x=x_{Ni}}r_i(z), where r_0(z)=1/4+3z_0/4 and r_i=0 for i>0.
The kernel is K(t)=1 if 0≤t≤1, otherwise zero; p=1/2, the principal averaging
distance is d=1, and b_N=floor_nat(N^(1/12)). For N>0 let F(z)=z_0, extending
F=false at N=0, and q_z=n_{F(z)}(z). Write R,Q,V_HAC,V_1,V_2,T for the
preceding explicit formulas using these data. Conditional probabilities given
F=a are defined as 2P(F=a and event). The exact asserted facts are:

- Bounded outcomes, quadratic spacing, the NED condition at d=1, and the
  kernel conditions; b_N→∞ and b_N=o(N^(1/6)); well-defined d=1 averages
  for N≥3; liminf Q_hom≥0; N Var(L)→0; P(not SparseGood)→0, where
  SparseGood means 2N/5≤n_1≤3N/5. For N≥10 on SparseGood, the interval is
  valid and Guarded(-2,2) iff z_0=1. For every N>0, P(z_0=1)=1/2.
  Also 0<2(1-Φ(2))<1 and 3/4≤1-2(1-Φ(2)).
- For EVERY N>0 and EVERY d≥0 all disk averages are well-defined, and
  R_i(z) at that d is (1/4+3F(z)/4)/#B_D(i,d) if D(i,0)≤d, otherwise zero.
- For EVERY d≥0 the stated NED condition holds. For every such d,N,i,s≥0,
  the conditional-approximation L² error is at most 1 when s≤d and at most
  zero when s>d; at d=1 it is exactly zero for all N,i,s≥0.
- Metric node distances hold at every N. For every N≥3, outcomes have
  absolute value <2, #B_D(i,s)≤3(1+s²) for all i,s≥0,
  τ_i=3/4 for i=0 and zero otherwise, τ=3/(4N), Q_ij=1_{i=j},
  and b_N/N^(1/6)≤N^(-1/12).
- For N≥3, Q_hom=9(N-1)/(16N²), Var(L)=25(N-1)/(16N³).
- For N≥3, every a∈{0,1} and every natural k≤N-1,
  P(q_z=k+1 | F=a)=choose(N-1,k)/2^(N-1).
  P(not(2≤q_z≤N-1))=4/2^N. Conditional on either F=a,
  E(q_z/N)=1/2+1/(2N) and Var(q_z/N)=(N-1)/(4N²).
  For each a, q_z/N→1/2 in conditional probability.
- For every N≥3 and assignment with 2≤q_z≤N-1, the interval is valid and

      H = 1/q_z if F=1, otherwise -1/(4q_z),
      V_HAC = (q_z-1)/q_z³ if F=1, otherwise (q_z-1)/(16q_z³),
      T = (1-3q_z/(4N))sqrt(q_z/(q_z-1)) if F=1,
          otherwise -(1+3q_z/N)sqrt(q_z/(q_z-1)).

  Conditional on F=1, T→5/8 in probability, and conditional on F=0,
  T→-5/2 in probability.
- 5/8<q(39/40)<5/2. P(Covered(-2,2))→1/2 and
  P(Covered(q(1/40),q(39/40)))→1/2, with 1/2<19/20.
- For every N≥3 and every assignment, 0≤V_1≤4/N² and 0≤V_2≤16/N²;
  E V_2=17(N-1)/(8N³). The assignment supremum sup_z|V_2| is O(N^-2),
  V_HAC=O_p(N^-2), and all three N-scaled differences
  V_HAC-V_1, V_1-V_2, V_2-E V_2 tend to zero in probability.
  For N≥3 the bias N(E V_2-Var L)=9(N-1)/(16N²)≥0.

Junk conventions: all common divisions at N=0 are zero and the first coin is
explicitly false there. Empty sums/products follow the conventions above.
The natural floor truncates negative inputs to zero, but N^(1/12)≥0 and
b_N≥1 for N≥1. Negative real powers have the Mathlib totalized rpow meaning
at N=0; integer power N^(-2:ℤ) is the inverse square, zero at N=0. These
appear only in asymptotic assertions or formulas for N≥3. Nat subtraction
N-1 is truncated, but all count-law formulas assume N≥3. At positive N the
disk mass is positive and finite, including d=0; the N=0 well-defined condition
is vacuous because there is no i. Every conditional first-coin law is used at
positive N or asymptotically, where its mass is genuinely 1/2. L² radicands
are genuine nonnegative second moments under fair independent coins.
Arm means use zero for empty arms. V_HAC might be nonpositive outside the
validity event, in which case sqrt(V_HAC)=0 and T is a totalized quotient.
The exact T formulas are asserted only when q_z≥2 and q_z≤N-1, forcing both
arms nonempty and V_HAC>0; the complement has probability tending to zero.
The final coverage events reject invalid intervals. The inherited Guarded
event counts invalid intervals as successes but is used on SparseGood, where
validity is also proved. The supremum over assignments is over a finite,
nonempty type even at N=0. Gaussian CDF masses are finite; the two quantile
levels lie strictly inside (0,1), so their defining sets are nonempty and
bounded below. There is no reliance on an empty/unbounded sInf or liminf.

The docstring explicitly calls this a counterexample to a reading of the
coverage assertion using the uniform C_b(1+s²) spacing bound. The mathematics
asserts the actual coverage limit and also asserts its vanishing N Var(L).

## SAP.P004b.T28

For EVERY sequence of metric/measurable spaces and populations, then EVERY
p,d∈ℝ, K:ℝ→ℝ, b:ℕ→ℝ, assume in order: 0<p<1; d≥0; bounded outcomes;
well-defined averages at EVERY N; the NED condition at p,d; metric node
distances at EVERY N; quadratic spacing; the kernel conditions; b_N>0 at
EVERY N; b_N→∞; b_N=o(N^(1/6)); liminf Q_hom≥0 in the explicit eventual
lower-bound sense. Then, for R,D,Q and the independent V_1 above:

1. At EVERY N and assignment z with both arms nonempty, V_1=V_row.
2. At EVERY N,z, V_2 equals ∑_i v_i(μ_1,μ_0;z), with each μ_a the
   deterministic mean of the conditional arm means. This is a definitional
   equality in this encoding.
3. All three RAW errors N(V_HAC-V_1), N(V_1-V_2), and N(V_2-E_p V_2)
   tend to zero in probability. These errors are not replaced by zero on
   assignments with empty arms.
4. liminf N(E_p V_2-Var_p L)≥0 in the explicit eventual-lower-bound sense.
5. If, additionally, ∃v>0 eventually v≤N Var_p L, then for EVERY real
   α with 0<α<1 both quantile sets at α/2 and 1-α/2 are nonempty and bounded
   below, and ∀ε>0 eventually

       P_p(valid interval AND q(α/2)≤(H-τ)/sqrt(V_HAC)≤q(1-α/2))
         ≥1-α-ε.

Junk conventions: the only possible zero N is a finite prefix; all natural casts
are exact. Empty-arm h_a and λ denominators are totalized to zero. This affects
raw error values on all-one/all-zero assignments, whose probabilities are
p^N+(1-p)^N→0. The row identity only assumes nonempty arms. The final coverage
event requires both arms and strictly positive variance, so division by zero or
sqrt of a negative variance cannot manufacture coverage. The variance lower
bound is only required for conclusion 5, not conclusions 1–4. b_N is positive
at every N; no negative kernel arguments occur because D≥0. Well-definedness
at every N rules out zero/infinite averaging mass and nonintegrable integral
branches wherever there is a node. The conditional denominators are positive
under 0<p<1. All assignment extrema are finite; q is used only for levels in
(0,1) and finite-quantile properties are conclusions. No totalized order
liminf appears here. The power N^(1/6) is zero at N=0 and ordinary positive
rpow thereafter; little-o ignores the finite prefix.

## SAP.P004b.T29

The theorem is a conjunction of FOUR universally quantified assertions.

1. For every sequence of metric/measurable spaces, populations P, reals p,d,
   functions K,ψ:ℝ→ℝ, and real bandwidth sequence b, assume: 0<p<1;
   bounded outcomes; metric node distances; quadratic spacing; kernel
   conditions; ψ≥0 and antitone on [0,∞); ∃G∈ℝ such that for every N,i,s≥0
   the conditional-approximation L² error of R_{Ni} at radius s is ≤Gψ(s);
   well-defined averages at every N; and b_N≥1 at every N. There is no
   d≥0 hypothesis, no decay or power bound on ψ, and no bandwidth rate.
   The conclusion is ∃C∈ℝ such that eventually in N, simultaneously for
   all i,j with D(i,j)>3b_N,

       |Cov_p(v_i(μ_1,μ_0),v_j(μ_1,μ_0))|
         ≤ C b_N²/N⁴ · max(
              ∑_{k∈B_D(i,b_N)} ψ(D(i,j)/3-D(i,k)),
              ∑_{l∈B_D(j,b_N)} ψ(D(i,j)/3-D(j,l))).

   The deterministic centers are specifically the population arm means.
2. For EVERY N, real table R, symmetric nonnegative real D with zero
   diagonal, kernel K satisfying the stated conditions, reals b,p with b>0,
   and assignment z with both arms nonempty,
   V_HAC(z)=F(z,e(z),Q,n_1(z),n_0(z)). Here p is quantified but unused in
   both sides, and need not lie in (0,1). No triangle inequality is assumed
   in this purely algebraic clause.
3. For EVERY z,w∈{0,1} and reals n,p,y_i,y_j,h_1,h_0,b_1,b_0, assume
   n≠0,p≠0,1-p≠0. Put
   E(a,y,c_1,c_0)=a(y-c_1)/(np)-(1-a)(y-c_0)/(n(1-p)). Then

       E(z,y_i,h_1,h_0)E(w,y_j,h_1,h_0)
         - E(z,y_i,b_1,b_0)E(w,y_j,b_1,b_0)
       = zw/(n²p²)[-(y_i+y_j)(h_1-b_1)+h_1²-b_1²]
       + (1-z)(1-w)/(n²(1-p)²)[-(y_i+y_j)(h_0-b_0)+h_0²-b_0²]
       - (1-z)w/(n²p(1-p))[-y_i(h_1-b_1)-y_j(h_0-b_0)+h_0h_1-b_0b_1]
       - z(1-w)/(n²p(1-p))[-y_i(h_0-b_0)-y_j(h_1-b_1)+h_0h_1-b_0b_1].

   The variable n here is a real number, not a natural sample size.
4. For EVERY N>0, p∈(0,1), real table R, and arbitrary real matrix Q,
   use ε_i=ε_i(μ_1,μ_0). Then E_p ε_i=(τ_i-τ)/N for every i, and

       ∑_{i,j}Q_ij[E_p(ε_iε_j)-Cov_p(ε_i,ε_j)]
         = N^{-2}∑_{i,j}Q_ij(τ_i-τ)(τ_j-τ).

Junk conventions: the only possibly bad real denominators in the algebraic
epsilon identity are explicitly nonzero. In the HAC expansion n_0,n_1,b>0;
its unused p introduces no division. The far-pair inequality is eventual in N
and b_N≥1, with D≥0. Its ψ arguments are strictly positive since D(i,j)>3b_N
and D(i,k)≤b_N. Population means and conditional expectations have genuine
positive denominators under 0<p<1, and all spatial averages are well-defined.
N=0 affects no eventual conclusion; finite algebraic mean identities assume
N>0. Empty arms in globally defined h_a are assigned zero but the HAC identity
requires both arms nonempty. Square roots in L² norms have nonnegative inputs.
Node infima are genuine because the node sets are nonempty. There are no
logarithms, rpow, partial functions, quantiles, or real liminf/supremum of
unbounded sets in this statement.

The docstring discloses uniform quadratic spacing, metric distances, all-size
well-definedness, all-size b_N≥1, and population-mean centers as restrictions;
it also explicitly omits V1's independent formula-to-row equality, a separate
V2-definition clause, and two numerical misprint checks.

## SAP.P004b.T30

The theorem asserts FOUR clauses, the last itself a conjunction.

1. For EVERY natural N,n_1 with 1≤n_1≤N-1, then EVERY i∈I_N, let
   S={z∈Ω_N:∑_j z_j=n_1} and, for a∈{0,1},
   U_a={u:{j∈I_N:j≠i}→{0,1}:∑_j u_j=n_1-a}.
   Then #S>0, U_0 and U_1 are disjoint, and for EVERY a the set
   S_a={z∈S:z_i=a} and U_a both have positive cardinality, #S_a/#S>0,
   and for EVERY remainder vector u,

       #{z∈S_a:z_{-i}=u}/#S_a = 1/#U_a if u∈U_a, otherwise 0.

2. For EVERY N, propensity array π with 0<π_j<1 for every j, and i∈I_N,
   for EVERY a both P_π(z_i=a)>0 and, for EVERY remainder vector u,

       P_π(z_i=a,z_{-i}=u)/P_π(z_i=a)=∏_{j≠i}coin(π_j,u_j).

   Also the two conditional masses given z_i=0 and z_i=1 agree for each u;
   for EVERY real table R and arm a,
   m_i(a)=E_π[R_i(z with coordinate i replaced by a)].
3. For EVERY N>0, p∈(0,1), and real table R, L equals the function

       z ↦ τ+N^{-1}∑_i[z_i(R_i(z)-μ_1)/p
                              -(1-z_i)(R_i(z)-μ_0)/(1-p)],

   equals the augmented function with g_i(a)=μ_a, and the variances of these
   two displayed functions agree. For EVERY z the augmented estimator fitting
   μ_1 in BOTH arms minus L equals

       (μ_1-μ_0)[n_0(z)/(N(1-p))-1].

   The wrong-fit estimator equals L as a function on ALL assignments iff
   μ_1=μ_0. This is functional equality, not equality on one assignment.
4. For EVERY N>0, p∈(0,1), and real table R, define

       m_{i;ab}^{ij}=E_p[1_{z_i=a,z_j=b}R_i(z)]/[coin(p,a)coin(p,b)],
       Δ=N^{-1}∑_{i≠j}(m_{i;11}^{ij}-m_{i;01}^{ij}-τ_i),
       c*=μ_1/p+μ_0/(1-p)+Δ/(1-p),
       C=Var_p(HT)-p(1-p)(c*)²/N.

   Then C≥0; for EVERY real pair c_1,c_0,

       Var_p(A_{constant(c_1,c_0)})
         =p(1-p)/N·(c_1/p+c_0/(1-p)-c*)²+C;
       Var_p(L)=C+pΔ²/[N(1-p)].

   For EVERY ε≥0 with |Δ|≤ε,
   0≤Var_p(L)-C≤pε²/[N(1-p)]. If Δ=0 then Var_p(L)=C.
   C is defined independently of the subsequently quantified fits c_1,c_0.

Junk conventions: n_1-a and N-1 are NATURAL truncated subtraction in clause 1,
but 1≤n_1≤N-1 implies N≥2, so both are ordinary integer subtractions there.
All finite support and conditional-event cardinalities are explicitly proved
positive, rather than assumed. Remainder index types may be empty for N=1 in
clause 2; their single empty assignment has product probability one. No node i
exists for N=0. Strict Bernoulli propensities make both conditioning events
positive. N,p,1-p denominators in clauses 3–4 are positive. Pair conditional
denominators are only used for i≠j; the globally defined pair formula would
not be a joint conditional law at i=j, but no such value enters Δ. No empty-arm
mean, logarithm, sqrt, rpow, spatial integral, supremum/infimum, real liminf, or
partial function is used. All finite reals are integrable under these finite
laws. Function.update is total and simply sets the specified coordinate.
