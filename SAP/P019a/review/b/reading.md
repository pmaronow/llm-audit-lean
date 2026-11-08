# Blind reading

Saved before opening `claims.json` or `record.json`. This reading uses only the
Defs, Challenge, and the Mathlib definitions they use. Each Challenge theorem
asserts the corresponding `TnStatement`; its `sorry` is not evidence of truth.

## Common mathematical objects and conventions

`FiniteLaw Ω`, for a finite type Ω, is a real probability vector
`p(ω) ≥ 0`, `Σω p(ω) = 1`. Write `E f = Σω p(ω)f(ω)` and
`P(D) = E 1_D`. Zero-mass atoms are allowed. Such a law cannot exist on an empty
type. `ce(f,D) = E(f 1_D)/P(D)`; `cv(f,D) = ce(f²,D)-ce(f,D)²`;
`ccov(f,g,D) = ce(fg,D)-ce(f,D)ce(g,D)`. Unconditional variance and covariance
use the analogous unconditioned moments. These are finite sums, not Bochner
integrals. Division is real division, so a zero denominator would give zero;
below, positive or nonzero conditioning probabilities are part of the relevant
hypotheses or conclusions. A Boolean's numeric value is 1 for true and 0 for
false. I identify Booleans with 0 and 1 in the formulas below.

A `Study Ω` consists of one such law and maps `W,V : Ω → ℕ` and
`X,Y,Z : Ω → {0,1}`. There is no additional fixed bound on W or V in the type.
Its properties mean:

* `monotone`: at every atom of positive mass, Y=1 implies X=1.
* `noLiarsDesign`: at every atom of positive mass, V=W+XZ, with this equation
  interpreted in ℝ (no natural-number subtraction).
* `treatmentIndependent`: for **every** real function f of (W,X,Y), and then
  **every** z∈{0,1}, `E[1_{Z=z}f(W,X,Y)] = P(Z=z)E[f(W,X,Y)]`.
  This is joint independence of Z from the whole triple (W,X,Y), not merely
  pairwise independence.
* `cell(z,y)` is {Z=z,Y=y}. `nondegenerate` says, for **every** z and y,
  both `P(cell(z,y))>0` and `Var(V|cell(z,y))>0`; it also requires
  `Var(Z)>0` and `Var(Y)>0`.
* `standing` is the conjunction of all four properties above.

Write μ=P(X=1), r=E[Y|X=1] (`truthRate`), γ=P(Z=1),
`m_zy=E[V|Z=z,Y=y]`, β=m_11−m_01, and
δ=E[Y|Z=1]−E[Y|Z=0]. These are definitions, not additional hypotheses.

The iid law at n is on **ordered** functions s:{0,…,n−1}→Ω and has mass
`Πi p(s_i)`. It includes n=0 and does not condition away any sample. For a
sample, let

* `N_zy=Σi 1_{Z_i=z,Y_i=y}` and `M_z=Σi 1_{Z_i=z}`;
  `Ybar=(Σi Y_i)/n` and `γhat=M_1/n` (both zero at n=0).
* `L_zy(c)=c` if N_zy=0, and `(Σi 1_cell V_i)/N_zy` otherwise.
  Thus an empty-cell value is a fixed real c, never a removed outcome.
* `O={N_10>0,N_00>0}` (`occupied`). `K=N_10+N_00`.
* `μhat(c1,c0)=Ybar+(1−Ybar)(L_10(c1)−L_00(c0))`.
  `A=1−Ybar`, `B=L_10(c1)−L_00(c0)−1`, so μhat=1+AB.
* `σ²_zy=Var(V|cell(z,y))`, and
  `h=σ²_10/N_10+σ²_00/N_00` (`sampleH`). h is used conditioned on O.
* The pattern fibre F_s consists of t with `(Y(t_i),Z(t_i))=(Y(s_i),Z(s_i))`
  for every i. It fixes the **whole ordered** Y,Z pattern.
* `s²_zy=0` if N_zy<2; otherwise
  `Σi 1_cell(V_i−L_zy(0))²/(N_zy−1)`, with the subtraction in ℝ.
* `μVarianceHat(c1,c0,cV)` equals
  `[((1−μhat)²/(1−Ybar))Ybar +
    (1−Ybar)(s²_10/γhat+s²_00/(1−γhat))]/n`
  when N_10,N_00≥2, Ybar<1, and 0<γhat<1. On every other sample it is cV.
* `βhat(c1,c0)=L_11(c1)−L_01(c0)`;
  `βVarianceHat(cV)=s²_11/N_11+s²_01/N_01` if both affirmative cells
  have size at least two, and is cV otherwise.

For asymptotics, Φ(t) is the mass of (−∞,t] under Mathlib's
`gaussianReal 0 1`, the mean-zero, variance-one Gaussian probability measure.
`q(u)=inf{x∈ℝ:u≤Φ(x)}` is the real conditional-complete-order infimum.
Where q is used, nonemptiness and a lower bound for this set are explicit
premises. `studentized(e,a,v)` is `(e−a)/sqrt(v)` if v>0 and 0 otherwise;
`normalPValue(e,a,v)=2Φ(−|studentized(e,a,v)|)`.
For a vector p indexed by {0,…,4}, `Fisher(p)=−2Σj log(p_j)`.
Mathlib's real log is total (`log 0=0`, and log of a negative number is log of
its absolute value), but here the arguments are finite Gaussian p-values.
`chiSquareTen` is the pushforward of ten independent standard normals by
`x↦Σj x_j²`.

`WeakLimit(P,T,Q)` asserts: for **every** real function f on the target E,
if f is continuous and there **exists** a finite real C such that
`∀x, |f(x)|≤C`, then
`lim_{n→∞} E_{P^n}[f(T(n,s))] = ∫f dQ`.
The target spaces used below are ℝ or ℝ⁵ with their usual topology and
measurable structure; all stated Q are actual probability measures.
`Measure.pi` is the finite product measure and `Measure.map` its pushforward.
The maps here are measurable (linear, polynomial, or Borel functions formed
from Φ, absolute value and log), so map's nonmeasurable fallback is irrelevant.
The Bochner integral is totalized to zero for nonintegrable functions in
Mathlib; bounded continuous tests under these probability laws are integrable.
`continuousVariance(Q)=∫x²dQ−(∫xdQ)²`; T9 separately asserts integrability
of both functions before using this variance.
`Tendsto … atTop (nhds a)` is the usual sequence limit. Real `IsBigO atTop f g`
means there exists a real C with `|f(n)|≤C|g(n)|` for all sufficiently large n.

## SAP.P019a.T1

There are no hypotheses or external quantified parameters. On w∈{0,1,2,3,4},
define the fixed law
`p=[81,216,216,96,16]/625`, the response functions
`a(w)=min(w+1,4)`, `b(w)=a(w)+1`, and `u(w)=w+1`.
For any response f define the deterministic mixture contrast
`C_f(ρ)=E[(1−ρ)u(W)+ρf(W)]−E[W]` under this fixed law.
The theorem is the conjunction of:

1. For every w, `p(w)=choose(4,w)(2/5)^w(3/5)^(4−w)`.
   Here 4−w is natural subtraction, but w≤4.
2. E[W]=8/5 and Var(W)=24/25.
3. For every w, `a(w)=[1,2,3,4,4]_w`,
   `b(w)=[2,3,4,5,5]_w`, and `u(w)=[1,2,3,4,5]_w`.
4. `C_a(1/5)=3109/3125`, `C_b(1/5)=3734/3125`;
   `C_a(1/5)−1=−16/3125`, `C_b(1/5)−1=609/3125`;
   `C_b(1/5)−C_a(1/5)=1/5`.

No joint random affected-status or assignment variable is part of this assertion.

## SAP.P019a.T2

For **every** real ρ, if 0≤ρ and ρ≤1, the following all hold, with the fixed
law and response functions from T1:

1. For every w∈{0,…,4}, `b(w)=w+2` if w<4, and b(4)=5.
2. For every w, then every Boolean d, the increment over w of the response
   b(w) when d=1 and u(w) otherwise is `1+1_{d=1,w<4}`.
   The corresponding increment using a(w) is `1−1_{d=1,w=4}`.
3. `C_b(ρ)=1+ρ(1−p(4))=1+(609/625)ρ` and
   `C_a(ρ)=1−ρp(4)=1−(16/625)ρ`.
4. `C_b(ρ)−C_a(ρ)=ρ`; if ρ>0, C_b(ρ)>1.
5. `C_b(1/5)=3734/3125` and `C_a(1/5)=3109/3125`.

The quantifiers in items 1 and 2 and the fixed evaluations in item 5 are inside
the universal quantification and hypotheses on ρ. No assertion of power appears.

## SAP.P019a.T3

No hypotheses. Fix the uniform law on 16 atoms, identified with four independent
fair bits X,C,W,Z, and put Y=XC and V=W+XZ. Fix its **four**-observation iid law
P, A=1−Ybar and B=L_10(0)−L_00(0)−1. The conjunction says:

1. This Study satisfies standing, including positive probabilities and positive
   V variances in all four cells.
2. For every n∈ℕ, then every z∈{0,1},
   `P_n(N_z0=0)=(5/8)^n>0`.
3. For a single atom, let `l_z=1_{Z=z,Y=0}V` (zero-completed singleton
   cell mean). `Cov(1−Y,l_1)=5/64`, `Cov(1−Y,l_0)=3/64`.
4. P(Y=0)>0, `P(Z=1|Y=0)=1/2`, `E[l_1|Y=0]=5/12`,
   whereas m_10=5/6.
5. The four purely numeric identities
   `1−(1−1/2)^k=0,1/2,3/4,15/16` for k=0,1,2,4 respectively.
   This item does not assert a conditioned count law for those k.
6. Under the four-observation law, P(O)=1431/2048>0;
   `Cov(A,B|O)=0`, `Cov(L_10(0),L_00(0)|O)=0`.
7. `Var(μhat(0,0)|O)=141205/404496`.
8. The expression
   `D=E[A|O]² Var(B|O)+Var(A|O)E[B|O]²+Var(A|O)Var(B|O)`
   equals 75809/202248, and
   `Var(μhat(0,0)|O)−D=−1157/44944`.
9. `4γ=2`, `P(M_1=2)=3/8`, and `P(M_1=0)=1/16` under P.

All zero completions in this theorem are explicitly fixed to zero.

## SAP.P019a.T4

For **every** finite type Ω (in every universe) and **every** Study S on Ω,
if S satisfies standing, the following four blocks hold. No additional
sample-size or moment hypotheses apply to the first block.

1. For every n∈ℕ, then every z∈{0,1},
   `P_n(N_z0=0)=(1−P(cell(z,0)))^n>0`.
2. For every n∈ℕ with n≥2, then **every** real c1,c0, set
   P=P_n, A=1−Ybar, B=L_10(c1)−L_00(c0)−1,
   h=σ²_10/N_10+σ²_00/N_00 and b=m_10−m_00−1.
   All the following hold:
   * P(O)>0.
   * For every k∈ℕ, if k≤n and P(K=k)≠0, then, for every i∈ℕ with i≤k,
     `P(N_10=i|K=k)=choose(k,i)γ^i(1−γ)^(k−i)`;
     also `P(N_10>0|K=k)=1−(1−γ)^k` and
     `P(N_00>0|K=k)=1−γ^k`. k−i is not truncated here because i≤k.
   * For every sample s, if O(s) and P(F_s)≠0, then, for every z,
     `E[L_z0(c_z)|F_s]=m_z0` and
     `Var(L_z0(c_z)|F_s)=σ²_z0/N_z0(s)`, where c_1=c1,c_0=c0.
     Further `Cov(L_10(c1),L_00(c0)|F_s)=0`,
     `E[B|F_s]=b`, and `Var(B|F_s)=h(s)`.
   * For every real a, if P(O∩{A=a})≠0, then, for every z,
     `E[L_z0(c_z)|O,A=a]=m_z0`.
   * For every z, `Cov(L_z0(c_z),A|O)=0`;
     also `Cov(L_10(c1),L_00(c0)|O)=0`.
   * Both `Var(μhat(c1,c0)|O)` and `Var(AB|O)` equal
     `b² Var(A|O)+E[A²h|O]`.
   * `D=E[A|O]² Var(B|O)+Var(A|O)E[B|O]²+Var(A|O)Var(B|O)`
     equals `b²Var(A|O)+E[A²|O]E[h|O]`.
   * `Var(AB|O)−D=Cov(A²,h|O)`.
3. For the sequence indexed by n∈ℕ,
   `R_n=Cov_{P_{n+2}}(A²,h|O)`, one has
   `R_n=O((1/(n+2))²)` and
   `lim (n+2)²R_n = −2 μr(σ²_10/γ+σ²_00/(1−γ))`.
4. For every positive n, `E_{P_n}[M_1]=nγ` and, for every sample s,
   `M_1(s)=n γhat(s)`.

The conditional-count block includes k=0 when n≥2, but does not cover sample
sizes n=0 or n=1. μr in block 3 uses the conditional definition of r above;
standing supplies positive affirmative Y probability, hence positive X
probability, so it is not a division-by-zero convention.

## SAP.P019a.T5

No hypotheses. Fix the uniform law on eight atoms, identified with three
independent fair bits X,W,Z, and put Y=X and V=W+XZ. This Study satisfies
standing. In addition,
`P(V=0|Z=0,Y=1)=1/2`,
`P(V+1=0|Z=1,Y=1)=0`, and
`P(V−1=0|Z=1,Y=1)=1/2`.
Both V+1 and V−1 are real-valued expressions. The theorem asserts these three
point probabilities only, not explicitly every conditional distribution value.

## SAP.P019a.T6

For every finite Ω and every Study S, assume, **in this order**,
monotonicity, noLiarsDesign, treatmentIndependent,
P(Z=0,Y=1)>0, and P(Z=1,Y=1)>0. Conclude P(Y=1)≠0 and,
for **every** real t, all four identities:

1. `P(V=t|Z=0,Y=1)=P(W=t|Y=1)`.
2. `P(V−1=t|Z=1,Y=1)=P(W=t|Y=1)`.
3. `P(V=t|Z=0,Y=1)=P(V−1=t|Z=1,Y=1)`.
4. `P(V=t|Z=0,Y=1)=P(V=t+1|Z=1,Y=1)`.

These are conditional **point** probabilities, with no bound on real t.
Because these are finite, integer-valued laws, equality at every real point
also determines equality of their laws. Assumption `nondegenerate` is absent.

## SAP.P019a.T7

No hypotheses. On 16 equiprobable atoms let B,C,X,Z be independent fair bits,
put W=B+C, Y=X·1_{C=Z}, and V=W+XZ. The conclusion is the conjunction:
monotonicity, noLiarsDesign, nondegenerate, δ=0, β=2, β≠1, and
failure of treatmentIndependent. Thus this explicitly does not assert standing
for this Study. The failed factorization is not supplied as a particular f,z.

## SAP.P019a.T8

For every finite Ω and every Study S, assume P(Z=0,Y=1)>0, then
P(Z=1,Y=1)>0. The conclusion is a conjunction of four implications:

1. If monotonicity and then noLiarsDesign hold,
   `β=1+E[W|Z=1,Y=1]−E[W|Z=0,Y=1]`.
2. If monotonicity, then noLiarsDesign, then treatmentIndependent hold,
   `E[W|Z=1,Y=1]=E[W|Z=0,Y=1]` and β=1.
3. If β≠1, then `¬monotone ∨ ¬noLiarsDesign ∨ ¬treatmentIndependent`.
4. If monotonicity, then noLiarsDesign, then β≠1 hold,
   treatmentIndependent fails.

Nondegenerate is not assumed. The first two cell-probability premises apply to
all four implications; the assumptions inside one implication do not become
global premises for the others.

## SAP.P019a.T9

No external hypotheses. Use the uniform law on 128 atoms, seven independent
fair bits X,B,Z_0,…,Z_4. Write b=2B−1, z_j=2Z_j−1,
`p_k=Π_{i=0}^{k−1}z_i` (p_0=1), and
`q_j=Π_{i=j+1}^4 z_i` (q_4=1). For j=0,…,4 define a Study on this
same law by
`W_j=2 if b p_j=1, and 1 otherwise`,
`Y_j=X·1_{q_j=1}`, `X_j=X`, `Z_j=Z_j`, `V_j=W_j+XZ_j`.
Define
`ψ_j=2Xb(p_{j+1}+p_5)` for j<4 and `ψ_4=2Xb p_5`.
For any Study, its `betaPsi` is
`[Y/P(Y=1)] [(Z−γ)/(γ(1−γ))] [W−E(W|Y=1)]`.
The theorem asserts:

1. For every j, its Study satisfies standing and β_j=1.
2. For every assignment vector a∈{0,1}⁵, its probability is 1/32.
3. For every j, then every atom ω, betaPsi_j(ω)=ψ_j(ω).
4. For every j, Eψ_j=0. For every j, then every k,
   `E[ψ_jψ_k]=4` if j=k<4, `2` if j=k=4, and `2` if j≠k.
5. For iid samples of the **common 128-atom population**, the vector
   `T_n,j=studentized(βhat_j(0,0),1,βVarianceHat_j(0))`
   converges weakly to G(e) for five independent standard normals e, where
   `G_j(e)=(e_j+e_4)/sqrt(2)` for j<4 and G_4(e)=e_4.
6. `Fisher((normalPValue(βhat_j(0,0),1,βVarianceHat_j(0)))_j)`
   converges weakly to Q, the law of
   `Fisher((2Φ(−|G_j(e)|))_j)` under the same independent normal e.
7. Both x and x² are integrable under Q;
   `∫x²dQ−(∫xdQ)²>20` and Q≠chiSquareTen.

All samples share observations across lists. The assertion of independent
assignments in item 2 does not assert independence of the assignment vector
from all latent coordinates jointly. Neither marginal normal/p-value limits
nor a numeric correlation or exact variance formula are separate conjuncts.

## SAP.P019a.T10

For every finite Ω, then every law P on Ω, then every family of five Studies
S_j on Ω, assume, in order:

1. For every j, S_j.law=P.
2. For every j, S_j satisfies standing.
3. `jointAssignmentStable P S`: for **every** real function f of the three
   five-vectors (W_j)_j,(X_j)_j,(Y_j)_j, then **every** Boolean assignment
   vector a,
   `E_P[1_{∀j Z_j=a_j} f(Wvector,Xvector,Yvector)] =
    (Πj P(Z_j=a_j)) E_P[f(Wvector,Xvector,Yvector)]`.
   Thus the entire assignment vector is independent of all those latent
   coordinates jointly, and its coordinates have the product marginal law.

Conclude the conjunction:

1. For every j, β_j=1.
2. For every j, then k, if j≠k, then for every atom ω with
   P(L_ω)≠0, `E[betaPsi_j betaPsi_k|L_ω]=0`, where
   L_ω={t: for every list l, (W_l,X_l,Y_l)(t)=(W_l,X_l,Y_l)(ω)}.
3. For every j, then k with j≠k, E[betaPsi_j betaPsi_k]=0.
4. The vector of zero-completed studentized β estimates as defined in T9
   converges weakly to the product of five standard normal laws.
5. The vector of their two-sided normal p-values converges weakly to the
   product of five Lebesgue measures restricted to [0,1] (uniform laws).
6. Their Fisher statistic converges weakly to chiSquareTen.

There are no empirical statistic or empirical p-value assertions. The stronger
joint premise in item 3 is an actual hypothesis, not an inferred conclusion of
the separate standing premises.

## SAP.P019a.T11

For every finite Ω and then every Study S, the theorem is a conjunction of
four separately conditional assertions:

1. If noLiarsDesign, then treatmentIndependent, then P(Z=0)>0, then
   P(Z=1)>0, one has
   `E[V|Z=1]=E[W]+μ`, `E[V|Z=0]=E[W]`, and
   `E[V|Z=1]−E[V|Z=0]=μ`.
2. If monotonicity and then P(Y=1)>0, then E[X|Y=1]=1.
3. If standing, then for every real α with 0<α<1, if
   `{x:1−α/2≤Φ(x)}` is nonempty and then bounded below,
   `lim_{n→∞} P_n(|μhat(0,0)−μ| ≤
      q(1−α/2) sqrt(μVarianceHat(0,0,0)))=1−α`.
   This is asymptotic coverage of a two-sided interval, not an explicit
   weak-limit assertion for μhat or a finite-sample coverage guarantee.
4. If monotonicity, then noLiarsDesign, then treatmentIndependent, then
   P(Z=0,Y=1)>0, then P(Z=1,Y=1)>0, one has m_11=m_01+1.

The standing assumption does not apply to the first, second, or fourth block
unless explicitly listed there. The quantile-set premises apply only to the
coverage assertion.

## Mathlib source checks

The lower-level meanings above were checked against:

* `Probability/Distributions/Gaussian/Real.lean`, `gaussianReal` (line 222):
  variance, not standard deviation, is the second parameter; variance one
  gives the ordinary Gaussian probability measure.
* `Analysis/Asymptotics/Defs.lean`, `IsBigOWith`/`IsBigO` (lines 73/85):
  eventual absolute-norm domination with an existential constant.
* `MeasureTheory/Integral/Bochner/Basic.lean`, `integral` (line 158), and
  `MeasureTheory/Function/L1Space/Integrable.lean`, `Integrable` (line 59):
  totalized integral and genuine integrability, respectively.
* `MeasureTheory/Measure/Map.lean`, `Measure.map` (line 99), and
  `MeasureTheory/Constructions/Pi.lean`, `Measure.pi` (line 210):
  pushforward and finite product measures.
* `Analysis/SpecialFunctions/Log/Basic.lean`, `Real.log` (line 44) and
  `log_zero` (line 103): the log convention stated above.
* `Order/Filter/Defs.lean`, `Tendsto` (line 422): filter-map convergence.

No claims or architect record have been used in this reading.
