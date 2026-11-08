# Blind reading of P002-T11 through P002-T15

Saved at stage 1, before reading either `claims.json` or `record.json`.
The sources read are the five Challenge docstrings/statements and every entry of
their elaborated closures in `closure.json`. Generated proof declarations were
also inspected by compiling `scratch/Blind.lean` (successful).

## Shared, fully expanded mathematical notation

The following notation is used below solely to avoid repeating finite sums. It
expands the SAP definitions to finite sets, real arithmetic and Mathlib limits.

* A population of size `n : ℕ` is a triple `(y,d,n1)` with
  `y : Fin n → Bool → ℝ`, `d : Fin n → Bool → Bool`, and `n1 : ℕ`.
  Here `Fin n` is the set of natural numbers less than n. `Population.mk` is the
  constructor and `.y`, `.d`, `.n1` are its projections; they impose no conditions.
* Write `b(t)=1` for `t=true` and `b(t)=0` for `t=false`.
  Write `n0=(n:ℝ)-(n1:ℝ)` and `p=(n1:ℝ)/(n:ℝ)`.
  A valid design means `2≤n`, `0<n1`, and `n1<n`.
* `C={i∈Fin n : d(i,false)=false and d(i,true)=true}` is the complier set.
  Monotone receipt means, for every i, `d(i,false)=true → d(i,true)=true`.
* For a real array z on `Fin n`, write
  `M(z)=(Σ_i z_i)/(n:ℝ)` and
  `M_H(z)=(Σ_{i∈H} z_i)/(|H|:ℝ)` for any finite subset H.
  `L=M_C(i↦y(i,true)-y(i,false))` is the complier average outcome difference.
  `V(z)=Σ_i(z_i-M(z))²/((n:ℝ)-1)`.
  For a finite H, `G_H(z,t)` is
  `Σ_{i∈H}(z_i-M_H(z))(t_i-M_H(t))/((|H|:ℝ)-1)` if `2≤|H|`,
  and is zero otherwise; `G_H(z,z)` is the group variance.
* For a Boolean assignment arm a and real β,
  `w_i(a,β)=y(i,d(i,a))-β*b(d(i,a))`, and
  `v_i(a,β)=w_i(a,β)-M(w(a,β))`.
  `S_a²(β)=p²(1-p)² V(w(a,β))`.
  The fourth norm of z is `sqrt(sqrt((Σ_i z_i⁴)/(n:ℝ)))`.
* The finite design space is
  `A={H⊆Fin n : |H|=n1}` (the `powersetCard` of the universal finite set).
  For a real function F on finite subsets,
  `E_A F=(Σ_{H∈A} F(H))/(|A|:ℝ)` and
  `Var_A F=E_A(H↦(F(H)-E_A F)²)`.
  For a predicate B, `P_A(B)=|{H∈A:B(H)}|/(|A|:ℝ)`.
  These are finite uniform averages, not Bochner integrals or sample estimates.
* Under an original assignment O, the observed adjusted array is
  `q^O_i=y(i,d(i,1_{i∈O}))-β*b(d(i,1_{i∈O}))`.
  The two arm means of a fixed array q under assignment H are `M_H(q)` and
  `M_{Hᶜ}(q)`, with complement taken inside `Fin n`.
  Write
  `t_q(H)=(Σ_i q_i(1_{i∈H}-p))/(n:ℝ)` and
  `s_q²(H)=p²(1-p)²[Σ_{i∈H}(q_i-M_H(q))²/(n1:ℝ)²
                     +Σ_{i∈Hᶜ}(q_i-M_{Hᶜ}(q))²/n0²]`.
  This last expression uses squared arm counts, not Bessel-corrected arm variances.
* `Θ(P;δ,r,A0)` means the conjunction of: a valid design; monotone receipt;
  C nonempty; `r*n≤n1≤(1-r)*n`; the inequality
  `G_C(w(true,L),w(false,L)) ≥
     -δ*sqrt(G_C(w(true,L),w(true,L)))*sqrt(G_C(w(false,L),w(false,L)))`;
  and, for both Boolean a,
  `sqrt(sqrt(M(i↦v_i(a,L)⁴))) ≤ A0*sqrt(V(w(a,L)))`.
  Positivity of either V is not part of this definition. Parameter signs are not
  imposed inside Θ; each theorem supplies its own parameter hypotheses.

## SAP.P002a.T11

Location: `SAP/P002a/Challenge/Part1.lean:113–122`. The docstring describes corrected
treated sample centering, exact finite expectations and their cancellation and rate.

The statement is the conjunction of four independently universally quantified
propositions, in this order:

1. For every natural n, population P of size n, proof of a valid design, real β,
   finite subset S, and proof `S∈A`, both of the following hold:
   `M_S(i↦(q^S_i-M_S(q^S))²)
       = M_S(i↦v_i(true,β)²)-B(S)²`, where
   `B(H)=M_H(w(true,β))-M(i↦y(i,d(i,true)))
                         +β*M(i↦b(d(i,true)))`;
   and `E_A(H↦B(H)²)=n0/[n1*n*(n-1)] * Σ_i v_i(true,β)²`.
   All count factors in these formulas are cast to reals. There is no monotonicity,
   complier or positivity assumption in this component.
2. For every n, P, valid-design proof, β and proof `0<S_true²(β)`,
   `E_A(H↦B(H)²/S_true²(β))
       =n0/[n1*n*(n-1)] * (Σ_i v_i(true,β)²)/S_true²(β)`.
3. For every n, P, valid-design proof, β and proof `0<S_true²(β)`,
   `(Σ_i v_i(true,β)²)/S_true²(β)=(n-1)/[p²(1-p)²]`, and
   `E_A(H↦B(H)²/S_true²(β))=n0/[n1*n*p²(1-p)²]`.
4. For every size map `sizes:ℕ→ℕ`, proof it is strictly increasing, dependent
   sequence `P_j:Population(sizes j)`, reals δ,r,A0, proofs
   `δ<1`, `0<r≤1/2`, `0<A0`, proofs `Θ(P_j;δ,r,A0)` for every j, and proofs
   `0<S_true,j²(L_j)` for every j, define
   `f_j=E_{A_j}(H↦B_j(H)²/S_true,j²(L_j))` with β replaced by L_j.
   Then `f=O(n0_j/(n1_j*sizes j))` at the natural-number atTop filter and
   `f_j→0`. The Big-O means that there exists a real constant c such that
   eventually `|f_j|≤c*|n0_j/(n1_j*sizes j)|`.

Closure read: `Population` and all five listed constructor/projection entries,
`binary`, `compliers`, `MonotoneReceipt`, `mean`, `groupMean`, `late`, `popVar`,
`groupCov`, `groupVar`, `w`, `v`, `fraction`, `controlSize`, `ValidDesign`,
`assignments`, `expectation`, `observedD`, `observedY`, `observedW`, `armMean`, `S2`,
`fourthNorm`, `Theta`, `T11Finite`, `T11Normalized`, `T11Rate`,
`T11WholeCancellation`, `T11WholeStatement`, and `T8Statement._proof_2`.
The last is only the Mathlib instance `(1+1).AtLeastTwo` used for real numeral syntax.

Junk conventions: real division has `x/0=0`. Unrestricted populations could have
empty means, empty assignments, n=0 or n=1, or n1 outside the design range. Here
validity guarantees n≥2, both arms nonempty and A nonempty; `S∈A` guarantees its
cardinality. Positive S² guards every displayed normalized expression and implies
its underlying variance is nonzero. The unnormalized assertion includes constant
arrays and correctly has both sides zero. In Θ, nonempty C guards L; group
covariance is explicitly zero when |C|<2, including singleton compliers. This is
a substantive convention to compare with the paper. Mathlib `Real.sqrt x=0` for
x≤0; here all radicands are variances or fourth moments and hence nonnegative.
Zero variances are permitted in Θ, but the treated one is excluded in the rate.
`n-1` is real subtraction, not truncated natural subtraction. Casts preserve
finite cardinalities and counts. Strictly increasing natural sizes tend to
infinity. There is no use of log, real powers, infima/suprema, limsup/liminf,
nonintegrable functions or default partial-function values.

## SAP.P002a.T12

Location: `SAP/P002a/Challenge/Part1.lean:124–126`. The docstring presents a concrete
eight-unit failure of a printed variance lower bound and attainment of a corrected
bound. There are no free parameters or implication hypotheses.

Take n=8, n1=4, `d(i,a)=a`, and `y(i,a)=-1` for i<4 and `+1` for i≥4,
independently of a. Set `S={0,1,2,3}` and β=0. The theorem asserts all of:

* `Θ(P;0,1/2,1)`, L=0 and `S∈A`;
* `Var_A(t_{q^S})=1/28`;
* `p²(1-p)²/(8-1) * (n0*n1/8) *
     (M_S(q^S)-M_{Sᶜ}(q^S))²=1/14`;
* the preceding variance is strictly smaller than that expression;
* |A|=70, `M_S(q^S)-M_{Sᶜ}(q^S)=-2`, and
  `p²(1-p)²/(8-1)*(M_S(q^S)-M_{Sᶜ}(q^S))²=1/28`.

Here the population and every statistical expression mean exactly the finite sums
in the shared expansion. In particular, the array q is held fixed while the
assignment argument of t varies in the design variance.

Closure read: `Population` and its listed constructor/projections, `binary`,
`compliers`, `MonotoneReceipt`, `mean`, `groupMean`, `late`, `popVar`, `groupCov`,
`groupVar`, `w`, `v`, `fraction`, `controlSize`, `ValidDesign`, `assignments`,
`expectation`, `designVariance`, `observedD`, `observedY`, `observedW`, `rawTau`,
`armMean`, `fourthNorm`, `Theta`, `signModel`, `T12Printed`, `T12Values`,
`T12Statement`, and all five `T12Printed._proof_1` through `_proof_5`.
The generated proofs certify `NeZero 8` and `AtLeastTwo` for 2,28,8,14; they only
justify finite literals and numeral syntax.

Junk conventions: all means, sample variances and design averages have nonzero
denominators: the sizes are 8,4,4,8−1=7, and |A|=70. C is all eight units.
Group variance is in its |C|≥2 branch. The only square roots occur in Θ, where
their arguments are nonnegative. The finite literal indices 0,1,2,3 denote
distinct valid elements of `Fin 8` (the general `Fin` numeral wraparound convention
does not alter them). `8-1` in the displayed real formulas is real subtraction.
No totalized division or square root can drive the counterexample. There are no
limits, extended-real conversions, integrals, empty index types, partial
functions, logarithms, real powers or extrema.

## SAP.P002a.T13

Location: `SAP/P002a/Challenge/Part1.lean:128–130`. The docstring calls this the
corrected finite reassignment-variance bound with an explicit balance constant.

For every n, population P of size n, valid-design proof, real array
`q:Fin n→ℝ`, finite subset S, proof `S∈A`, real r, proof `0<r≤1/2`, and proofs
`r*n≤n1` and `n1≤(1-r)*n`, the two conclusions are

`p²(1-p)²/(n-1)*(M_S(q)-M_{Sᶜ}(q))² ≤ Var_A(t_q)` and

`r²(1-r)²/n*(M_S(q)-M_{Sᶜ}(q))² ≤ Var_A(t_q)`.

The population's y and d are unrestricted and unused: it supplies only n1 for the
design. There is no Θ, treatment monotonicity, β, positivity, distributional
approximation or sequence hypothesis. q may be any deterministic real array.
The means, variance and reassignment law are the expanded finite formulas above.

Closure read: `Population`, `Population.mk`, `Population.n1`, `ValidDesign`,
`assignments`, `expectation`, `designVariance`, `fraction`, `groupMean`,
`armMean`, `rawTau`, `T13Statement`, and `T12Printed._proof_2` (only the
`AtLeastTwo 2` numeral-syntax instance).

Junk conventions: validity and membership ensure n≥2, 1≤n1≤n−1, both S and Sᶜ
nonempty and A nonempty. The denominators n, n−1 and |A| are positive. This
theorem permits a constant q and zero variance, in which case both lower bounds
are zero. All subtractions involving real factors are real subtractions. Natural
cardinalities are faithfully cast. There are no square roots, logs, real powers,
integrals, infinities, extrema, filter limits, partial functions or empty index
types in this closure's effective formulas.

## SAP.P002a.T14

Location: `SAP/P002a/Challenge/Part1.lean:132–138`. The docstring says the printed
claim is false and describes the balanced-sign family, exact laws, erroneous
standard-deviation/variance ratios, and corrected variance ratios.

For a natural m set n=2m, n1=m, `d(i,a)=a`, and let `z_i=-1` for i<m and +1
otherwise, with `y(i,a)=z_i` for both a. Let
`K_m(T)=|{i∈T:m≤i.val}|`, `h_m(T)=(2*K_m(T)-m)/m`,
`U_m(T)=sqrt(s_z²(T))/Var_A(t_z)`, and `R_m(T)=s_z²(T)/Var_A(t_z)`.
The theorem is the conjunction of four propositions:

1. For every m with 2≤m, `Θ(P;0,1/2,1)` and L=0. For every S∈A, take
   `q=q^S` at β=0. Then `Var_A(t_q)=1/[4*(2m-1)]`,
   `P_A(|sqrt(s_q²(T))/Var_A(t_q)-1|≥1/2)=1`, and for every real κ>0,
   `P_A(|s_q²(T)/Var_A(t_q)-1|≥κ)≤2/(2m*κ)`.
   In addition, the probability in the erroneous ratio expression with fixed
   q=z and m=j+2 tends to 1 as j→∞.
2. For every m≥2 and natural l,
   `P_A(K_m(T)=l)=choose(m,l)*choose(m,m-l)/choose(2m,m)` if l≤m,
   and equals zero otherwise. Natural binomial coefficients are cast to reals.
3. For every m≥2: every original assignment O∈A gives `q^O=z`;
   `E_A(h_m(T)²)=1/(2m-1)`; `Var_A(t_z)>0`; and for each T∈A,
   `M_T(z)=h_m(T)`,
   `s_z²(T)=(1-h_m(T)²)/(4*(2m))`,
   `U_m(T)=2*(2m-1)/sqrt(2m)*sqrt(1-h_m(T)²)`,
   `R_m(T)=(2m-1)*(1-h_m(T)²)/(2m)`,
   `h_m(T)²=1 → U_m(T)=0`, and
   `h_m(T)²≠1 → [8*(2m-2)/(2m)²≤1-h_m(T)² and 3≤U_m(T)]`.
   Also `0≤R_m(T)≤1`, and `E_A(1-R_m(T))=2/(2m)`.
4. For every `ms:ℕ→ℕ`, proof of strict increase and proofs `2≤ms j` for all j:
   for each ε>0,
   `P_{A_j}(|U_{ms j}(T)/sqrt(2*ms j)-2|≥ε)→0`;
   for every real M, `P_{A_j}(M<U_{ms j}(T))→1`;
   and for each κ>0, `P_{A_j}(|R_{ms j}(T)-1|≥κ)→0`.
   All arrows are real-valued Tendsto at the natural atTop filter.

All arrays, means and probability/variance expressions in this expansion are
finite sums as defined above. No independence across different sample sizes is
asserted or needed to state these limits of scalar finite probabilities.

Closure read: `Population` and all listed constructor/projections, `binary`,
`compliers`, `MonotoneReceipt`, `mean`, `groupMean`, `late`, `popVar`, `groupCov`,
`groupVar`, `w`, `v`, `fraction`, `controlSize`, `ValidDesign`, `assignments`,
`expectation`, `designVariance`, `probability`, `observedD`, `observedY`,
`observedW`, `rawTau`, `armMean`, `rawSigma2`, `fourthNorm`, `Theta`, `signModel`,
`W2sign`, `W2K`, `W2q`, `W2U`, `W2R`, `T14Statement`, `W2T14Finite`,
`W2T14Hypergeom`, `W2T14Limits`, `T14WholeStatement`, and the generated proofs
`T12Printed._proof_2`, `T14Statement._proof_1`, `W2q._proof_1`,
`W2T14Finite._proof_1`, `_proof_2`, `_proof_3`. These generated proofs are only
`AtLeastTwo` instances for the numerals 2,4,2,4,8,3 respectively.

Junk conventions: the helper definitions are total at m=0, but every quantified
use here assumes m≥2. Thus n≥4, n1=n0=m>0, n−1>0, A is nonempty, and the exact
reassignment variance is strictly positive. Sample within-arm variation can be
zero and sqrt(0)=0 is the intended value; the support assertions explicitly
include these zero numerators. `1-h²` is nonnegative on valid assignments, so
sqrt is never being used at a negative argument there. `Nat.choose m (m-l)`
contains truncated natural subtraction, but the formula uses that branch only
when l≤m, so it is the ordinary difference in every operative case. Expressions
like `(2*m:ℕ)-(1:ℝ)` cast 2m before subtraction; no unintended natural truncation
occurs. |A|=choose(2m,m)>0. All scalar limit expressions are ordinary Tendsto,
with no empty/unbounded limsup or sInf convention. There are no integrals, logs,
real powers, infinity-to-real conversions or partial functions.

## SAP.P002a.T15

Location: `SAP/P002a/Challenge/Part1.lean:140–148`. The docstring describes corrected
Lemma 12 with positive adjusted potential-outcome variances, simultaneous positive
tolerances, and any coupling of exact complete-randomization marginals.

Quantifiers, in order: every type Ω (in an arbitrary universe), measurable-space
structure on Ω, measure μ, proof μ is a probability measure, size map
`sizes:ℕ→ℕ`, proof sizes is strictly increasing, dependent population sequence
`P_j:Population(sizes j)`, assignment maps
`Z_j:Ω→Finset(Fin(sizes j))`, reals δ,r,A0, proofs
`δ<1`, `0<r≤1/2`, `0<A0`, proofs `Θ(P_j;δ,r,A0)` for every j, proofs
`0<V(w_j(a,L_j))` for every j and Boolean a, a proof of the marginal law below,
subsequence map `sub:ℕ→ℕ`, and proof sub is strictly increasing.

The marginal law is: for every j and every predicate E on finite subsets of
`Fin(sizes j)`, the set `{ω:E(Z_j(ω))}` is measurable and
`μ{ω:E(Z_j(ω))}=ENNReal.ofReal(P_{A_j}(E))`.
This is measurability and the exact uniform fixed-count marginal; it imposes no
joint independence. `ENNReal.ofReal x` is the nonnegative extended real obtained
from max(x,0); here each x is a finite probability in [0,1].

Conclusion: for μ-almost every ω, for every real κ>0,

`P_{A_{sub j}}({H:
  |s_{q_{j,ω}}²(H)/Var_{A_{sub j}}(t_{q_{j,ω}})-1|≥κ}) → 0`,

where `q_{j,ω,i}=y_{sub j}(i,d_{sub j}(i,1_{i∈Z_{sub j}(ω)}))
                  -L_{sub j}*b(d_{sub j}(i,1_{i∈Z_{sub j}(ω)}))`.
The variance and probability in this expression average independently over the
entire fixed finite reassignment design, holding q fixed. The almost-sure set
may depend on the fixed subsequence but is simultaneous for all positive κ.
There is no pointwise finite-size positivity hypothesis on this conditional
variance, no uniform lower variance bound, and no random reassignment sequence
among the universally quantified objects.

Closure read: `Population` and all listed constructor/projections, `binary`,
`compliers`, `MonotoneReceipt`, `mean`, `groupMean`, `late`, `popVar`, `groupCov`,
`groupVar`, `w`, `v`, `fraction`, `controlSize`, `ValidDesign`, `assignments`,
`expectation`, `designVariance`, `probability`, `observedD`, `observedY`,
`observedW`, `rawTau`, `armMean`, `rawSigma2`, `fourthNorm`, `Theta`,
`RandomizationSequence`, `T15WholeStatement`, and
`T7FiniteCounterexample._proof_1`. The last is just `AtLeastTwo 2` for numeral
elaboration, not a counterexample assumption.

Junk conventions: real division sets the conditional variance quotient to zero
at variance zero; then `|0-1|=1`, so its event can affect finite-size probabilities.
Eventual almost-sure positivity is described in the docstring, but is not itself
an additional conjunct in the theorem statement. This potential finite-size
totalization must be checked when comparing the claimed asymptotic meaning.
Validity gives nonempty finite arms and assignments for every j. Θ gives
nonempty C but explicitly zero group covariance/variance for a singleton C.
All fourth-moment and variance square roots have nonnegative arguments. Positive
population variances are assumed for both arms, without a uniform quantitative
lower bound. Casts, Boolean indicators and complements have their ordinary
finite meanings; no truncated natural subtraction is used. `ofReal` cannot
clip a genuine negative probability because these finite count ratios are
nonnegative, and no `toReal ∞` occurs. The almost-everywhere quantifier is with
respect to an actual probability measure, not an empty or zero-measure model
forced by the statement. No Bochner integral, log, real power, extrema,
limsup/liminf or default partial-function value is used.
