# Blind mathematical reading

This file was initially written from `SAP/P009b/Defs*.lean`, `Defs/Part1`–`Part5`, and the Challenge files before opening either `claims.json` or `record.json`. The original saved blind text is preserved in `scratch/reading-blind.md`. One postblind correction, concerning the parsing of `empiricalBias` in T25, is marked below and explained at the end. The theorem docstrings are not used to supply missing hypotheses or conclusions. All mathematical notation below expands the actual definitions.

## Common objects and conventions

* `Assignment n` is the full Boolean cube `{false,true}^{Fin n}`; `Fin n` is the set of natural numbers less than `n`. Write `z_i` as 0 or 1 using `bit`. A law `P` on a finite type Ω is a real mass function with `P(ω)≥0` and `Σω P(ω)=1`. Thus a law cannot exist on an empty Ω. `E_P X=Σω P(ω)X(ω)` and `P(A)=E_P 1_A`. Conditional expectation is `E_P(1_A X)/P(A)`. It equals zero if `P(A)=0`, because real division by zero is zero in Lean. Covariance is `E_P[(X−E_P X)(Y−E_P Y)]`, variance is covariance with itself, and conditional covariance uses the same construction with conditional expectations throughout. These are finite sums, without any measurability or integrability assumption.
* An experiment E consists of such a law on the full cube and arbitrary real outcome schedules `Y_i(z)` on the entire cube, including assignments of probability zero. Write `p_ib=P(z_i=b)`. Write `Y_i(b;z)=Y_i(z[i←b])`, `τ_i(z)=Y_i(1;z)−Y_i(0;z)`, `ATE(z)=Σi τ_i(z)/n`, and `EATE=E_P ATE`. No interference means that agreement at coordinate i implies equality of outcome i, for every pair of cube assignments.
* `ADSE=Σi{E[Y_i|z_i=1]−E[Y_i|z_i=0]}/n`. Write `μhat_b(z)=Σi 1{z_i=b}Y_i(z)/p_ib /n`, `Nhat_b(z)=Σi 1{z_i=b}/p_ib`, `μ_b=Σi E Y_i(b;Z)/n`, and `μbreve_b=Σi E[Y_i(b;Z)|Z_i=b]/n`. `HT=μhat_1−μhat_0`. `HJ=n μhat_1/Nhat_1−n μhat_0/Nhat_0` when both Nhat values are nonzero, and HJ is explicitly zero otherwise.
* `I_ij=1` precisely if `i=j` or there are two full-cube assignments differing only at i on which outcome j differs. Otherwise `I_ij=0`. Thus self-interference is inserted irrespective of the schedule. `d_ij=1` precisely if there exists ℓ with `I_ℓi=I_ℓj=1`; otherwise it is zero. Write `D_i=Σj d_ij`, `dAVG=Σi D_i/n`, `c_i=Σj I_ij` (outgoing), `a_i=#{j:I_ji=1}` (incoming, a natural number), `C2=sqrt(Σi c_i²/n)`, and `dMAX=sup_i D_i`.
* A pairing is a permutation ρ of `Fin n` with `ρ(ρ(i))=i` and no fixed point. `e_ij=1` precisely if `d_ij=0` and there exists ℓ with `I_ℓi=I_ρ(ℓ),j=1`; otherwise zero. `eAVG=Σij e_ij/n`; `rSUM=Σi I_ρ(i),i`.
* Bernoulli design means every `p_i1` lies strictly between zero and one and each cube mass equals `Πi p_i1^{z_i}(1−p_i1)^{1−z_i}`. Complete design with natural m means `0<m<n` and uniform mass `1/binomial(n,m)` on assignments with exactly m ones and zero elsewhere. Paired design means even n and mass `2^{−(n/2)}` on assignments having opposite treatments in every ρ-pair, and zero elsewhere. Here `n/2` is natural division.
* `Regular(E,k,q,s)` means, jointly: real `k>0`, `q≥2`, `s≥1`; `1/k≤p_i1≤1−1/k` for every i; `E|Y_i|^q≤k^q` for every i; and `E|Y_i(b;Z)|^s≤k^s` for every i and b. Real exponents use `Real.rpow`. On positive bases this is the ordinary real power, and at zero it is 1 for exponent zero and zero for nonzero exponents. All its uses as a moment have nonnegative bases and nonnegative orders.
* `masked_i(z)` keeps z_j when `I_ji=1` and puts false at other coordinates. `maskedOthers_i(z)` additionally forces coordinate i to false. For any finite law, `α_P(X,Y)` is the real supremum of `|P(X∈S,Y∈T)−P(X∈S)P(Y∈T)|` over all sets S,T in the respective codomains. This set is nonempty and bounded. `mixPower(a,θ)` is zero if a=0 and `a^θ` otherwise, including when θ=0. `αEXT(E,θ)=Σij(1−d_ij)mixPower(α_P(masked_i,masked_j),θ)/n`.
* `BER(z)=Σi[1{z_i=1}Y_i(z)²/p_i1²+1{z_i=0}Y_i(z)²/p_i0²]/n²`. `MSQ=Σi(E τ_i)²/n`. Set `ξ_ij(b)=E[Y_i(Z[i←b][j←1])−Y_i(Z[i←b][j←0])]` (j is overwritten last), `ξbreve_ij=(1−p_i1)ξ_ij(1)+p_i1 ξ_ij(0)`, and `ybreve_i=(1−p_i1)E[Y_i|Z_i=1]+p_i1 E[Y_i|Z_i=0]`. Then
  `B1=Σ_{i≠j}[ξbreve_ij ξbreve_ji+2 ybreve_j(ξ_ij(1)−ξ_ij(0))]/(n dAVG)` and
  `B2=Σ_{i≠j}Σ_{a,b∈{0,1}}(1−2a)(1−2b)Cov(Y_i,Y_j|Z_i=a,Z_j=b)/(n dAVG)`.
* `λMAX=sup{Σij v_i d_ij v_j:Σi v_i²=1}`, a Rayleigh-quotient maximum when n>0, with finite dimension and bounded quadratic form. `AVG=dAVG·BER`, `MAX=dMAX·BER`, `SR=λMAX·BER`. For the theorems using these real suprema, n>0 ensures nonempty domains. `sqrt` is the nonnegative square root on nonnegative inputs; Mathlib sets it to zero on negative inputs.
* A study S has natural sizes N_t>0 for every natural t, N_t→∞, and an experiment E_t of each size. `size S t` is N_t as a real. A regular sequence requires the same k,q,s for every t. `LittleO(f,g)` means the real sequence f(t)/g(t) tends to zero. `InProbability(S,X)` means, in quantifier order, for every real ε>0, `P_t(ε<|X_t|)→0`; laws may vary with t.
* `bal(G,z)=Σ_{j∈G}(2z_j−1)` for an unweighted finite subset G. `M(x)=2` for x>0, 1 for x=0, and zero for x<0. `fullOutcome(b)` is `Y_i(z)=M(bal(Fin n\{i},z))z_i+b_i`. `oneSourceOutcome(h,c)` is `Y_i(z)=2z_0 z_i+c_i` for `0<i<h`, and `Y_i(z)=z_i+c_i` otherwise. It uses the zero coordinate only where n>0 follows from existence of i. A fair law gives mass `2^{−n}` to each assignment; `fairExperiment` uses it with the indicated schedules.
* `armVariable(E,b,a,i)=1{Z_i=b}Y_i(Z)^a`, with natural a (so zero outcomes to the zeroth power are 1 within the selected arm). `treatedIncoming_i(z)=Σj 1{j≠i,I_ji=1,z_j=1}`. `H(n,m,r,t)=binomial(m,t)binomial(n−m,r−t)/binomial(n,r)`, where the subtractions inside the binomial coefficients are natural truncated subtraction. The ranges in T18 avoid unintended truncation and zero denominators.
* **Postblind correction:** `empiricalBias(R,x)=(Σ_{r∈Fin R}x_r−1)/R` and `reportedBias=|empiricalBias|`: the subtraction of 1 occurs after summation. For positive R this is `mean(x)−1/R`. The initial reading incorrectly put the subtraction inside the sum. `uniformBaselines(n)` is the product probability measure under which all x_i are independent uniform [0,3], all u_i are independent uniform [0,7], and the two vectors are independent. It is built as finite products of restricted Lebesgue measures scaled by 1/3 and 1/7. `AdjacentRanks(x,ρ)` means that there exists a permutation σ with `x_{σ(i)}` nondecreasing in i and `ρ(σ(i))=σ(j)` whenever i≠j and `floor(i/2)=floor(j/2)`; ties may be ordered arbitrarily.
* `SimulationIntegrable(P,Q)` asks, for each of the two choices of design and each of the two estimators HT/HJ, integrability under uniformBaselines of signed design bias, design variance, and design mean squared error about EATE (twelve integrands). The complete experiment uses P; the paired experiment uses Q(x); both use `fullOutcome(x+u)`. `Integrable` means almost everywhere strong measurability and finite integral of the absolute value. The displayed integrals are Mathlib Bochner integrals, ordinarily zero if nonintegrable; T23 explicitly assumes integrability for every integrand it uses.
* For any finite law and real α, `err(P,α,f)=|P(f=1)−α/2|+|P(f=−1)−α/2|`. `dist3(x)=min(|x+1|,|x|,|x−1|)`. `sharpLaw(α)` on `Fin 3` has masses `(α/2,1−α,α/2)`, and `sharpValue=(-1,0,1)`. `CDF_α(x)` is 0 for x<−1, α/2 for −1≤x<0, 1−α/2 for 0≤x<1, and 1 for x≥1.

Mathlib operations checked directly include function update and involution (`Logic/Function/Basic.lean`), natural binomial coefficients (`Data/Nat/Choose/Basic.lean`), real powers (`Analysis/SpecialFunctions/Pow/Real.lean`), square root (`Analysis/Real/Sqrt.lean`), finite/binary product measures (`MeasureTheory/Constructions/Pi.lean`, `MeasureTheory/Measure/Prod.lean`), integrability and Bochner integrals (`MeasureTheory/Function/L1Space/Integrable.lean`, `MeasureTheory/Integral/Bochner/Basic.lean`), and filters (`Order/Filter/Defs.lean`, `Order/Filter/AtTopBot/Defs.lean`). Limits at `atTop` are ordinary sequence limits; eventually means for all sufficiently large natural indices. Natural subtraction truncates at zero; subtraction of cast real sizes does not.

## SAP.P009b.T18

For every natural n, experiment E, natural m with Complete(E,m), unit i, and `a_i≤min(m,n−m)`, put natural `r=a_i−1`. The following all hold, with no regularity or outcome-moment assumptions:

1. For every natural t≤r, `P(treatedIncoming_i=t)=H(n,m,r,t)`.
2. For every natural t and Boolean b, if t≤r, `P(treatedIncoming_i=t|Z_i=b)=H(n−1,m−b,r,t)` (m−b is natural subtraction).
3. If r=0, then for every b the conditional probability of count zero divided by its unconditional probability is 1; also the unconditional probability of count zero is 1.
4. For every t,b with t≤r and r>0, the conditional/unconditional count-probability ratio minus one equals
   `r/[p_ib(n−r)]·[p_ib−b t/r−(1−b)(r−t)/r]`.
5. For those same t,b the bracket lies strictly between −1 and 1, and the absolute ratio minus one is at most
   `r/[p_ib(n−r)] ≤ a_i/[p_ib(n−a_i)] ≤ a_i/[p_ib min(m,n−m)]`.
6. For every full-cube vector w and Boolean b, if `P(maskedOthers_i=w)>0`, the absolute conditional/unconditional probability ratio for this vector minus one is at most `a_i/[p_ib min(m,n−m)]`.

Every universal statement here is inside the preceding quantifiers; w is not restricted syntactically to a masked-vector image, but its positive probability forces it into that image.

## SAP.P009b.T19

There are no hypotheses or free parameters. Let n=6, use the fair law, let `Y_0=z_0+z_2+z_4`, `Y_1=z_1+z_3+z_5`, and `Y_i=z_i` for all other i. Pair 0↔1, 2↔3, 4↔5. Then `d_01=0`, `e_01=1`, `Σℓ(1−d_01)I_ℓ0 I_ρ(ℓ),1=3`, and real 1≠3. In addition, the displayed partner map is involutive; for every j, `I_j0=1 ↔ j∈{0,2,4}` and `I_j1=1 ↔ j∈{1,3,5}`; for every i,j with j≠0,1, `I_ij=1 ↔ i=j`; and for every ℓ the summand in the witness count is 1 exactly for ℓ∈{0,2,4}, and zero otherwise.

## SAP.P009b.T20

For every n>0, every experiment E and every pairing ρ, simultaneously: for every i,j,
`e_ij ≤ Σℓ(1−d_ij)I_ℓi I_ρ(ℓ),j ≤ Σℓ I_ℓi I_ρ(ℓ),j`, and `eAVG≤C2²`. There are no randomization, marginal, regularity, or moment hypotheses. All indicators must come from the full-cube outcome schedule, rather than being independently supplied arrays.

## SAP.P009b.T21

There are no hypotheses or free parameters. Take n=6, fair independent assignment, and the one-source model h=4 with `c_0=−1/4` and all other c_i=1. Then the design is Bernoulli, `dAVG=3`, `6dAVG=18`, `MSQ=1`, `B1=1/6`, `B2=1/3`, `E BER=229/144`, `Var(HT)=241/144`, and
`6/dAVG·(E BER−Var(HT))=MSQ/dAVG−B1−B2=−1/6`.
Also `1/3≠4·3/(6+4·3)`, `4·3/(6+4·3)=2/3`, `−1/6≠(6−3−12)/18`, and `(6−3−12)/18=−1/2`, all in the reals.

## SAP.P009b.T22

This is a conjunction of three separately quantified statements.

For every n>0, natural h with 1≤h≤n, and arbitrary real baseline vector c, take the fair one-source experiment, and put `A=n+h(h−1)` using real arithmetic. Then
`n dAVG=A`, `MSQ=1`, `B2=(h−1)(h−2)/A`, `B1=(2+4c_0)(h−1)/A`, and
`n²(E BER−Var HT)=n−2(h−1)(1+2c_0)−(h−1)(h−2)`.
If c_0=−1/4, both `MSQ/dAVG−B1−B2` and `n/dAVG·(E BER−Var HT)` equal `C=(n−(h−1)²)/A`.
Always `0≤2(h−1)/A≤1/sqrt(n)`.

Separately, for every natural n,h satisfying the same inequalities,
`(n−(h−1)²)/A − (n−(h−1)−h(h−1))/A = 2(h−1)/A`.

Separately, for every study S, real k,q,s, common RegularSequence(S,k,q,s) with q≥4, natural sequence h_t with 1≤h_t≤N_t, and baseline vectors c_t with c_{t,0}=−1/4, if each design is exactly fair and each schedule is exactly oneSourceOutcome(h_t,c_t), then
`N_t/dAVG_t·[BER_t(Z)−Var_t HT_t] − [N_t−(h_t−1)²]/[N_t+h_t(h_t−1)] → 0` in probability as defined above. No rate of growth or limiting regime for h_t is required.

## SAP.P009b.T23

For every positive even natural n, law P, complete-design hypothesis for P with exactly n/2 treated units, every function ρ taking each real vector x to a pairing adjacent in nondecreasing x-rank, every law-valued function Q(x) giving the paired design for ρ(x), and the twelve-integrand hypothesis SimulationIntegrable(P,Q), the following sampling integrals hold. In each experiment the outcome schedule is fullOutcome(x+u). Let `E_c` denote the experiment using P and `E_p` the one using Q(x), with sampling measure uniformBaselines(n).

For each T∈{HT,HJ},
`∫[E_c T−EATE_c]=−1`, `∫[E_p T−EATE_p]=−1`,
`∫Var_c T=58/(3n)`, `∫Var_p T=49/(3n)+36/[n(n+1)(n+2)]`,
`∫E_c[(T−EATE_c)²]=58/(3n)+1`, and
`∫E_p[(T−EATE_p)²]=49/(3n)+36/[n(n+1)(n+2)]+1`.
Finally `1/[58/(3n)]=3n/58`. The variance here is first taken in the finite assignment law at fixed x,u, and then integrated; it is not defined as a joint-space variance. There is no separate limit or fixed-baseline variance identity in this theorem.

## SAP.P009b.T24

For every positive even n, experiment E and arbitrary real b, if the outcome schedule is fullOutcome(b) and the design is either complete with n/2 treated or paired under some pairing, then EATE=1. For every assignment z of strictly positive mass, simultaneously: for every i, `Y_i(z)=b_i` and `τ_i(z)=2(1−z_i)`; `ATE(z)=1`; `HT(z)=HJ(z)`; and `HT(z)=2/n·Σi(2z_i−1)b_i`. Also both estimators have mean zero, signed bias −1 relative to EATE, absolute bias 1, and design mean squared error equal to their respective design variance plus 1. The absolute-bias conclusions are separately quantified over precisely the same objects and hypotheses.

## SAP.P009b.T25

Three conjuncts: (1) for every positive natural R and every R-tuple of real estimates, reportedBias is nonnegative and equals the absolute empiricalBias; also |−1|=1 and −1≠1. (2) For every n,E,b and design satisfying exactly T24's positive-even, fullOutcome, and balanced-complete-or-paired hypotheses, HT and HJ both have signed bias −1 and absolute bias 1 relative to EATE. (3) For the one-element tuple (0), empiricalBias is −1; for (2), it is 1; their reportedBias values are equal. **Postblind correction:** the quantity in (1) is the absolute value of `(Σr estimates_r−1)/R`, hence the absolute deviation of the sample mean from 1/R when R>0. At R=1, used in (3), this happens to agree with mean error about 1.

## SAP.P009b.T26

For every study S and real 0<p<1, assuming each E_t has NoInterference and gives mass p to the all-true assignment, mass 1−p to the all-false assignment and zero to every other assignment, then: for every t and distinct i,j, `α_Pt(masked_i,masked_j)=p(1−p)`; for every t and every real exponent θ, `αEXT(E_t,θ)=(N_t−1)[p(1−p)]^θ`; in particular `αEXT(E_t,1)=(N_t−1)p(1−p)`. Furthermore `αEXT(E_t,1)/N_t→p(1−p)` and αEXT at exponent 1 is not LittleO of N_t. No moment or regularity bound is assumed; even constant outcome schedules qualify because I includes self-interference.

## SAP.P009b.T27

Three conjuncts with separate quantification:

1. For every natural n (possibly zero), experiment E, reals k,q,s with Regular(E,k,q,s), Bernoulli design, finite set G⊆Fin n, and cube assignment a,
   `(1/k)^|G| ≤ P(∀i∈G,Z_i=a_i) ≤ (1−1/k)^|G|`.
2. For every finite type Ω, law P, reals δ,α with each mass at most δ and 0<α<1, there exists a map f:Ω→{−1,0,1} whose mass at each of +1 and −1 differs from α/2 by at most δ. δ need not be stated positive; existence of P and the mass bound imply it is positive.
3. For every study S, reals k,q,s,α with common regularity, Bernoulli designs for every t and 0<α<1, and natural b_t≤N_t with b_t→∞, consider any supplied maps `f_t:{0,1}^{b_t}→{−1,0,1}`. Suppose for every t their err is no larger than that of every three-point-valued map on the same cube, when evaluated under E_t on the first b_t coordinates (indices 0 through b_t−1). Then for every t their error is at most `2(1−1/k)^{b_t}`, and for each Boolean a the probability that f_t of these coordinates equals +1 if a=true and −1 otherwise tends to α/2. The theorem does not quantify existentially over minimizing sequences.

## SAP.P009b.T28

Four separately quantified assertions. For every finite law P and three-point-valued F, `E F=P(F=1)−P(F=−1)`. For every such P,F, real x distinct from −1,0,1, and `|E F|<dist3(x)`, `P(F−E F≤x)=P(F≤x)`. For every real sequence μ_t→0 and every such x, eventually `|μ_t|<dist3(x)`. Finally, for every sequence of finite types Ω_t, laws P_t, three-point-valued maps F_t with E F_t→0, and such x, `dist3(x)>0` and eventually all three hold together: `|E F_t|<dist3(x)`, `P_t(F_t−E F_t≤x)=P_t(F_t≤x)`, and it is false that `dist3(x)<E F_t`.

## SAP.P009b.T29

For every natural n, experiment E, real k>0, real q≥2, observed-moment bound `E|Y_ℓ|^q≤k^q` for every ℓ, natural a satisfying 2a≤q, units i,j and Boolean arm b, let `X_i=1{Z_i=b}Y_i^a` and similarly X_j. Then the entire chain holds:

`|Cov(X_i,X_j)| ≤ sqrt(Var X_i Var X_j)`
`≤ sqrt(E|Y_i|^{2a} E|Y_j|^{2a})`
`≤ sqrt((E|Y_i|^q)^{2a/q}(E|Y_j|^q)^{2a/q})`
`≤ sqrt((k^q)^{2a/q}(k^q)^{2a/q})`
`=sqrt(k^{4a})=k^{2a}`.

The endpoint `|Cov(X_i,X_j)|≤k^{2a}` is also stated separately. There are no overlap, independence, or potential-outcome hypotheses. a=0 is included with the real-power convention described above.

## SAP.P009b.T30

For every n>0, every experiment E satisfying `p_i1>0` and `p_i0>0` for every i, and every cube assignment z (not only supported z), `MAX(z)=dMAX·BER(z)` and `SR(z)=λMAX·BER(z)`. Also
`AVG(z)=dMAX·BER(z) ↔ dAVG=dMAX or BER(z)=0`, and
`AVG(z)=λMAX·BER(z) ↔ dAVG=λMAX or BER(z)=0`.
No regularity assumption, inequality between the graph statistics, or asymptotic claim occurs here.

## SAP.P009b.T31

For every real 0<α<1 and every real x, the probability that sharpValue under sharpLaw(α) is ≤x equals CDF_α(x) including all three atom thresholds. Separately, for every sequence of finite types Ω_t, laws P_t and maps F_t into {−1,0,1}, every real 0<α<1, and hypotheses `P_t(F_t=−1)→α/2` and `P_t(F_t=1)→α/2`, for every real x, `P_t(F_t≤x)→CDF_α(x)`. This is pointwise convergence even at the three jumps, under the exact support hypothesis.

## SAP.P009b.T32

Four separate assertions: for every n,G,i,z,b, `bal(G,z[i←b])−bal(G,z)` equals `2(b−z_i)` when i∈G and zero otherwise. For every n,G,i∈G and z with z_i=false, flipping i to true increases balance by 2. For every integer h, `M(h+2)≠M(h) ↔ h∈{−2,−1,0}` and `M(h−2)≠M(h) ↔ h∈{0,1,2}`. For every n,G, distinct i,j and assignment z with z_i=false and z_j=true, simultaneously flipping i to true and j to false changes balance by `(2 if i∈G else 0)−(2 if j∈G else 0)`. No pairing or randomization is required for the last assertion.

## SAP.P009b.T33

For every n>0, natural h with 1≤h≤n, and arbitrary real baseline vector c, use the fair one-source experiment. For every distinct i,j, `ξ_ij(false)=0`, `ξ_ij(true)=2` precisely when `0<i<h` and j=0 and otherwise zero, and `ξbreve_ij ξbreve_ji=0`. Also `ybreve_0=1/2+c_0` and `B1=(2+4c_0)(h−1)/[n+h(h−1)]` with real arithmetic.

## SAP.P009b.T34

For every n>0, experiment E, pairing ρ under which E is paired, reals k,q,s with Regular(E,k,q,s), and every unit i and Boolean b,
`|E[Y_i(b;Z)|Z_i=b]−E Y_i(b;Z)|`
`= (1/2)|E[Y_i(b;Z)|Z_i=b]−E[Y_i(b;Z)|Z_i=1−b]| ≤ k`.
Furthermore `k≥2`, `2k≤2k²`, and `|ADSE−EATE|≤2k² rSUM/n`.
With the same objects and hypotheses, separately quantified, the sum of the two absolute conditional-versus-unconditional differences for b=true and b=false is at most 2k for every i. No bound by the unconditional absolute first moment is stated as a separate link.

## Postblind erratum: the parsing of T25

The original blind reading and initial step-2 verdict treated `SAP/P009b/Defs/Part2.lean:82`, `(∑ r, estimates r-1)/(R:ℝ)`, as a sum of estimate-minus-one. A subsequently compiled R=2 check exposed that misreading. `scratch/Parse.lean` proves by `rfl` that this definition is `((∑ r, estimates r)-1)/(R:ℝ)`. With notation disabled, the printed definition in `scratch/Parse.log` is `HDiv.hDiv (HSub.hSub (Finset.univ.sum fun r => estimates r) 1) ↑R`.

The same scratch file proves that constant estimates 1 give reportedBias=1/2 at R=2 and reportedBias=49999/50000 at R=50000. The corresponding absolute mean error about 1 is zero. Only T25 uses these definitions. This is the cited misreading that changes its step-2 verdict from whole to different; the original step-2 file is preserved in `scratch/claim-stage-before-record.json`.
