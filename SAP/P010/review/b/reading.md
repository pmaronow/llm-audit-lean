# Blind reading

This file was written after reading all Defs and Challenge sources and the relevant Mathlib definitions, and before opening either `claims.json` or `record.json`. The readings below are of the propositions, not of what their docstrings suggest the paper says. There are 23 stubs, `SAP.P010.T1` through `SAP.P010.T23`; each asserts its correspondingly numbered `T…Statement`. No statement has a proof premise from a Solution.

## Conventions and expansion of definitions

`Fin K` is the finite set {0,…,K−1}. A population state is `(Y,S,Z,X)` in R^K × {false,true}^K × Fin K × R^d, with the product Borel/discrete measurable structure. Write Y_a for potential outcome a, S_a for potential check a, Z for assignment, X for features, Y=Y_Z for response and S=S_Z for observed check. Let A={all S_a=true}, C={all S_a equal}, D_a={Z=a}, P={S=true}, W_a={S_a=true}, and O_a={all S_b=true for b≠a}. These are actual coordinate-defined measurable sets and functions. If K=0 the state space is empty; any probability-population hypothesis then has no instance. Statements with a specified a:Fin K already require K>0.

All measures are Mathlib measures with values in [0,+∞]. Probability means μ(universe)=1. Independence is independence of the two pulled-back sigma algebras: the probability of every measurable preimage intersection factors. In particular, it is pairwise independence of the stated functions, without any unstated joint independence. `Integrable f μ` means almost everywhere strong measurability and finite integral of |f|. A real Bochner integral is defined to be ZERO when its integrand is not integrable. The restricted integral is with respect to μ restricted to the event. Define

M_μ(f;E) = (∫_E f dμ)/(μ(E)).toReal.

This is exactly `meanOn`, including real division by zero giving zero and `ENNReal.toReal(+∞)=0`. It is an ordinary event conditional mean only when the event has positive finite mass and f is integrable there. When f is not integrable on E it returns zero. Every occurrence of M below has this literal meaning; an integrability premise is recorded where one is present.

Define p_a=μ(P∩D_a).toReal/μ(D_a).toReal (`passRate`). `randomAssignment` means, for EVERY a, (Y_a,S_a) is independent of Z, and μ(D_a)>0. `populationAssumptions` adds that μ is a probability measure and EVERY p_a>0. `covariateRandomAssignment` replaces the independent pair by (Y_a,S_a,X), still separately for every a, and keeps μ(D_a)>0. `covariateBalance` says: for every Boolean b with μ(S=b)>0, X and Z are independent under μ(S=b)⁻¹ times the restriction of μ to {S=b}.

For a measurable f and event E define L_μ(f;E)=μ(E)⁻¹·((μ restricted to E) pushed forward by f). This is `conditionalLaw`. Pushforward here is Mathlib `Measure.map`; its arbitrary fallback for non-a.e.-measurable functions is not triggered by these coordinate maps. Let F_a=L_μ(Y;P∩D_a), and r_a=(Σ_{b≠a}(1−p_b))/p_a. Define potential trim ratio v_a=(Σ_{b≠a}μ(S_b=false).toReal)/μ(W_a).toReal.

For a real measure F and real u, Q_F(u) is the infimum IN THE EXTENDED REALS of {x∈[-∞,+∞]: u≤F({y∈R:y≤x}).toReal}. `realQuantile` is Q_F(u).toReal, sending either infinity to zero. For a probability F this gives Q_F(u)=−∞ for u≤0 and Q_F(u)=+∞ for u>1; at u=1 the value may be finite or +∞. No general integrability is built into this definition. Define

L_a=M_μ(Y;P∩D_a∩{Y≤Q_{F_a}(1−r_a)}),
U_a=M_μ(Y;P∩D_a∩{Q_{F_a}(r_a)≤Y}),
H_F(t)=M_F(id;{Q_F(t)≤y}).

Comparisons to Q take place in the extended reals. Atomless means every real singleton has measure zero. Full real support for f means μ(l<f<u)>0 for every real l<u. All moments means integrability of |f|^n for every natural n, including zero. The essential endpoints e_a^−,e_a^+ are ess inf and ess sup of the extended-real identity under F_a. Mathlib defines these by the a.e. filter liminf/limsup in the complete lattice EReal, so they retain infinite endpoints.

ν is compatible with μ if it satisfies populationAssumptions, ν(A)>0, and the distributions of the triple (Y,S,Z) agree exactly. There is NO matching requirement on X or the joint potential vector, and NO integrability premise in this definition. B_a is the set of real m for which such a ν has M_ν(Y_a;A)=m (`compatibleMeans`). Its extended version is just the image of B_a in EReal, without adding infinities. `IsGLB(B,e)` means e is the greatest of the lower bounds of B; `IsLUB` has the dual meaning. These are sharp extrema, not necessarily members of B. Corrected endpoints are (L_a,U_a), cast to EReal, if r_a<1, and (e_a^−,e_a^+) otherwise.

For a probability F, `tailCoupling F p γ` means γ is a probability law on R×Bool, has first marginal F, and γ(second=false).toReal=p. This does not require the second coordinate to be a deterministic function of the first.

All finite mixtures below are sums of nonnegative-extended-real coefficients times measures. A real coefficient is embedded by `ofReal`, which clips negative numbers to zero. Write J for a fair independent arm in {0,1}. A stratum law T(s0,s1;F0,F1) samples independent F0,F1,J and records (Y0,Y1) from them, checks (s0,s1), assignment J, and no features (d=0). A common law C(s;F) samples y∼F,J independently and uses Y0=Y1=y and S0=S1=s.

The auxiliary continuous laws are: E has density exp(−x) for x>0 and zero otherwise; Lap(r) has density r exp(−r|x|)/2; B has density 30x²(1−x)² on 0<x<1 and zero elsewhere; T has density 5/[2(1+|x|)^6]. These are `withDensity` measures with respect to Lebesgue measure, using `ofReal` on the displayed density. N(m,v) is Mathlib `gaussianReal m v`, where v is the VARIANCE, and is Dirac at m if v=0. Its density for v>0 is φ_{m,v}(x)=exp(−(x−m)²/(2v))/sqrt(2πv).

## T1

The three fixed arms have sample sizes n=(544,538,533), failures f=(35,182,40), preference-one counts c=(61,162,327), and approval-one counts h=(192,188,324). Set N_a=n_a−f_a in natural numbers, q_a=f_a/n_a rationally, t_a=Σ_{b≠a}q_b/(1−q_a), k_a^−=max(ceil(N_a(1−t_a))−1,0), and k_a^+=N_a−max(floor(N_at_a),0), the latter subtraction also truncated at zero. For counts v define l_a(v)=max(k_a^−−max(N_a−v_a,0),0)/k_a^− and u_a(v)=min(k_a^+,v_a)/k_a^+ in Q. I_a(v) is the closed real interval [l_a(v),u_a(v)]. Counts are supplied constants, without a link to raw data.

T1 is the conjunction: I_0(c) and I_1(c) are disjoint; I_0(c) and I_2(c) are disjoint; it is false that for every a then every b there exists an x in both I_a(c) and I_b(c); and there does not exist an x belonging to I_a(c) for every a. There are no hypotheses.

## T2

There are no hypotheses. With the preceding definitions, all of the following hold:

* For every a, N_a=(509,356,493)_a, t_a=(32239072/72978893,10871635/51611456,31403827/72143648)_a, k_a^−=(284,281,278)_a, and k_a^+=(285,282,279)_a.
* For every a the preference bounds are ((0,61/285),(87/281,27/47),(56/139,1))_a and approval bounds are ((0,64/95),(113/281,2/3),(109/278,1))_a.
* For every a, every natural j, then hypotheses 1≤j and j≤N_a, both equivalences hold: j/N_a<1−t_a iff j≤k_a^−; j/N_a>t_a iff N_a−k_a^+<j.
* 1/2 belongs to every approval interval and to preference intervals 1 and 2. Preference interval 0's upper endpoint is below the lower endpoints of 1 and 2, with respective differences 7654/80085 and 7481/39615, each positive.
* z=1−Σ_a q_a=40739821/77997088>0. For each a let a_z=c_a/n_a, and define the fractional preference bounds as (max(0,(a_z−Σ_{b≠a}q_b)/z), min(1,a_z/z)). They equal ((0,8745997/40739821),(12614477/40739821,23486112/40739821),(16448045/40739821,1))_a. The lower endpoints of 1 and 2 minus the upper endpoint of 0 are respectively 3868480/40739821 and 7702048/40739821, each positive.

## T3

For EVERY Boolean upper define μ_upper as (1/4)T(true,true;E if upper, reflected E otherwise; Lap(1)) + (1/4)T(true,false;reflected E if upper, E otherwise;Lap(1)) + (1/2)T(false,true;Lap(2),Lap(1)). Reflection is pushforward by negation. For each of these two measures the following conjunction holds: populationAssumptions; μ(A)=1/4; the observed response distribution is atomless; full observed real support; all observed moments finite; p0=1/2, p1=3/4, r0=1/2; F0=Lap(1) with Q_F0(1/2)=0; M_μ(Y;{Y≤0}∩D0)=−3/4; M_μ(Y;{0≤Y}∩D0)=3/4; M_μ(Y0;A)=1 if upper and −1 otherwise; it is false that this last mean lies between the preceding two unselected-tail means; and L0=−1,U0=1. In addition the two μ_upper have identical (Y,S,Z) laws. There are no external premises.

## T4

For every K,d, measure μ on the stated population space, then hypotheses populationAssumptions μ, a:Fin K, μ(A)>0, atomlessness of F_a, integrability of Y on P∩D_a, and r_a<1, the following hold: L_a≤M_μ(Y_a;A)≤U_a; both L_a and U_a belong to B_a; every real m∈B_a lies between L_a and U_a; p_a(1−r_a)=1−Σ_b(1−p_b); r_a<1 iff 1−Σ_b(1−p_b)>0; if r_a=0 then both endpoints equal M_μ(Y;P∩D_a); and, writing z=1−Σ_b(1−p_b),

L_a=(p_a/z)∫_0^{z/p_a} Q_Fa(u).toReal du,
U_a=(p_a/z)∫_{1−z/p_a}^1 Q_Fa(u).toReal du.

These last integrals are oriented Mathlib real interval integrals against Lebesgue measure. The quantified compatible ν are not assumed atomless or integrable by definition, beyond what follows from matching observables and independence.

## T5

Define μ=(1/3)C(true;B)+(2/3)C(false;T). No hypotheses. It satisfies populationAssumptions, μ(A)=1/3, observed atomlessness and full real support, ∫Y=1/6, ∫Y²=13/63, ∫|Y|³=19/84, and integrability of |Y|³. For EVERY real R≥1, both μ(Y>R).toReal and μ(Y<−R).toReal equal 1/[3(1+R)^5]. For EVERY a:Fin 2, p_a=1/3,r_a=2, every m∈B_a satisfies 0<m<1, the extended set has GLB 0 and LUB 1, and it does not have GLB −∞ or LUB +∞.

For every real t, then hypotheses 0<t<1, B((0,t)).toReal=10t³−15t⁴+6t⁵. For every Boolean upper the following ν_{t,upper} is compatible with μ. Put E_t=(1−t,1) if upper and (0,t) otherwise, q=B(E_t).toReal, F=L_B(id;E_t), G=L_B(id;(0,1)\E_t), and

ν=(q/3)T(true,true;F,F)+((1−q)/3)T(true,false;G,T)+((1−q)/3)T(false,true;T,G)+((1+q)/3)T(false,false;T,T).

For every a:Fin 2, M_ν(t,false)(Y_a;A)=t(15/2−12t+5t²)/(10−15t+6t²), this is strictly between 0 and t, and M_ν(t,true)(Y_a;A)=1−M_ν(t,false)(Y_a;A).

## T6

For every K,d,μ, then populationAssumptions μ, a:Fin K, μ(A)>0, observed response atomlessness, integrability of Y on P∩D_a, and 1≤r_a: the equivalence 1≤r_a iff Σ_b p_b≤K−1 holds; e_a^−≤M_μ(Y_a;A)≤e_a^+ in EReal; for every real l equal to e_a^− the first inequality is strict; for every real u equal to e_a^+ the second is strict; e_a^− and e_a^+ are respectively GLB and LUB of extended B_a; every such finite l and u is absent from B_a; and [the extended set has GLB −∞ and LUB +∞] iff [F_a((−∞,M))>0 and F_a((M,+∞))>0 for EVERY real M]. No full-support or tail premise is assumed.

## T7

μ is the equally weighted four-state law, all with both checks true and d=0:

((Y0,Y1),Z)=((0,0),0), ((1,1),0), ((0,1),1), ((1,0),1).

With no hypotheses, μ satisfies populationAssumptions, μ(C)=μ(A)=1; the PAIR (entire Y vector, observed S) is not independent of Z; μ(Y0=Y1=0,S=true,Z=0)=1/4 whereas μ(Y0=Y1=0,S=true)μ(D0)=1/8; both selected arm response means are 1/2; and M_μ(Y0−Y1;A)=0.

## T8

For every K,d,μ, then populationAssumptions μ, μ(C)=1, a:Fin K and global integrability of Y_a: S=S_a μ-a.e.; (Y_a,S) is independent of Z; for every t, p_t=μ(P).toReal>0; P=A μ-a.e.; M_μ(Y;P∩D_a)=M_μ(Y_a;P∩D_a)=M_μ(Y_a;P)=M_μ(Y_a;A). Integrability is assumed only for the chosen a.

## T9

For parameters p0,p1,ρ,λ,σ let a=p0p1+ρsqrt(p0(1−p0)p1(1−p1)). Define the simulation μ as the mixture over checks (false,false),(true,false),(false,true),(true,true) with masses 1−p0−p1+a,p0−a,p1−a,a embedded by `ofReal`. Within a stratum, independently draw ε∼N(0,σ²), J fair, and set Y0=Y1=λ(1_{S1}−1_{S0})+ε, Z=J. Correlation means [μ(W0∩W1).toReal−μ(W0).toReal μ(W1).toReal]/sqrt(p0'(1−p0')p1'(1−p1')), using the actual marginal probabilities p0',p1'. Width W(μ)=(U1−L0)−(L1−U0). Define G_w=(1−w)N(0,1)+wN(−1,1), l(w)=M_Gw(id;{y≤Q_Gw(3/4)}), u(w)=H_Gw(1/4).

T9 has no external premises. For EVERY ρ in {1/4,1/2}, μ=simulation(4/5,4/5,ρ,1,1) satisfies populationAssumptions, μ(A)>0, observed atomlessness and full real support, check correlation ρ, both p's equal 4/5 and both r's equal 1/4. The all-pass masses at ρ=1/4,1/2 are 17/25,18/25; arm-0 passer laws are G_{3/20},G_{1/10}; arm-1 passer laws are their reflected laws. The G means are −3/20,−1/10 and variances (displayed as integrals centered at those means) 451/400,109/100. W at each design is 2(u(w)−l(w)) with its respective w. The widths lie respectively in [1798577298898/10^12,1798577299027/10^12] and [1767983385194/10^12,1767983385319/10^12], and the former minus the latter exceeds 30593913580/10^12.

## T10

For EVERY ordered tuple of real p0,p1,ρ,λ,σ, then premises 0<p0<1,0<p1<1,σ≥0, and, with a as in T9, a≥0,1−p0−p1+a≥0,a≤p0,a≤p1, the conjunction is:

1. For every natural K,d, every μ,ν on that same population space, then populationAssumptions μ and ν, then every a:Fin K, equality of the entire pass-rate functions and equality F_a(μ)=F_a(ν) imply equality of the corrected endpoint pairs. No atomlessness/integrability premise is in this clause.
2. Let w0=1−a/p0,w1=1−a/p1 and μ be the simulation. It satisfies populationAssumptions, μ(A).toReal=a, actual check correlation ρ, rates p0,p1, passer laws (1−w0)N(0,σ²)+w0N(−λ,σ²) and (1−w1)N(0,σ²)+w1N(λ,σ²), and selected response means −λw0,λw1.
3. If λ≠0, then for EVERY real ρ'≠ρ, BOTH −λ[1−(p0p1+ρ'sqrt(p0(1−p0)p1(1−p1)))/p0] and the analogous positive-λ formula divided by p1 differ from their values at ρ. No feasibility premise is imposed on ρ'; this is a numerical comparison of formulas, not an assertion that it gives a law.
4. The two particular widths in T9 are unequal.

## T11

No hypotheses. Define sigmoid(η)=exp(η)/(1+exp(η)). Then sigmoid(log(1/3))=1/4 and sigmoid(log(1/3)+log 9)=3/4. For EVERY real q0,q1, then premises 0<q0<1 and 0<q1<1, the expression log q0+3log(1−q0)+3log q1+log(1−q1) is at most its value at (1/4,3/4), with equality iff q0=1/4 and q1=3/4.

On cells x∈Fin 2 define fO=(3/4,1/4), fR=(1/4,3/4), e(x)=(fR(x)/2)/(fR(x)/2+fO(x)/2), odds(e)=e/(1−e), reverseOdds(e)=(1−e)/e, and normalized mass f(x)w(x)/Σ_u f(u)w(u). For EVERY cell, fO,fR>0 and 0<e<1. The e values are 1/4,3/4; odds values 1/3,3; weighted fR masses 1/12,9/4, with total 7/3. The normalized odds-weighted fR mass in cell 1 is 27/28≠fO(1); reverse-odds-weighted fR normalizes to fO on EVERY cell.

## T12

For EVERY type Ω with a measurable space (the type and measurable structure are theorem parameters), then EVERY measure ν, real π and real-valued functions fR,fO, then ordered premises 0<π<1, fR>0 ν-a.e., fO>0 ν-a.e., integrability of fR and fO under ν, and ∫fR=∫fO=1, define e=πfR/[πfR+(1−π)fO], odds=e/(1−e), rev=(1−e)/e and normalized density N(f,w)(x)=f(x)w(x)/∫f(u)w(u)dν. All of the following hold:

* ν-a.e., 0<e<1, odds=(π/(1−π))(fR/fO), and fO/fR=(π/(1−π))rev.
* ∫fR·rev=(1−π)/π; N(fR,rev)=fO ν-a.e.
* For EVERY real c>0, N(fR,c·rev)=fO ν-a.e.
* IF fR²/fO is integrable, its integral is positive, N(fR,odds)=(fR²/fO)/∫fR²/fO ν-a.e., and N(fR,odds)=fO ν-a.e. iff fR=fO ν-a.e.

The final branch makes no assertion when fR²/fO is nonintegrable. There is no finite base-measure or nonempty-space premise; unit integrals themselves exclude a zero base measure.

## T13

μ=(4/5)C(true;N(0,1))+(1/5)C(false;N(0,1)). No hypotheses. It satisfies populationAssumptions, μ(A)=4/5, observed atomlessness and full real support; for every arm p_a=4/5,F_a=N(0,1); v0=r0=1/4; M_μ(Y0;A)=M_μ(Y0;O0∩W0)=0. For q=Q_N(3/4).toReal, M_μ(Y0;{Y0≤q})=−φ(q)/(3/4)<0 and the inequality M_μ(Y0;A)≤that lower-tail mean is false. Finally U0=φ(Q_N(1/4).toReal)/(3/4)>0.

## T14

For every K,d,μ, then μ a probability measure, a:Fin K, μ(A)>0, atomlessness of F=L_μ(Y_a;W_a), and integrability of Y_a on W_a:

* For EVERY real p with 0≤p<1, for EVERY γ satisfying tailCoupling(F,p,γ), M_γ(first;{second=true})≤H_F(p). The deterministic γ given by pushing F through y↦(y,decide(Q_F(p)≤y)) is such a coupling and attains equality.
* For EVERY real p,q, then 0≤p≤q<1, H_F(p)≤H_F(q).
* μ(O_a^c∩W_a).toReal/μ(W_a).toReal≤v_a.
* If v_a<1, M_μ(Y_a;A)≤H_F(v_a).

No assignment-independence premise is made in this theorem.

## T15

For every K,d,μ, then populationAssumptions μ, a:Fin K, μ(A)>0, observed response atomlessness, and integrability of Y on P∩D_a: L_μ(Y_a;W_a)=F_a; for EVERY b, μ(W_b).toReal=p_b; v_a=r_a; H_{L_μ(Y_a;W_a)}(r_a)=U_a; and IF r_a<1 then M_μ(Y_a;A)=M_μ(Y_a;O_a∩W_a)≤U_a. The H=U identity is unconditional in r_a, using the literal totalized definitions even outside the finite branch.

## T16

For EVERY real q, then 0<q<1, define μ_q as the six-state law obtained by crossing each of three equally likely strata [(Y0,Y1)=(1,1),(S0,S1)=(false,true)], [(0,0),(true,false)], [(0,0),(true,true)] with Z=0 of probability q and Z=1 of probability 1−q, independently; every X=0 in R^1. This law satisfies populationAssumptions, covariateRandomAssignment and covariateBalance; μ_q(A)=1/3; every p_a=2/3; S and Z are independent; Y1−Y0=0 μ_q-a.e.; ∫(1_{S1}−1_{S0})=0; the Y1−Y0 means on A, on {S0=true,S1=false}, and on {S0=false,S1=true} are each zero; the selected response means in arms 0 and 1 are 0 and 1/2 respectively; their difference is 1/2; and 1/2≠0.

## T17

For every K,d,μ, then μ a probability measure and randomAssignment μ: for EVERY a, p_a=μ(W_a).toReal; and [every p_a>0] iff [for EVERY a, μ(W_a)>0]. No outcome-integrability premise is made or needed in the statement.

## T18

For every K,d,μ, then populationAssumptions μ, μ(C)=1, a,b:Fin K and global integrability of both Y_a and Y_b: M_μ(Y;P∩D_a)−M_μ(Y;P∩D_b)=M_μ(Y_a−Y_b;A). There is no requirement a≠b.

## T19

For every K,d,μ, then μ a probability measure, randomAssignment μ, a,b:Fin K, and global integrability of both Y_a and Y_b: M_μ(Y;D_a)=∫Y_a, M_μ(Y;D_b)=∫Y_b, and their difference equals ∫(Y_a−Y_b). No passing-rate or common-check assumption is made, and a may equal b.

## T20

For every K,d,μ, then μ a probability measure, randomAssignment μ and μ(C)=1: S and Z are independent. There is no passing-rate or outcome-integrability premise.

## T21

There EXISTS a measure μ on Population(2,1) such that populationAssumptions μ, S independent of Z, μ(A)>0, and

M_μ(Y;P∩D1)−M_μ(Y;P∩D0) ≠ M_μ(Y1−Y0;A).

There is NO integrability requirement for the selected outcomes or the effect. Thus all three M expressions are the totalized restricted Bochner-integral ratios; the proposition does not itself assert that any of these are ordinary finite conditional means.

## T22

For every K,d,μ, then μ a probability measure, covariateRandomAssignment μ and μ(C)=1: covariateBalance μ holds, i.e. for each b with μ(S=b)>0, X and Z are independent under the normalized restriction to {S=b}. No passing-rate, moment, or feature-distribution regularity hypothesis is present.

## T23

There EXISTS a measure μ on Population(2,1) which is a probability measure, has EVERY observed p_a>0, satisfies covariateRandomAssignment and covariateBalance, has μ(A∩{X=0})>0, and

M_μ(Y;(P∩D1)∩{X=0})−M_μ(Y;(P∩D0)∩{X=0}) ≠ M_μ(Y1−Y0;A∩{X=0}).

Here X=0 is equality of the entire one-dimensional function-valued feature coordinate to the zero function. There is no atomlessness or integrability premise; all three means are the literal totalized M.

## Mathlib source checkpoints

The expanded meanings were checked against `Probability/Independence/Basic.lean` (and its kernel definitions), `MeasureTheory/Measure/{Map,Restrict}.lean`, `MeasureTheory/Measure/Typeclasses/Probability.lean`, `MeasureTheory/Function/L1Space/{Integrable,HasFiniteIntegral}.lean`, `MeasureTheory/Integral/Bochner/Basic.lean`, `MeasureTheory/Function/EssSup.lean`, `Order/Bounds/Defs.lean`, `Data/EReal/Basic.lean`, and `Probability/Distributions/Gaussian/Real.lean`, all under the supplied Mathlib source root. In particular, ess extrema live in EReal; Bochner integrals are zero when nonintegrable; Gaussian's second argument is variance and variance zero is a Dirac law; and EReal.toReal sends infinities to zero. Arithmetic in R and Q uses zero inverse at zero, while the explicitly identified natural-number subtractions are truncated.
