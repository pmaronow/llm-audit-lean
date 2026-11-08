# Blind mathematical reading

This file was written using only the Defs and Challenge files and the Mathlib definitions they use, before opening claims.json or record.json. Names T1, ..., T15 below refer to SAP.P002a.T1, ..., SAP.P002a.T15. There is no T7 stub. The Challenge stubs merely assert the propositions expanded below; none has an additional hypothesis outside its proposition, except that T9 and T15 also quantify over a type Ω and a measurable-space structure on Ω.

## Objects and conventions used throughout

A population P of size n consists of real potential outcomes y_i(0), y_i(1), binary receipts d_i(0), d_i(1), and an integer n1. Indices are i = 0,...,n-1 (Lean Fin n), and arms/receipts are Booleans. A covariate population additionally has vectors x_i in R^k. Nothing in these structures itself asserts positivity, monotonicity, centering, or a valid design.

Write n0 = n-n1 as a REAL subtraction, π=n1/n, and C={i:d_i(0)=0 and d_i(1)=1}. The predicate ValidDesign means n≥2 and 0<n1<n. MonotoneReceipt means, for every i, d_i(0)=1 implies d_i(1)=1. The parameter β_P=late(P) is |C|^{-1} sum over C of (y_i(1)-y_i(0)). Thus the outcome supplied under assignment a is y_i(d_i(a)); there is no separately assignment-dependent outcome.

For a real vector q, write bar(q)=n^{-1}Σ_i q_i, bar(q)_H=|H|^{-1}Σ_{i∈H}q_i, V(q)=(n-1)^{-1}Σ_i(q_i-bar(q))², and Cov(q,t)=(n-1)^{-1}Σ_i(q_i-bar(q))(t_i-bar(t)). Group covariance Cov_H and variance V_H use denominator |H|-1 if |H|≥2, and are DEFINED TO BE ZERO for |H|<2. All other real divisions are Lean's totalized real division, so a/0=0; an empty group mean and the mean on Fin 0 are zero. The fourth norm is F4(q)=sqrt(sqrt(n^{-1}Σ_i q_i^4)). Real.sqrt returns the nonnegative root on nonnegative inputs and zero on negative inputs.

Define w_ai(β)=y_i(d_i(a))-β d_i(a), where a Boolean receipt is interpreted as 0 or 1; v_ai(β)=w_ai(β)-bar(w_a(β)). Let A_P be the finite set of all n1-element subsets of {0,...,n-1}. E_P f is the arithmetic mean of f over A_P, Pr_P(E)=#{S∈A_P:E(S)}/#A_P, and Var_P f=E_P[(f-E_P f)²]. These are finite sums, not integrals; for an invalid design with A_P empty their totalized values are zero. ValidDesign makes A_P nonempty and both arms nonempty. Complement H^c is relative to the full Fin n population.

For an assignment S, observed receipts are d_i(1_{i∈S}), observed outcomes are y_i(d_i(1_{i∈S})), and q^S_i(β)=observedW(P,β,S)_i=observed outcome minus β times observed receipt. For a FIXED q and reassignment T, define

* t_P(q,T)=n^{-1}Σ_i q_i(1_{i∈T}-π). On a valid assignment this is π(1-π)(bar(q)_T-bar(q)_{T^c}).
* τ_P(β,S)=t_P(q^S(β),S); here q varies with S.
* s²_P(q,T)=π²(1-π)²[Σ_{i∈T}(q_i-bar(q)_T)²/n1² + Σ_{i∈T^c}(q_i-bar(q)_{T^c})²/n0²].
* Student(t,s²) is an extended nonnegative real: 0 if s²=t=0; infinity if s²=0 and t≠0; otherwise ENNReal.ofReal(|t|/sqrt(s²)). ENNReal.ofReal truncates a negative real to zero and never maps a finite real to infinity. All s² occurring here are nonnegative for valid designs.
* AR_P(q,T)=Student(t_P(q,T),s²_P(q,T)). For g:A_P→[0,infinity], Q_P(g,α) is the smallest value in the finite image g(A_P) having Pr_P(g≤value)≥1-α; it is infinity if that filtered image is empty. For a valid design and 0<α<1 it is nonempty.
* Acceptance at β on S means AR_P(q^S(β),S)≤Q_P(T↦AR_P(q^S(β),T),α). The same observed q is FROZEN for reassignments T. Coverage c_P(β,α) is the probability of acceptance over original assignments S. Ties are accepted, and an infinity quantile accepts an infinity statistic.
* S_a²(P,β)=π²(1-π)² V(w_a(β)). The unused Sdiff2 definition is π²(1-π)²/(n-1) times Σ_i(v_1i-v_0i)².

Theta(P;δ,r,A) is the conjunction of: ValidDesign; MonotoneReceipt; C nonempty; rn≤n1≤(1-r)n; Cov_C(w_1(β_P),w_0(β_P))≥-δ sqrt(V_C(w_1(β_P)))sqrt(V_C(w_0(β_P))); and, for EACH a∈{0,1}, F4(v_a(β_P))≤A sqrt(V(w_a(β_P))). The predicate itself does not require δ<1, r>0, A>0, or any strictly positive outcome variance. Those are separate hypotheses when present.

## Regression definitions

Augmented vectors are z_i=(1,x_i), indexed by Option(Fin k): none is the intercept and some(j) is covariate j. xCirc=(0,x_i). The notation |b|² below means normSq(b)=Σ_j b_j², and dot products and matrix-vector multiplication are their ordinary finite sums. For H, G_H=|H|^{-1}Σ_{i∈H}z_i z_i' and score_H(q)=|H|^{-1}Σ_{i∈H}z_i q_i. RSS_H(q,b)=Σ_{i∈H}(q_i-z_i'b)². OLS_H(q) is G_H^{-1}score_H(q) when det G_H≠0. Otherwise it is an arbitrarily chosen global RSS minimizer if a minimizer exists, and zero if none exists. No canonical singular-fit coefficient is specified. Finite real least squares does have a minimizer, so the last branch is not normally reached. Mathlib's matrix inverse is determinant-inverse times adjugate; the OLS definition explicitly checks nonsingularity before using it.

Let ψ_a(β)=OLS_all(w_a(β)) and u_ai(β)=w_ai(β)-z_i'ψ_a(β). For b indexed by the augmented coordinates, slopeDot(x_i,b)=Σ_{j<k}x_ij b_j, excluding the intercept. Define

* D(q,S;b1,b0)=bar(q-x'b1)_S-bar(q-x'b0)_{S^c}.
* Feasible adjusted t, t_adj(q,S)=D(q,S;OLS_S(q),OLS_{S^c}(q)).
* Oracle t, t_or(P,β,S)=D(q^S(β),S;ψ_1(β),ψ_0(β)).
* oracleStar(P,q,S)=D(q,S;OLS_all(q),OLS_all(q)).
* s²_adj(q,S)=RSS_S(q,OLS_S(q))/n1²+RSS_{S^c}(q,OLS_{S^c}(q))/n0².

Adjusted AR, acceptance, and coverage c_adj are defined by replacing t and s² with t_adj and s²_adj in the earlier definitions. There is NO π(1-π) scaling in the adjusted t or s² definitions.

Xi(P;δ,e,A,B,r) is the conjunction of: ValidDesign and MonotoneReceipt of P.pop; C nonempty; rn≤n1≤(1-r)n; Cov(u_1(β_P),u_0(β_P))≥-δ sqrt(V(u_1(β_P)))sqrt(V(u_0(β_P))); F4(u_a(β_P))≤B sqrt(V(u_a(β_P))) for EACH arm a; Σ_i x_ij=0 for EACH covariate j; n^{-1}Σ_i x_ij^4≤A for EACH j; and, for EVERY b∈R^k, e|b|²≤n^{-1}Σ_i(x_i'b)². It has no explicit positivity requirements on δ,e,A,B,r, k, or the residual variances.

Let I_Theta(n;δ,r,A,α) be the infimum, in the COMPLETE lattice [0,infinity], first over β∈R and then over populations P with Theta(P;δ,r,A) AND β_P=β, of ENNReal.ofReal(c_P(β,α)). Define I_Xi similarly for covariate populations and adjusted coverage. The equality β_P=β only selects the true parameter. If the population class at a size is empty, its infimum is infinity, not a probability. thetaSizes and xiSizes are exactly the sets of sizes with a nonempty respective class.

All Tendsto statements below are ordinary limits along integer indices tending to infinity, with the order topology when the range is [0,infinity]. liminf is Mathlib Filter.liminf, the supremum of eventual lower bounds. A filter atTop ∧ principal(H) means taking arbitrarily large sizes within H. NeBot for this filter means H is unbounded in N. Consequently the restricted-size liminfs below do not get their content from empty classes. A real Big-O statement f=O(g) means there exists a real constant C such that eventually |f_j|≤C|g_j|. StrictMono on N means strictly increasing, and so such sizes tend to infinity.

RandomizationSequence(P,μ,Z) means: for EVERY index j and EVERY predicate E on finite subsets of the population at j, {ω:E(Z_j(ω))} is measurable and μ{ω:E(Z_j(ω))}=ENNReal.ofReal(Pr_{P_j}(E)). It imposes precisely complete-randomization marginals, not independence. IndependentAssignments means that for EVERY finite index set I and EVERY family of assignment predicates E_j, the probability of their intersection over I is the product of their marginal probabilities. T9 spells this hypothesis out rather than naming the definition. Almost everywhere means that the exceptional set has μ-measure zero.

## Explicit families

* N_m=negativeDeltaModel(m): n=12m, n1=2m, all units comply, y_i(0)=y_i(1)=-1 for even i and +1 for odd i; one covariate is -1 when i mod 4<2 and +1 otherwise.
* C4=centringModel: n=4,n1=2, all comply, y_i(a)=b_i+2a, where b=(-1,-1,1,1).
* H_m=signModel(m): n=2m,n1=m, all comply, y_i(0)=y_i(1)=-1 for i<m and +1 for i≥m.
* interceptExampleX has n=2,k=1, x_0=2,x_1=-2.
* D_n(β)=degenerateModel(n,β): n1=floor(n/2), all comply, y_i(0)=0,y_i(1)=β. Its covariate version has k=1 and x_i=(2(i+1)-n-1)/n.
* R_m=nearSingularModel(m): n=2m,n1=m,k=1, all comply; t_i=[2(i mod m)-m+1]/(m-1), v_m=(m+1)/(3(m-1)), η=2^{-(2m)^2}, y_i(a)=t_i+(t_i²-v_m)/10, and x_i=(1 if i<m, else -1)+ηt_i. Subtractions in t_i and v_m are real subtractions; remainders and exponents are natural-number operations.
* O_n=oddNearModel(n): n1=floor(n/2),k=1, all comply; x_i=2i/(n-1)-1 and y_i(a)=(x_i²-bar(x²))/10.

## T1

This is a conjunction with no external hypothesis.

1. For P=N_1: Theta(P.pop;-1/2,1/6,2), Xi(P;-1/2,1/2,2,2,1/6), β_P=0, #A_P=66, S_1²(P,0)=S_0²(P,0)=25/1188, Var_P(τ_P(0,·))=5/396, and Var_P(t_or(P,0,·))=36/55. Moreover each actual variance is STRICTLY LESS than its expression (1-δ)[n0/(n n1) times the arm-1 variance plus n1/(n n0) times the arm-0 variance], at δ=-1/2, with S_a² for the raw statistic and V(u_a) for the oracle statistic.
2. For EVERY integer m≥1, P=N_m satisfies those same Theta and Xi conditions and β_P=0. Its raw design variance is 5/[36(12m-1)], and oracle design variance is 36/(60m-5). For EACH statistic, the lower-bound expression just described equals (13/12) times its actual variance.
3. The real arithmetic equalities 12/11+12/11+2(-1/2)(12/11)=12/11 and 12/11+12/11+(-1/2)(10/2)(12/11)+(-1/2)(2/10)(12/11)=-36/55 hold, and 12/11≤-36/55 is false.
4. For EVERY arm a, ψ_a(N_1,0)=the zero augmented coefficient vector. This last coefficient assertion is only for m=1.

## T2

Conjunction of two universal implications. First quantify n, P, δ,r,A, then assume δ<1, 0<r≤1/2, A>0, and Theta(P;δ,r,A). Then

    (1-max(δ,0)) [n0/(n n1) S_1²(P,β_P) + n1/(n n0) S_0²(P,β_P)] ≤ Var_P(τ_P(β_P,·)).

Separately quantify n,k,P,δ,e,A,B,r, then assume k>0, δ<1, e>0, A>0, B>0, 0<r≤1/2, and Xi(P;δ,e,A,B,r). Then

    (1-max(δ,0)) [n0/(n n1) V(u_1(β_P)) + n1/(n n0) V(u_0(β_P))] ≤ Var_P(t_or(P,β_P,·)).

## T3

Both following universal propositions are false: the first implication of T2 with multiplier 1-δ in place of 1-max(δ,0), and the second implication of T2 with the same replacement. The quantified populations, parameter signs, positive covariate dimension, and all Theta/Xi conditions are exactly those in T2. This asserts the existence of a counterexample to EACH universal bound, not that every admissible population violates it, and not that either printed bound fails for δ≥0.

## T4

Conjunction of four assertions.

1. For EVERY n,q with n≥2 and F4(q)≤(1/2)sqrt[Σ_i q_i²/(n-1)], EVERY q_i is zero. No centering hypothesis is imposed on q.
2. For EVERY n,P with Theta(P;0,1/4,1/2), there EXISTS one c∈R such that for EVERY arm a and EVERY unit i, w_ai(β_P)=c. The same c works for both arms.
3. For EVERY α∈(0,1): for EVERY n≥2 and EVERY β∈R, D_n(β) satisfies Theta(·;0,1/4,1/2) and has late β; for EVERY n≥2 and EVERY P in that Theta class, c_P(β_P,α)=1; I_Theta(n;0,1/4,1/2,α)=1 for EVERY n≥2; these infima tend to 1; and they do NOT tend to ENNReal.ofReal(1-α).
4. Separately for EVERY α∈(0,1): for EVERY n≥2 and EVERY β, the covariate D_n(β) satisfies Xi(·;0,1/4,4,1/2,1/4) and has late β; for EVERY n≥2 and EVERY k=1 population P in this Xi class, c_adj(P,β_P,α)≥max(0,1-1548/(n-1)); I_Xi(n,1;0,1/4,4,1/2,1/4,α) tends to 1 and does NOT tend to ENNReal.ofReal(1-α). It does not assert adjusted coverage equals one at each finite size.

## T5

Three conjuncts.

1. For EVERY δ,r,A,α, assume δ<1, 0<r≤1/2, A>0, 0<α<1, and that the set of sizes admitting Theta(P;δ,r,A) is unbounded. Then the liminf of I_Theta(n;δ,r,A,α) along those nonempty sizes is at least ENNReal.ofReal(1-α).
2. For EVERY k,δ,e,A,B,r,α, assume k>0, δ<1, e,A,B>0, 0<r≤1/2, 0<α<1, and that the sizes admitting this Xi class are unbounded. The analogous liminf of I_Xi along those sizes is at least ENNReal.ofReal(1-α).
3. For EVERY size sequence sizes, assume it is strictly increasing; then quantify a population sequence P_j of those sizes and δ,r,A,α. Assume δ<1, 0<r≤1/2, A>0, α∈(0,1), and Theta(P_j;δ,r,A) for EVERY j. Additionally assume for EVERY j there EXISTS β_j such that for EVERY unit i, y_ji(1)=y_ji(0)+β_j; and for EVERY j, V(y_j(0))>0. Then c_{P_j}(β_{P_j},α), embedded in [0,infinity], tends to ENNReal.ofReal(1-α), AND the liminf of I_Theta over ALL nonempty sizes of this parameter class equals ENNReal.ofReal(1-α). The null set/probability-space notions play no role in this conjunct. There is no adjusted sharpness conclusion and no necessity implication for the constant-effect sequence condition.

## T6

No external hypotheses. For EVERY integer m≥4, P=R_m satisfies Xi(P;0,1/4,16,5,1/3), has β_P=0, and for EVERY S∈A_P both G_S and G_{S^c} have nonzero determinant. For EVERY such original S, freeze q=q^S(0). Then

    Var_P(T↦t_adj(q,T)) ≥ 8·2^{2(2m)^2}/2^{2m};
    for EVERY T∈A_P, 0≤s²_adj(q,T)<5/(2m);
    Pr_P(T: |s²_adj(q,T)/Var_P(t_adj(q,·))-1|≥1/2)=1.

Separately, for EVERY odd n≥9, Xi(O_n;0,1/4,16,5,1/3) holds. Finally, along P=R_{j+4} and frozen q_i=y_i(0), the same displayed error probability tends to 1 as j→infinity. No assertion transfers the exploding variance to the odd family.

## T8

For the specific two-unit covariate x=(2,-2): EACH covariate column sums to zero and has fourth mean 16; for EVERY scalar b, 2|b|²≤mean[(x_i'b)²]. For the SPECIFIC augmented vector v=(1,0), mean[(z_i'v)²]=1, |v|²=1, and mean[(z_i'v)²]<2|v|². No population outcome or random assignment is quantified here.

## T9

For EVERY measurable space Ω, this is a conjunction of three assertions.

1. For EVERY n,k,x, assume n>0; then quantify ANY real e, assume each x column sums to zero and e|b|²≤mean[(x_i'b)²] for EVERY b∈R^k. The population augmented Gram matrix has intercept entry 1, intercept/covariate cross entries zero, and covariate entries mean(x_s x_t). Moreover for EVERY augmented b, min(1,e)|b|²≤mean[(z_i'b)²]. There is no e>0 or k>0 hypothesis in this conjunct.
2. For EVERY n,k,x with n>0,k>0 and centered columns, the infimum over all unit augmented b of mean[(z_i'b)²] equals min(1, infimum over all unit b∈R^k of mean[(x_i'b)²]). These are real sInf's (leastRayleigh on the right). With k>0 both unit spheres are nonempty; their values are bounded below by zero.
3. Quantifier order: probability measure μ on Ω; size sequence sizes and strict increase; fixed k; covariate population sequence P_j; assignment maps Z_j; δ,e,A,B,r; assumptions k>0, δ<1, e,A,B>0, 0<r≤1/2; Xi(P_j;δ,e,A,B,r) for EVERY j; RandomizationSequence of their underlying populations; independence of the assignment coordinates in the finite-event/product sense defined above; then a subsequence map sub:N→N and its strict increase. For μ-almost EVERY ω there EXISTS a real sequence err_j, tending to zero, such that for ALL sufficiently large j and BOTH arms a: put N=sub(j), S=Z_N(ω), q=q^S(β_{P_N}), and b=OLS_{S if a=1 else S^c}(q)-OLS_all(q), all using P_N's covariates. Then

    (min(1,e)+err_j)|b|² ≤ b'G_{S if a=1 else S^c}b.

The exceptional set and err may depend on the fixed subsequence; the same err works for both arms. This is an inequality only for the ACTUAL coefficient-error vectors, not an assertion for every possible b at each realized arm. The independence assumption is additional to complete-randomization marginals.

## T10

No external hypotheses. Fix P=C4 and S={0,1}. Theta(P;0,1/2,1), β_P=2, and S∈A_P. On S the observed arm-1 centered second moment is 0. Put

    B_-(T)=bar(w_1(2))_T - mean(y_i(d_i(1))) - 2 mean(d_i(1)),
    B_+(T)=bar(w_1(2))_T - mean(y_i(d_i(1))) + 2 mean(d_i(1)).

Then bar(v_1(2)²)_S-B_-(S)²=-24, E_P[B_-(T)²]=49/3, and [n0/(2·4·(4-1))]Σ_i v_1i(2)²=1/3. Also S_1²(P,2)>0 and S_1²(P,2)=1/12; mean(y_i(d_i(1)))=2; mean(d_i(1))=1; bar(w_1(2))_S=-1; bar(v_1(2)²)_S=1; B_-(S)=-5; B_+(S)=-1; bar(v_1(2)²)_S-B_+(S)²=0; and E_P[B_+(T)²]=1/3. Thus the statement gives concrete unequal sides of two proposed equalities; it does not take those equalities as assumptions.

## T11

Three universal implications. Define for arbitrary P,β the corrected center

    B_P,β(T)=bar(w_1(β))_T-mean(y_i(d_i(1)))+β mean(d_i(1)).

1. For EVERY n,P with ValidDesign, EVERY β, EVERY S∈A_P: the observed treatment-arm centered second moment equals bar(v_1(β)²)_S-B_P,β(S)², AND

    E_P[B_P,β(T)²]=n0/[n1·n·(n-1)] Σ_i v_1i(β)².

Neither monotonicity nor β=β_P nor Theta is required for these finite identities.
2. For EVERY n,P with ValidDesign, EVERY β with S_1²(P,β)>0:

    E_P[B_P,β(T)²/S_1²(P,β)]
      = n0/[n1·n·(n-1)] (Σ_i v_1i(β)²)/S_1²(P,β).

3. For EVERY strictly increasing size sequence sizes, population sequence P_j of those sizes, and δ,r,A with δ<1, 0<r≤1/2, A>0, assume Theta(P_j;δ,r,A) AND S_1²(P_j,β_{P_j})>0 for EVERY j. Put f_j=E_{P_j}[B_{P_j,β_{P_j}}(T)²/S_1²(P_j,β_{P_j})]. Then f_j=O(n0_j/(n1_j sizes_j)) and f_j→0.

## T12

No external hypotheses. Fix P=H_4, so n=8,n1=4, and S={0,1,2,3}. Theta(P;0,1/2,1), β_P=0, S∈A_P, and #A_P=70. Freeze q=q^S(0), which is the same balanced sign vector for every original assignment. Var_P(t_P(q,·))=1/28 and Δ=bar(q)_S-bar(q)_{S^c}=-2. The quantity π²(1-π)²/(8-1)·(n0 n1/8)·Δ²=1/14 is strictly greater than this variance. The quantity without factor n0 n1/8 equals 1/28.

## T13

For EVERY n,P with ValidDesign, EVERY fixed real vector q, EVERY S∈A_P, and EVERY r with 0<r≤1/2 and rn≤n1≤(1-r)n, let Δ=bar(q)_S-bar(q)_{S^c}. BOTH inequalities hold:

    π²(1-π)²/(n-1) Δ² ≤ Var_P(t_P(q,·)),
    r²(1-r)²/n Δ² ≤ Var_P(t_P(q,·)).

There is no outcome/receipt/monotonicity/moment hypothesis on q and no requirement that q be an observed adjusted outcome.

## T14

No external hypotheses. For EVERY integer m≥2, P=H_m satisfies Theta(P;0,1/2,1) and β_P=0. For EVERY S∈A_P freeze q=q^S(0). Its reassignment variance is 1/[4(2m-1)]. The probability

    Pr_P(T: |sqrt(s²_P(q,T))/Var_P(t_P(q,·))-1|≥1/2)

is EXACTLY 1, whereas for EVERY real κ>0 the corrected probability with s²_P(q,T) instead of its square root is at most 2/[(2m)κ]. Along m=j+2 and q_i=y_i(0), the first probability tends to 1. No separate zero limit of the corrected probabilities is a conjunct (it follows from the bound).

## T15

For EVERY measurable space Ω, quantifier order is: probability measure μ; size sequence sizes and strict increase; population sequence P_j; assignment maps Z_j; parameters δ,r,A; assumptions δ<1, 0<r≤1/2, A>0; Theta(P_j;δ,r,A) for EVERY j; strictly positive V(w_a(β_{P_j})) for EVERY j and BOTH arms; RandomizationSequence(P,μ,Z); subsequence sub and strict increase; finally the assumption that for EVERY j and EVERY ω (not merely almost every ω), with q=q^{Z_j(ω)}(β_{P_j}), Var_{P_j}(T↦t_{P_j}(q,T))>0.

Conclusion: for μ-almost EVERY ω, for EVERY real κ>0, as j→infinity, with N=sub(j) and q=q^{Z_N(ω)}(β_{P_N}),

    Pr_{P_N}(T: |s²_{P_N}(q,T)/Var_{P_N}(t_{P_N}(q,·))-1|≥κ) → 0.

The almost-everywhere quantifier is outside ALL positive tolerances, giving one full-measure set for them for each fixed subsequence. No independence across the original assignments is assumed. The reassignment probability is a finite probability for a fixed realized q, and its denominator is the reassignment variance of that q, not the original-assignment variance of τ.
