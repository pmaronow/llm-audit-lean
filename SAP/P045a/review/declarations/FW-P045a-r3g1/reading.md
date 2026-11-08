# Blind reading of P045a T1–T5

Saved before opening `claims.json` or `record.json`. This reading uses the Challenge docstrings, source definitions, and `closure.json` only. All 67 distinct generated auxiliary declarations in the closures were printed by `scratch/ClosurePrint.lean` and read in `scratch/ClosurePrint.out`: they are proofs of `Nat.AtLeastTwo` or `NeZero` for concrete numerals, used to elaborate rational literals and finite indices, with no statistical hypotheses or conclusions.

## Common notation, fully unfolded

All probabilities below are finite sums of real numbers, not integrations over an implicit measure. For a finite type Ω and functions q,X:Ω→ℝ,

- E_q X = Σω q(ω)X(ω) (`expect`).
- P_q(A) = Σω q(ω)1_A(ω) (`prob`).
- E_q[X|A] = (Σω∈A q(ω)X(ω))/P_q(A) (`condMean`).
- Var_q X = Σω q(ω)(X(ω)−E_q X)² (`variance`).
- av_S x = (Σi∈S x(i))/|S| (`average`); av_I means the entire finite index type (`mean`). Cardinalities are cast from ℕ to ℝ.
- s²_S(x) = (Σi∈S(x(i)−av_S x)²)/(|S|−1), with subtraction in ℝ (`rawSampleVar`); S²(x)=s²_I(x) (`popVar`). Thus population variance uses the finite-population denominator N−1.

A size-n assignment is a Boolean-valued function on {0,…,n−1} (`Assignment`). Write z_i∈{0,1} for its real indicator (`bit`), K(z)=Σi z_i for its natural-number treated count (`treatedCount`), and T(z)={i:z_i=1} (`treatedSet`). `fixedAssignments n k` is the finite set F(n,k)={z:K(z)=k}. B_p(z)=∏i p^{z_i}(1−p)^{1−z_i}, interpreted literally as ∏i(if z_i then p else 1−p), is `bernoulli`. R(n,k)(z)=1/|F(n,k)| on F(n,k), zero elsewhere, is `crMass`.

For local potential outcomes y_i(z) (arbitrary real functions of all assignments in that group), define:

- μ_i(b;q)=E_q[y_i(z)|z_i=b] (`marginal`).
- A_b(y,z)=(Σi:z_i=b y_i(z))/(Σi1_{z_i=b}) (`armMean`).
- D_b(z) is ∃i,z_i=b (`armExists`).
- O(y,z)=n⁻¹Σi y_i(z) (`groupOverall`).
- H_b(p,y,z)=(Σi:z_i=b y_i(z))/(n·(p if b=1 else 1−p)) (`groupHT`).
- c_i(z)=Σj≠i z_j (`coMembers`).

For G groups, sizes n_g, `GroupAssignments n` is the dependent product ∏g({0,1}^{n_g}). Let ℋ(G,C)={H⊆{0,…,G−1}:|H|=C} (`firstStageSets`). A `Design Ω` is a real function q on a finite Ω together with proofs q≥0 and Σq=1; its constructor and mass projection introduce no further constraints. The product law L(C,q)(H,z)=|ℋ(G,C)|⁻¹∏g q_g(z_g) for H∈ℋ, zero otherwise (`selectedLaw`), samples H uniformly independently of all coordinates z_g, which are independent under this product. M_C(X)(H,z)=C⁻¹Σg∈H X_g(z_g) (`selectedMean`).

For the more general joint law, Q assigns a finite probability design on all z to every H⊆{0,…,G−1}. J(C,Q)(H,z)=Q_H(z)/|ℋ(G,C)| on H∈ℋ, zero otherwise (`w1JointMass`). Put H_1=H, H_0=Hᶜ (`w1RegimeSet`), C_1=C, C_0=G−C, where this last subtraction is natural (`w1RegimeCount`), and M_{C,h}(X)=C_h⁻¹Σg∈H_h X_g(z_g) (`w1RegimeMean`). The condition CL(C,h,Q,q) says, in this order, ∀H∈ℋ ∀g∈H_h ∀v∈{0,1}^{n_g}, Σz Q_H(z)1_{z_g=v}=q_g(v) (`w1CoordinateLaw`). It specifies conditional coordinate marginals, not independence. The target U_b(q,y)=G⁻¹Σg n_g⁻¹Σi μ_{gi}(b;q_g) is `w1ArmTarget`.

`w1UnbiasedContrasts(law,X,μ)` is the conjunction of (i) ∀h,b E_law X_{h,b}=μ_{h,b}; (ii) ∀h E_law(X_{h,1}−X_{h,0})=μ_{h,1}−μ_{h,0}; (iii) E_law(X_{1,0}−X_{0,0})=μ_{1,0}−μ_{0,0}; and (iv) E_law(X_{1,1}−X_{0,0})=μ_{1,1}−μ_{0,0}. It is a proposition defining the asserted equalities, not a hypothesis silently imposed on a law.

For arrays a_i,b_i, d(a,b,z)=av_{T(z)}a−av_{T(z)ᶜ}b (`directGroup`). Put

w(a,b,z)=1_{|T|≥2}s²_T(a)/|T|+1_{|Tᶜ|≥2}s²_{Tᶜ}(b)/|Tᶜ| (`droppedWithin`),

where each absent term is explicitly set to zero by an if-then-else. Then

Vhat(C,a,b)(H,z)=((1−C/G)/C)s²_H(g↦d(a_g,b_g,z_g))+(CG)⁻¹Σg∈H w(a_g,b_g,z_g)

is `directVarianceEstimate`. `requiredDirectVariance` returns `some Vhat` exactly when C≥2, |H|=C, and both arm sizes in every selected group are ≥2; otherwise it returns `none`.

An adjacency matrix is a Boolean function A(i,j). `Network n` additionally requires symmetry A(i,j)=A(j,i) and zero diagonal A(i,i)=false. Its constructor/projection in the closure do not remove these requirements. N_A[i]={i}∪{j:A(i,j)=true} is the finite closed neighborhood (`neighborhood`); t_A(z,i)=|{j∈N_A[i]:z_j=true}| (`neighborhoodCount`). E_1 means t_A=|N_A[i]| (`allTreated`), E_0 means t_A=0 (`allControl`), and E_bad means t_A<|N_A[i]| (`badAllControl`). For outcomes Y_i(z), the extreme contrast estimator is

F_correct(q,A,Y,z)=n⁻¹Σi[1_{E_1}Y_i(z)/P_q(E_1)−1_{E_0}Y_i(z)/P_q(E_0)],

and F_bad replaces both occurrences of E_0 by E_bad (`fullHT`, Boolean flag true/false). τ(Y)=n⁻¹Σi[Y_i(1,…,1)−Y_i(0,…,0)] (`allVsNone`).

## SAP.P045a.T1

The declaration has no external parameters or hypotheses. It asserts the conjunction `T1WholeStatement`, which contains `T1Statement`, `w1WitnessTargets`, and further explicit identities. The docstring says that this is a two-group four-unit counterexample to Bernoulli arm-ratio unbiasedness, with all conditioning domains explicit and an unbiased overall contrast.

The fixed sample space is Ω={false,true}×{0,1}⁴×{0,1}⁴ (512 points). The Boolean chooses which physical group is high: z_H=z_1 if the Boolean is true and z_2 otherwise; z_L is the other coordinate (`witnessHigh/Low`). Its mass is q(w)=½B_{1/2}(z_H)B_{1/4}(z_L) (`bernoulliWitnessMass`). Thus the choice of high group is fair; conditional on it the local group assignments are independent Bernoulli draws. Outcomes are c_i(z) in both groups. `witnessArm(b,h)` is A_b(c,z_h), `witnessDomain(b,h)` is D_b(z_h), `witnessDirect(h)` is A_1(c,z_h)−A_0(c,z_h), `witnessIndirect` is A_0(c,z_H)−A_0(c,z_L), `witnessTotal` is A_1(c,z_H)−A_0(c,z_L), and `witnessOverall` is O(c,z_H)−O(c,z_L).

The complete conjunction says:

1. |Ω|=512, Σq=1 and ∀w q(w)≥0.
2. ∀real p, 0<p→p<1→∀i∈Fin 4 ∀b∈Bool, μ_i(b;B_p)=3p. Also ∀z∈{0,1}⁴ ∀i, c_i(z)=K(z)−z_i.
3. ∀w ∀h, D_1(z_h)→D_0(z_h)→`witnessDirect(h,w)`=−1.
4. P_q(D_1(z_H)∩D_0(z_H))=7/8, P_q(D_1(z_L)∩D_0(z_L))=87/128. P_q(D_0(z_H)∩D_0(z_L)) and P_q(D_1(z_H)∩D_0(z_L)) both equal 3825/4096. The conditional indirect and total means on these respective domains are 224/255 and 37/255.
5. P_q(∀b,h D_b(z_h))=609/1024; conditional on this event the indirect and total means are 16/29 and −13/29.
6. ∀z∈{0,1}⁴, O(c,z)=3K(z)/4, and E_q `witnessOverall`=3/4.
7. E_{B_p}[A_b(c,z)|D_b] for (p,b)=(1/2,1),(1/2,0),(1/4,1),(1/4,0) is respectively 17/15, 28/15, 81/175, 84/85.
8. ∀h, the both-arms probability is 7/8 or 87/128 according to h, and the conditional direct mean given both arms is −1. ∀p∈(0,1), av_i μ_i(1;B_p)−av_i μ_i(0;B_p)=0.
9. ∀p∈(0,1) ∀i, E_{B_p}c_i=3p. ∀p∈(0,1) ∀b, the group and two-identical-group averages of both μ_i(b;B_p) and E_{B_p}c_i are all 3p. At p_H and p_L, both arm targets are 3/2 and 3/4. ∀b,c∈Bool, the high b target minus the low c target is 3/4; the high-minus-low unconditional average target is also 3/4.
10. ∀z, D_1↔K>0 and D_0↔K<4. K>0→A_1(c,z)=K−1; K<4→A_0(c,z)=K.
11. `w1BothArmMean` is E_{B_p}[A_b(c,z)|D_1∩D_0]. Its four values in the same order as item 7 are 1,2,13/29,42/29.
12. ∀h∈Bool ∀b∈Bool (then p=1/2 if h else 1/4), the joint own-arm probability equals P_{B_p}(D_b) and is positive, the joint own-arm conditional mean has the item-7 value, and the joint both-arms conditional mean has the item-11 value.

Junk conventions: real division by zero yields zero. Consequently A_b=0 on an empty b arm, and `condMean` is zero on a zero-probability event. Every arm-ratio assertion here either gives an explicit positive-arm hypothesis or conditions on exactly the arms used, with positive event probabilities given in the conjunction. The counterexample does not rely on A_b on an empty arm. All ordinary means use Fin 4 or Fin 2. The subtraction K−1 in the arm formulas is in ℝ and guarded by K>0. The product has four factors. No logs, square roots, powers with domain issues, infinite sums, integrals, extrema, limits, partial functions, or empty population indices occur. Generated numeral witnesses do not change this meaning.

## SAP.P045a.T2

No outer parameters or hypotheses: this is a conjunction of the following universally quantified results and fixed numerical assertions. The docstring presents it as a repair of biased Bernoulli ratios, retaining joint two-regime contrasts, fixed-count ratios, and arbitrary-law overall means.

1. In order, ∀n∈ℕ, n>0→∀p∈ℝ, p>0→p<1→∀y:(Fin n→{0,1}ⁿ→ℝ) ∀b∈Bool: ∀i, E_{B_p}(1_{z_i=b}y_i(z))=P_b μ_i(b;B_p), where P_b=p or 1−p; and E_{B_p}H_b(p,y)=av_i μ_i(b;B_p).
2. ∀G,C, C>0→C≤G→∀(n_g), (∀g n_g>0)→∀p∈(0,1)→∀local y ∀b, E_{L(C,B_p)}M_C(g↦H_b(p,y_g))=G⁻¹Σg n_g⁻¹Σi μ_{gi}(b;B_p).
3. ∀n,k, k>0→k<n→∀local y ∀b, E_{R(n,k)}A_b(y)=av_i μ_i(b;R(n,k)).
4. ∀G,C, C>0→C≤G→∀(n_g),(k_g), (∀g 0<k_g<n_g)→∀local y ∀b, E_{L(C,R)}M_C(g↦A_b(y_g))=G⁻¹Σg n_g⁻¹Σi μ_{gi}(b;R(n_g,k_g)).
5. ∀k∈Fin 4, k>0→(∀i∈Fin 4, μ_i(1;R(4,k))=k−1 and μ_i(0;R(4,k))=k); the fixed-count direct target is −1 whereas the B_{k/4} direct target is 0.
6. ∀n>0 ∀finite probability design q on {0,1}ⁿ ∀local y, E_q O(y)=av_i E_q y_i. ∀G,C, 0<C≤G→∀n_g>0→∀probability designs q_g→∀local y, E_{L(C,q)}M_C(g↦O(y_g))=G⁻¹Σg n_g⁻¹Σi E_{q_g}y_{gi}.
7. ∀p∈(0,1) ∀z∈{0,1}⁴, H_1(p,c,z)=K(K−1)/(4p), H_0(p,c,z)=K(4−K)/(4(1−p)). ∀p∈(0,1), E_{B_p}H_1=E_{B_p}H_0=3p and E_{B_p}(H_1−H_0)=0.
8. The fixed `w1RatioFailure` repeats T1's example: P_{B_{1/2}}D_1=15/16, E[A_1|D_1]=17/15, the target is 3/2, and 17/15≠3/2. In the two-regime experiment, conditional direct means given both own-regime arms are −1, the indirect mean on its two-control-arm domain is 224/255, and the total mean on its treated-high/control-low domain is 37/255.
9. ∀G,C with 0<C≤G→∀n_g>0→∀p∈(0,1)→∀Q:(H↦Design(∏g{0,1}^{n_g})), CL(C,1,Q,(g↦B_p))→∀local y ∀b, E_{J(C,Q)}M_{C,1}(g↦H_b(p,y_g))=U_b(B_p,y).
10. `w1BernoulliJointResult`: ∀G,C with 0<C<G→∀n_g>0→∀p:Bool→ℝ with ∀h 0<p_h<1→∀Q with ∀h CL(C,h,Q,(g↦B_{p_h}))→∀local y: all four arm means, the direct contrast at each h, the indirect contrast, and total contrast under the same J(C,Q) are unbiased for the corresponding U_b(B_{p_h},y), in the exact expansion of `w1UnbiasedContrasts` above.
11. `w1CRJointResult`: ∀G,C with 0<C<G→∀n_g and k_{h,g} with ∀h,g 0<k_{h,g}<n_g→∀Q with the two CL conditions for R(n_g,k_{h,g})→∀local y: the same collection of unbiased means and contrasts, now using A_b and fixed-count targets; also ∀w, J(C,Q)(w)>0→∀h ∀g∈H_h ∀b, D_b(z_g).
12. `w1OverallJointResult`: ∀G,C with 0<C<G→∀n_g>0→∀q_{h,g}:Design({0,1}^{n_g})→∀Q with both CL conditions for their masses→∀local y, E_J[M_{C,1}(O)−M_{C,0}(O)]=av_g av_i E_{q_{1,g}}y_{gi}−av_g av_i E_{q_{0,g}}y_{gi}.
13. `w1CRSingleResult`: ∀G,C, 0<C≤G→∀n_g,k_g with ∀g 0<k_g<n_g→∀Q with CL(C,1,Q,R)→∀local y ∀b, E_J M_{C,1}(A_b)=U_b(R,y).
14. `w1OverallSingleResult`: ∀G,C, 0<C≤G→∀n_g>0→∀designs q_g→∀Q with CL(C,1,Q,q)→∀local y, E_J M_{C,1}(O)=av_g av_i E_{q_g}y_{gi}.
15. ∀n,k, 0<k<n→∀z∈F(n,k) ∀b, Σi1_{z_i=b}=k if b else n−k (natural subtraction before casting), and this real arm count is positive.
16. ∀n∈ℕ ∀p∈ℝ ∀y ∀b ∀z, ¬D_b(z)→H_b(p,y,z)=0. This isolated zero-sum identity has no p or n positivity conditions.
17. ∀k∈Fin 4, k>0→∀i∈Fin 4 ∀b, μ_i(b;B_{k/4})=3k/4.
18. In T1's fixed two-regime law, ∀h the mean of H_1(p_h,c,z_h)−H_0(p_h,c,z_h) is zero; E[H_0(1/2,c,z_H)−H_0(1/4,c,z_L)]=3/4 and E[H_1(1/2,c,z_H)−H_0(1/4,c,z_L)]=3/4.

Junk conventions: B_p is merely a signed weight function outside [0,1], but every statistical Bernoulli assertion assumes 0<p<1 or uses 1/2,1/4,k/4 with k=1,2,3. Empty-arm A_b=0 occurs in totalized definitions; fixed-count identities have both arms positive on support. Bernoulli H_b has deterministic positive denominator and equals zero on an empty arm by its empty numerator. The unrestricted auxiliary item 16 also reads 0/0=0 for n=0 or P_b=0; it asserts only that totalized identity and is not the substantive unbiasedness theorem. `condMean` zero-event values are excluded by Bernoulli positivity or 0<k<n. ℋ(G,C) is nonempty under 0<C≤G, all group sizes and C are positive, and dual-regime results require C<G so G−C>0 and natural subtraction is exact. Outside support arbitrary assignments receive zero mass; all real-valued functions remain finite there. Cross-group dependence is allowed in J but outcomes are explicitly local functions. No analytically undefined functions, infinity casts, integrals, limits or extrema occur. `Design` cannot exist on an empty sample space because its total must equal one.

## SAP.P045a.T3

No external parameters or hypotheses. This fixes six groups of three units each, with baseline x=(1,2,3). The docstring states exact finite counterexamples for a convention that drops uncomputable singleton-arm within-group variance terms.

First, `T3Statement` defines n_g=3, C=3, law_m=L(3,(g↦R(3,m))), point(a,b)=M_3(g↦d(a,b,z_g)), and vest(a,b)=Vhat(3,(g↦a),(g↦b)). It asserts:

- ∀m∈{1,2}, E_law_m point(x+1,x)=1, Var_law_m point(x+1,x)=1/2, E_law_m vest(x+1,x)=1/3.
- For (m,a,b)=(2,2x,5x/4), variance and expected estimate are 9/8,43/48; for (1,3x/2,x), they are 8/9,19/36; for (2,x,0), they are 1/18,1/9.
- ∀m∈{1,2}, E_{R(3,m)}d(x+1,x)=1, Var_{R(3,m)}d(x+1,x)=3/2, and E_{R(3,m)}w(x+1,x)=1/2.

The added whole statement uses the actual two-regime space Ω_t={H⊆Fin 6}×(Fin 6→{0,1}³) (`W1ToyOutcome`). Its support S_t consists of |H|=3 and K(z_g)=2 for g∈H, K(z_g)=1 for g∉H (`w1ToySupport`). Its mass q_t(H,z)=|ℋ(6,3)|⁻¹∏g R(3,2 if g∈H else 1)(z_g) for |H|=3, zero otherwise (`w1ToyMass`). Thus it is uniform first stage followed by independent local fixed-count assignments with the correct regime-specific counts. Define P_h(a,b)=3⁻¹Σg∈H_h d(a,b,z_g) (`w1ToyPoint`), B_h(a,b)=s²_{H_h}(g↦d(a,b,z_g)) (`w1ToySampleVar`), and W_h(a,b)=Vhat(3,(g↦a),(g↦b))(H_h,z) (`w1ToyVest`). `w1ToyBaseline` is x_i=i+1. For h, `w1SingletonBaseline` is Σi:z_i=!h x_i, which is the singleton baseline on F(3,m_h), m_h=2 if h else 1. `w1TwoArmVariance` is s²_T(x+1) if h, otherwise s²_{Tᶜ}(x).

The complete additional assertions are |S_t|=14580, ∀w q_t≥0, Σq_t=1, and ∀w q_t(w)=1/14580 on S_t and zero elsewhere. Then ∀h∈Bool, letting m=m_h and x as above:

1. av_i[(x_i+1)−x_i]=1 and the equal six-group mean of this target is 1.
2. ∀z∈F(3,m), d(x+1,x,z)=4−(3/2)·singleton(z) if h, otherwise (3/2)·singleton(z)−2.
3. ∀t∈{1,2,3}, P_{R(3,m)}(singleton=t)=1/3; ∀t∈{−1/2,1,5/2}, P_{R(3,m)}(d(x+1,x)=t)=1/3.
4. E_{R(3,m)}twoArmVariance=1.
5. E_{q_t}P_h(x+1,x)=1, Var_{q_t}P_h(x+1,x)=1/2, E_{q_t}B_h(x+1,x)=3/2, E_{q_t}W_h(x+1,x)=1/3; expected estimate minus true variance is −1/6 and their ratio is 2/3.

Finally the actual joint law has variance/expected-estimate pairs 9/8,43/48 for P_1,W_1 at (2x,5x/4); 8/9,19/36 for P_0,W_0 at (3x/2,x); and 1/18,1/9 for P_1,W_1 at (x,0). It explicitly asserts 43/48<9/8,19/36<8/9,1/18<1/9.

Junk conventions: selected-arm point means always have arm sizes 1 and 2 on support, so those ratios are defined. The singleton raw sample variance would be 0/0=0 in ℝ, but `droppedWithin` explicitly branches on arm size ≥2 and assigns zero for a singleton. This is the declared modified estimator, not an implicit interpretation of a conventional sample variance. Between-group sample variance has three groups; the retained local sample variance has two units. `selectedMean` divides by 3, first-stage normalization by 20, local normalization by 3. The final ratio has denominator 1/2. Off-support empty arms and tiny selected sets have finite totalized values but zero probability. The singleton sum is asserted only on support where the specified arm is unique. All casts i.val+1 are exact real casts of i∈Fin 3. No other potentially partial operations occur.

## SAP.P045a.T4

No external parameters; it asserts `T4Statement`, a conjunction of four independently universally quantified results. The docstring describes mathematical parts (a)–(d) as retained and explicitly excludes executing R, propagating R NA/warnings, replacing reported toy entries, and the optional regenerated toy.

Part 1 quantifies, in order: ∀G,C∈ℕ, C≥2→C≤G→∀n,m:Fin G→ℕ, (∀g, m_g≥2 and m_g+2≤n_g)→∀a,b:∏g(Fin(n_g)→ℝ). Define q_g=R(n_g,m_g), law=L(C,q), θ_g=av_i a_{gi}−av_i b_{gi},

V_g=S²(a_g)/m_g+S²(b_g)/(n_g−m_g)−S²(a_g−b_g)/n_g,

where n_g−m_g is natural subtraction before casting; point=M_C(g↦d(a_g,b_g)); vest=Vhat(C,a,b). It concludes the conjunction:

- ∀g, E_{q_g}d(a_g,b_g)=θ_g and Var_{q_g}d(a_g,b_g)=V_g.
- E_law point=av_g θ_g.
- Var_law point=((1−C/G)/C)S²(θ)+(CG)⁻¹Σg V_g.
- E_law vest−Var_law point=G⁻²Σg S²(a_g−b_g)/n_g.
- That bias is nonnegative.
- E_law vest=Var_law point iff ∀g∀i∀j, a_{gi}−b_{gi}=a_{gj}−b_{gj}. The constant may vary with g.

Part 2 independently quantifies ∀G,C with 2≤C≤G→∀a,b:Fin G→Fin 3→ℝ. Let bias(m)=E_{L(C,R(3,m))}Vhat(C,a,b)−Var_{L(C,R(3,m))}M_C(d). It concludes

bias(2)=G⁻²Σg[S²(a_g−b_g)/3−S²(b_g)],

bias(1)=G⁻²Σg[S²(a_g−b_g)/3−S²(a_g)].

Part 3 independently quantifies ∀G,C with 2≤C≤G→∀x:Fin G→Fin 3→ℝ, using the same bias but with explicit a,b arguments. It concludes

bias(2,2x,5x/4)=−11/(8G²)·ΣgS²(x_g),

bias(1,3x/2,x)=−13/(6G²)·ΣgS²(x_g),

and (∃g,i,j, x_{gi}≠x_{gj}) implies that both displayed biases are strictly negative. The final syntactic clause is an implication, not an explicit iff; the formulas and nonnegative variances also imply the converse.

Part 4 independently quantifies, in order, ∀m∈ℕ, m∈{1,2}→∀a,b:Fin 6→Fin 3→ℝ→∀H⊆Fin 6, H∈ℋ(6,3)→∀w:Fin 6→{0,1}³, (∀g∈H w_g∈F(3,m))→`requiredDirectVariance(3,a,b)(H,w)=none`. This tests either regime separately with a common selected-group count m. Since every size-three group with m=1 or 2 has a singleton arm, the domain check fails.

Junk conventions: Part 1 implies G≥2, C≥2, n_g≥4 and each arm size ≥2 on the fixed-count support. Thus all means, local sample variances, group sample variances and real denominators in the substantive formula are proper. Natural n_g−m_g is positive and exact. C=G is permitted, with a genuine zero finite-population correction multiplying a defined between-group variance. Parts 2 and 3 use exactly the explicit singleton-dropping convention, with positive point-estimator arms. Part 4 represents undefined corrected estimates by `none`, so no junk real value is used to say that the corrected estimate exists. Totalized off-support means/variances have zero mass. For empty S, av_S=0 and s²_S=0/(−1)=0; for |S|=1, s²_S=0/0=0. These off-domain conventions are present in the definitions but do not establish conservativeness or equality on a forbidden domain. There are no other partial operations or analytic limits.

## SAP.P045a.T5

No external parameters; it asserts `T5WholeStatement`, containing `T5Statement` and general count identities plus complete two-unit tables. The docstring describes the coded complement event, its discrepancy from all-untreated, and the exact effect on two outcome schedules.

The fixed graph (`edge2`) has vertices Fin 2 and A(i,j)=1 iff i≠j. The sample law is B_{1/2} on its four assignments. For each i, `linear2` has Y_i(z)=1+z_0+z_1 and `threshold2` has Y_i(z)=1+2·1_{z_0=z_1=1}. `w1TwoAssignment` maps k=0,1,2,3 to 00,01,10,11, respectively. All graph/event/HT symbols below have the common finite-sum definitions above.

The conjunction says:

1. ∀i∈Fin 2, N[i]=Fin 2. For z=10, ∀i, E_bad(z,i) and ¬E_0(z,i).
2. ∀i, P(E_1)=1/4, P(E_bad)=3/4, P(E_0)=1/4.
3. τ(linear2)=2. F_bad(linear2) at 00,01,10,11 is −4/3,−8/3,−8/3,12; E F_bad(linear2)=4/3; E F_correct(linear2)=2.
4. τ(threshold2)=2. E F_bad(threshold2)=E F_correct(threshold2)=2.
5. ∀n∈ℕ ∀A:Network n ∀z∈{0,1}ⁿ ∀i∈Fin n, Σj z_j·1_{j=i or A(j,i)}=t_A(z,i) and Σj1_{i=j or A(i,j)}=|N_A[i]|. Symmetry identifies the column neighborhood in the first sum with the row neighborhood in t_A.
6. ∀i∈Fin 2, |N[i]|=2 and ∀k∈Fin 4, t_A(z^k,i)=(0,1,1,2)_k, E_1(z^k,i)↔k=3, E_bad(z^k,i)↔k≠3, E_0(z^k,i)↔k=0.
7. ∀k∈Fin 4, B_{1/2}(z^k)=1/4, F_correct(linear2,z^k)=(−4,0,0,12)_k, F_bad(threshold2,z^k)=(−4/3,−4/3,−4/3,12)_k, and F_correct(threshold2,z^k)=(−4,0,0,12)_k.
8. The real numbers 4/3 and 2 are unequal.

Junk conventions: general `fullHT` would use zero for division by an exposure probability of zero and for n=0, but all substantive HT instances here have n=2 and event probabilities 1/4 or 3/4. The generic graph identities use no division and, if n=0, have no i to instantiate; the n=2 example is nonempty. Closed neighborhoods contain i, hence are nonempty whenever an i exists. The finite assignment table indexes are Fin 4 and all accesses are total; no array defaults are used. All expectations are sums of four finite numbers. Neither truncated subtraction nor any analytic partial operation appears in these conclusions.

## Closure coverage

Every source declaration listed in `closure.json` has been read in its defining file. Common definitions above cover repeated dependencies for every target, including structure constructors/projections and dependent assignment types. `T1Statement`, `T2Statement`, `T3Statement`, `T4Statement`, and `T5Statement` were read in `Defs/Part4.lean`; all `WholeStatement` wrappers and all `w1*` dependencies were read in `Defs/WholeW1.lean`; the assignment/probability/statistic/graph definitions were read in `Defs/Part1.lean` and the exposure HT witnesses in `Defs/Part2.lean`. Every line-zero auxiliary proof was additionally inspected using Lean, as recorded at the start. No canonical claim or architect record has yet been consulted.
