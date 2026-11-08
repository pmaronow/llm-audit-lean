# Blind reading of the Challenge

This file was written before opening claims.json or record.json. It reads the actual propositions, including all imported SAP definitions; theorem docstrings are not treated as hypotheses. There are nine stubs: T1, T2, T4, T5, T6, T7, T8, T9, T10. There is no T3 stub.

## Common objects and Mathlib semantics

All subtraction below is real or rational field subtraction, not truncated subtraction. All maxima/minima are finite binary maxima/minima. All divisions are field divisions, so a zero denominator would give zero. The places where an ordinary conditional expectation is asserted must therefore be checked for positive mass.

For the measure-theoretic statements, an arbitrary type Ω and an arbitrary measurable-space structure on Ω are universally quantified first. A CausalModel on that space consists of:

* A Mathlib measure μ with μ(Ω)=1.
* Measurable maps S:Ω→{0,1,2}, Z:Ω→{false,true}, and Y₀,Y₁:Ω→ℝ.
* Both Y₀ and Y₁ are globally μ-integrable, meaning almost everywhere strongly measurable with finite integral of absolute value. In addition, the structure requires actual measurability everywhere.
* The joint random variable (S,Y₀,Y₁) is independent of Z. This is independence of the generated sigma algebras, equivalently factorization of probabilities of measurable preimage events.
* Both assignment events A_z={Z=z} have strictly positive real probability.
* The integral of D₁−D₀ is nonzero, where S=0 gives D₀=D₁=1 (always-taker), S=1 gives D₀=D₁=0 (never-taker), and S=2 gives D_z=z (complier). Boolean values are converted to 0 or 1 before integration. Thus monotonicity and exclusion are encoded by the objects rather than additional premises. The nonzero first stage excludes zero complier mass but permits full compliance.

Let C={S=2}, A={S=0}, N={S=1}, NC=Cᶜ. Observed treatment is D=D_Z; observed outcome is Y=Y_D. Let P(E)=μ.real(E)=(μ(E)).toReal. Although toReal sends infinite mass to zero in general, this measure is a probability measure, so all event masses here are finite. Bool and Fin 3 have the discrete measurable structures; ℝ has its usual Borel structure.

Write m(f,E)=(∫_E f dμ)/P(E). The integral is the Mathlib Bochner integral with respect to μ restricted to E. Its definition returns zero for a nonintegrable function; here integrability follows from the structure for potential outcomes and their finite selections, and for all bounded products used below. On a null event m is the totalized value zero, not a conditional mean with a probabilistic interpretation.

Use the following notation throughout:

* p=P(C); e_z=m(Y,A_z); x_d=m(Y_d,C); n=m(Y,NC); CACE=m(Y₁−Y₀,C).
* B_dz={D=d,Z=z}; q_dz=P(B_dz)/P(A_z); b_dz=m(Y,B_dz).
* j_dz=m(1_{D=d}Y,A_z).
* k=∫_A Y₁ dμ+∫_N Y₀ dμ (the noncomplier contribution, not a conditional mean).
* boundedOutcomes means 0≤Y_d(ω)≤1 for every d and every ω, not merely almost surely.

Given real p,e₀,e₁, define t=(e₁−e₀)/p and

    L₀=max(0,−t,1−(1−e₀)/p), U₀=min(1,1−t,e₀/p),
    L₁=max(0,t,1−(1−e₁)/p),  U₁=min(1,1+t,e₁/p).

The notation for three arguments means the nested binary max/min in the files; associativity makes the displayed version identical.

The mixture system Mix(p,e₀,e₁,x₀,x₁) says that there exists a real n with

    p x₀+(1−p)n=e₀, p x₁+(1−p)n=e₁,
    x₀,x₁,n ∈ [0,1].

The corrected system Corr says

    p x₀+e₁−p x₁=e₀, x₀,x₁∈[0,1], 0≤e₁−p x₁≤1−p.

The printed system Print has exactly the same clauses except the last upper bound is 1.

The Mathlib source definitions checked were Measure.real (as documented in MeasureTheory/Measure/Real.lean), IsProbabilityMeasure (Measure/Typeclasses/Probability.lean), Measurable (MeasurableSpace/Defs.lean), Integrable (Function/L1Space/Integrable.lean), integral and set-integral notation (Integral/Bochner/Basic.lean), restrict (Measure/Restrict.lean), IndepFun and its measurable-preimage characterization (Probability/Independence/Basic.lean), and the Bool/Fin measurable instances (MeasurableSpace/Instances.lean).

## Finite-law objects used in T1 and T7

A BinaryAtom is a tuple (d₀,d₁,y₀,y₁,r₀,r₁) of six Booleans. For assignment z, D_z=d_z, observed outcome V_z=y_{d_z}, and response R_z=r_z. A complier atom has d₀=0,d₁=1. A BinaryLaw consists of 17 such labelled atoms and 17 rational weights; the type itself imposes no validity conditions.

For weights w_i, fprob(E)=Σ_i 1_E(i)w_i; fexpect(f)=Σ_i w_i f(i); fmean(f,E)=Σ_i 1_E(i)w_i f(i)/fprob(E). Fin 17 and Bool are nonempty finite index types, and all sums are genuine finite sums. Define p_f=fprob(compliers), e_fz=fexpect(V_z), x_fd=fmean(y_d,compliers), q_fdz=fprob(D_z=d), and b_fdz=fmean(V_z,D_z=d). Respondent arm and cell means restrict additionally to R_z=1. All Boolean outcomes in these expressions are the rational numbers 0 or 1.

finiteValid means: every weight is strictly positive; the weights sum to one; d₀≤d₁ at every atom; fexpect(d₁−d₀)=p_f; and p_f>0. Assignment has masses a₀=99/200 and a₁=101/200. The joint mass on atom i and assignment z is w_i a_z. The observed-law function on (z,d,r,v) is

    a_z fprob(D_z=d, R_z=r, R_z V_z=v).

Thus a missing outcome is recorded as zero together with its separate response flag; its actual value is not observed. The law is joint in assignment, treatment, response and recorded outcome.

The two explicit laws have the following exact atoms and weights (0=false, 1=true):

| i | lower atom | lower weight | upper atom | upper weight |
|---|---|---|---|---|
|0|110010|104/12375|110001|1/495|
|1|110011|871/12375|110011|13/165|
|2|000001|738/15655|000010|26/505|
|3|000011|4346/15655|000011|164/505|
|4|110101|1/495|110110|32/5841|
|5|110111|8/99|110111|40/531|
|6|001010|26/505|001001|936/20503|
|7|001011|26/101|001011|4342/20503|
|8|010000|40958176/44062954375|010011|6746986/511698825|
|9|010001|343024724/44062954375|010110|79537936/30190230675|
|10|010010|2170783328/396566589375|010111|19884484/548913285|
|11|010011|18180310372/396566589375|011001|79169476/11541651275|
|12|010101|29736094/1762518175|011011|3305325623/103874861475|
|13|010111|1576012982/15862663575|011100|933302176/680957425225|
|14|011010|13228208/12792470625|011101|233325544/12381044095|
|15|011011|110786242/12792470625|011110|38965365848/6128616827025|
|16|011111|9603827/511698825|011111|9741341462/111429396855|

The recorded counts c_zdv (columns v=0,1), missing counts h_zd, and arm counts n_z are:

| z | d | c_zd0 | c_zd1 | h_zd | n_z |
|---|---|---|---|---|---|
|0|0|212|167|36|495|
|0|1|39|40|1|495|
|1|0|164|130|26|505|
|1|1|67|110|8|505|

For rational inputs, corollaryPair(p,q,r,e₀,e₁,a,n) is the pair

    ((e₀−qa−rn)/p, (e₀−qa−rn)/p+(e₁−e₀)/p).

fullCorollary uses full-law p_f,q_f10,q_f01,e_f0,e_f1,b_f10,b_f01. respondentCorollary uses the same p_f and treatment probabilities but replaces both arm means and both pure-cell means by respondent means.

## SAP.P028.T1

This is a closed assertion with no hypotheses. It is the conjunction of all the following facts:

1. Both explicit laws are finiteValid, both have p_f=2047/9999, and assignment has the two strictly positive masses a₀=99/200,a₁=101/200.
2. For each law the sum of all 34 joint masses is 1 and every joint mass is strictly positive.
3. For each law (universally quantified over membership in [lowerLaw,upperLaw]), both respondent arm events have positive mass, all four treatment cells have positive mass, and all four respondent treatment cells have positive mass.
4. For each of those laws, every atom-index predicate E, and every assignment z, Σ_i 1_E(i)w_i a_z=fprob(E)a_z. This is factorization for every latent event, not a restriction on just observed events.
5. For every z,d,v, each law has recorded probability c_zdv/n_z, and for every z,d each has missing probability h_zd/n_z.
6. The observed-law functions are equal. The complier pairs are exactly (1423/10235,6749/10235) for lowerLaw and (7633/10235,7642/10235) for upperLaw. Both coordinates differ.
7. For each law, q_f10=16/99, q_f01=64/101, respondent arm means are 207/458 and 240/471, and respondent pure-cell means b^R_10=40/79,b^R_01=130/294. The full arm means are 208/495,266/505 for lowerLaw and 27/55,248/505 for upperLaw.
8. fullCorollary equals the corresponding true complier pair in both laws. respondentCorollary equals (1594452863/3629163146,896530960/1244058109) in both laws and differs from the true pair in each law.
9. For every d∈Bool there does not exist a function F from rational-valued observed-law tables on Bool⁴ to ℚ such that, for every BinaryLaw M, finiteValid(M) implies F(observedLaw(M))=x_fd(M).

The last quantifier is ∀d, ¬∃F, ∀M, validity→identification; it rules out identification of either coordinate even on this 17-label class. There is no connection asserted to a particular parametric response construction beyond the explicit tables and randomization factorization.

## SAP.P028.T2

For every measurable Ω, the proposition is the conjunction of a universal model/response statement and eight closed rational calculations. A Response is any measurable Boolean map R:Ω→Bool; it need not be independent or positive by definition. Let H={R=1}, e^R_z=m(Y,A_z∩H), b^R_dz=m(Y,B_dz∩H). For a positive q_dz put w_dz=q_dz b^R_dz; otherwise put w_dz=0. Let v_dz=m(R 1_{D=d}Y,A_z), and h_dz=P(R=0,D=d,Z=z)/P(A_z).

For every CausalModel M and then every Response T, if all potential outcomes are in [0,1] everywhere, the following all hold:

1. p>0, p=1−q_10−q_01, p x₀=j_00−j_01, and p x₁=j_11−j_10.
2. If q_10>0, then q_01>0, then both respondent arms and both respondent pure cells have positive joint mass, then e^R_z=e_z for both z and b^R_10=b_10,b^R_01=b_01, then

       x₀=(e^R₀−q_10 b^R_10−q_01 b^R_01)/p,
       x₁=x₀+(e^R₁−e^R₀)/p.

   These are nested implications with precisely the displayed antecedents.
3. If both respondent arm events have positive joint mass, and for every z the random variable R is independent of (Y,D) under the probability measure μ(·∩A_z)/μ(A_z), then both respondent arm means equal the full arm means. Furthermore, if q_10>0 and q_01>0, then all four mean equalities and all four respondent positivity conditions from item 2 hold, as do both formulas in item 2.
4. If for every d,z with q_dz>0 the respondent cell has positive joint mass and b^R_dz=b_dz, then for every z,

       e_z=Σ_d w_dz, x₀=(w_00−w_01)/p, x₁=(w_11−w_10)/p.

5. With no response positivity or ignorability assumptions, the four inequalities

       (v_00−v_01−h_01)/p ≤ x₀ ≤ (v_00+h_00−v_01)/p,
       (v_11−v_10−h_10)/p ≤ x₁ ≤ (v_11+h_11−v_10)/p

   hold.

The eight unconditional numerical identities, all in ℝ, are:

    (167/495−130/505−26/505)/(2047/9999)=1423/10235;
    (167/495+36/495−130/505)/(2047/9999)=7633/10235;
    (110/505−40/495−1/495)/(2047/9999)=6749/10235;
    (110/505+8/505−40/495)/(2047/9999)=7642/10235;
    (207/458−(16/99)(40/79)−(64/101)(130/294))/(2047/9999)
       =1594452863/3629163146;
    [the preceding expression]+(240/471−207/458)/(2047/9999)
       =896530960/1244058109;
    ((415/495)(167/379)−(320/505)(130/294))/(2047/9999)
       =16568969/38014837;
    ((185/505)(110/177)−(80/495)(40/79))/(2047/9999)
       =295510/414829.

There is no assertion in this proposition that any sensitivity endpoint is attainable, nor an existential counterexample separating cellwise and armwise response mean equality. The reweighting conclusion permits zero treatment cells but uses ordinary respondent means only in cells assumed to have respondents.

## SAP.P028.T4

This closed assertion first universally quantifies real p,e₀,e₁,x₀,x₁, assumes 0<p and p<1, and asserts the conjunction:

1. Mix↔Corr.
2. For every real n, p x₁+(1−p)n=e₁ implies n=(e₁−p x₁)/(1−p).
3. p x₀+e₁−p x₁=e₀ iff x₀=x₁−t.
4. If x₀=x₁−t, then x₀∈[0,1] iff t≤x₁≤1+t.
5. 0≤e₁−p x₁≤1−p iff (e₁+p−1)/p≤x₁≤e₁/p.
6. (e₁+p−1)/p=1−(1−e₁)/p.
7. Mix iff x₀=x₁−t and L₁≤x₁≤U₁.
8. L₁−t=L₀ and U₁−t=U₀.
9. 0≤e₁−p x₁≤1 iff (e₁−1)/p≤x₁≤e₁/p.
10. If e₁≤1 and x₁≥0, then (e₁−1)/p≤x₁ and the printed residual condition is equivalent to x₁≤e₁/p.
11. Mix implies Print.

There are no hypotheses e₀,e₁∈[0,1] in this universally quantified part. Separately the proposition asserts Print(1/2,3/4,3/4,0,0) and ¬Mix(1/2,3/4,3/4,0,0), establishing strict weakening at one explicit input.

## SAP.P028.T5

This closed assertion has no hypotheses. It asserts Print and failure of both Mix and Corr at (p,e₀,e₁,x₀,x₁)=(1/2,3/4,3/4,0,0). At that candidate the solved noncomplier value is (3/4−(1/2)0)/(1−1/2)=3/2. The printed residual lower endpoint is −1/2; the corrected endpoint is 1/2. The four interval endpoints L₀,U₀,L₁,U₁ are respectively 1/2,1,1/2,1.

It also asserts there exists a CausalModel on the standard discrete four-point space Bool×Bool such that its outcomes are everywhere in [0,1], p=1/2, e₀=e₁=3/4, and x₀=x₁=1. The existential quantifier follows the closed numerical assertions. This is an admissible realization of the input triple, not a realization of the rejected candidate x₀=x₁=0. The theorem does not prescribe that model's type distribution, assignment probability or individual noncomplier outcomes.

## SAP.P028.T6

For every measurable Ω, the proposition is a conjunction of a universal assertion and a numerical endpoint assertion. For every CausalModel M with outcomes everywhere in [0,1], all the following hold:

1. 0<p≤1; 0≤k≤1−p; for every z, e_z=p x_z+k; and k=j_10+j_01.
2. If p<1, then P(NC)=1−p>0, k=(1−p)n, and 0≤n≤1.
3. If p=1, then k=0, x₀=e₀ and x₁=e₁.
4. For every z, x_z=(e_z−k)/p.
5. For every d, 0≤x_d≤1.
6. For every z, 0≤e_z−p x_z≤1−p.
7. For every z, 1−(1−e_z)/p≤x_z≤e_z/p.
8. L₀≤x₀≤U₀, L₁≤x₁≤U₁, and x₁=x₀+t (using this model's p,e₀,e₁).

Separately, for every real e₀,e₁, assuming each is in [0,1], the four endpoints with p=1 equal L₀=U₀=e₀ and L₁=U₁=e₁. No positive noncomplier mass is assumed outside the p<1 branch. There is no model existence assertion and no separate null-cell product identity.

## SAP.P028.T7

This closed assertion uses a fixed latent atom (d₀,d₁,y₀,y₁,r₀,r₁)=(0,1,0,1,1,1). Its sample space is Bool with mass 1/2 at each assignment value. The atom is constant across the two points. twoAtomProb is the corresponding rational finite sum, and twoAtomMean is its normalized weighted sum. The assertion is the conjunction:

* Total mass is 1 and each assignment event has mass 1/2. Treatment is monotone; both potential outcomes belong to [0,1]. The mean first stage and the complier probability both equal 1.
* Observed arm means are 0,1 and complier potential means are 0,1.
* The noncomplier probability, 1−p, and the numerator 1−p·1 are all zero. Each pure joint cell {D=1,Z=0} and {D=0,Z=1} has probability zero.
* For every real n, 1·0+(1−1)n=0 and 1·1+(1−1)n=1. For every real a,n, 0a+0n=0.
* For every predicate E on BinaryAtom and every z, the joint probability of E(the fixed atom) and assignment z equals their probability product.
* For every z, D_z=z and V_z=z.
* Let q=P(D=1,Z=0)/P(Z=0), r=P(D=0,Z=1)/P(Z=1), both rational. Then q=r=q+r=0, and for every rational a,n, qa+rn=0.
* L₀(1,0,1)=U₀(1,0,1)=0 and L₁(1,0,1)=U₁(1,0,1)=1.

It asserts that the mixture equations do not determine a noncomplier mean at this boundary; it does not assign an ordinary mean to the null noncomplier or pure-cell events. It describes the finite randomized law directly rather than packaging it as a CausalModel.

## SAP.P028.T8

For every measurable Ω, this is the conjunction of two assertions:

1. For every CausalModel on Ω with outcomes everywhere in [0,1], p>0, both coordinate interval inclusions L₀≤x₀≤U₀,L₁≤x₁≤U₁ hold, and x₁=x₀+t.
2. For every real p,e₀,e₁ in that order, if 0<p≤1, e₀,e₁∈[0,1], and |e₁−e₀|≤p, then both intervals are nonempty. Moreover, for every real x₁ in [L₁,U₁], there exists a CausalModel on Bool×Bool with bounded outcomes, this p,e₀,e₁, complier means (x₁−t,x₁). Also, for every real x₀ in [L₀,U₀], there exists such a model with complier means (x₀,x₀+t).

The existential models depend on the triple and then the chosen coordinate; they need not live on the initially arbitrary Ω. The p=1 case is included. No positivity of individual treatment cells or of noncomplier mass is required.

## SAP.P028.T9

For every measurable Ω, for every CausalModel M, if every joint treatment-assignment cell B_dz has strictly positive probability, then all the following hold. There is no bounded-outcome assumption here; global measurability and integrability of both potentials are still structure hypotheses.

* p>0, P(A)>0, P(N)>0, P(NC)>0 and q_10+q_01>0.
* For every z, e_z=Σ_d q_dz b_dz.
* q_10=P(A), q_01=P(N), p=1−q_10−q_01.
* b_10=m(Y₁,A), b_01=m(Y₀,N).
* n=(q_10 b_10+q_01 b_01)/(q_10+q_01).
* x₀=(e₀−q_10 b_10−q_01 b_01)/p.
* x₁=x₀+(e₁−e₀)/p and also x₁=(e₁−q_10 b_10−q_01 b_01)/p.

Every denominator in these displayed means and formulas is positive under the hypotheses, including noncomplier mass. The theorem does not cover full compliance under its four-positive-cells antecedent.

## SAP.P028.T10

For every measurable Ω, the first conjunct says: for every CausalModel M on Ω, with no boundedness or cell-positivity assumptions beyond the structure,

    E[D|Z=1]−E[D|Z=0]=p>0,
    e₁−e₀=p·CACE,
    CACE=(e₁−e₀)/p
        =(e₁−e₀)/(E[D|Z=1]−E[D|Z=0]).

Here assignment-conditioned treatment means use m(1_{D=1},A_z), and CACE is m(Y₁−Y₀,C). Both potential outcomes remain globally measurable and integrable as structure fields.

The second conjunct asserts there exist two CausalModels M₀,M₁ on Bool×Bool, both with bounded outcomes and both with p=1/2, e₀=e₁=3/4 and CACE=0. Their complier means are x₀=x₁=1/2 for M₀ and x₀=x₁=1 for M₁. Thus the three figures p,e₀,e₁ and the effect agree while both complier levels differ. No claim is made that the two models have equal entire observed treatment-outcome distributions or equal pure-cell means.
