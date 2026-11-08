# Blind reading

This file was written before opening `claims.json` or `record.json`. The reviewed theorem stubs are in `SAP/P006a/Challenge/Part1.lean`; their statements are the indicated propositions in Defs. All declarations listed in `closure.json` were read. The generated auxiliary declarations were printed by `scratch/Blind.lean`; they prove only that the natural-number denominators 2 and 4 are at least two, the scalar-tower instance for nonnegative extended reals, and `0 < 1` for the one-unit experiment. They add no mathematical assumptions.

## SAP.P006a.T11

Sources: Challenge/Part1.lean:87–90; Defs/Part6.lean:20–54; Defs/Part4.lean:47–78; Defs/Part1.lean:15–16,37–43.

Fix, universally and in this order, a type C with a sigma algebra, a set P of functions C → R, a proof that each member is measurable and lies pointwise in [0,1], a proof that the constant zero function belongs to P, and an arbitrary real-valued reward function R(D,p) of a measure D on C × (R × R) and a policy p. Write coordinates of this product as (x,(y0,y1)). A finite outcome law means a probability measure D for which both coordinate functions y0 and y1 are Bochner integrable. An optimizer of f over P means exactly p ∈ P and f(p') ≤ f(p) for every p' ∈ P. Define

* W_D(p) = integral p(x)(y1-y0) dD;
* supW_D = the real supremum of {W_D(p') : p' ∈ P};
* regret_D(p) = supW_D - W_D(p).

There are two further universally supplied hypotheses. Nondegeneracy means that there exist a finite outcome law D and a reward optimizer p with integral p(x) dD > 0. Treated-data invariance means: for every two finite outcome laws D,D', if their pushforwards under (x,(y0,y1)) ↦ (x,y1) agree, then R(D,p)=R(D',p) for every p ∈ P. This invariance uses the full joint law of X and the treated potential outcome; it is not an assertion about the realized selected treated subsample alone.

The first conjunct concludes that, for every real M > 0, there exist a finite outcome law D and a reward optimizer p having regret_D(p) > M. The order permits the witness D and the optimizer to depend on M and on all the preceding data.

The second conjunct inside the same universal assertion gives the construction for every finite D and every reward optimizer p for which q=integral p(x) dD > 0. For every real B > 0, let D_B be the pushforward of D under (x,(y0,y1)) ↦ (x,(y1+B,y1)). Then D_B is a finite outcome law, its (X,Y1) pushforward is unchanged, and p remains a reward optimizer. For every p' ∈ P,

    W_(D_B)(p') = -B integral p'(x) dD ≤ 0.

The supremum of this welfare over P is 0, zero is a welfare optimizer, and regret_(D_B)(p)=Bq. For every M>0 the real number B=(M+1)/q is positive and gives regret strictly greater than M.

Finally, a separate conjunct, independent of the universal data above, states that for every B>0 the Dirac law at ((),(1+B,1)), on the one-point covariate type Unit, and P={constant zero, constant one}, have the following properties: the law is finite; the identically zero reward is nondegenerate and treated-data invariant; every p ∈ P is a reward optimizer; zero maximizes welfare; zero has regret 0; one has regret B. Thus this conjunct distinguishes existence of a bad optimizer from a statement about every optimizer.

Junk-value audit: the definitions use real `sSup`, which is 0 for an empty or unbounded-above subset of R. Here P contains zero; bounded policies and the two integrable outcome coordinates give |W_D(p)| ≤ integral |y1-y0| dD uniformly over P. Consequently these suprema are nonempty and bounded; after shifting their value 0 is attained. The Bochner integrals are totalized to 0 on nonintegrable functions, but probability, coordinate integrability, and measurable bounded policies prevent that case. The only division is (M+1)/q; q>0 is explicit. The pushforward maps are measurable coordinate maps and addition. There is no natural subtraction, logarithm, square root, real power, `toReal`, conditional expectation, limsup/liminf, empty sum, or partial function here. Empty C cannot support the required probability-law witness.

## SAP.P006a.T12

Sources: Challenge/Part1.lean:92–105; Defs/WholeW1.lean:204–243; Defs/Part6.lean:57–65; Defs/Part4.lean:80–83; Defs/Part1.lean:15–18,53–83,115–120; Defs/Part2.lean:16–51,65–69.

This is a fixed conjunction, with no free mathematical data or antecedents. On R with its usual Borel sigma algebra and topology, let L be Lebesgue measure restricted to the closed interval [0,1], and let A=(1/2)L+(1/2)delta_(1/2). It asserts:

* L(R)=A(R)=1;
* the topological supports of both measures equal [0,1];
* L is absolutely continuous with respect to A (every A-null measurable set is L-null);
* L({1/2})=0 and A({1/2})=1/2;
* A is not absolutely continuous with respect to L;
* there is no measurable f:R→[0,infinity] for which A=L.withDensity(f), where withDensity assigns to a measurable set S the nonnegative Lebesgue integral of f over S under L;
* for every set S of reals, (1/2)L(S) ≤ A(S), an extended-real inequality.

For each of the two choices nu=A and nu=L it also constructs a one-unit experiment E_nu. The covariate space is R and the sample space is R×R. It has population measure nu; mean potential outcomes mu0(x)=0, mu1(x)=1; a law nu×L independent of the policy; X_0(x,u)=x; potential outcomes identically 0 and 1; treatment T_p,0(x,u) is the Boolean decision u ≤ p(x); estimator muhat_p,(x,u)(z)=0. The number of units is 1, with the explicit proof that this is positive. For all admissible policies p (measurable and [0,1]-valued), both of these experiments satisfy all the following `Standing` conditions, fully unpacked:

1. The population measure is a probability measure; mu0 and mu1 are measurable and integrable under it.
2. The sample law is a probability measure. Each X_i,Y0_i,Y1_i,T_p,i is measurable; Y0_i,Y1_i and the evaluated estimator muhat_p,omega(X_i(omega)) are integrable.
3. Each X_i has the population law: the functions X_i and the identity on the population space are almost everywhere measurable and have equal pushforward measures.
4. The joint law of (X_i,Y0_i,Y1_i) is unchanged by replacing any admissible policy by any other.
5. For each policy the unit vectors (X_i,Y0_i,Y1_i,T_p,i) are independent and identically distributed: finite intersections of inverse images of measurable sets have product probabilities, and all the unit-vector pushforwards agree. There is only one unit here.
6. Conditional on the sigma algebra pulled back from X_i, conditional expectations of Y0_i and Y1_i are respectively mu0(X_i) and mu1(X_i), almost everywhere.
7. The conditional expectation of the real indicator 1{T_p,i=true} given that same sigma algebra is p(X_i).
8. For every Borel B⊆R×R, the conditional expectation of 1{T_p,i=true}1{(Y0_i,Y1_i)∈B} equals p(X_i) times the conditional expectation of 1{(Y0_i,Y1_i)∈B}. Thus treatment is conditionally independent of the potential-outcome pair in the stated indicator formulation.

The further conjuncts say the two population measures equal A and L respectively, each is absolutely continuous with respect to A, and both effects mu1-mu0 are identically 1. For each experiment and every admissible policy, the conditional expectation of the evaluated estimator given the sigma algebra generated jointly by the full covariate vector and treatment vector equals mu0(X_i), almost everywhere. Finally the two coordinate projections are independent under (A×L)×(L×L); this supplies an independent joint coupling of the agents' entire experiments.

The docstring describes this as a counterexample to a sufficiency reading of the printed absolute-continuity direction, and expressly excludes a refutation under a separate existence assumption for the named density.

Junk-value audit: 1/2 is a nonzero-denominator rational in R or [0,infinity], with the relevant generated nontrivial-denominator proofs checked. The only real integrals and conditional expectations are of bounded functions under probabilities. Conditional expectation is generally zero by definition when the input is nonintegrable, the conditioning sigma algebra is not a subalgebra, or the trimmed measure is not sigma-finite; here the functions are bounded, X and (X,T) are measurable, and all measures are finite. None of these defaults is used. A uniform seed equal to the threshold is included by ≤; its probability is zero, including threshold 0 and 1 endpoints, so Bernoulli probabilities remain correct. The density nonexistence statement quantifies over ENNReal-valued measurable functions, allowing infinity without converting it to a spurious real value; absolute continuity still precludes an atom at an L-null singleton. Support is ordinary topological measure support. No real supremum, natural subtraction, `toReal`, logarithm, square root, real power, limsup/liminf, partial function, or empty index type contributes to this assertion.

## SAP.P006a.T13

Sources: Challenge/Part1.lean:107–110; Defs/Part6.lean:68–112; Defs/Part4.lean:18–33; Defs/Part2.lean:58–63,104–138; Defs/Part1.lean:15–18,29–46,53–86,101–103,115–116.

Quantification is universal in this order: a natural number K; a measurable covariate type C; measurable sample types Omega_k for k∈Fin K; unit counts n_k; an experiment E_k on Omega_k,C,n_k for each k; a reference probability P0; then the hypotheses below. Each experiment consists of a proof n_k>0, a measure P_k on C, two real mean functions mu0_k,mu1_k, a law L_k,p on Omega_k depending on a function p:C→R, covariates X_k,i, potential outcomes Y0_k,i,Y1_k,i, Boolean treatments T_k,p,i, and a possibly policy- and sample-dependent estimator muhat_k,p,omega(x). Define tau_k=mu1_k-mu0_k.

The hypotheses are:

1. Every E_k satisfies `OutcomeStanding`. For every admissible (measurable [0,1]-valued) policy p, P_k and L_k,p are probabilities; mu0_k and mu1_k are measurable and integrable under P_k; all unit covariates, potential outcomes and treatments are measurable; both potential outcomes of every unit are integrable. Covariate pushforwards equal P_k. The joint law of (X_k,i,Y0_k,i,Y1_k,i) is the same under any two admissible policies. The full unit vectors including treatment are independent and have identical pushforwards under each policy. Given the sigma algebra pulled back from X_k,i, conditional means of potential outcomes equal their mu0_k and mu1_k evaluations, the conditional mean of the treatment indicator equals p(X_k,i), and, for every Borel set B of potential-outcome pairs, the conditional mean of treatment-indicator times 1_B factors as p(X_k,i) times the conditional mean of 1_B. Independence and identical distribution have the same finite-event-factorization and pushforward meanings specified above. Unlike `Standing`, this structure does not require integrability of the estimator on all observations.
2. For every pair j,k the functions mu0_j and mu0_k agree exactly, including null-set values.
3. P0 is absolutely continuous with respect to each P_k.
4. Each tau_k is integrable under P0.
5. For every k, every admissible policy p, and every i∈Fin n_k, the treated estimator residual r_k,p,i = 1{T_k,p,i=true}(muhat_k,p,omega(X_k,i)-mu0_k(X_k,i)) is integrable under L_k,p.
6. For these k,p,i, its conditional expectation given X_k,i is zero almost everywhere.
7. Define g_k(x)=(n_k:R)^(-1) * toReal(dP0/dP_k(x)). For each k,p,i as above the real function

       (Yobs_k,p,i-muhat_k,p,omega(X_k,i)) * 1{T_k,p,i=true} * g_k(X_k,i)

   is integrable under L_k,p, where Yobs equals Y1 when treated and Y0 otherwise.

Define score_k(p) as the integral under L_k,p of the sum of this last expression over i∈Fin n_k. Thus the weight is evaluated at the same unit's covariate inside the finite sum. The conclusions, in a conjunction, are:

* For every k and every admissible p,

      score_k(p) = n_k integral tau_k(x)p(x)g_k(x) dP_k
                 = integral tau_k(x)p(x) dP0.

* For each k, the measurable policy p_k^+(x)=1 if tau_k(x)>0 and 0 otherwise is a score optimizer over all admissible policies. The real supremum of that score over the same set equals integral tau_k(x)1{tau_k(x)>0} dP0.
* For every j,k, if tau_k(x)≤tau_j(x) for every x, then the corresponding positive-part integrals are ordered.
* `UniformRankPreservation` means precisely that for every such pair with pointwise effect dominance the real supremum of score_k over all admissible policies is at most the real supremum of score_j over all admissible policies. Each side uses its own agent's score.
* If, additionally, tau_k(x)≥0 for every agent and every x, then each score supremum equals integral tau_k dP0, and `RelativeRankPreservation` holds: for every j,k, integral tau_k dP0≤integral tau_j dP0 implies that agent k's score supremum is at most agent j's.

Junk-value audit: n_k is cast exactly into R and is positive by the Experiment field, so its inverse is not the 0^(-1)=0 convention. The RN derivative is Mathlib's ENNReal-valued derivative, which is defined even absent absolute continuity via the absolutely continuous part of a Lebesgue decomposition. Here both measures are probabilities and P0≪P_k, so it represents the entire reference measure and is finite P_k-almost everywhere. Although `ENNReal.toReal infinity=0`, this can change only a P_k-null set and its pullbacks under X, hence cannot alter any asserted integral or the weight's intended almost-everywhere meaning. Conditional expectations have the defaults described for T12, ruled out by probability, measurable covariates and explicit residual integrability; the indicator/means conditions are on bounded or integrable variables. Weighted reward terms are explicitly integrable; their finite sum is integrable. The population tau integrals are integrable after multiplication by p∈[0,1], as are positive parts; change of measure controls the weighted population integrals. All score suprema are over a nonempty class containing zero and have an attained, finite upper bound supplied by the positive rule and the integrable positive part, so real sSup defaults do not intervene. K=0 is allowed and makes the agent-indexed clauses empty, but the universal assertion also ranges over nonempty K and does not depend on this special case. Each actual unit set Fin n_k is nonempty. There is no truncated subtraction, log, sqrt, rpow, limsup/liminf, sInf, or partial function.

## SAP.P006a.T14

Sources: Challenge/Part1.lean:112–120; Defs/WholeW1.lean:245–264; Defs/Part4.lean:29.

First, for every real t, t times the strict-positivity indicator equals max(t,0). Write t^+ for this function.

Second, universally quantify a type C, an arbitrary sigma algebra on it, an arbitrary measure P0 on it, and arbitrary real functions tau_j,tau_k. If tau_k(x)≤tau_j(x) for every x, then

    lower-integral of ENNReal.ofReal(tau_k(x)^+) dP0
      ≤ lower-integral of ENNReal.ofReal(tau_j(x)^+) dP0.

Both sides live in [0,infinity], with infinity allowed. No measurability, sigma-finiteness, probability normalization, or integrability antecedent is present in this clause. For measurable functions this is exactly monotonicity of extended nonnegative expectations. The lower Lebesgue integral is also defined on nonmeasurable functions; this formally supplies a more general monotonicity assertion.

Third, with the same universal quantifier order and the same pointwise dominance assumption, if both positive-part functions are Bochner integrable under P0, then their real integrals are ordered. There is no experiment, score, ranking predicate, weighted reward, reference density, unit count, or optimizer in the elaborated statement. The final sentences of the docstring refer to corrections in other declarations rather than additional conjuncts of this theorem.

Junk-value audit: the positive-part indicator gives exactly zero at t=0 and is identically max(t,0); `ofReal` truncates negative real inputs to 0 but its actual input is already nonnegative. Infinity in the nonnegative integral is a legitimate extended value; no `toReal` is applied. The real-integral clause expressly assumes integrability of both functions, so the totalized value 0 for a nonintegrable Bochner integral is not used. The nonnegative integral on a nonmeasurable function is a lower integral rather than an ordinary expectation; all measurable functions remain included. Empty C and zero measures are permitted and give valid zero comparisons. No real supremum, division, subtraction on natural numbers, log, sqrt, rpow, limit, or partial function occurs.

## SAP.P006a.T15

Sources: Challenge/Part1.lean:122–125; Defs/Part6.lean:124–140; Defs/Part4.lean:85–97; Defs/Part3.lean:17–19,26.

The statement is a fixed finite counterexample conjunction followed by a universal singleton-private-coordinate fact. A binary policy is a real pair (p0,p1), interpreted as p(false)=p0 and p(true)=p1. A Bernoulli mass at t∈Bool is p when t=true and 1-p otherwise. With deterministic potential-outcome functions y0,y1:Bool→R and a fair binary covariate, the observed mass assigned to a record (x,t,y) is

    sum over a,b∈Bool of (1/2)*BernoulliMass(p(a),b)
      * 1{(x,t,y)=(a,b, if b then y1(a) else y0(a))}.

For a singleton covariate with certain treatment, the mass at record (t,y) is the analogous sum over b∈Bool, using Bernoulli probability 1 and potential outcomes y0,y1∈R. Equality of these mass functions is asserted at every record, not merely at selected records.

For the singleton experiment it asserts that y0=0,y1=1 and y0=2,y1=1 have equal observed mass functions; treatment probability 1 is positive; the probability of no treatment is 0; and 0≠2. Its final conjunct explicitly identifies this common observed mass function as mass one at (true,1) and zero at all other records.

For the binary experiment it fixes p=(1,1/2), y1≡1, and compares y0≡0 against y0(false)=2,y0(true)=0. Their observed mass functions agree at every record. Both covariate-specific treatment probabilities are strictly positive. There is no untreated probability at x=false, whereas the marginal untreated probability is 1/4. Under the first y0, the records (false,true,1), (true,true,1), and (true,false,0) have masses 1/2,1/4,1/4 respectively.

Finally, for every measurable type X, every (not necessarily measurable) real function mu0 on X×Unit, and every measure PX on that product, define

    D_mu0(c) = real sSup { |mu0(c)-mu0(c.first,u)| : u∈Unit }.

The statement asserts D_mu0(c)=0 for every c and integral D_mu0(c) dPX=0. Since Unit contains exactly one element this supremum is over the singleton {0}. This proves zero maximum within-public-type variation when the private coordinate has just one value. The text itself does not mention an estimator, the actual conditional-mean construction, or a formula from Lemma 3; the displayed lack of untreated mass is the finite obstruction to which the docstring refers.

Junk-value audit: these Bernoulli masses would be signed weights for a real p outside [0,1], but the only policies used are 1 and (1,1/2), so they are genuine nonnegative normalized probabilities. Finite sums are over the inhabited finite Bool type. Fractions 1/2 and 1/4 have nonzero denominators; no conditioning-on-null division is actually performed. Real record equality is handled classically, without a partial or undecidable computation default. The maximumDeviation definition would have real-sSup defaults for an empty or unbounded range in general; here the private type is Unit, the range is exactly {0}, and neither default is used. Its integral is of an identically zero measurable integrable function even for an arbitrary measure or nonmeasurable mu0, so the Bochner integral does not use its nonintegrability default. X may be empty, but the finite witnesses have concrete inhabited covariates and the universal singleton fact remains valid. There is no `toReal`, RN derivative, conditional expectation, truncated subtraction, logarithm, square root, rpow, limsup/liminf, or partial function.
