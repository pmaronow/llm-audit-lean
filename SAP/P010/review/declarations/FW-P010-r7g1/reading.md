# Blind reading

Written before opening `claims.json` or `record.json`. Sources read: every entry of `closure.json`, the five docstrings in `SAP/P010/Challenge/Part1.lean`, and all source declarations in their closures. Generated closure auxiliaries were also printed and read using `scratch/ClosureAux.lean` (successful Lean compilation). They supply only numeral/finite-index instances or a scalar-tower instance; none supplies a statistical hypothesis or conclusion.

## Shared mathematical expansion for T3–T5

For natural numbers K,d, a state is a tuple (y,s,z,x) in
R^(Fin K) × Bool^(Fin K) × Fin K × R^(Fin d), equipped with its product measurable space. The potential response in arm a is y_a; the potential passing indicator is s_a; assignment is z; observed response is Y=y_z and observed passing is S=s_z. Let A={all s_a=true}, Z_a={z=a}, and P={S=true}. Finite products of real Borel spaces and finite discrete spaces are standard Borel.

For a measure mu, an event E, and a real function f, write
M_mu(f;E)=(integral over E of f dmu)/(mu(E)).toReal. This is the restricted Bochner integral and real division, not a conditional-expectation random variable. For a probability measure and positive event mass it is the ordinary event-conditional mean whenever f is integrable there. Define p_a=mu(P intersection Z_a)/mu(Z_a), with both masses converted from nonnegative extended reals to reals before division. The population assumptions are: mu is a probability measure; for each a, the pair (y_a,s_a) is independent of z under mu; every Z_a has positive mass; and every p_a is strictly positive. Independence is arm by arm, not independence of the full vector of potentials from assignment.

The normalized conditional law of f on E is (mu(E))^(-1) times the pushforward of mu restricted to E by f. Let F_a be this law for f=Y and E=P intersection Z_a. The trimming ratio is r_a=(sum over b != a of (1-p_b))/p_a. For a real measure F and real u, its extended-real left quantile is
Q_F(u)=inf{x in extended R : u <= F({y : y<=x}).toReal}.
The real quantile is Q_F(u).toReal. A measure is atomless exactly when every real singleton has mass zero. Full real support of f means that every open interval (l,u), l<u, has a preimage of strictly positive mass. All moments of f means integrability of |f|^n for every natural n, including n=0.

The lower endpoint is M_mu(Y; P intersection Z_a intersection {Y<=Q_Fa(1-r_a)}); the upper endpoint is M_mu(Y; P intersection Z_a intersection {Q_Fa(r_a)<=Y}). Comparisons here take place in the extended reals.

A measure nu is compatible with mu when nu satisfies the population assumptions, nu(A)>0, and the pushforward laws of (Y,S,z) under nu and mu are equal. It need not preserve the covariate distribution or latent joint law. The compatible mean set C_mu,a is the set of real values M_nu(y_a;A) for such nu. The extended compatible mean set is precisely the image of C_mu,a under the inclusion R into extended R; it contains no infinite element. An asserted extended-real greatest lower bound or least upper bound can nevertheless be infinite.

Common conventions to inspect separately in each use: Bochner integrals of nonintegrable functions are zero; division by zero in R or Q gives zero; ENNReal.toReal(infinity)=0; EReal.toReal(plus/minus infinity)=0. The infimum defining Q is in the complete lattice of extended reals, so an empty set gives plus infinity and an unbounded-below set gives minus infinity. For a probability distribution, Q(u)=-infinity for u<=0, Q(u)=plus infinity for u>1, Q(u) is finite for 0<u<1, and Q(1) can be finite or plus infinity. In this Mathlib version, a pushforward by a non-AE-measurable map of a nonzero measure defaults to an arbitrary Dirac measure; map of the zero measure remains zero. All maps used below are Borel, so that fallback is inactive. If the conditioning mass is zero, normalized restriction is zero (ENNReal infinity times zero is zero); if it is infinite its inverse is zero. These are not ordinary conditional laws in those cases.

## SAP.P010.T1

Docstring: asserts a refutation of a printed claim, describing the unweighted 90–90 preference interval as disjoint from each other arm. No canonical claim has yet been read.

There are exactly three arms, a=0,1,2, named 90–90, 90–70, 90–45. Fixed natural sample sizes are n=(544,538,533), failures f=(35,182,40), passers m_a=n_a-f_a, and preference-one counts c=(61,162,327). In exact rational arithmetic let q_a=f_a/n_a and r_a=(sum over b!=a of q_b)/(1-q_a). Let k^-_a=max(ceil(m_a*(1-r_a))-1,0), where the maximum is the conversion of an integer to a natural; and k^+_a=m_a-max(floor(m_a*r_a),0), where the last subtraction is natural truncated subtraction. Define rational endpoints
l_a=max(k^-_a-max(m_a-c_a,0),0)/k^-_a,
u_a=min(k^+_a,c_a)/k^+_a.
Regard I_a=[l_a,u_a] as a closed subset of R by rational inclusion.

This is a closed proposition, with no supplied data or hypotheses. It asserts all four clauses: I_0 and I_1 are disjoint; I_0 and I_2 are disjoint; it is false that for every ordered pair a,b of arms there exists a real x in both intervals; and there does not exist a single real x belonging to every I_a. In the third clause the order is forall a, forall b, exists x. In the fourth it is exists x, forall a, negated. Disjoint means the intersection is empty.

Junk conventions: both natural differences saturate at zero, including m_a=n_a-f_a; Int.toNat discards a negative result; ceil and floor are exact rational rounding; rational division at zero returns zero. For these fixed inputs f_a<n_a, 0<r_a<1, k^-=(284,281,278), k^+=(285,282,279), so no denominator vanishes and no negative rounded count is discarded. The saturation of the binary lower numerator is intentional: a smallest subset can contain zero ones. All preference counts are <=m_a. Rational-to-real casts are exact. Fin 3 is nonempty; no empty-index issue, integral, logarithm, square root, real power, limsup, partial function, or supremum appears.

## SAP.P010.T2

Docstring: exact trimming counts and endpoints, common overlap for approval, and positive preference gaps under integer trimming and a fractional rule.

All sample sizes, failures, passers, ratios, rounding, endpoints, intervals and preference counts have exactly the expansion given in T1. Approval-one counts are additionally c'=(192,188,324), and the same endpoint formula is applied with c'. Let B=1-sum_a q_a. For each arm set v_a=c_a/n_a, and define fractional preference endpoints
(max(0,(v_a-sum_{b!=a}q_b)/B), min(1,v_a/B)).

This is again a proposition about fixed constants, without premises. The conclusions, joined by conjunction, are:

* For every a, m_a=(509,356,493)_a; r_a=(32239072/72978893,10871635/51611456,31403827/72143648)_a; k^-_a=(284,281,278)_a; k^+_a=(285,282,279)_a.
* For every a, the preference pair (l_a,u_a) equals ((0,61/285),(87/281,27/47),(56/139,1))_a, and the approval pair equals ((0,64/95),(113/281,2/3),(109/278,1))_a.
* For every arm a and natural j, then for each proof of 1<=j and j<=m_a: (j/m_a<1-r_a iff j<=k^-_a), and (j/m_a>r_a iff m_a-k^+_a<j). The subtraction in the last inequality is in the naturals. These are strict empirical-CDF cutoff rules.
* The real number 1/2 lies in every approval interval and in preference intervals I_1,I_2. Also u_0<l_1, u_0<l_2, l_1-u_0=7654/80085>0, and l_2-u_0=7481/39615>0.
* B=40739821/77997088>0. The three fractional preference pairs equal ((0,8745997/40739821),(12614477/40739821,23486112/40739821),(16448045/40739821,1)) respectively. Their arm-1 minus arm-0 and arm-2 minus arm-0 gaps are 3868480/40739821>0 and 7702048/40739821>0.

Junk conventions: the exact same natural truncation, integer rounding and nonzero-denominator checks as T1 apply independently here. The added denominator B is explicitly positive, and all other displayed rational denominators are positive numerals. min/max in fractional endpoints are explicit clipping of binary-outcome bounds, not partial functions. Approval counts are also <=m_a. For the j clauses m_a>0 for every arm and j ranges over an inhabited finite interval (for example j=1). The universal proofs hj,hjn are genuine range restrictions. No other analytic default is used.

## SAP.P010.T3

Docstring: calls two same-observable continuous populations counterexamples to bounds whose outcome-tail conditioning omits passing.

Use K=2,d=0 and the shared expansions above. Let E be the real probability distribution with density 1_{x>0} exp(-x) with respect to Lebesgue measure; let E^- be its image under x->-x. Let L_r have density (r/2)exp(-r|x|). Only r=1,2 are used. For fixed check statuses (s_0,s_1) and two outcome distributions H_0,H_1, a stratum distribution is the pushforward of H_0 product H_1 product ((1/2)delta_0+(1/2)delta_1): its two outcomes are the first two coordinates, checks are the fixed statuses, assignment is the last coordinate, and its Fin 0 covariate vector is the unique empty vector. Thus outcomes in each stratum and assignment are mutually independent by construction.

For each Boolean b define mu_b as the mixture:

* mass 1/4 on checks (true,true), with arm-0 outcome E if b=true and E^- otherwise, and arm-1 outcome L_1;
* mass 1/4 on checks (true,false), with arm-0 outcome E^- if b=true and E otherwise, and arm-1 outcome L_1;
* mass 1/2 on checks (false,true), with outcome distributions L_2,L_1.

For every Boolean b, after setting mu=mu_b, the theorem asserts: the population assumptions; mu(A)=1/4; the observed-response law has no atoms; observed response has full real support and all absolute natural moments; p_0=1/2, p_1=3/4, r_0=1/2; F_0=L_1 and its half quantile is zero; M_mu(Y;{Y<=0} intersection Z_0)=-3/4; M_mu(Y;{0<=Y} intersection Z_0)=3/4; M_mu(y_0;A)=1 if b=true and -1 otherwise; the conjunction of the two inequalities putting this always-passer mean between those last two observed tail means is false; and the endpoints defined with P additionally in their conditioning are -1 and 1. Finally the two mu_b have exactly the same joint (Y,S,z) law.

There are no universally quantified candidate measures or assumptions to supply: both concrete mixtures and all their properties are conclusions. The Boolean quantification has two cases, followed by the one equality of observable laws.

Junk conventions: normalization denominators are positive: assignment masses are 1/2, passing-in-arm-0 mass is 1/4, A has mass 1/4, and each sign-tail in arm 0 has mass 1/4. The more restricted passing sign-tails have mass 1/8. All real quantities and potential outcomes here have finite absolute moments. The half quantile is finite and equals zero. The exponentials have no domain restriction; the two positive Laplace rates produce bona fide probability densities. Rational constants in ENNReal are nonnegative and finite. There are no sqrt/log/rpow operations. The EReal quantile uses an infimum but is evaluated only at 1/2, so it has neither an empty-set default nor infinity-to-real loss. Fin 0 appears only as the covariate dimension and is harmless; the treatment type Fin 2 is inhabited. The auxiliary declarations in this closure are only finite-index/numeral and scalar instances.

## SAP.P010.T4

Docstring: corrected finite-branch trimmed means bound every compatible always-passer mean, attain both endpoints, and equal quantile integrals.

Quantifier order is: for every natural K,d, every measure mu on the shared population state space, every proof of the population assumptions, every a in Fin K, every proof mu(A)>0, every proof F_a is atomless, every proof that Y is integrable on P intersection Z_a, and every proof r_a<1, the following conjunction holds. Let l_a,u_a be the shared lower/upper endpoints, m=M_mu(y_a;A), and B=1-sum_b(1-p_b).

1. l_a<=m<=u_a.
2. l_a and u_a each belong to C_mu,a; in full, for each endpoint there exists a possibly different probability measure nu on the same population state type with positive assignment and passing rates, arm-by-arm independence, nu(A)>0, the same (Y,S,z) law, and conditional y_a mean equal to that endpoint.
3. For every real m' and every proof m' belongs to C_mu,a, l_a<=m'<=u_a.
4. p_a(1-r_a)=B and (r_a<1 iff B>0).
5. If r_a=0, both endpoints equal M_mu(Y;P intersection Z_a).
6. l_a=(p_a/B) integral from 0 to B/p_a of Q_Fa(u).toReal du; u_a=(p_a/B) integral from 1-B/p_a to 1 of Q_Fa(u).toReal du. These are Mathlib interval Bochner integrals with Lebesgue measure.

This does not assert every interior real number is itself a compatible mean; it asserts containment and endpoint attainment, hence extremal sharpness. Only this fixed arm's passing distribution is required atomless and integrable.

Junk conventions: probability plus positive assignment/passing rates rule out infinity-to-real and zero normalization. 0<=r_a<1, p_a>0, and B=p_a(1-r_a)>0. The endpoint events have positive conditional fraction 1-r_a; atomlessness handles exact quantile masses. Integrability of the passing response transfers through arm-by-arm independence to y_a on {s_a=true} and hence on A; the same is true for compatible measures with the identical observed law, so C_mu,a is not intended to contain nonintegrable-integral default values. At r_a=0, Q(0)=-infinity and Q(1) is possibly plus infinity; these select the whole distribution up to null sets in the extended-real comparisons. In the quantile integrals the EReal-to-real convention can replace infinite quantile values at u=0 or u=1 by zero; endpoint changes on Lebesgue-null sets do not affect an integrable quantile integral. Interior u in (0,1) has a finite quantile. No empty infimum at an interior quantile, no unbounded limsup/liminf, no logarithm/square root/rpow or partial-function default appears. K=0 has no a and contributes no case; K>=1 cases exist. d=0 is allowed without deleting an outcome or treatment.

## SAP.P010.T5

Docstring: calls a full-real-support observed-response law with finite sharp passing-mean endpoints 0 and 1 a refutation of a printed claim.

Take K=2,d=0. Let H have density 30x^2(1-x)^2 on 0<x<1 and zero elsewhere with respect to Lebesgue measure. Let J have density 5/(2(1+|x|)^6) on R. For a Boolean s and real law F, let the common-outcome population be the pushforward of F product a fair independent assignment: y_0=y_1 is the sampled real value, both potential checks equal s, and covariates are the unique empty vector. Let mu be 1/3 times the common-outcome population with true checks and law H plus 2/3 times the common-outcome population with false checks and law J.

For t in R and Boolean b, set E=(1-t,1) if b=true, E=(0,t) otherwise; q=H(E).toReal; F=H conditioned on E; G=H conditioned on (0,1) minus E. Define nu_t,b as the sum of four independently assigned stratum populations (as expanded for T3): weight q/3 with checks (true,true) and outcomes F,F; weight (1-q)/3 with checks (true,false) and outcomes G,J; weight (1-q)/3 with checks (false,true) and outcomes J,G; weight (1+q)/3 with checks (false,false) and outcomes J,J. Each real weight is converted with ENNReal.ofReal before scaling the stratum law.

The theorem is the conjunction of the following fixed-witness properties and quantified conclusions; it has no antecedent hypotheses:

* mu satisfies the population assumptions and mu(A)=1/3. Its observed-response law is atomless and its observed response has full real support. Its first, second and third absolute moments (the second written as Y^2) are 1/6, 13/63, 19/84. |Y|^3 is explicitly integrable.
* For every real R with 1<=R, each tail mu(Y>R), mu(Y<-R), converted to reals, is 1/(3(1+R)^5).
* For every a in Fin 2, p_a=1/3, r_a=2; every m in C_mu,a satisfies 0<m<1; the extended compatible set has greatest lower bound 0 and least upper bound 1; minus infinity is not its greatest lower bound and plus infinity is not its least upper bound.
* For every real t, then every proof 0<t and t<1, H((0,t)).toReal=10t^3-15t^4+6t^5; for every Boolean b, nu_t,b is compatible with mu; and for every a in Fin 2,
  M_nu_t,false(y_a;A)=t(15/2-12t+5t^2)/(10-15t+6t^2),
  this mean is strictly between 0 and t, and
  M_nu_t,true(y_a;A)=1-M_nu_t,false(y_a;A).

Thus 0 and 1 are limiting extrema, not attained members of the compatible real mean set. The theorem does not assert that the passing response distribution has full real support. In this witness it is H, supported in (0,1); the nonpassing outcomes give the observed response full real support.

Junk conventions: 1+|x| is strictly positive, so the heavy-tail density never divides by zero. All powers are natural powers, with no rpow domain issue. H and J are probability laws; J has finite third absolute moment (its density decays as |x|^-6), so the moments used here are ordinary finite integrals. The tail denominator is positive for R>=1. For 0<t<1, q is strictly between 0 and 1, the F,G conditioning events have positive mass, all four mixture coefficients are positive, and 10-15t+6t^2 is positive (its discriminant is negative). The always-passing mass in nu_t,b is q/3>0. All compatible y_a means are ordinary finite means because their always-passers lie within passing potential outcomes supported in (0,1), as follows from independence and the shared observed law. No EReal-toReal is used in the infimum/supremum assertion: the real mean set is embedded into EReal, and IsGLB/IsLUB are genuine order-theoretic bounds. The compatible set is nonempty (mu itself, and nu at t=1/2); the extended extrema are not consequences of an empty set convention. There is no quantile in the T5 statement closure and no sInf/sSup or limsup/liminf computation. ENNReal.toReal is applied only to finite masses; assignment and passing masses are positive. Fin 2 is nonempty and Fin 0 is only the empty covariate vector. The generated dependencies bearing other witness names are only numeral instances, not extra assumptions or statistical constructions.
