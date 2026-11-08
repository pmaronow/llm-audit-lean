# Blind reading (saved before opening claims.json or record.json)

I read the five Challenge docstrings and statements, all source declarations in their closures, and the elaborated printout of all 90 distinct closure constants in `scratch/blind-print.txt`. The latter includes the structure constructors/projections, generated pattern matchers, and generated numeral proof constants. None of claims.json or record.json has been opened at this stage. This document records statements, not an assessment against an intended claim.

## Common mathematical expansion used in the sections below

These are explicit mathematical abbreviations for the Mathlib finite sets, sums, real arithmetic and predicates occurring in the statements, not additional assumptions.

* A vertex is an element of the disjoint union `N ⊔ (N × N)`. Write `s(i)` for the left injection of i and `u(i,k)` for the right injection of (i,k). These injections are injective and have disjoint ranges. Unobserved vertices need not be right injections: any vertex outside the specified sampled set is unobserved.
* Data is a tuple `(S,B,a,t,d,b)`, where S and B are finite subsets of N, a,t,d are total functions N → N, and b is a total function N → {false,true}. Put N₀ = S\B, V_S = {s(i): i∈S}, and E_R = {{s(a(j)),s(j)}: j∈N₀}, a finite SET of finite vertex sets. Put r_i = #{e∈E_R:s(i)∈e}, spare_i = max(d(i)-r_i,0), and C_i = {j∈N₀:a(j)=i}. The natural subtraction in spare is truncated.
* Data is admissible precisely when B⊆S; t restricted to S is injective; for every j∈N₀, a(j)∈S and t(a(j))<t(j); and r_i≤d(i) for every i∈S. In particular recruitment edges then have two distinct endpoints, no directed time cycle occurs, and spare_i is the ordinary nonnegative difference at sampled i.
* A state is a tuple H=(V,E,Z), with V a finite set of vertices, E a finite set of finite vertex sets, and Z a total Boolean function on the ambient vertex type. Put k_H(v)=#{e∈E:v∈e}. A simple state means that every e∈E has cardinality two and is contained in V. An augmented state for S is a simple state in which each edge contains some s(i), i∈S. Thus edges between two unobserved vertices are excluded.
* A compatible pair/state means: the state is augmented; V_S⊆V; E_R⊆E; Z(s(i))=b(i) for i∈S; every v∈V\V_S has an edge {s(i),v}∈E for some i∈S; and k_H(s(i))=d(i) for each i∈S. A graph-compatible state imposes exactly those conditions with the observed-trait equalities omitted. Thus no isolated unobserved vertices are permitted, whereas isolated sampled vertices are permitted.
* Let m_H=#E, A_H(v,w)=1 if v≠w and {v,w}∈E, and 0 otherwise, and z_H(v)=1 if Z(v)=true, and 0 otherwise. All sums in the next display range over v,w∈V:

  a_H = Σ_v Σ_w (A_H(v,w) - k_H(v)k_H(w)/(2m_H)) z_H(v)z_H(w),

  c_H = Σ_v Σ_w (1_{v=w} k_H(v) - k_H(v)k_H(w)/(2m_H)) z_H(v)z_H(w).

  The raw homophily value is a_H/c_H in the total real field. Homophily is the partial value `some(a_H/c_H)` exactly if m_H>0 and c_H≠0, and is `none` otherwise. Write this domain condition as Hdom(H).
* A vertex is not yet sampled just before j when it is u(i,k), or when it is s(k) and either k∉S or t(j)≤t(k). Write Q_H(i,j) for the finite set of v∈V such that {s(i),v}∈E and v is not yet sampled by that rule. This includes j itself at its recruitment time. Write Q⁼_H(i,j)={v∈Q_H(i,j):Z(v)=Z(s(i))}.
* Put PΣ(D,H)=Σ_{j∈N₀}(1_{Z(s(j))=Z(s(a(j)))} - #Q⁼_H(a(j),j)/#Q_H(a(j),j)), and raw P(D,H)=PΣ(D,H)/#N₀. Preferential recruitment is `some(P(D,H))` exactly if #N₀>0 and #Q_H(a(j),j)>0 for every j∈N₀, and is `none` otherwise. Write this domain condition as Pdom(D,H).
* The homophily value set is {x∈R: there exists a compatible H with Hdom(H) and a_H/c_H=x}. The preferential value set is {x∈R: there exists a compatible H with Pdom(D,H) and P(D,H)=x}. A value set is point identified precisely when it equals {x} for some real x.
* A full homophily region with endpoints L,U means that EVERY compatible H satisfies Hdom(H), L belongs to the homophily value set and L≤x for all its members, and U belongs to that value set and x≤U for all its members. A full preferential region is defined identically using Pdom and the preferential value set. In particular these definitions require nonempty value sets and attained endpoints; they are not supremum conventions.
* For q∈{false,true}, define the private-leaf completion by V=V_S∪{u(i,k):i∈S,0≤k<spare_i} and E=E_R∪{{s(i),u(i,k)}:i∈S,0≤k<spare_i}. The trait at s(i) is b(i); the trait at u(i,k) is b(i) if q=true and its Boolean negation otherwise. Flipping a trait at v keeps V,E and replaces Z(v) by its negation, agreeing with Z everywhere else. Unobserved(H) means V\V_S.
* The induced state has vertex set V_S, edge set {e∈E:e⊆V_S}, and the SAME total trait function Z. Induced compatibility means simplicity, vertex set exactly V_S, E_R contained in its edge set, and k(s(i))≤d(i) for sampled i. It imposes no trait agreement and no equality of degrees.

The structure constructors simply form these tuples; their projections select the corresponding fields. Generated `leafCompletion.match_1` and `notYetSampled.match_1` perform the exhaustive disjoint-union/pair cases just described. The closure's `_proof_*` constants prove numeral `AtLeastTwo` conditions (2, 3, 5, or 7 at least two); they add no assumptions and make no statistical definitions.

## SAP.P012b.T13

Source: `Challenge/Part1.lean:8-10`; statement `Defs/Part3.lean:13-55`.

This is the conjunction of two universally quantified assertions, with all the data, graph, compatibility and value notions expanded above.

1. For EVERY data tuple D, then a proof of admissibility, then natural i,j, assume i∈S, j∈S\B, a(j)=i, and r_i<d(i). AFTER those choices there exist states H,K and a vertex v∈V_H\V_S such that:
   * both H,K are compatible; v=u(i,0); V_H and E_H are exactly the vertex/edge sets of the private-leaf completion (q=true); and for all k∈S, {s(k),v}∈E_H iff k=i;
   * Z_H(v)=true and K is exactly the trait flip of H at v. This does not require all the other unobserved traits of H to equal those in the completion;
   * for each ℓ∈S\B, Q_H(a(ℓ),ℓ)=Q_K(a(ℓ),ℓ), and v∈Q_H(a(ℓ),ℓ) iff a(ℓ)=i;
   * P(D,H)-P(D,K) = σ_i/#N₀ · Σ_{ℓ∈C_i} 1/#Q_H(i,ℓ), where σ_i=-1 for b(i)=true and σ_i=+1 for b(i)=false;
   * P(D,H)≠P(D,K), and the set of DEFINED preferential values over compatible states is not a singleton;
   * if b(i)=true, the difference is ≤ -1/(#N₀·#Q_H(i,j))<0, with equality in the first comparison iff C_i={j}.
2. For EVERY admissible D, compatible H, natural i,j with i∈S, j∈N₀ and a(j)=i, and EVERY v∈V_H\V_S which has an edge to exactly the sampled vertex i and has Z_H(v)=true, let K be its trait flip. Then K is compatible, the two assertions about Q in item 1 hold, the same signed full-sum identity and unequal raw P values hold, and the same bound/strict sign/sole-child equality equivalence holds if b(i)=true. Unlike item 1 there is no separate strict spare-degree hypothesis and no explicit non-singleton value-set conclusion.

The docstring describes two compatible completions, nonidentification, the corrected full sum, and the extension to any compatible private-leaf starting graph.

Junk conventions: all numeric quotients are real divisions (x/0=0 in Lean). Here j∈N₀ gives #N₀>0. For a compatible H and every ℓ∈N₀, s(ℓ)∈Q_H(a(ℓ),ℓ), because the recruitment edge is present and its own time is allowed. Thus every displayed reciprocal has positive denominator. C_i contains j, so its sum is nonempty. The leaf-completion use of truncated natural subtraction is safe for sampled indices by admissibility. The empty-sample and empty-nonseed cases cannot satisfy either assertion's i,j hypotheses. Total values of a,t,d,b outside S are not additional observations and do not affect the relevant quantities. Boolean negation and Function.update are total. No integrals, logarithms, roots, real powers, `toReal`, extrema of empty sets, or limsup/liminf occur.

## SAP.P012b.T14

Source: `Challenge/Part1.lean:12-20`; statement `Defs/WholeW1.lean:94-124`, including `Defs/Part3.lean:57-77`.

This is a conjunction of concrete assertions and assertions universally quantifying compatible states for four fixed data tuples. Here the letter A/B/C/D in an example is a name, not the arbitrary-data variable of the common expansion.

* A: S={1,2}, B={1}, a(k)=1, t(k)=max(k-1,0), d(k)=1, b(k)=false for all k. A is admissible. The state V={s(1),s(2)}, E={{s(1),s(2)}}, Z=false on V is compatible, has a_H=c_H=0, homophily none and preferential some 0. For EVERY compatible H, V and E equal those of this dyad and its traits agree on V (total traits outside V may differ); the same raw zero values and partial values hold.
* B: same S,a,t,d as A, but B={1,2} and b(k)=(k=2). B is admissible. The dyad with traits false,true at s(1),s(2) is compatible, has a_H=-1/2, c_H=1/2, and homophily some(-1). Its nonseed count and recruitment sum are zero. For EVERY state H whatsoever the nonseed count is zero, PΣ(B,H)=0, and preferential(B,H)=none. No conclusion here says all compatible B graphs are this dyad.
* C: S=B={1}, a(k)=1, t(k)=k, d(k)=0, b(k)=false. C is admissible. The state V={s(1)}, E=∅, Z=false is compatible, with both partial statistics none. For EVERY compatible H its displayed vertex/edge/trait data are equal to this state; #E=0; for all v,w∈V, k(v)k(w)=0 and 2#E=0; #N₀=0; both partial statistics are none.
* D: S={1,2}, B={1}, a(k)=1, t(k)=max(k-1,0), d(1)=1 and d(k)=4 for k≠1, and b(k)=true. D is admissible. For EVERY three Booleans t3,t4,t5, the graph on {s(1),s(2),u(3,0),u(4,0),u(5,0)} with edges {s(1),s(2)} and {s(2),u(k,0)} for k=3,4,5, and corresponding leaf traits t3,t4,t5 (true elsewhere), is compatible. The all-true one has a_H=c_H=0 and homophily none. The leaf patterns false,false,false; true,false,false; and true,true,false have homophily some(-3/5), some(-1/3), and some(-1/7), respectively. All eight have preferential some 0.
* More generally, for EVERY D-compatible H there EXISTS a finite U disjoint from {s(1),s(2)} such that #U=3, V={s(1),s(2)}∪U, E={{s(1),s(2)}}∪{{s(2),v}:v∈U}. If r=#{v∈U:Z_H(v)=true}, then r≤3 and preferential is some 0. Homophily is some(-3/5), some(-1/3), some(-1/7), or none with raw numerator and denominator zero, according as r=0,1,2,3.
* There are NO real L,U making a full homophily region for A, and NO such endpoints for D, using the everywhere-defined and attained-extrema definition given above.

The docstring explicitly calls this a refutation of a printed claim, asserting undefined quotients in these four examples. This blind reading cannot yet check whether the purportedly refuted claim actually asserts those quotients are defined.

Junk conventions: x/0=0 is relevant to the raw h formulas for C (the inner normalization is 0/0), to raw hValue for A and the all-true D graph, and to raw pValue for B/C. These raw total values are NOT asserted to be defined statistical values: the partial wrappers return none. PΣ on an empty nonseed set is the ordinary empty sum 0. A/D have a nonempty recruitment set and positive susceptible denominators. All cardinalities/casts are natural counts, converted exactly to reals. The sample times use natural truncated subtraction, giving t(1)=0,t(2)=1, which are distinct as required. No extrema via sInf/sSup or empty-set defaults are used: nonexistence of a full region includes its explicit domain requirement. No integration, log/sqrt/rpow, `toReal`, or limsup/liminf occurs.

## SAP.P012b.T15

Source: `Challenge/Part1.lean:22-31`; statement `Defs/WholeW1.lean:126-153`, including `Defs/Part3.lean:79-115`.

For a state H put d₁=Σ_{v∈V:Z(v)=true} k(v), d₀=Σ_{v∈V:Z(v)=false} k(v). These are natural numbers; in real expressions they are cast to R. Put A_b(D)=Σ_{i∈S:b(i)=b} d(i), a natural sampled-degree total for trait b. The following is a conjunction; all universal variables in different bullets are independent.

* For EVERY simple H with #E=m>0, Σ_v k(v)z(v)=d₁; d₁+d₀=2m; and c_H has each of the three expressions d₁-d₁²/(2m), d₁d₀/(2m), and d₁(2m-d₁)/(2m). Moreover c_H>0 iff d₀>0 and d₁>0, and Hdom(H) iff the same two inequalities. If d₁=0 or d₁=2m, both a_H and c_H are zero.
* For EVERY admissible D and EVERY compatible H, Pdom(D,H) iff #B<#S. For each j∈N₀, s(j) lies in Q_H(a(j),j), whose cardinality is strictly positive.
* For EVERY admissible D, (all compatible H satisfy Hdom) iff A_false(D)>0 and A_true(D)>0. Independently, (all compatible H satisfy Pdom) iff #B<#S.
* For EVERY admissible D, if there EXIST sampled i,j with r_i<d(i), r_j<d(j), and b(i)≠b(j), both sampled trait-degree totals are positive. If there EXISTS j∈N₀ with r_{a(j)}<d(a(j)), then #B<#S.
* For EVERY admissible D, under the two positive sampled trait-degree totals, for EVERY real L,U, being a full homophily region is equivalent to L being a least DEFINED compatible homophily value and U being a greatest such value. Under #B<#S the analogous equivalence holds separately for preferential recruitment. If the two-positive-totals condition fails, no full homophily region exists.
* For EVERY state H (simplicity not required), Σ_v k(v)(1-z(v))=d₀. For EVERY simple H, including empty graphs, Hdom(H) iff m>0 and d₀>0 and d₁>0.
* For EVERY admissible D there EXISTS a compatible H. If its two sampled trait-degree totals are positive, there EXIST real L,U such that they give a full homophily region, its interval [L,U] is the smallest interval containing the defined value set, and for EVERY L',U' giving a full homophily region, L'=L,U'=U. Independently, if #B<#S, the analogous existence, smallest-interval assertion, and uniqueness hold for preferential recruitment.
* Here “smallest interval” means both that the value set is contained in [L,U], and that for EVERY order-connected subset I of R (whenever x,y∈I and x≤z≤y then z∈I), if the value set is contained in I, then [L,U]⊆I. I may be open, closed, unbounded or empty. Endpoints are attained because full regions require membership of L and U in the value set.
* For A as explicitly specified in the T14 section: {H:compatible with A and Hdom(H)}=∅, its homophily value set is ∅, every compatible H has preferential some 0, and A has full preferential region with L=U=0.

The docstring describes exact individual and whole-set domains, separately conditional existence of unique attained smallest containing intervals, the empty h-defined set in A, and the domain implications of the two indicated nonidentification hypotheses.

Junk conventions: raw h formulas use total real division, but their algebraic identities above have m>0. The separately asserted domain equivalence includes m>0, so empty graphs do not acquire a homophily value. Raw recruitment quotients have positive susceptible denominators whenever a summand exists, by the explicitly asserted inclusion of s(j). An empty average is excluded by Pdom. An empty compatible set is not being used to satisfy universal domain assertions vacuously: compatible-state existence is asserted for every admissible D. A has an empty defined h-value set, and is not assigned artificial extrema. IsLeast/IsGreatest require membership; SmallestValueInterval is conjoined with full regions, so L>U or empty intervals cannot manufacture a result. Natural degrees and counts cast exactly to reals, and natural subtraction used by N₀/spare/time has the meanings above. No log/sqrt/rpow, integral, `toReal`, default partial-function value, limsup/liminf, or sInf/sSup occurs.

## SAP.P012b.T16

Source: `Challenge/Part1.lean:33-35`; statement `Defs/Part4.lean:13-31`; cooling `Defs/Part2.lean:116-117`.

The only SAP function here is the real sequence C_{ε,T₁}:N→R defined by C(0)=T₁ and C(n)=1/(ε log(n+1)) for n≠0, where log is Mathlib's real logarithm. The proposition is the conjunction of:

1. For EVERY sequence T:N→R, if T(n)>0 for EVERY n and T is nondecreasing (n≤m implies T(n)≤T(m)), then T does NOT converge to 0 along natural n→∞.
2. For EVERY real ε there does NOT exist a real T such that T(ε log 1)=1. This tests existence of a genuine reciprocal at the printed initial index rather than accepting the real field's assigned value for 1/0.
3. For EVERY ε,T₁∈R, if ε>0 and 1/(ε log 2)≤T₁, then C(n)>0 for EVERY n; C is nonincreasing on N; C is strictly decreasing on {n∈N:n≥1}; and C(n)→0 as n→∞. The first-index bound is an explicit hypothesis, not a conclusion about arbitrary positive T₁.
4. For EVERY ε,D,t∈R with ε>0, t≥2, 0≤Dε≤1,
   exp(-D/(1/(ε log t)))=exp(-Dε log t)=1/t^(Dε), and 1/t≤exp(-D/(1/(ε log t))). The power is the real power.
5. For EVERY ε,D∈R with ε>0 and 0≤Dε≤1, and THEN EVERY real `first`, the real partial sums `first + Σ_{0≤n<N} exp(-D/(1/(ε log(n+2))))` tend to +∞ as natural N→∞. This is divergence to positive infinity of the partial sums, not a totalized infinite real sum. D is an arbitrary real obeying the inequalities; there is no finite state space, objective, communication depth construction, or theorem that any particular optimization problem supplies such a D.

The docstring calls the function a corrected logarithmic schedule and records both printed schedule defects, the conditional depth-series divergence, positivity, monotonicity and convergence.

Junk conventions: log 1=0 is deliberately exposed in item 2. No log 0 or negative log argument is needed anywhere. In the corrected sequence the n=0 branch avoids log 1; for n≥1, n+1≥2 and ε log(n+1)>0. The initial lower bound implies T₁>0. Items 4/5 use t≥2 or n+2≥2, so the nested reciprocal is strictly positive. Real powers have strictly positive base, so no negative-base or 0^0 convention matters even for Dε=0. D=0 is allowed and gives positive summands 1, consistent with divergence. Natural-to-real casts are exact, and range 0 gives a partial sum equal to `first` without affecting its limit. No sInf/sSup, limsup/liminf, Bochner integration, `toReal`, or default partial values occur.

## SAP.P012b.T17

Source: `Challenge/Part1.lean:37-44`; statement `Defs/WholeW1.lean:155-182`.

This is a conjunction of a general graph assertion and fixed examples. All graph, induced-state, and compatibility definitions are as fully expanded in the common section. In particular the assumptions are graph compatibility (traits ignored), and the first conclusion is induced compatibility with upper bounds, also ignoring traits.

* For EVERY data tuple D and state H, if D is admissible and H is graph compatible, then the induced state on V_S is simple, contains E_R, and has k_induced(s(i))≤d(i) for every i∈S. Also all three equivalences hold:
  1. (for EVERY i∈S, k_induced(s(i))=d(i)) iff V_H=V_S;
  2. (for EVERY i∈S and v∈V_H, {s(i),v}∈E_H implies v∈V_S) iff V_H=V_S;
  3. V_H=V_S iff BOTH V_H=V_induced and E_H=E_induced.
* For the fixed B data from T14 (two sampled vertices, both seeds, degrees 1, times 0 and 1, observed traits false,true), B is admissible. The common-neighbour state H_c has V={s(1),s(2),u(0,0)}, E={{s(1),u(0,0)},{s(2),u(0,0)}}, and Z identically false. The comparison H_e is the single-edge dyad with displayed traits false,true. BOTH are graph compatible with B. For EVERY i∈{1,2}, each original graph has degree 1 at s(i); the induced H_c has degree 0 there, and the induced H_e still has degree 1. The induced H_c has no edges, is induced-compatible (upper bounds), and is NOT graph compatible (exact degrees). The induced H_e IS graph compatible.

The docstring accurately distinguishes upper-bound and exact-degree graph compatibility, characterizes the latter by no unobserved vertices, and describes the common-neighbour versus seed-edge comparison. The general result and example do not assert the common-neighbour state's observed traits match B: they do not, and graph compatibility intentionally has no trait condition. All assertions in this theorem concern graphs/degrees.

Junk conventions: there are no numeric divisions, real analytic functions, integrals, infinities, extrema or limits in this closure. All degrees are finite natural cardinalities; the sole natural subtraction in the dependencies is S\B (finite-set difference), and the fixed times in B use max(i-1,0), giving 0,1 on the sample. The universal assertion permits empty S and empty graphs, but is not limited to them and has the explicit nonempty examples just described. Removal of all unobserved vertices is not confused with a default value: the induced edge set is filtered exactly by endpoint inclusion. Total trait functions outside the graph are retained but unused in the graph predicates.
