# Blind reading of the four declarations

This file was written before opening `claims.json` or `record.json`. Source locations below are in this workspace. I read every declaration listed in `closure.json`, including the generated declarations at line 0, whose elaborated bodies were printed by `scratch/ClosureBlind.lean` (output: `scratch/closure-blind.out`). The generated bodies supply numeral bounds, nonempty/probability instances, graph symmetry and absence of loops, finite-index inequalities, a sum/sigma pattern matcher, positivity of row sizes, or their divergence. They introduce no statistical hypotheses.

## SAP.P011a.T11

Source: `Challenge/Part1.lean:119–124`; statement: `Defs/Part6.lean:28–34`, `Defs/Part4.lean:238–252`, `Defs/Part5.lean:17–38`.

The theorem is a conjunction of assertions about one specified sequence of finite probability models, with no external hypotheses. For each natural row index k, set n=k+1, q=floor((n+1)/2), t=n/(2q), and p=floor((n+1)/2)-floor(n/2), where these floors and the subtraction are natural-number operations. The probability space is the pushforward of the uniform probability mass function on the finite, nonempty set of all maps u:{0,...,n-1}→{false,true}. Write s_i=1 when u_i=true and s_i=-1 otherwise. Thus the s_i are independent fair signs. The observation is Y_i=2·1_{i even}+s_i, the fixed coefficient is theta_i=t, and the weighted observation is X_i=tY_i. The true graph and the required-edge graph both have every Boolean adjacency entry false, and every degree cap is zero. A graph here is a symmetric Boolean matrix on Fin n with a false diagonal; its real adjacency matrix has entries 0 or 1 and its degree is its number of true entries in a row. Compatibility means inclusion of every required edge and satisfaction of each natural-number degree cap.

For an arbitrary real vector x on Fin n, let bar(x)=sum_i x_i/n, c_i(x)=x_i-bar(x), S(x)=sum_i c_i(x)^2/n. For this probability model define E[f] as the real Bochner integral of f against its pushforward probability measure, betaHat=bar(X), beta=E[betaHat], Var(f)=E[(f-E[f])^2], C_ij=E[(X_i-E[X_i])(X_j-E[X_j])], delta_i=E[X_i]-beta, v=sum_i C_ii/n, H=sum_i delta_i^2/n, and r(Y)=S(X)-v-H. The graph estimator is

V2(A,x)=S(x)/n·(1+sum_{i,j}a_ij/n).

The correlation-adjusted estimator is V2star(Y)=S(X)/n·(1+sum_{i,j}a_ij rho_ij/n), with rho_ij=0 if v=0 and rho_ij=C_ij/v otherwise. Here a_ij=0, so both estimators are S(X)/n. Set tau=n Var(betaHat). Every probability in the conclusion is the real value of the corresponding measure, i.e. ENNReal.toReal of its measure.

First conjunct (the fixed counterexample):

* This sequence satisfies `Scaling` with constants c1=2,c2=1,c3=1,c4=2. Expanded, all four constants are strictly positive; n is positive and tends to infinity; n is nondecreasing; for every k there is an injection Fin n→Fin(n+1) preserving the true graph's adjacency; the coordinate variables Y have a dependency graph; almost surely all |X_i-beta|≤2; all graph degrees are ≤1 as real numbers; n Var(betaHat)→1; and |theta_i|<2 for every row and coordinate. The dependency condition means that for every two disjoint finite sets of coordinates S,T with no graph edges between them, the vector-valued maps (Y_i)_{i∈S} and (Y_j)_{j∈T} are independent (`ProbabilityTheory.IndepFun`) under the row law. There is no condition coupling the probability spaces of different rows.
* The true graph is compatible with the required graph and caps in every row.
* For every k, C_ii=C_jj for every i,j, beta=1, and tau=t².
* For every real epsilon>0, P(|n V2(G,X)-tau-1|>epsilon)→0.
* P(|n V2(G,X)-tau|>1/2)→1 and P(|n V2(G,X)-tau|<3/2)→1.
* For every real epsilon>0, P(n(Var(betaHat)-V2(G,X))>epsilon)→0.

Second conjunct (finite moments), universally quantified over k, with n,m,t fixed as above:

* 1/2≤t≤1, beta=1, C_ii=t² and delta_i=t(2·1_{i even})-1 for every i.
* H=t²(1-p²/n²).
* For every sign assignment u,
  S(X)=t²+H+(2t/n)sum_i delta_i s_i-(t²/n²)(sum_i s_i)².
* E[r]=-t²/n and E[r²]=4t²H/n+t⁴(3/n²-2/n³).
* If n is even, then t=1, H=1, E[(n V2(G,X)-1-1)²]=4/n+3/n²-2/n³. With B=1-4(4/n+3/n²-2/n³), both P(|n V2(G,X)-1|>1/2) and P(|n V2(G,X)-1|<3/2) are ≥B.

Third conjunct: for every k and every real observation vector y (including vectors outside the law's finite support), V2star(y)=V2(G,theta·y), n V2(G,theta·y)=S(theta·y), and n V2star(y)-tau=H+r(y).

Junk-value check: real division is total and division by zero gives zero. All n in these assertions are ≥1 and q≥1, so n, n², n³ and 2q are nonzero. Although the underlying definitions also accept n=0 (giving t=0 and empty averages zero), no row here has n=0. The natural subtraction defining p is truncated; its minuend is at least its subtrahend, so p is the actual parity indicator 0 or 1. The branch rho=0 at v=0 is a convention, but v=t²>0 for this model, and zero adjacency makes the correlation factor immaterial in any case. Bochner integrals would return a default zero for nonintegrable integrands; here the laws have finite support and all integrands used are finite polynomial expressions, hence measurable and integrable. Probability is `toReal` of a measure, which would erase infinity, but all laws are probability measures. Finite sums over empty coordinate sets in the dependency condition are allowed and give constant empty vectors; this does not empty the row index type. There is no log, square root, real power, infimum, supremum, limsup or liminf in this statement. All limits are `Filter.Tendsto` along natural `atTop`, and all natural-to-real casts are exact.

Blind docstring reading: this is asserted to refute both the printed auxiliary step with a less-than event and the greater-than consistency reading, while leaving one-sided conservativeness intact. The two explicit limits distinguish those readings.

## SAP.P011a.T12

Source: `Challenge/Part1.lean:126–132`; statement and auxiliary definitions: `Defs/WholeW1.lean:13–70`, with shared quantities in `Defs/Part1.lean` and `Defs/Part2.lean`.

Quantifiers, in order: for every family F, then every four real constants c1,c2,c3,c4, if `WholeScaling F c1 c2 c3 c4`, and if every row is homoskedastic, the finite conclusions hold for every row k, and an asymptotic conservativeness conclusion holds for the family. A family consists of a natural-valued sequence n_k>0 tending to infinity and, for each k, a probability measure on the finite-dimensional real observation space R^{n_k}, fixed real coefficients theta_i, two symmetric loopless Boolean graphs G,R, and natural caps d_i. The graphs R and caps have no role in the hypotheses or conclusions here.

For a row write X_i=theta_i Y_i, bar(x)=sum_i x_i/n, S(x)=sum_i(x_i-bar(x))²/n, betaHat=bar(X), beta=E[betaHat], Var(f)=E[(f-E[f])²], C_ij=E[(X_i-E[X_i])(X_j-E[X_j])], delta_i=E[X_i]-beta, v=sum_i C_ii/n, H=sum_i delta_i²/n, U(Y)=sum_i(X_i-beta)²/n, r(Y)=S(X)-v-H, and g=1+sum_{i,j}a_ij/n, where a is the 0/1 adjacency matrix of G. E is the real Bochner integral under the row's probability measure. V2(G,x)=S(x)g/n. Homoskedastic means C_ii=C_jj for all i,j; this is equality of weighted coordinate variances.

The hypothesis `WholeScaling` requires: c1,c2,c3,c4>0; every row's unweighted coordinates Y have G as a dependency graph; almost surely all |X_i-beta|≤c1; every degree of G, cast to R, is ≤c2; n_k Var(betaHat_k)→c3; and |theta_i|<c4 in every row. A dependency graph means independence of the vectors on any disjoint coordinate sets with no graph edges between them, expressed by Mathlib `IndepFun`. It imposes no relationship between row probability spaces or graphs. In particular it does not require nesting, monotone row sizes, equal unit means, positive variance in every row, or a limit for v or H.

The complete finite conclusion, for every k, is the following conjunction (n=n_k):

1. For every real y, S(theta·y)=U(y)-(betaHat(y)-beta)².
2. E[U]=v+H; Var(U)≤(1+c2)c1⁴/n; E[(betaHat-beta)²]≤(1+c2)c1²/n; E[(betaHat-beta)⁴]≤(1+c2)c1⁴/n; E[r²]≤4(1+c2)c1⁴/n.
3. For every i, v=C_ii; H≥0; n Var(betaHat)=sum_{i,j}C_ij/n≤v g; and 1≤g≤1+c2.
4. For every real y,
   n V2(G,theta·y)=g S(theta·y),
   n Var(betaHat)-n V2(G,theta·y)≤g(v-S(theta·y))=-g(H+r(y))≤(1+c2)|r(y)|.
5. For every real epsilon>0,
   P(n Var(betaHat)-n V2(G,X)>epsilon)≤4(1+c2)³c1⁴/(n epsilon²).

The final conclusion is: for every real epsilon>0, P(n_k(Var(betaHat_k)-V2(G_k,X_k))>epsilon) tends to zero. Probabilities are the row measures evaluated on the specified sets and converted from extended nonnegative reals to reals.

Junk-value check: n_k>0 excludes every sample-size division by zero, and epsilon>0 excludes zero in the tail denominator. There is no division by v, so zero early common variances are legitimate. All integrands are measurable polynomial functions of finitely many coordinates. The almost-sure uniform bound on X_i-beta and finite probability law imply integrability of every weighted quantity and its powers, so the Bochner default for nonintegrable functions is not used, including if an unweighted coordinate with theta_i=0 lacks moments. Probability measures exclude infinity in `toReal`. No truncated subtraction is used; `r=S-v-H` is real subtraction. There are no partial inverses, empty-index defaults affecting a conclusion, logarithms, roots, real powers, infima/suprema or liminf/limsup. The definition has no hidden positivity condition on v or H. Row-size and degree casts are exact.

Blind docstring reading: the theorem asserts all six finite moment assertions, the covariance/scalar comparison chain, the explicit finite tail bound, and one-sided conservativeness under the two named assumptions. It specifically allows unequal unit means and varying or initially zero common variance.

## SAP.P011a.T13

Source: `Challenge/Part1.lean:134–145`; statement: `Defs/Part6.lean:38`, `Defs/Part5.lean:61–101`; definitions: `Defs/Part2.lean:164–219`, `Defs/Part3.lean:29–39`.

An edge on n vertices is an ordered pair (i,j) of elements of Fin n together with a proof i<j; thus each undirected nonloop edge occurs once. A problem P consists of a finite set F of forced edges, natural caps b_i, and a rational weight w_e for every edge. For a finite edge set S let deg_S(i) be the cardinality of the subset of S incident to i, and W(S)=sum_{e∈S}w_e. Feasibility is F⊆S and deg_S(i)≤b_i for every i. Define c_i=min(b_i,n-1)-deg_F(i), using natural truncated subtraction, and O=all edges minus F. Let L be the finite-set least common multiple of the positive rational denominators of w_e for e∈O. For any edge set z_e=(L as integer)·num(w_e)/den(w_e), with integer division; let M=1+max_{e∈O}|z_e|, taking this maximum in naturals (empty maximum zero).

The gadget has c_i distinct slot vertices for each original vertex i, and two further vertices (e,false),(e,true) for each e∈O. Its edge type contains one internal edge joining (e,false) and (e,true) for every e∈O, of weight 4M; and, for each side of each e, one edge to each slot of that endpoint, of weight 2M+z_e. False selects the smaller endpoint, true the larger. A matching is a finite set of gadget edges such that any two distinct edges have all four endpoint inequalities, so they share no vertex. Decoding D(J) selects an optional original edge exactly when J includes a slot edge on each of its two sides. This need not mean that every gadget matching is optimal or complete.

The first conjunct quantifies over a natural n with 0<n, and then every problem P. It asserts:

* There exists a feasible S if and only if deg_F(i)≤min(b_i,n-1) for every i.
* If those forced-edge inequalities hold, then for every S, S is feasible if and only if there exists a finite edge set T with T⊆O, deg_T(i)≤c_i for every i, and S=F∪T.
* Under the same condition, for every finite gadget edge set J, if J is a matching and every matching J' has weight ≤weight(J), then F∪D(J) is feasible, every feasible S satisfies W(S)≤W(F∪D(J)), and
  W(F∪D(J))=W(F)+(weight(J)-4M|O|)/(2L), with the integer numerator cast to rationals.
* Regardless of the forced-edge inequalities, 2|O|+sum_i c_i≤2n(n-1) and |O|+sum_{e=(i,j)∈O}(c_i+c_j)≤|O|(2n-1). These are inequalities of natural numbers.

The second conjunct quantifies over every natural n (including zero) and problem P, and asserts exact finite-type cardinalities:

|gadget vertices|=2|O|+sum_i c_i,
|gadget edges|=|O|+sum_{e=(i,j)∈O}(c_i+c_j).

The third conjunct fixes two four-vertex problems, indexed by a Boolean `second`. Their weight vector is h=(3/2,1/2,-1/2,-3/2), and w_(i,j)=h_i h_j. For second=false: F={(0,2),(2,3)}, caps=(2,1,2,7), proposed solution F∪{(0,1)}. For second=true: F={(0,2)}, all caps 1, proposed solution F. It asserts, conjunctively: remaining caps are respectively (1,1,0,2) and (0,1,0,1); for every choice of `second`, L=4 and M=10; optional-edge counts are respectively 4 and 5; for each choice, the proposed solution is feasible, has objective respectively 3/4 and -3/4, and dominates every feasible T; for each choice there exists a genuine maximum-weight gadget matching with weight respectively 166 and 200.

There is no general existence quantifier for a maximum gadget matching, no separately defined optimum value, no explicit uniqueness statement for T, no equivalence to a separately defined paper program, and no algorithm, running-time, bit-length or complexity-class assertion. The universal maximum-matching implication is supplemented by actual existence in the two named instances.

Junk-value check: min(b_i,n-1) uses truncated n-1, and c_i uses truncated subtraction. For feasible forced data this is the actual residual capacity; for infeasible data the exact cardinality and size-bound assertions still use saturated residual capacities, while decoding correctness has a feasibility antecedent. The n=0 case only occurs in the exact-count conjunct and has empty original, slot and gadget types, cardinality zero. Integer division is total but rational denominators are positive, and L is positive (the lcm of an empty set is 1); for optional edges every denominator divides L, making z_e exactly the cleared weight. A forced edge's denominator need not divide L, but its z_e is never used for gadget weights or the maximum. Empty optional sets have L=1 and M=1, an empty decoded set and empty edge sums, so the objective-recovery denominator 2L is nonzero. Natural `sup` of the empty finite set is explicitly zero, not an unbounded real supremum. All integer/rational casts preserve exact values. There are no measures, analytic limits, logs, roots, real powers, or partial function defaults here. Gadget endpoints are well-typed and no gadget edge is a self-loop.

Blind docstring reading: this is explicitly labelled a restriction. Its list of retained finite feasibility/decomposition, supplied-optimum decoding, counts, combinatorial bounds and attained instances agrees with the forms above; it explicitly disclaims the missing program equivalences, uniqueness, optimum identities, generic optimum existence and computational conclusions.

## SAP.P011a.T14

Source: `Challenge/Part1.lean:147–152`; statement: `Defs/Part6.lean:40–41`, `Defs/Part5.lean:103–130,197–221`; definitions: `Defs/Part1.lean:16–47`, `Defs/Part2.lean:221–242`.

For a natural n, an undirected edge e=(i,j) is represented once with i<j. A graph is a symmetric, false-diagonal Boolean adjacency matrix. `fromUpper` maps a Boolean edge function b to the symmetric graph with b_(i,j) in its two corresponding entries and false on the diagonal; `toUpper` reads a graph on i<j. Required-edge graph R and natural caps d define compatibility by required-edge inclusion and every graph degree ≤d_i.

For a real edge vector a, relaxed feasibility means: for every e, 0≤a_e≤1; every required edge has a_e=1; for every vertex i, sum_{e incident to i}a_e≤d_i (cast to reals). For real weights w, the relaxed objective is sum_e w_e a_e. For Boolean b, its objective is sum_e(if b_e then w_e else 0). For x∈R^n set bar(x)=sum_i x_i/n, c_i=x_i-bar(x), and S(x)=sum_i c_i²/n. With a graph's real 0/1 adjacency a_ij,

V1(A,x)=[sum_i c_i²+sum_{i,j}a_ij c_i c_j]/n²,
V2(A,x)=S(x)/n·[1+sum_{i,j}a_ij/n].

The first conjunct has the ordered universal quantifiers: n, proof n>0, R, d, w:Edge(n)→R, U:R. It assumes every relaxed-feasible a has sum_e w_e a_e≤U. It concludes, conjunctively:

* For every Boolean b, compatibility of fromUpper(b) implies its Boolean objective ≤U.
* For every x and Boolean b, if fromUpper(b) is compatible and w_(i,j)=c_i(x)c_j(x) for every edge, then V1(fromUpper(b),x)≤[n S(x)+2U]/n².
* If w_e=1 for every edge, then for every x and compatible Boolean b, V2(fromUpper(b),x)≤S(x)/n·(1+2U/n).

This is conditional on a certified global upper bound. It does not require U to be attained or require an algorithm that computes it.

The second conjunct contains two explicit optimality-gap examples. For n=6 take x=(1,1,1,-1,-1,-1), R empty, all caps 1, w_(i,j)=x_i x_j, and f_(i,j)=1/2 when x_i=x_j, zero otherwise. It asserts that f is relaxed-feasible, its objective is 3, every relaxed-feasible a has objective ≤3, there exists a compatible Boolean b of objective 2 with V1=5/18, every compatible Boolean b has objective ≤2, and (6+2·3)/6²=1/3. For n=3, R empty, all caps 1 and all weights 1, the all-halves vector is relaxed-feasible of objective 3/2, every relaxed-feasible a has objective ≤3/2, there exists a compatible graph with ordered adjacency sum 2, and every compatible graph has ordered adjacency sum ≤2 (thus at most one undirected edge).

The third conjunct repeats the six-unit values with the program's doubled edge objective: bar(x)=0, S(x)=1, 2 times the specified relaxed objective is 6 and is a global upper bound, there exists a compatible Boolean b with doubled objective 4 and V1=5/18 and no compatible Boolean vector exceeds 4, and the resulting relaxed variance bound is 1/3. It likewise asserts the triangle's doubled relaxed objective 3 and its global upper bound. Finally it asserts that there exist some relaxed-feasible a0 and some compatible Boolean b on the six-unit problem for which objective(a0)<objective(b). This illustrates that a merely feasible fractional value need not be an upper bound.

The fourth conjunct names `sixIntegerEdges`: b_(i,j)=true exactly for (0,1) or (3,4). It asserts its compatibility with empty R and all caps 1, its objective 2 for the six-unit weights, and V1=5/18.

Junk-value check: every variance and mean division in the general result has n>0; the concrete n=6 and n=3 denominators and rational fractions are nonzero. Empty original edge types at n=1 give empty sums, but a compatible Boolean vector then exists and forces any certified U≥0. The general conditional statement does allow infeasible constraints, in which case its bound antecedent and conclusions about compatible graphs can all be vacuous; this does not empty the entire theorem because it also covers feasible data and includes explicit feasible, nonzero-gap witnesses. No subtraction is on naturals in the closure of this statement. No probabilistic integrals, `toReal`, log, root, real power, real extrema or liminf/limsup are involved. Sum, subtype and Bool defaults only implement finite simple graphs, and the diagonal false branch explicitly excludes loops. The natural capacities are cast exactly to reals.

Blind docstring reading: the theorem gives the transfer of certified relaxed upper bounds to integer edge objectives and the two variance formulas, with strict relaxation gaps at the six-unit and triangle instances. It does not claim a fractional optimizer is unique; the strict gap means every optimizer in each example is nonintegral.
