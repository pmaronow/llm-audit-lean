# Blind reading of the P030 Challenge

This document was written from `SAP/P030/Defs.lean`, every `Defs/Part*.lean`, and the Challenge files, before opening `claims.json` or `record.json`. The Challenge contains fifteen closed theorem propositions. A conjunction below asserts every listed component; a numbered component is not an additional hypothesis. Notation introduced here is expanded explicitly and is shared between readings.

## Underlying objects and operations

For a natural number (N), the unit set is (I_N=\{0,\ldots,N-1\}\), Lean's `Fin N`. An assignment is an arbitrary function (z:I_N\to\{\mathrm{false},\mathrm{true}\}\). Its numerical treatment (z_i^*) is 1 for true and 0 for false. An assignment set Ω is a finite set of such functions, without repetitions. A fixed-unit indicator (S:I_N\to\mathrm{Bool}\) determines (F=\{i:S_i=\mathrm{true}\}\). The conditional assignment set is

\[
C(\Omega,S,a)=\{z\in\Omega:\ \forall i\in I_N,\ S_i=\mathrm{true}\implies z_i=a_i\}.
\]

Potential outcomes are arbitrary real-valued functions (Y(i,z)) on all units and all assignments. The three null predicates expand as follows:

* No effects on Ω: for every unit (i), every (z\in\Omega), and every (z'\in\Omega), (Y(i,z)=Y(i,z')).
* No interference on Ω: for every (i,z\in\Omega,z'\in\Omega), if (z_i=z'_i), then (Y(i,z)=Y(i,z')). Here the quantifiers mean (i\in I_N), followed by the two assignments and their membership hypotheses.
* Fixed-outcome null on (C): for every unit (i) with (S_i=\mathrm{true}), and then every (z,z'\in C), (Y(i,z)=Y(i,z')).

The fixed-outcome vector is (y_F(z)=(Y(i,z))_{i\in F}). An arbitrary statistic function (g:\mathbb R^F\times\{\mathrm{Bool}\}^{I_N}\to\mathbb R) gives the actual statistic (t(z)=g(y_F(z),z)) and reference statistic (r(a,z)=g(y_F(a),z)). There is no assumption that (g) is constant, continuous, or a correlation.

A finite law μ on any type (A) consists of a finite set (K\subseteq A), real masses (m(z)) defined on all (A), nonnegative for (z\in K), and \(\sum_{z\in K}m(z)=1\). Masses outside (K) are ignored and need not be nonnegative. Write

\[
P_\mu(E)=\sum_{z\in K}\mathbf1_E(z)m(z),\quad
L_f(x)=P_\mu(f\le x),\quad U_f(x)=P_\mu(f\ge x).
\]

For a finite set (K), (P_K(E)=|\{z\in K:E(z)\}|/|K|), where both cardinalities are cast to real numbers **before** division. Without a nonemptiness condition this definition would be Lean's total real division, which gives zero at denominator zero. The uniform law on (K) has this support and mass (1/|K|), and its constructor requires (K\ne\varnothing).

For real α and real p-values define:

\[
R_{\rm print}(\alpha,p)\iff p<\alpha/2\ \lor\ 1-\alpha/2<p,
\]
\[
R_{\rm corr}(\alpha,p_L,p_U)\iff p_L<\alpha/2\ \lor\ p_U<\alpha/2,
\qquad p_2(p_L,p_U)=\min(1,2\min(p_L,p_U)).
\]

All tail comparisons defining (L,U) are inclusive, while both rejection rules use strict inequalities.

For (a:I_n\to\mathbb R), define the midrank and centered midrank by

\[
q_a(k)=|\{l:a_l<a_k\}|+(|\{l:a_l=a_k\}|+1)/2,
\qquad v_a(k)=q_a(k)-(n+1)/2.
\]

Let (Q(a)=\sum_k v_a(k)^2) and (B(a,b)=\sum_k v_a(k)v_b(k)). Define

\[
\rho(a,b)=\frac{B(a,b)}{\sqrt{Q(a)Q(b)}},\qquad
\operatorname{Cov}_m(a,b)=B(a,b)/m,
\qquad \widetilde\rho_m(a,b)=\frac{B(a,b)/m}{(Q(a)/m)(Q(b)/m)}.
\]

These formulas are total Lean real expressions. In particular, zero denominators give zero; the square root is Mathlib's nonnegative square root (zero on negative arguments). A vector is nonconstant exactly when there exist (i,j\in I_n) with (a_i\ne a_j).

Given real positions (x_i), let (V(S,z)=\{j:S_j=\mathrm{false},z_j=\mathrm{true}\}\). The nearest distance (D(x,S,z,i)) is the minimum of |x_i-x_j| over (j\in V(S,z)) when (V(S,z)\ne\varnothing), and is defined to be zero otherwise. Mathlib's `Finset.inf'` is the finite nonempty infimum, hence the ordinary minimum here. This is distance to treated **variant** units, not to all treated units.

Finite sets, filtering, image, erasing an element, cardinality, and finite sums have their ordinary Mathlib meanings. An image removes duplicate values. The Mathlib sources inspected include `Data/Finset/{Filter,Image,Erase,Card}.lean`, `Data/Finset/Lattice/Fold.lean`, `Order/Bounds/Defs.lean`, `Order/Filter/Defs.lean`, `Topology/Defs/Filter.lean`, and `Analysis/Real/Sqrt.lean`. `IsGreatest E b` means (b\in E) and ∀(e\in E), (e\le b). `Tendsto` from `nhdsWithin 0 (Ioi 0)` to `nhds A` means the real right-hand limit as (d\to0^+) is (A). Mathlib's real exponential is the usual real exponential.

## Fully specified examples shared by the theorems

### Five-unit design

The positions are (x=(0,4,8,-1,-2)); (F=\{0,1,2\}). Assignment (z^a), for (a\in I_2), treats only unit (a+3); Ω₅={z⁰,z¹}. On **every** assignment, (Y(i,z)=(0,1,2,0,0)_i). The fixed-outcome vector (y=(0,1,2)) is taken from units 0,1,2. Let (d^a=(D(x,S,z^a,i))_{i=0,1,2}) and (s_a=\rho(d^a,y)).

### Ten-unit and six-row designs

Positions are (x_i=i+1) for (i\in I_{10}), and (F=\{0,7,8,9\}), in that order. Assignment (e^j) treats only unit (j\in I_{10}); Ω₁₀ is the set of all ten such assignments. The six rows are indexed by (r\in I_6), with assignment (b^r=e^{r+1}); (K=\{b^r:r\in I_6\}). The observed assignment is (e^6=b^5). The assignment-independent null schedule is

\[
Y_0(i,z)=(1,2,2,2,2,3,2,3,2,1)_i.
\]

Let (y=(Y_0(i,e^6))_{i=0,7,8,9}), (d^r=(D(x,S,b^r,i))_{i=0,7,8,9}), and (h_r=\rho(d^r,y)). The statistic function (g_{10}(u,z)) computes ρ between the four distances (D(x,S,z,i)) and the four entries (u_i), ordered as 0,7,8,9.

The block called **Design** in the readings below is exactly this conjunction:

1. |Ω₁₀|=10, |K|=6, and (C(\Omega_{10},S,e^6)=K).
2. (P_{\Omega_{10}}(\forall i\in F,z_i=e^6_i)=3/5).
3. For every (j\in I_{10}), (e^j) treats exactly one unit and (P_{\Omega_{10}}(z=e^j)=1/10).
4. For every (r\in I_6), (P_K(z=b^r)=1/6), and this equals (P_{\Omega_{10}}(z=b^r)/P_{\Omega_{10}}(\forall i\in F,z_i=e^6_i)).

The block called **Numerics** is exactly this conjunction:

1. (y=(1,3,2,1)).
2. The ordered rows (d^0,\ldots,d^5) are
   ((1,6,7,8),(2,5,6,7),(3,4,5,6),(4,3,4,5),(5,2,3,4),(6,1,2,3)).
3. ((h_0,\ldots,h_5)=(-1/\sqrt{90},-1/\sqrt{90},-1/\sqrt{90},-5/6,-3/\sqrt{10},-3/\sqrt{10})).
4. For every row (r), (V(S,b^r)\ne\varnothing) and (Q(d^r)>0); also (Q(y)=9/2).
5. (-3/\sqrt{10}<-5/6<-1/\sqrt{90}<0), and every (h_r<0).
6. |−1/√90+0.105|<0.0005, |−5/6+0.833|<0.0005, and |−3/√10+0.949|<0.0005.

The block called **Weak** asserts all of:

* For every (i,j\in I_3), ((1,2,3)_i\le(1,2,3)_j) implies ((0,0,1)_i\le(0,0,1)_j).
* (Q(1,2,3)=2), (Q(0,0,1)=3/2), and ρ(( (1,2,3),(0,0,1))=\sqrt3/2).
* √3/2 is neither 1 nor −1.

The block called **Null-varying** asserts all of:

* (Y_0) has no effects and no interference on Ω₁₀.
* (C(\Omega_{10},S,e^6)=K), and (Y_0) satisfies the fixed-outcome null on (K).
* Both (b^0) and (b^3) belong to (K).
* **Numerics** holds, and the actual statistics (g_{10}(y_F(b^0),b^0)) and (g_{10}(y_F(b^3),b^3)) are unequal.

## SAP.P030.T1

This is a closed conjunction about the five-unit design, with no external hypotheses:

1. For every unit (i), followed by every two assignments (z,z') (not just those in Ω₅), (Y(i,z)=Y(i,z')). No effects and no interference also hold on Ω₅.
2. |Ω₅|=2, (C(\Omega_5,S,z^0)=\Omega_5), and for each (a\in I_2), (P_{\Omega_5}(z=z^a)=1/2).
3. For every (z\in\Omega_5), every fixed unit is untreated. Each (z^a) treats exactly one unit.
4. (y=(0,1,2)), (d^0=(1,5,9)), (d^1=(2,6,10)); (q_y=(1,2,3)), (v_y=(-1,0,1)). For every (a\in I_2), (q_{d^a}=(1,2,3)), (v_{d^a}=(-1,0,1)), (B(d^a,y)=2), (Q(d^a)=Q(y)=2), and (s_a=1).
5. For every (a), both rank-square sums are positive and (V(S,z^a)) is nonempty.
6. For every (a\in I_2), the uniform probabilities over (b\in I_2) of (s_b\le s_a) and (s_a\le s_b) are both 1.
7. For every real α, if (0<\alpha<1), the uniform probability over (a\in I_2) that (R_{\rm print}(\alpha,P_{I_2}(s_b\le s_a))) holds is 1; the probability of (R_{\rm corr}(\alpha,P_{I_2}(s_b\le s_a),P_{I_2}(s_a\le s_b))) is 0; and α<1.
8. ((1/20)/2=1/40), (1-(1/20)/2=39/40<1), and (R_{\rm print}(1/20,1)) holds.

## SAP.P030.T2

A closed conjunction about the ten-unit null schedule:

1. For every (i\in I_{10}), followed by every two assignments (z,z'), (Y_0(i,z)=Y_0(i,z')). No effects and no interference hold on Ω₁₀.
2. **Design** and **Numerics** both hold.
3. For every (r\in I_6), the actual statistic at (b^r) is (h_r). For every (r,s\in I_6), the reference statistic using observation (b^r) and assignment (b^s) is (h_s).
4. For each (r\in I_6), (P_{I_6}(h_s\le h_r)=(1,1,1,1/2,1/3,1/3)_r), and (P_{I_6}(h_r\le h_s)=(1/2,1/2,1/2,2/3,1,1)_r).
5. For every real α with (0<\alpha\le2/3), sample (z\in K) uniformly and form (p_L(z)=P_K(r(z,w)\le t(z))), (p_U(z)=P_K(t(z)\le r(z,w))), using (Y_0,g_{10}). Then (P_K(R_{\rm print}(\alpha,p_L(z)))=1/2) and (P_K(R_{\rm corr}(\alpha,p_L(z),p_U(z)))=0).
6. (1/20<1/2).

## SAP.P030.T3

The first conjunct universally quantifies, in order, an arbitrary type (A), a finite law μ on (A), and (f:A\to\mathbb R). It asserts:

1. For every real (x), (U_f(x)=1-L_f(x)+P_\mu(f=x)), and (1-L_f(x)\le U_f(x)).
2. For every real (u), assuming (0\le u\le1), both (P_\mu(L_f(f(z))\le u)\le u) and (P_\mu(U_f(f(z))\le u)\le u).
3. For every real α, assuming (0<\alpha<1), all of the following hold:
   * The probability of (R_{\rm corr}(\alpha,L_f(f(z)),U_f(f(z)))) is at most (P_\mu(L_f(f(z))\le\alpha/2)+P_\mu(U_f(f(z))\le\alpha/2)); this sum is at most α; the corrected rejection probability is at most α.
   * For every real (x), (U_f(x)<\alpha/2\implies1-\alpha/2<L_f(x)).
   * For every real (x), (R_{\rm corr}(\alpha,L_f(x),U_f(x))\implies R_{\rm print}(\alpha,L_f(x))).
   * For every two **arbitrary real numbers** (p_L,p_U), (p_2(p_L,p_U)\le\alpha\iff p_L\le\alpha/2\lor p_U\le\alpha/2).
   * (P_\mu(p_2(L_f(f(z)),U_f(f(z)))\le\alpha)\le\alpha).

The second conjunct is the entire five-unit assertion in **T1**, including its strict difference between printed and corrected rejection probabilities. There is no hypothesis connecting this particular example to the arbitrary μ in the first conjunct.

## SAP.P030.T4

The negation of this precise universal statement:

For every (N\in\mathbb N), assignment set Ω, indicator (S), and assignment (a), if (C=C(\Omega,S,a)) is nonempty, then for every outcome function (Y) and statistic function (g), if (Y) has no interference on Ω, then for every real α with (0\le\alpha\le1),

\[
P_C\bigl(R_{\rm print}(\alpha,
 P_C(r(z,w)\le t(z)))\bigr)\le\alpha.
\]

Here (z) is the outer random assignment and (w) the inner one; (r(z,w)=g(y_F(z),w)), (t(z)=g(y_F(z),z)). The negated universal does not require (a\in\Omega), only nonempty (C). In classical mathematics this negation asserts the existence of such (N,\Omega,S,a,Y,g,\alpha), satisfying those hypotheses, for which the displayed probability exceeds α. The theorem itself has no hypotheses.

## SAP.P030.T5

A closed conjunction:

1. For every unit (i\in I_{10}) and then every two assignments (z,z'), (Y_0(i,z)=Y_0(i,z')).
2. **Design**, **Numerics**, and **Null-varying** hold in their entirety.
3. For every row (r\in I_6), the actual statistic using (Y_0,g_{10}) at (b^r) equals (h_r).
4. (P_{I_6}(h_s\le h_5)=1/3).
5. For every type (A) and finite set (K'\subseteq A), if (K'\ne\varnothing), then for every (t':A\to\mathbb R), if ∀(z,z'\in K'), (t'(z)=t'(z')), then for every (z\in K'), (P_{K'}(t'(w)\le t'(z))=1).

## SAP.P030.T6

The first conjunct universally quantifies (N,\Omega,S,\mathrm{obs}) in that order, assumes “obs∈Ω”, and then universally quantifies (Y,g). With (C=C(\Omega,S,\mathrm{obs})), it asserts:

1. No interference on Ω implies the fixed-outcome null on (C).
2. If the fixed-outcome null on (C) holds, then: for every (z\in C), (y_F(z)=y_F(\mathrm{obs})); for every (z\in C), (r(\mathrm{obs},z)=t(z)); and for every real (x), (P_C(r(\mathrm{obs},z)\le x)=P_C(t(z)\le x)).

The second conjunct is **Null-varying**, including the explicit ten-unit schedule, nonempty conditional design, exact six correlations and positive variances, and two unequal actual statistics despite fixed outcomes. No constancy of the statistic is assumed in the universal part.

## SAP.P030.T7

For every (N,\Omega,S,\mathrm{obs}), in that order, assume obs∈Ω and put (C=C(\Omega,S,\mathrm{obs})). The following conjunction holds:

1. For every (z\in C), every (z'\in C), and every (i\in I_N), (S_i=\mathrm{true}\implies z_i=z'_i).
2. For every (Y), no interference on Ω implies the fixed-outcome null on (C).
3. For every (Y), if there exists a unit (i) with (S_i=\mathrm{true}), then assignments (z,z'\in C), with (Y(i,z)\ne Y(i,z')), then no interference on Ω is false.
4. For every two real-valued unit functions (c,\tau:I_N\to\mathbb R), the schedule (Y(i,z)=c_i+\tau_i z_i^*) has both no interference on Ω and the fixed-outcome null on (C).
5. For every (Y), no effects on Ω implies no interference on Ω.

## SAP.P030.T8

A closed conjunction:

1. **Numerics** holds.
2. For every (r\in I_6), ~ρ₄((d^r,y)=(-4/45,-4/45,-4/45,-20/27,-4/5,-4/5)_r).
3. For every (r\in I_6), ~ρ₃((d^r,y)=(-1/15,-1/15,-1/15,-5/9,-3/5,-3/5)_r).
4. (-4/5\ne-3/\sqrt{10}), (-3/5\ne-3/\sqrt{10}), and (-4/5\ne-3/5).
5. Put (a=(1,2,1,1)), (b=(0,2,1,1)). Then (Q(a)>0,Q(b)>0), ρ((a,y)=\sqrt6/3), ρ((b,y)=5/6), ~ρ₄((a,y)=8/9), ~ρ₄((b,y)=20/27), √6/3<5/6, and 20/27<8/9.
6. **Weak** holds, with its monotonicity implication, rank-square sums, correlation √3/2, and inequality to both signs of one.

## SAP.P030.T9

The first conjunct universally quantifies a natural number (n), assumes (2\le n), then universally quantifies (a,b:I_n\to\mathbb R), and assumes (a) nonconstant and (b) nonconstant, in that order. It asserts:

1. \(\sum_k q_a(k)=n(n+1)/2\) and \(\sum_k q_b(k)=n(n+1)/2\).
2. (Q(a)>0,Q(b)>0).
3. For every real (m>0), ρ((a,b)=\operatorname{Cov}_m(a,b)/\sqrt{(Q(a)/m)(Q(b)/m)}).
4. (-1\le\rho(a,b)\le1).
5. |ρ((a,b))|=1 iff there exists a real (c\ne0) such that, for every (k), (v_a(k)=c v_b(k)).
6. For every real (c\ne0), if (v_a=c v_b), then (c>0\implies\rho(a,b)=1) and (c<0\implies\rho(a,b)=-1).
7. If for all (k,l), (a_k<a_l\iff b_k<b_l), then the full midrank vectors are equal and ρ((a,b)=1).
8. If for all (k,l), (a_k<a_l\iff b_l<b_k), then (q_a(k)=n+1-q_b(k)) for every (k), and ρ((a,b)=-1).

The remaining conjuncts are **Weak** and **Numerics**, with all components stated above. They do not depend on the universally quantified (n,a,b).

## SAP.P030.T10

A conjunction of six statements:

1. For every natural (N), real-valued matrix (d:I_N\times I_N\to\mathbb R), assignment (z), and unit (i), if (d_{ii}=0), then ((1-\mathbf1_{i=i})z_i^*=0), (((3/2)d_{ii})^2=0), and the **partial** quotient of this numerator by this denominator has no real value (`none`). The partial quotient returns `none` iff its denominator is zero, and otherwise returns `some (numerator/denominator)`.
2. For every (N,d), if for every (i\ne j), (d_{ij}>0), then all (((3/2)d_{ij})^2\ne0) for (j\in I_N\setminus\{i\}). For every assignment (z) and unit (i), the indirect exposure is the sum \(\sum_{j\ne i}z_j^* f(d_{ij})\), and the spatial exposure is \(\sum_{j\ne i}f(d_{ij})\), where (f(d)=1/((3/2)d)^2). These latter identities expand the definitions; no symmetry or triangle inequality is imposed on the matrix.
3. For every real (d>0), (f(d)=4/(9d^2)), (f(2d)/f(d)=1/4), (f(2/3)=1), (f(1)=4/9), and (f(2)=1/9).
4. There do not exist real (A,c) such that for every real (d>0), (f(d)=A\exp(-cd)).
5. For every real (B,d), assuming (B>0,d>0,d<2/(3\sqrt B)), one has (B<f(d)).
6. For every real (A,c), \(\lim_{d\to0^+} A\exp(-cd)=A\).

No global assertion evaluates the indirect/spatial sums on a zero off-diagonal distance. The partial diagonal quotient is distinct from Lean's total real division.

## SAP.P030.T11

A closed conjunction:

1. For every type (A) with decidable equality and every four finite sets (U,F,C,T\subseteq A), assume, in order, (U=(F\cup C)\cup T), (F\cap C=\varnothing), (F\cap T=\varnothing), and (C\cap T=\varnothing). Then |U|=|F|+|C|+|T|, and it is false that simultaneously |U|=344056, |F|=114629, |C|=191228, |T|=38198.
2. (114629+191228+38198=344055\ne344056), and (344056-191228-38198=114630) in natural-number arithmetic (subtraction truncates, but both subtractions here are nonnegative).
3. For every natural quadruple (N,F,C,T), the conjunction “(N=F+C+T) and exactly one of the four displayed original entries differs while the other three are retained” is equivalent to membership in this explicit list of quadruples:
   ((344055,114629,191228,38198)),
   ((344056,114630,191228,38198)),
   ((344056,114629,191229,38198)),
   ((344056,114629,191228,38199)).
   Precisely, the changed-entry condition is the disjunction of (N\ne344056) with all three group counts original, or (F\ne114629) with the other three entries original, or (C\ne191228) with the other three original, or (T\ne38198) with the other three original.

## SAP.P030.T12

Universally quantify, in order: (N), Ω, (S), an assignment (a), a proof that (C=C(\Omega,S,a)\ne\varnothing), (Y), and (g). Assume **either** no interference on Ω **or** the fixed-outcome null on (C). Let μ be the uniform law on (C), and let (t(z)=g(y_F(z),z)). Then:

1. For every (z\in C), followed by every (w\in C), (g(y_F(z),w)=t(w)).
2. For every (z\in C), (L_t(t(z))=P_C(t(w)\le t(z))).
3. For every real (u) with (0\le u\le1), (P_\mu(L_t(t(z))\le u)\le u).
4. For every (z\in C), (P_\mu(L_t(t(w))\le L_t(t(z)))=L_t(t(z))).
5. For **every real** (u) without a range condition, (P_\mu(L_t(t(z))\le u)) is a greatest element of
   \(\{0\}\cup\{p:\exists z\in C,\ p=L_t(t(z))\ \text{and}\ p\le u\}\).

The last clause includes membership in that set as well as domination of every element of the set. The threshold restriction (p\le u) applies only to the second set; the first set always contains zero. The original assignment (a) need not belong to Ω, and the reference observations in clause 1 are the quantified (z\in C), not necessarily (a).

## SAP.P030.T13

For every pair of natural numbers (N,M), assume (2\le N), then (M\le N). For every unit (i\in I_N) and finite neighbor set (H\subseteq I_N), assume (i\notin H). Let Ω be all Boolean assignments with exactly (M) true coordinates, Ω₁ the assignments in Ω with (z_i=\mathrm{true}), and Ω₀ those with (z_i=\mathrm{false}). Let (X(z)=\sum_{j\in H}z_j^*). For any finite set (J), write \(\overline X_J=(\sum_{z\in J}X(z))/|J|\), using real division, so it is zero on an empty set. Put (E=\overline X_\Omega), (E_1=\overline X_{\Omega_1}), and (E_0=\overline X_{\Omega_0}). Assert:

1. Ω is nonempty; (M\ge1\implies\Omega_1\ne\varnothing); (M\le N-1\implies\Omega_0\ne\varnothing).
2. (E=|H|M/N).
3. (M\ge1\implies E_1=|H|(M-1)/(N-1)).
4. (M\le N-1\implies E_0=|H|M/(N-1)).
5. For every unit (j\in I_N) and finite set (H'\subseteq I_N), if (j\notin H'), (M\ge1), and |H|<|H'|, then (E<\overline{X'}_\Omega), where (X'(z)=\sum_{k\in H'}z_k^*).
6. If (M\ge1), (M\le N-1), and |H|≥1, then (E_1<E<E_0).
7. If (M\ge1) and (M\le N-1), then ((M/N)E_1+((N-M)/N)E_0=E).

Every quotient in these displayed conclusions is real arithmetic: in particular (M-1) in clause 3 is subtraction **after** casting (M) to a real number. The bound (N-1) in hypotheses is natural subtraction, which is ordinary subtraction because (N\ge2).

## SAP.P030.T14

Use the ten-unit positions and fixed-unit set above, but the assignment-dependent schedule

\[
\psi_i=|\{j:|x_i-x_j|=1\}|,\quad
\theta_i(z)=|\{j:z_j=\mathrm{true},\ |x_i-x_j|=1\}|,\quad
Y_e(i,z)=\psi_i+\theta_i(z).
\]

This theorem has no hypotheses and asserts all of:

1. \(\psi=(1,2,2,2,2,2,2,2,2,1)\).
2. \(\theta(e^6)=(0,0,0,0,0,1,0,1,0,0)\).
3. \(Y_e(\cdot,e^6)=(1,2,2,2,2,3,2,3,2,1)\), and its fixed-unit subvector is ((1,3,2,1)).
4. (d^5=(6,1,2,3)), **Design** holds, and **Numerics** holds in full.
5. For every (r\in I_6), (g_{10}(y_F(e^6),b^r)=h_r), with outcomes here taken from (Y_e).
6. (g_{10}(y_F(e^6),e^6)=-3/\sqrt{10}).
7. Exactly two row indices (r\in I_6) satisfy (h_r\le h_5).
8. (P_K(g_{10}(y_F(e^6),w)\le g_{10}(y_F(e^6),e^6))=1/3), and |1/3−0.333|<0.0005.

Unlike the null schedule used in other theorems, (Y_e) is expressly allowed to depend on assignments. Clause 5 freezes its observed fixed-unit outcomes rather than substituting its unobserved outcomes.

## SAP.P030.T15

First, for every two real numbers (C,f),

\[
f(C-f)=C^2/4-(f-C/2)^2.
\]

Second, for every two integers (C,M), assume (C\ge1) and (M\ge1). Define the integer objective (J(f)=f(C-f)M). Then both statements hold:

1. For every integer (k), if (C=2k), then for every integer (f\in[0,C]), “for every integer (g\in[0,C]), (J(g)\le J(f))” is equivalent to (f=k).
2. For every integer (k), if (C=2k+1), then for every integer (f\in[0,C]), the same global-maximizer condition is equivalent to (f=k\lor f=k+1).

No probability law, actual assignment set, power function, or optimal-design objective beyond the specified product (J) is quantified in this statement.
