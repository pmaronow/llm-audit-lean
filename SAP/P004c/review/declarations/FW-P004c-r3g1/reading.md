# Blind reading

Completed before opening `claims.json` or `record.json`. Sources: all entries in
`closure.json`, `SAP/P004c/Challenge/Part1.lean`, and the corresponding definitions
in Defs Parts 1, 2, 4, and 5. The structure constructor and projections were also
printed in `scratch/BlindPrint.lean`. All generated `_proof_` entries were printed:
they merely establish that the numeral exponents/constants 2, 5, 8, 4, 9, 25 are at
least two, as required by numeral elaboration. They impose no hypotheses.

## Common fully expanded notation

This notation abbreviates explicit Mathlib operations below, not additional SAP
assumptions. A sample size is a natural number N. Its nodes are the finite type
I = Fin N, and Z = (Fin N → Bool) is the finite set of all assignments. A table R
is a function I → Z → ℝ. Write t(a)=1 for Boolean true and t(a)=0 for false,
s(a)=1 for true and s(a)=-1 for false. For real probabilities π_i let
q_i(true)=π_i and q_i(false)=1-π_i. Define, in ordinary finite-sum notation,

* W_π(z) = ∏_{i∈I} q_i(z_i), and E_π F = ∑_{z∈Z} W_π(z) F(z).
* Cov_π(F,G) = E_π(FG) - E_π(F)E_π(G), and V_π(F)=Cov_π(F,F).
* m_i(a) = E_π[1_{z_i=a}R_i(z)]/q_i(a).
* For any assignment function F, m_ij^{ab}(F) =
  E_π[1_{z_i=a,z_j=b}F(z)]/[q_i(a)q_j(b)].
* τ_i=m_i(true)-m_i(false), τ̄=(∑_i τ_i)/N, and
  m̄(a)=(∑_i m_i(a))/N.
* H_π,R(z)=(∑_i[t(z_i)R_i(z)/π_i
  -(1-t(z_i))R_i(z)/(1-π_i)])/N.
* For fixed fits g_i(a), U_i^g(z)=t(z_i)(R_i(z)-g_i(true))/π_i
  -(1-t(z_i))(R_i(z)-g_i(false))/(1-π_i), and
  δ_i^g=τ_i-(g_i(true)-g_i(false)).
* A_g(z)=(∑_i[g_i(true)-g_i(false)+U_i^g(z)])/N.
  L_π,R=A_g with g_i(a)=m̄(a) is the linearized estimator.

All sums/products here are Mathlib sums/products over finite types or Finsets.
Indicators mean `if ... then ... else 0`; they do not involve conditioning on a
measure-zero event. With π_i∈(0,1), W_π is the independent Bernoulli probability
mass function. No integrability hypothesis is needed for these real functions on
a finite space.

The dependency relation J_R(i,j) means i=j OR there exist z,z'∈Z agreeing at all
k≠j such that R_i(z)≠R_i(z'). The relation S_R(i,j) means that some l∈I satisfies
J_R(i,l) AND J_R(j,l). A neighborhood B is a function I → Finset I. Its degree
Δ_B is the finite supremum in ℕ of |B_i|, with supremum of no natural numbers
equal to 0. Given a real function D:I→I→ℝ, B_D(i,r)={j∈I:D(i,j)≤r}.
Locality at h means ∀i,j, h<D(i,j) implies ¬S_R(i,j).

For later formulas define the following explicit scalar expressions, evaluated
with the probabilities and table indicated in context:

* Q_g = [∑_i{m_i(true; (R-g_true)²)/π_i
  +m_i(false; (R-g_false)²)/(1-π_i)}
  +∑_i∑_{j∈B_i, j≠i}∑_{a,b∈Bool}s(a)s(b)
  m_ij^{ab}((R_i-g_i(a))(R_j-g_j(b)))]/N².
  Here `m_i(a; F)` means E_π[1_{z_i=a}F_i(z)]/q_i(a).
* E_g = [∑_i{m_i(true; (R-g_true)²)/π_i
  +m_i(false; (R-g_false)²)/(1-π_i) - (δ_i^g)²}
  +∑_i∑_{j∈B_i, j≠i}∑_{a,b∈Bool}s(a)s(b)
  {m_ij^{ab}((R_i-g_i(a))(R_j-g_j(b)))
  -(m_i(a)-g_i(a))(m_j(b)-g_j(b))}]/N².

For a spatial population, X is any type (in the theorem's universe) with a
Mathlib metric and a measurable-space structure; these structures need not be
compatible. The data are nonempty sets A_i⊆X, a measure ζ, potential outcomes
Y:X→Z→ℝ, and an arbitrary function bands:ℝ→Set ℝ. Distance from node i to x is
Metric.infDist(x,A_i), the infimum of ordinary metric distances. The region at d
is C_i(d)={x:infDist(x,A_i)∈bands(d)}. The circle table is
R_i^d(z)=[∫_{C_i(d)}Y(x,z)dζ]/(ζ(C_i(d))).toReal, with a Bochner set integral.
The genuine-average condition means, for every i: C_i(d) is measurable,
0<ζ(C_i(d))<∞, and every Y(·,z) is integrable on C_i(d) with respect to ζ.
The node separation is
D(i,j)=sInf{dist(x,y):x∈A_i,y∈A_j}, a real infimum. Node nonemptiness makes this
distance set nonempty, and 0 is a lower bound.

## SAP.P004c.T32

Source: Challenge/Part1.lean:15-18; Defs/Part4.lean:45-87.
The declaration is the conjunction of five separate universally quantified
statements; an earlier conjunct's premises do not scope over the later ones.
Every occurrence of π below is the constant vector π_i=p.

1. For every N∈ℕ, p∈ℝ, table R:I→Z→ℝ, and neighborhood B, assume N>0,
   0<p<1, ∀i i∈B_i, and ∀i,j, j∉B_i implies ¬S_R(i,j). Then
   V_π(H_π,R)=E_0, and V_π(H_π,R)≤U, where E_0 is the expression E_g above with
   g_i(a)=0 and
   U=[∑_i{m_i(true;R²)/p+m_i(false;R²)/(1-p)}
   +∑_i∑_{j∈B_i,j≠i}∑_{a,b}s(a)s(b)
   {m_ij^{ab}(R_iR_j)-m_i(a)m_j(b)}]/N².
   No boundedness, symmetry of B, or geometry is assumed in this conjunct.
2. For every N,p,b,R,B, assume N>0, 0<p<1, ∀i,z |R_i(z)|<b,
   ∀i i∈B_i, ∀i,j (j∈B_i↔i∈B_j), and ∀i,j (j∉B_i→¬S_R(i,j)). Define
   D0=[∑_i{m_i(true;R²)/p+m_i(false;R²)/(1-p)-τ_i²}]/N² and
   C_ab=[∑_i∑_{j∈B_i,j≠i}{m_ij^{ab}(R_iR_j)-m_i(a)m_j(b)}]/N².
   The conclusions are 0≤D0≤b²/(Np)+b²/[N(1-p)],
   ∀a,b∈Bool |C_ab|≤2b²(Δ_B-1)/N, and
   V_π(H_π,R)≤b²/(Np)+b²/[N(1-p)]+8b²(Δ_B-1)/N.
   The repeated letter b in C_ab is a Boolean index, separate from the real bound.
3. For every fixed p,b∈ℝ and family R_N:Fin N→Z_N→ℝ, assume 0<p<1 and
   eventually as N→∞, ∀i,z |R_N,i(z)|<b. Then D0_N=O(N⁻¹).
   Precisely, ∃c∈ℝ and N0∈ℕ such that ∀N≥N0,
   |D0_N|≤c|(N:ℝ)⁻¹|. No locality or B occurs here.
4. For every fixed p,b, family R_N, family B_N, and D∈ℕ, assume 0<p<1 and
   eventually, simultaneously, |R_N,i(z)|<b for all i,z, i∈B_N,i for all i,
   and Δ_{B_N}≤D. For each a,c∈Bool, C_ac,N=O(N⁻¹) in the same absolute-value
   sense. There is no symmetry or outside-neighborhood independence premise in
   this particular rate statement.
5. Universally choose a type family X_N with metric and measurable structures,
   a spatial population P_N of N nodes for every N, and fixed p,d∈ℝ. Assume
   0<p<1, d≥0, and all three conditions:
   (i) ∃b>0, eventually ∀x,z |Y_N(x,z)|<b;
   (ii) ∃h:ℝ→ℝ, ∀d'≥0 h(d')≥0, and ∀d'≥0 eventually in N,
   ∀i,j, h(d')<D_N(i,j)→¬S_{R_N^{d'}}(i,j);
   (iii) ∃c:ℝ→ℝ, ∀r≥0 eventually in N, ∀i,
   |{j:D_N(i,j)≤r}|≤c(r).
   Also assume eventually the genuine-average condition at the fixed d.
   Then V_π(H_π,R_N^d)=O(N⁻¹), with the absolute-value definition above.
   Thresholds in (ii) and (iii) can depend on radius; the final well-definedness
   premise concerns only the chosen d. These are eventual, not all-N premises.

The docstring describes the exact local expansion, corrected component/total
bounds, and 1/N variance order. It does not claim a positive lower bound.

Junk conventions: real division by zero and 0⁻¹ are 0. N>0 and 0<p<1 prevent
them in the finite formulas, and eventually N>0 suffices for all rates. Strict
boundedness in a positive sample implies b>0 even though not separately stated.
Δ_B-1 is subtraction in ℝ AFTER casting Δ_B, not truncated natural subtraction;
self-inclusion makes Δ_B≥1 when N>0. Finite `Finset.sup` is 0 at N=0, a harmless
initial term in rates. The pair formula is a true conditional mean for distinct
i,j; every use excludes i=j by Finset.erase, so its otherwise incorrect
same-coordinate denominator does not enter a conclusion. Finite real sums cause
no integrability or conditional-probability junk.

Spatial `infDist` is defined via an extended nonnegative infimum followed by
toReal (empty-node distance would be 0), but nodes are nonempty. Node separation
has a nonempty set bounded below, so real sInf is genuine even without closed or
compact nodes or attained separation. Circle integrals of nonintegrable functions
would be 0, and `(∞).toReal=0` or zero region mass would produce a zero average;
the genuine-average condition rules these out eventually at the radius of the
variance conclusion. Other radii in the locality premise can have totalized
averages; that fact does not by itself make the chosen-radius conclusion a junk
value. No Real.log, rpow, sqrt, limsup, liminf, or default partial function occurs.
An empty X is possible at N=0 but is excluded at N>0 by nonempty nodes.

## SAP.P004c.T33

Source: Challenge/Part1.lean:20-24; Defs/Part4.lean:89-116.
This is the conjunction of two independently universally quantified statements.

1. For every N∈ℕ, p∈ℝ, table R and neighborhoods B, assume N>0, 0<p<1,
   ∀i i∈B_i and ∀i,j (j∉B_i→¬S_R(i,j)). Put π_i=p, g_i(a)=m̄(a), and
   Qhom=[∑_i(τ_i-τ̄)∑_{j∈B_i}(τ_j-τ̄)]/N. Then all of:
   V_π(L_π,R)=E_g;
   Q_g-V_π(L_π,R)=Qhom/N;
   [V_π(L_π,R)≤Q_g ↔ Qhom≥0];
   and [Qhom≥0→V_π(L_π,R)≤Q_g].
   The inner neighborhood sum in Qhom includes i. Neither symmetry, boundedness,
   positive variance, nor Qhom≥0 is a premise of the first three assertions.
   Definitions of L, E_g and Q_g are explicitly given above, down to finite
   sums, arithmetic, indicator functions and products of Bernoulli coin masses.
2. For every N,p,R, assume N>0, 0<p<1, and V=V_π(H_π,R)>0. Define for each
   i,z, ξ_i(z)=[t(z_i)R_i(z)/p-(1-t(z_i))R_i(z)/(1-p)-τ_i]/[N√V].
   Then ∀z, ∑_iξ_i(z)=[H_π,R(z)-τ̄]/√V; ∀i, E_πξ_i=0; and
   V_π(z↦∑_iξ_i(z))=1. There is no locality premise in this conjunct.

The docstring claims a corrected linearized variance expansion, an exact
homophily identity and iff criterion, and normalized HT summands with the three
displayed properties. These are the literal formulas in this statement.

Junk conventions: all finite sample/population means have nonzero N and all arm
probabilities are positive. The real square root is 0 for nonpositive inputs,
but the only use has V>0, ensuring √V>0 and N√V≠0. This is a square root, not
real rpow. As above, pairMarginal is used only at distinct i,j and natural
indices are cast to ℝ before multiplication/division. A zero variance is allowed
in the first conjunct, which never standardizes. All assignment spaces are
nonempty and all sums are finite. No spatial integral, sInf/sSup, asymptotic
limsup/liminf, log, truncated subtraction, or default partial function occurs.

## SAP.P004c.T34

Source: Challenge/Part1.lean:26-34; Defs/Part5.lean:12-36.
The four conjuncts are independent.

1. For every N∈ℕ, assignment z:Fin N→Bool and p,S∈ℝ, if N>0,
   n1=∑_i1_{z_i=true}>0, and 0<p<1, then
   |N[(NS)/n1²-(NS)/(N²p²)]|=|N²/n1²-1/p²||S|, and
   |N²/n1²-1/p²|=|[(n1/N-p)(n1/N+p)]/[p²(n1/N)²]|.
   n1 is defined as a REAL sum of 0s and 1s. S is an arbitrary real scalar,
   with no requirement to be a kernel sum.
2. For every N,z,e:Fin N→ℝ, D:Fin N→Fin N→ℝ, K:ℝ→ℝ, and b,Kmax∈ℝ,
   assume N>0, b>0, ∀t≥0 |K(t)|≤Kmax, ∀t>1 K(t)=0, and
   ∀i,j D(i,j)≥0. Then
   |[∑_i∑_{j≠i}t(z_i)t(z_j)e_ie_jK(D(i,j)/b)]/N|
   ≤ Kmax [sup_{i∈Fin N}|e_i|]² Δ,
   where Δ is the maximum over i of |{j:D(i,j)≤b}|. The supremum is the
   Mathlib real sSup of the range of i↦|e_i|. No symmetry, triangle inequality,
   distinctness, or zero diagonal is imposed on D. No assignment probability
   is involved in this finite inequality. The kernel need not be nonnegative.
3. For every fixed p∈(0,1), use independent Bernoulli(p) assignments at each N.
   Let U_N(z)=|N²/n1(z)²-1/p²| if n1(z)>0, and U_N(z)=0 otherwise.
   Then U_N=O_p((√N)⁻¹). Fully expanded, for every real ε>0 there exists C>0
   such that for all sufficiently large N,
   ∑_{z∈Z_N} [∏_i q(z_i)] 1_{C|(√(N:ℝ))⁻¹|<|U_N(z)|}<ε.
   The choice of C may depend on ε and p, and the eventual N threshold may
   depend on both. This is tightness at the stated scale, not a little-o claim.
4. The scalar identities
   |8²/5²-1/(1/2)²||-1/4|=9/25,
   (8²/5²-1/(1/2)²)|-1/4|=-9/25,
   and ¬(9/25≤-9/25). All these divisions are in ℝ.

The docstring expressly omits a bandwidth-composed stochastic rate/little-o
conclusion and any realization of an eight-node assignment/residual/kernel
example. It retains only scalar arithmetic, imposes positive N,b in the kernel
bound, and discloses the zero extension of U_N on empty treated arms.

Junk conventions: the first conjunct protects every denominator by N>0,n1>0,
and p>0. In the second, N,b>0, and the real sSup is of a nonempty finite set,
so it is an actual maximum and neither an empty nor an unbounded-supremum
default. The kernel bound at t=0 forces Kmax≥0. The degree supremum is over a
nonempty finite type. The third conjunct explicitly avoids zero treated-count
reciprocals using an if; at N=0, U_0=0 and (√0)⁻¹=0, irrelevant to the eventual
assertion. For N>0 the square root and its inverse are positive; negative sqrt
arguments cannot occur because N is cast from ℕ. Although real division by
zero is globally totalized, it is not used as the asserted error on empty arms.
No integral, ENNReal conversion, log, rpow, limsup/liminf, truncated subtraction
or partial-function default occurs. The scalar example alone does not establish
that a kernel configuration with S=-1/4 exists.

## SAP.P004c.T39

Source: Challenge/Part1.lean:36-40; Defs/Part5.lean:38-43.

For every N∈ℕ, p∈ℝ and arbitrary R:Fin N→(Fin N→Bool)→ℝ, if N>0 and
0<p<1, then

E_π H_π,R = (1/N)∑_i {∑_{z∈Z}W_π(z)R_i(z[i:=true])
                         -∑_{z∈Z}W_π(z)R_i(z[i:=false])},

with π_i=p. Here z[i:=a] is the ordinary total function update: coordinate i is
a, every other coordinate retains its previous Boolean value. The right side
averages the forced-coordinate marginal effects, integrating the other
coordinates with their independent Bernoulli law. The summed-out original
value at coordinate i has total weight 1. There are no interference, locality,
boundedness, spatial, or positive-variance premises.

The docstring calls this unbiasedness for the forced-coordinate AME at positive
sample size and interior common Bernoulli probability.

Junk conventions: N,p,1-p are nonzero under the explicit premises. Fin N is
nonempty, and the assignment type has 2^N elements. Real finite sums/products
are genuine expectations of finite real outcomes. Function.update is total on
this finite index type and invokes no default value. There is no conditioning
denominator on the right, nor any integral, square root, log, rpow, sInf/sSup,
limsup/liminf, truncated subtraction or infinite extended-real conversion.

## SAP.P004c.T40

Source: Challenge/Part1.lean:42-46; Defs/Part5.lean:45-55.

Quantifier order: for every N∈ℕ; every type X with metric and measurable-space
structures; every spatial population (nonempty node sets A_i, measure ζ,
outcomes Y and real distance-band function) on X; every d∈ℝ; every
w:Fin N→(Fin N→Bool)→ℝ; every g:Fin N→X→ℝ; and every f:X→ℝ, assume:

* N>0;
* ∀i, ∑_{z∈Z}w_i(z)=1;
* ∀i,z, w_i(z)≥0;
* ∀x,z, Y(x,z)=∑_{j∈Fin N}t(z_j)g_j(x)+f(x);
* ∀i, the region C_i(d) is measurable with 0<ζ(C_i(d))<∞, and
  ∀z, Y(·,z) is integrable on C_i(d) under ζ.

For any F:Z→ℝ define its forced effect under node i's law by
T_i(F)=∑_z w_i(z)F(z[i:=true])-∑_z w_i(z)F(z[i:=false]).
Then all three conclusions hold:

1. ∀i,x, T_i(z↦Y(x,z))=g_i(x).
2. ∀i, T_i(z↦[∫_{C_i(d)}Y(x,z)dζ]/ζ(C_i(d)).toReal)
   =[∫_{C_i(d)}g_i(x)dζ]/ζ(C_i(d)).toReal.
3. (1/N)∑_i T_i(z↦[∫_{C_i(d)}Y(x,z)dζ]/ζ(C_i(d)).toReal)
   =(1/N)∑_i[∫_{C_i(d)}g_i(x)dζ]/ζ(C_i(d)).toReal.

The laws can depend on i and need not arise as marginals of one joint law.
They are laws on all coordinates, but the overwritten coordinate is immaterial,
so their pushforwards to the remaining coordinates are arbitrary marginal laws.
No independent Bernoulli structure, interior probability, locality, boundedness,
or sign restriction on d is imposed. bands(d) is arbitrary. The docstring says
the additive point effect, its spatial average, and its node mean do not depend
on the assignment law, as these universally quantified conclusions express.

Junk conventions: positive finite region measures ensure a finite, strictly
positive real denominator; no toReal(∞), zero measure, or division-by-zero
average is used. Outcome integrability is explicit. Although integrability of
g_i is not a separate premise, on each C_k(d) it follows by taking the
difference of the all-false outcome and the outcome with only i set true;
f is the all-false outcome. Thus the conclusion's Bochner integrals are genuine
as well. The forced effect consists of finite real sums, so no integrability
condition on w is needed beyond its finite normalization/nonnegativity. N>0
protects the final mean, and nonempty nodes protect infDist from its empty-set
default. Function.update has no partial/default branch. Node separation sInf
does not occur in this target's dependency closure. No sSup, log, sqrt, rpow,
limsup/liminf, truncated subtraction or default partial function occurs.
