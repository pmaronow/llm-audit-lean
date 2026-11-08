# Blind reading

Saved before opening `claims.json` or `record.json`. This reading uses only the
Defs, Challenge and Mathlib sources. The Challenge has ten declarations, all in
`SAP/P012b/Challenge/Part1.lean`; their propositions are definitions in Defs.

## Common objects and fully expanded notation

All graphs and samples here are finite. The ambient vertex set is the disjoint
union `ℕ ⊕ (ℕ × ℕ)`. Write `s(i)` for a vertex in the first summand and `u(i,k)`
for a vertex in the second. These tags are injective and disjoint. Vertices
outside the sample may have either tag; they are not required to be `u` vertices.

A datum D consists of finite sets S of sampled natural-number labels and B of
seed labels; functions parent, time and degree from ℕ to ℕ; and a Boolean trait
function a on ℕ. Put N=S\B, n=|N|, X={s(i):i∈S}, and
R={{s(parent(j)),s(j)}:j∈N}. Edges are finite sets of vertices, and an edge
collection is a finite set of these finite sets: no multiplicities survive.
Let r_i be the number of edges of R containing s(i), and q_i=degree(i)−r_i
with natural-number subtraction (truncated at zero in unrestricted data).
Write A_b=Σ_{i∈S,a(i)=b} degree(i) and C_i={j∈N:parent(j)=i}.

**Admissible(D)** means, conjunctively: B⊆S; for every i∈S and j∈S,
time(i)=time(j) implies i=j; for every j∈N, parent(j)∈S and
time(parent(j))<time(j); and for every i∈S, r_i≤degree(i).
Thus q_i is ordinary nonnegative surplus for admissible data. Times are distinct
natural numbers, not arbitrary real times.

A state H consists of a finite vertex set V, finite edge set E, and Boolean
function τ on the entire ambient vertex type. Put d_H(v)=#{e∈E:v∈e}.
**Simple(H)** means every e∈E has exactly two elements and is a subset of V.
**Augmented(D,H)** means Simple(H), and every e∈E contains s(i) for some i∈S.
**Compatible(D,H)** means Augmented(D,H), X⊆V, R⊆E, τ(s(i))=a(i) for every
i∈S, every v∈V\X has an edge {s(i),v} for some i∈S, and
d_H(s(i))=degree(i) for every i∈S. Sampled vertices of degree zero are allowed;
unsampled isolated vertices are forbidden. Edges between unsampled vertices
are forbidden. **GraphCompatible** has exactly these requirements except the
sampled-trait equalities. Write U_H=V\X.

For all ambient vertices v,w, put A_H(v,w)=1 if v≠w and {v,w}∈E, and 0
otherwise; z_H(v)=1 if τ(v)=true, and 0 otherwise; m=|E|; and
S_b(H)=Σ_{v∈V,τ(v)=b}d_H(v). All cardinalities in real expressions are cast
to ℝ. Define

    Num(H) = Σ_{v,w∈V} (A_H(v,w)−d_H(v)d_H(w)/(2m)) z_H(v)z_H(w),
    Den(H) = Σ_{v,w∈V} (1_{v=w}d_H(v)−d_H(v)d_H(w)/(2m)) z_H(v)z_H(w),
    h_raw(H) = Num(H)/Den(H).

`HomophilyDefined(H)` means m>0 and Den(H)≠0. The partial homophily h(H)
is `some h_raw(H)` when this condition holds and `none` otherwise. The raw
real expressions still exist when denominators vanish: Mathlib real division
uses x/0=0. `none` is a separate Option constructor and never a real value.

For i,j∈ℕ, Q_H(i,j) is the set of v∈V such that {s(i),v}∈E and v is
not yet sampled at time(j): v=u(k,l) always qualifies; v=s(k) qualifies
exactly when k∉S or time(j)≤time(k). Equality of times is included. Put
Q_H^=(i,j)={v∈Q_H(i,j):τ(v)=τ(s(i))}. Define

    Psum(D,H) = Σ_{j∈N} [1_{τ(s(j))=τ(s(parent(j)))}
                         − |Q_H^=(parent(j),j)|/|Q_H(parent(j),j)|],
    p_raw(D,H) = Psum(D,H)/n.

`PreferentialDefined(D,H)` means n>0 and, for every j∈N,
|Q_H(parent(j),j)|>0. The partial preferential quantity p(D,H) is
`some p_raw(D,H)` if this holds, and `none` otherwise. Raw divisions are
again totalized; an empty finite sum is zero.

Let Hvals(D)={r∈ℝ:there exists a state H with Compatible(D,H) and h(H)=some r},
and Pvals(D) analogously with p(D,H). `PointIdentified(W)` means there exists
r∈ℝ such that W={r}; the empty set is not point identified.
`FullHomophilyRegion(D,L,U)` means: every compatible H has defined homophily,
L∈Hvals(D) and L≤r for every r∈Hvals(D), and U∈Hvals(D) and r≤U for every
r∈Hvals(D). `FullPreferentialRegion` is the same definition for p. These are
attained marginal endpoint assertions; they do not say every real point
between the endpoints is attained, and they do not assert a joint rectangle
is attainable.

Let L_same(D) be the leaf completion with vertices
X∪{u(i,k):i∈S,0≤k<q_i}, edges
R∪{{s(i),u(i,k)}:i∈S,0≤k<q_i}, traits a(i) on every s(i), and a(i) on
every u(i,k). The parameter-false version instead gives u(i,k) trait ¬a(i).
`flip(H,v)` changes τ(v) to its Boolean opposite, leaving everything else
unchanged. `recruitmentState(D)` has vertices X, edges R, traits a on s tags
and false on u tags. `induced(D,H)` has vertices X, edges {e∈E:e⊆X}, and
the original trait function. `InducedCompatible(D,J)` means Simple(J),
V_J=X, R⊆E_J, and d_J(s(i))≤degree(i) for every i∈S. In particular this
last predicate imposes no trait agreement at all.

The Mathlib notions used above are finite-set image, difference, union,
filter, biUnion and cardinality; real arithmetic; and `Function.update`.
`IsLeast(W,L)` is membership plus being a lower bound; `IsGreatest(W,U)`
is membership plus being an upper bound (Order/Bounds/Defs.lean).
`Monotone` means nondecreasing, `Antitone` means nonincreasing, and
`StrictAntiOn f (Ici 1)` means f(b)<f(a) whenever 1≤a<b
(Order/Monotone/Defs.lean). `Tendsto f atTop (𝓝 0)` is the usual limit
to zero, and `Tendsto f atTop atTop` means eventual exceedance of each
real bound (Order/Filter/Defs.lean and AtTopBot/Defs.lean). `Real.log`
is ordinary natural logarithm at the positive arguments used here;
`Real.exp` is the real exponential; for positive t, `t^x` with real
exponent x is exp(x log t) (Analysis/SpecialFunctions/Log/Basic.lean,
Exp.lean and Pow/Real.lean). No limsup, integrals, or infinite vertex sums occur.

## SAP.P012b.T13

The proposition is the conjunction of the following two universally quantified
statements, with independent choices in each.

1. For every datum D, then proof of Admissible(D), then i,j∈ℕ, then
   i∈S, j∈N, parent(j)=i and r_i<degree(i), there exist states H,K and
   then a vertex v∈U_H such that all of the following hold:
   Compatible(D,H) and Compatible(D,K); v=u(i,0); V_H and E_H are those of
   L_same(D); for every k∈S, {s(k),v}∈E_H iff k=i; τ_H(v)=true;
   K=flip(H,v); for every ℓ∈N,
   Q_H(parent(ℓ),ℓ)=Q_K(parent(ℓ),ℓ); and for every ℓ∈N,
   v∈Q_H(parent(ℓ),ℓ) iff parent(ℓ)=i. Moreover

       p_raw(D,H)−p_raw(D,K)
         = (if a(i) then −1 else 1)/n · Σ_{ℓ∈C_i} 1/|Q_H(i,ℓ)|,

   the two raw p values differ, and Pvals(D) is not point identified.
   If a(i)=true, the difference is ≤−1/(n|Q_H(i,j)|), this displayed
   bound is strictly negative, and equality holds iff C_i={j}.
   H's traits away from sampled vertices and v are otherwise unspecified;
   H is not asserted to equal L_same(D) as a full state.
2. For every D, proof of admissibility, H, proof of compatibility, i,j,
   i∈S, j∈N, parent(j)=i, then vertex v∈U_H, then the private-neighbor
   condition (for every k∈S, {s(k),v}∈E_H iff k=i), then τ_H(v)=true,
   let K=flip(H,v). K is compatible; the same susceptible-set equalities,
   membership equivalence, exact signed sum, distinctness, and conditional
   negative bound and sole-child equality criterion above hold. This
   second conjunct does not explicitly repeat non-point-identification.

## SAP.P012b.T14

An unconditional conjunction of four concrete families, with these exact data:

* A: S={1,2}, B={1}, parent(i)=1 for every i, time(i)=i−1 in ℕ,
  degree(i)=1 for every i, and a(i)=false for every i. The dyad state has
  V={s(1),s(2)}, E={{s(1),s(2)}} and both traits false. A is admissible,
  this state is compatible, Num=Den=0, its h is none, and its p is some 0.
* B: the same as A except B={1,2} and a(i) is the Boolean test i=2.
  Its dyad has τ(s(1))=false and τ(v)=true at every other ambient vertex.
  B is admissible, this state is compatible, h=some(−1), n=0,
  Psum=0, and for every state H whatsoever p(B,H)=none.
* C: S=B={1}, parent(i)=1, time(i)=i, degree(i)=0, a(i)=false.
  Its state has V={s(1)}, E=∅, and all traits false. C is admissible,
  this state is compatible, m=0, h=none, and p=none.
* D: S={1,2}, B={1}, parent(i)=1, time(i)=i−1,
  degree(i)=1 if i=1 and 4 otherwise, and a(i)=true for every i.
  For every ordered Boolean triple (t3,t4,t5), the state with
  V={s(1),s(2),u(3,0),u(4,0),u(5,0)},
  E={{s(1),s(2)},{s(2),u(3,0)},{s(2),u(4,0)},{s(2),u(5,0)}},
  traits t3,t4,t5 at these three u vertices and true elsewhere, is compatible
  with admissible D. At (true,true,true), Num=Den=0 and h=none;
  h(false,false,false)=some(−3/5), h(true,false,false)=some(−1/3),
  h(true,true,false)=some(−1/7). For every Boolean triple, p=some 0.

There is no uniqueness/classification assertion or region-endpoint assertion.

## SAP.P012b.T15

This is a conjunction of two universal statements.

1. For every state H, then Simple(H), then m>0, write S1=S_true(H) and
   S0=S_false(H). All of these hold:
   Σ_{v∈V}d_H(v)z_H(v)=S1; S1+S0=2m in ℕ;
   Den=S1−S1²/(2m)=S1 S0/(2m)=S1(2m−S1)/(2m) in ℝ;
   Den>0 iff S0>0 and S1>0; HomophilyDefined(H) iff S0>0 and S1>0;
   and if S1=0 or S1=2m, then Num=Den=0.
2. For every datum D and then Admissible(D), all the following hold:
   for every compatible H, PreferentialDefined(D,H) iff |B|<|S|, and
   for every j∈N, s(j)∈Q_H(parent(j),j) and this set has positive size;
   every compatible H has defined h iff A_false>0 and A_true>0;
   every compatible H has defined p iff |B|<|S|;
   if there exist i∈S and then j∈S with r_i<degree(i),
   r_j<degree(j), and a(i)≠a(j), then A_false>0 and A_true>0;
   if there exists j∈N with r_parent(j)<degree(parent(j)), then |B|<|S|;
   if A_false>0 and A_true>0, then for every L,U∈ℝ,
   FullHomophilyRegion(D,L,U) iff L and U are respectively the least and
   greatest elements of Hvals(D);
   if |B|<|S|, the corresponding equivalence holds for every L,U for p;
   if the conjunction A_false>0 and A_true>0 fails, there exist no L,U
   satisfying FullHomophilyRegion(D,L,U).

These conditional equivalences do not assert that endpoints exist.

## SAP.P012b.T16

The proposition is a conjunction of five statements:

1. For every sequence T:ℕ→ℝ, then positivity T(n)>0 for every n, then
   monotonicity T(a)≤T(b) for a≤b, T does not tend to zero as n→∞.
2. For every ε∈ℝ there exists no real T with T·(ε log 1)=1.
3. For every ε,T1∈ℝ, then ε>0, then 1/(ε log 2)≤T1, define
   c(0)=T1 and c(n)=1/(ε log(n+1)) for n≥1. For every n, c(n)>0;
   c is nonincreasing on ℕ; c(b)<c(a) whenever 1≤a<b; and c(n)→0.
4. For every ε,D,t∈ℝ, then ε>0, t≥2, 0≤Dε, and Dε≤1,
   exp(−D/(1/(ε log t)))=exp(−Dε log t)=1/t^(Dε),
   and this quantity is at least 1/t.
5. For every ε,D∈ℝ, then ε>0, 0≤Dε, Dε≤1, then every real first,
   the sequence first+Σ_{n=0}^{N−1} exp(−D/(1/(ε log(n+2))))
   tends to +∞ as the natural N tends to infinity.

## SAP.P012b.T17

For every datum D, then state H, then Admissible(D), then
GraphCompatible(D,H), the induced state J with vertices X and edges
{e∈E_H:e⊆X} is InducedCompatible(D,J) (simple, vertices exactly X,
contains R, sampled degrees bounded above by the reported degrees).
In addition, (for every i∈S, d_J(s(i))=degree(i)) iff V_H=X.
There is no requirement on the traits of H or J and no example is asserted.

## SAP.P012b.T18

For every D1,D2, then states H,K, then Admissible(D1), Admissible(D2),
Compatible(D1,H), Compatible(D2,K), then V_H=V_K, E_H=E_K, and
(for every v∈V_H, τ_H(v)=τ_K(v)), the Option values h(H) and h(K)
are equal, including equality of undefined cases. No p comparison occurs.

## SAP.P012b.T19

This negates a universal implication: it is not the case that, for every D,
then H,K, then Admissible(D), Compatible(D,H), and Proposal(D,false,H,K),
Compatible(D,K) holds. In classical terms, there is an admissible datum with
a compatible starting state and an allowed literal proposal giving an
incompatible final state.

Here is the entire relevant proposal relation, expanded from Defs/Part2.
Let remove(H,v,w) erase {v,w} from E, add(H,v,w) insert {v,w} in E, and
addVertex(H,v,t) insert v into V and set its trait to t. The replacement pool
for sampled label i is {v∈U_H:{s(i),v}∉E_H}. Given an original/current H
and pending state J, a replacement (v,P) either chooses v in this pool and
sets P=J, or chooses v∉V_J with arbitrary Boolean t and sets
P=addVertex(J,v,t). Its pool is computed from the original H.
For repaired=false, cleanup(J) deletes all degree-zero vertices from V_J
and changes neither edges nor traits. A GraphProposal(D,false,H,K) is
exactly one of these four constructor cases:

* Delete an unobserved edge: choose i∈S, j∈V_H with s(i)≠j,
  {s(i),j}∈E_H\R and j∉X; choose replacement (v,P) from
  J=remove(H,s(i),j). K=cleanup(add(add(P,s(i),v),j,v)).
* Delete an observed edge: choose i,j∈S with i≠j and
  {s(i),s(j)}∈E_H\R; choose replacement (v,P) from
  remove(H,s(i),s(j)), then replacement (w,Q) using original H's pool
  for j and pending add(P,s(i),v).
  K=cleanup(add(Q,s(j),w)).
* Add an edge: choose i∈S and j∈V_H with s(i)≠j,
  {s(i),j}∉E_H; choose v,w∈U_H with {s(i),v}∈E_H and {j,w}∈E_H.
  K=cleanup(add(remove(remove(H,s(i),v),j,w),s(i),j)).
  There is no explicit constructor hypothesis that j is sampled or v≠w.
* Unchanged: choose i∈S and j∈V_H with s(i)≠j for which neither
  ({s(i),j}∈E_H and {s(i),j}∉R) nor
  ({s(i),j}∉E_H and there exist v,w∈U_H with both foregoing incident
  edges) holds. K=cleanup(H).

A TraitProposal(D,false,H,K) chooses any v∈U_H and K=flip(H,v).
The other TraitProposal constructor requires false=true, hence cannot occur.
Proposal is the disjunction of GraphProposal and TraitProposal.
The repaired=true variant is defined too but is not used in this theorem:
cleanup retains sampled isolates, the first graph case omits the added
{j,v} edge, and an empty unsampled set permits an identity trait move.

## SAP.P012b.T20

For every ordered triple of data (Dsex,Dcrack,Dhome), it is impossible that
all the following requirements simultaneously hold:

* Each of these three data is admissible, has |S|=527, |B|=6, and
  Σ_{i∈S} degree(i)=4487.
* Their sampled sets agree, their seed sets agree, and for every nonseed
  in Dsex their parent functions agree; for every sampled label in Dsex
  their degrees and times agree. Traits may differ between data.
* There exist, in order, real Ls,Us,Lc,Uc,Lh,Uh such that each datum's
  corresponding FullHomophilyRegion holds and

      |Ls−(−7027/10000)|≤1/20000, |Us−8292/10000|≤1/20000,
      |Lc−(−6918/10000)|≤1/20000, |Uc−8231/10000|≤1/20000,
      |Lh−(−7179/10000)|≤1/20000, |Uh−8242/10000|≤1/20000.

In particular these hypothesized regions include definedness at every compatible
state and actual attainment of their endpoints. This is an impossibility
statement, not a certification of numerical endpoints.

## SAP.P012b.T22

The proposition is a conjunction of three universal statements:

1. For every D, then Admissible(D), A_false>0, A_true>0, and |B|<|S|,
   all these conclusions hold:
   Hvals(D) and Pvals(D) are both point identified iff
   degree(i)=r_i for every i∈S;
   (degree(i)=r_i for every i∈S) iff
   (for every compatible H, V_H=X and E_H=R);
   if there exists i∈S with r_i<degree(i), Hvals(D) is not point identified;
   and if degree(i)=r_i for every i∈S, then every compatible H has
   the same vertices and edges as recruitmentState(D) and agrees with
   that state's traits at every vertex in V_H.
2. For every D, then Admissible(D), A_false>0, A_true>0, then i∈ℕ,
   i∈S, and r_i<degree(i), L_same(D) is compatible, its flip at u(i,0)
   is compatible, and their raw h values differ. This conjunct does not
   require |B|<|S|.
3. For every D, then Admissible(D), A_false>0, A_true>0, and |B|<|S|,
   Pvals(D) is point identified iff, for every i∈S, if C_i is nonempty
   then degree(i)=r_i.

## SAP.P012b.T23

An unconditional concrete assertion. The datum F has S={1,2,3,4,5}, B={1},
time(i)=i, parent(j)=2 when j=3 or j=5 and 1 otherwise,
degree(1)=5, degree(2)=4, degree(5)=2, degree(i)=3 otherwise,
and trait a(i)=false exactly when i=4. Thus its recruitment edges are
{1,2}, {2,3}, {1,4}, {2,5} under the s embedding.
F is admissible; FullHomophilyRegion(F,−5/8,79/105) and
FullPreferentialRegion(F,−11/80,49/120) both hold. In addition, for every
compatible state H, h(H)=some h_raw(H), p(F,H)=some p_raw(F,H),
−5/8≤h_raw(H)≤79/105 and −11/80≤p_raw(F,H)≤49/120.
Each of the four marginal endpoints is attained by a compatible state;
no common extremizer, uniqueness, or nonuniqueness assertion occurs.
