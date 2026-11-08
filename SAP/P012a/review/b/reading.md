# Blind mathematical reading

Saved before opening `claims.json` or `record.json`. This reading uses only the
Defs and Challenge sources and the Mathlib definitions to which they reduce.
Docstrings are not hypotheses. All twelve theorems have no external arguments:
each asserts the entire proposition described below, including its internal
universal quantifiers and conjunctions.

## Objects and common notation

The vertex universe is the disjoint union `N + (N x N)`. Write `s_i` for the
left-hand copy of `i`, and `u_ik` for the right-hand copy of `(i,k)`. All these
labels are distinct in the indicated way. Being of the form `s_i` does not by
itself mean that the vertex is sampled.

A datum D consists of finite subsets S,B of N, and total functions
`p,t,d : N -> N` and `z : N -> {false,true}`. They mean sampled indices, seed
indices, parent, time, reported degree, and trait. There are no structure-level
constraints. Write N_D = S\B, V_S = {s_i : i in S}, and
`E_R = {{s_(p(j)),s_j} : j in N_D}`. These are finite sets, so repeated elements
are removed. Let r_i be the number of edges of E_R containing s_i. The spare
degree is `sigma_i = d_i - r_i`, using truncated natural-number subtraction.
Let `Sigma = sum_(i in S) sigma_i`, `Sigma_b = sum_(i in S,z_i=b) sigma_i`, and
`D_b = sum_(i in S,z_i=b) d_i`.

The hypothesis **admissible D** means exactly:

1. B is a subset of S.
2. For every i in S, then every j in S, t_i=t_j implies i=j.
3. For every j in N_D, p(j) is in S and t_(p(j)) < t_j.
4. For every i in S, r_i <= d_i.

A state H consists of a finite vertex set V_H, a finite set E_H of finite sets
of vertices, and a total Boolean trait function Z_H on the whole vertex
universe. Define `deg_H(v) = |{e in E_H : v in e}|`, even for malformed states.
**Simple H** says that every e in E_H has cardinality two and is a subset of
V_H. Thus these are undirected edges with distinct endpoints, without parallel
edges. **Augmented D H** says Simple H and that every edge contains s_i for
some i in S; it excludes edges between two unsampled vertices.

**Compatible D H** means exactly: augmented D H; V_S is a subset of V_H; E_R
is a subset of E_H; Z_H(s_i)=z_i for every i in S; every v in V_H\V_S has an
edge to at least one s_i with i in S; and deg_H(s_i)=d_i for every i in S.
It permits isolated sampled vertices, including isolated seeds, but no isolated
unsampled vertices. `GraphCompatible` is the same conjunction with the
sampled-trait equality omitted (it is not used by any theorem statement).

Write x_v=1 if Z_H(v)=true, and x_v=0 otherwise. A_H(v,w) is 1 exactly when
v != w and {v,w} is an edge of H, and is 0 otherwise. For m=|E_H| define

```
num(H) = sum_(v in V_H) sum_(w in V_H)
           (A_H(v,w) - deg_H(v) deg_H(w)/(2m)) x_v x_w,
den(H) = sum_(v in V_H) sum_(w in V_H)
           (1_(v=w) deg_H(v) - deg_H(v) deg_H(w)/(2m)) x_v x_w,
hval(H) = num(H)/den(H).
```

These are real sums and divisions. Raw values are totalized, with division by
zero equal to zero in the real field. **H-defined H** means m>0 and den(H)!=0.
`homophily H = some r` means H-defined H and hval(H)=r; otherwise homophily
is `none`.

For indices i,j, the susceptible set T_H(i,j) consists of vertices v in V_H
such that {s_i,v} is an edge and either v=u_ab, or v=s_k with
`k not in S or t_j <= t_k`. Its same-trait subset M_H(i,j) consists of those
v with Z_H(v)=Z_H(s_i). Define

```
pval(D,H) = (1/|N_D|) sum_(j in N_D)
   (1_(Z_H(s_j)=Z_H(s_(p(j)))) - |M_H(p(j),j)|/|T_H(p(j),j)|).
```

**P-defined D H** means |N_D|>0 and |T_H(p(j),j)|>0 for every j in N_D.
`preferential D H = some r` means P-defined D H and pval(D,H)=r; otherwise
preferential is `none`.

Let e_b(H) count edges all of whose vertices have trait b, and c(H) count
edges with a true vertex and a false vertex. On simple states these are the
two monochromatic edge counts and the mixed count. The recruitment state has
vertices V_S, edges E_R, traits z_i on every s_i and false on every u_ik.
Write a=e_true(recruitment state), b=e_false(recruitment state), and c_R for
its mixed count. Let

```
phi(x,y,c) = 1 - c/(2x+c) - c/(2y+c),
L_h = phi(a,b,c_R+Sigma),
U_h = phi(a+Sigma_true,b+Sigma_false,c_R),
Qlower = (4ab-(c_R+Sigma)^2)/((2a+c_R+Sigma)(2b+c_R+Sigma)).
```

For j define C_j = {k in N_D : p(k)=p(j) and t_j <= t_k},
q_j = |{k in C_j : z_k=z_(p(j))}|, and o_j=1_(z_j=z_(p(j))). Put

```
L_p = (1/|N_D|) sum_(j in N_D)
         (o_j - (q_j+sigma_(p(j)))/(|C_j|+sigma_(p(j)))),
U_p = (1/|N_D|) sum_(j in N_D)
         (o_j - q_j/(|C_j|+sigma_(p(j)))).
```

`hValues D` is the set of real r for which there exists a compatible H with
homophily H=some r. `pValues D` is defined with preferential in place of
homophily. `FullHomophilyRegion D L U` says: every compatible H is H-defined;
L belongs to hValues and is <= every member; U belongs to hValues and is >=
every member. `FullPreferentialRegion` says the analogous three facts with
P-defined and pValues. Neither predicate says that every real number between
L and U is achieved. `PointIdentified A` means there exists r with A={r}.

The leaf completion F_same has vertices V_S plus u_ik for i in S and
0<=k<sigma_i, and edges E_R plus {s_i,u_ik} for those i,k. Traits on s_i are
z_i for every i; on u_ik they are z_i when same=true and Boolean negation of
z_i when same=false. Denote these two states F+ and F-.

The induced state I_D(H) has vertices V_S, the edges of H wholly contained in
V_S, and H's trait function. `InducedCompatible D J` means Simple J,
V_J=V_S, E_R subset E_J, and deg_J(s_i)<=d_i for every i in S. It contains
no trait-agreement clause.

## The proposal relations, fully expanded

`removeEdge H v w` erases the one finite-set edge {v,w}, if present;
`addEdge` inserts that edge, with no multiplicity if already present.
`addVertex H v b` inserts v and changes the total trait function only at v to
b. `flipTrait H v` changes only that trait to its Boolean negation.
U_D(H)=V_H\V_S. R_D(H,i)={v in U_D(H) : {s_i,v} not in E_H}.
Cleanup C_e(H) retains exactly the vertices v in V_H satisfying
`(e=true and v in V_S) or deg_H(v)!=0`, and leaves edges and traits untouched.

A replacement for i, relative to original state H and pending state P, is
either (v,P) with v in R_D(H,i), or (v,addVertex P v b) with v not in V_P
and b an arbitrary Boolean. These are the only possibilities.

`GraphProposal D e H K` is the relation generated by exactly four cases:

1. Choose i in S, j in V_H, s_i!=j, with {s_i,j} in E_H\E_R and j not in
   V_S. Choose a replacement (v,P) for i relative to H and H-{s_i,j}.
   The output is C_e(P+{s_i,v}) if e=true; if e=false it is
   C_e(P+{s_i,v}+{j,v}).
2. Choose distinct i,j in S with {s_i,s_j} in E_H\E_R. Choose replacement
   (v,P) for i relative to H and H-{s_i,s_j}; then replacement (w,Q) for j
   relative to H and P+{s_i,v}. The output is C_e(Q+{s_j,w}). The second
   existing-vertex pool is evaluated in the original H.
3. Choose i in S and j in V_H with s_i!=j and {s_i,j} not in E_H. Choose
   v,w in U_D(H), with {s_i,v} and {j,w} in E_H. No explicit v!=w hypothesis
   is imposed. The output is C_e(H-{s_i,v}-{j,w}+{s_i,j}).
4. Choose i in S and j in V_H with s_i!=j. Require that it is false that
   {s_i,j} is a nonrecruitment edge, and false that {s_i,j} is absent with
   unsampled neighbours v,w as in case 3. The output is C_e(H).

`TraitProposal D e H K` holds either for K=flipTrait H v with v in U_D(H),
or for e=true, U_D(H) empty, and K=H. `Proposal` is the disjunction of the
graph and trait relations. These are possible-execution relations; they do
not encode probabilities, frequencies, or uniform/Bernoulli random sampling.

## SAP.P012a.T1

There are no hypotheses. Four concrete conjunctions are asserted.

(a) Set S={1,2}, B={1}, p(j)=1 for every j, t(j)=j,
d(i)=2 if i=1 and 1 otherwise, and z_i=true exactly when i=2.
H has vertices {s_1,s_2,u_30}, edges {{s_1,s_2},{s_1,u_30}}, and true trait
exactly at s_2. D is admissible, H is compatible, and R_D(H,1) is empty.
For each Boolean beta, form K_beta by removing {s_1,u_30}, adding fresh
u_40 with trait beta, adding {s_1,u_40} and {u_30,u_40}, then applying
C_false. For every beta, Proposal D false H K_beta and K_beta is not
compatible. Also homophily H=some(-1/3) and preferential D H=some(-1/2).

(b) S={1,2,3}, B={1}, p(3)=2 and p(j)=1 otherwise, t=id,
d(2)=3 and d(i)=1 otherwise, and z_i=true exactly when i=2.
H has vertices {s_1,s_2,s_3,u_40}, edges
{{s_1,s_2},{s_2,s_3},{s_2,u_40}}, and true trait exactly at s_2.
D is admissible, H is compatible, and R_D(H,2) is empty. For every Boolean
beta, the state obtained by removing {s_2,u_40}, adding fresh u_50 with
trait beta, adding {s_2,u_50} and {u_40,u_50}, and applying C_false is an
original proposal output and is incompatible.

(c) S={1,2,3}, B={1,3}, p constantly 1, t=id,
d(3)=0 and d(i)=1 otherwise, and z_i=true exactly when i=2.
H has vertices {s_1,s_2,s_3}, sole edge {s_1,s_2}, and true trait exactly
at s_2. D is admissible and H compatible. Proposal D false H C_false(H)
holds, but C_false(H) is incompatible. Homophily H=some(-1) and
preferential D H=some 0.

(d) S={1,2}, B={1}, p constantly 1, t(i)=i-1 (natural subtraction),
d constantly 1, and z_i=true exactly when i=2. H is the dyad on s_1,s_2,
with its sole edge, trait false at s_1 and true at every other label.
D is admissible, H compatible, and U_D(H) empty. There does not exist
any K with TraitProposal D false H K. Homophily H=some(-1) and
preferential D H=some 0.

## SAP.P012a.T2

For every D, then every state H, then every state K, assuming in order
admissible D, compatible D H, and Proposal D true H K, conclude compatible
D K. There are no nonemptiness or functional-definedness hypotheses.

## SAP.P012a.T3

First, for every D, assuming admissibility, |S|=527, |B|=6, and
sum_(i in S)d_i=4487, in that order, F- has true and false edge counts a,b,
mixed count c_R+3445, and hval(F-)=Qlower.

Second, universally over D with those same hypotheses in the same order:
F- is compatible; Sigma=3445; a+b+c_R=521; F- is H-defined;
hval(F-)=L_h; and its value is <= -1462/1983 and <= -178409/241987 and
strictly less than each of -7027/10000, -6918/10000, -7179/10000.

Third, for every real a,b,c, assuming successively a>=0,b>=0,c>=0 and
a+b+c=521,
`(4ab-(c+3445)^2)/((2a+c+3445)(2b+c+3445)) <= -1462/1983`.
Fourth, for every natural a,b,c with a+b+c=521, that same real quotient
is <= -178409/241987.

Finally the following unconditional numerical identities/inequalities hold:

```
-1462/1983 < -7179/10000 < -7027/10000 < -6918/10000,
-7027/10000 + 1462/1983 = 685459/19830000,
-6918/10000 + 1462/1983 = 450803/9915000,
-7179/10000 + 1462/1983 = 384043/19830000,
phi(260,261,3445) = phi(261,260,3445) = -178409/241987.
```

## SAP.P012a.T4

First, for every D, assuming admissibility, |S|=527, |B|=6, and total reported
degree 4487, then for every real L assumed to be a greatest lower bound of
hValues D, conclude L<=-1462/1983, L<=-178409/241987, and

```
-7027/10000-L >= 685459/19830000,
-6918/10000-L >= 450803/9915000,
-7179/10000-L >= 384043/19830000.
```

Second, for every D, then arbitrary state Hnom, assuming admissibility,
|S|=527, |B|=6, and sum_(i in S)deg_Hnom(s_i)=4487, then for every real L
assumed to be a greatest lower bound of hValues D, and assuming there exists
q in {-7027/10000,-6918/10000,-7179/10000} with |L-q|<=1/20000,
conclude: the reported degree sum is not 4487; there exists i in S with
d_i != deg_Hnom(s_i); and Hnom is incompatible. No simplicity or compatibility
assumption is made on Hnom. A greatest lower bound here means a lower bound
at least as large as every other lower bound; its existence is a hypothesis.

## SAP.P012a.T5

First, for every D, assuming admissibility and then
`Sigma>0 or (2a+c_R>0 and 2b+c_R>0)`, L_h is a member of hValues D and is
<= every member; F- is compatible; homophily F-=some L_h; L_h=Qlower;
and for every H, assuming compatibility and H-definedness in that order,
L_h<=hval(H).

Second, for every D, assuming admissibility, |S|=527, |B|=6, and reported
degree sum 4487, Sigma=3445, a+b+c_R=521, L_h<=-1462/1983 and
L_h<=-178409/241987. The first part allows undefined compatible states;
only their defined values enter hValues.

## SAP.P012a.T6

First, for every D, assuming admissibility, D_false>0, and D_true>0, in that
order, the following entire conjunction holds:

* For every H, if compatible, putting A=e_true(H), B=e_false(H), C=c(H),
  `den(H)=(2A+C)(2B+C)/(2(A+B+C))`, den(H)>0, and hval(H)=phi(A,B,C).
  Also a<=A<=a+Sigma_true, b<=B<=b+Sigma_false,
  c_R<=C<=c_R+Sigma, and L_h<=hval(H)<=U_h.
* F- and F+ are compatible, homophily F-=some L_h and homophily F+=some U_h.
* Every compatible state is H-defined, L_h is the attained least member of
  hValues D, and U_h is its attained greatest member.

Second, independently, for every real x,y,c, assuming 2x+c!=0 and then
2y+c!=0, `phi(x,y,c)=(4xy-c^2)/((2x+c)(2y+c))`.

## SAP.P012a.T7

First, for every D, assuming admissibility and |B|<|S|, in that order:

* For every H, assuming compatibility, then every j in N_D, the set
  {s_k:k in C_j} is a subset of T_H(p(j),j). There exist naturals y,q
  (depending on D,H,j) such that y<=sigma_(p(j)), q<=y,
  |T_H(p(j),j)|=|C_j|+y, |M_H(p(j),j)|=q_j+q, and
  `q_j/(|C_j|+sigma_(p(j))) <= (q_j+q)/(|C_j|+y)
    <= (q_j+sigma_(p(j)))/(|C_j|+sigma_(p(j)))`.
* F+ and F- are compatible; preferential D F+=some L_p and
  preferential D F-=some U_p.
* Every compatible state is P-defined, L_p is the attained least member of
  pValues D, and U_p is its attained greatest member.

Second, independently quantified for every D, assuming admissibility and
|B|<|S|, then for every j in N_D, j is in C_j and |C_j|>0.

## SAP.P012a.T8

No hypotheses. Define D by S={1,2,3}, B={1}, p(3)=2 and p(j)=1 otherwise,
t=id, d(2)=2 and d(i)=3 otherwise, z_i=true exactly when i=3.
H has vertices {s_1,s_2,s_3,u_40}, edges
{12,23,13,1u,3u} (where u=u_40 and ij denotes {s_i,s_j}), and true trait
exactly at s_3. Let K=C_true(H-1u-3u+13). Then D is admissible and H
compatible; 1<3; 3 is a nonseed with p(3)!=1; r_1<d_1 and r_3<d_3;
1u,3u,13 all belong to E_H; K is incompatible; I_D(H) and I_D(K) have
equal edge sets; V_K=V_S; E_K={12,23,13}; the degrees of s_1,s_2,s_3
are (3,2,3) in H and (2,2,2) in K.

## SAP.P012a.T9

No hypotheses. Use the same D as T8. H has vertices
{s_1,s_2,s_3,u_40,u_50}, edges {12,23,1u,3v,1v,3u} with u=u_40,v=u_50,
and true trait exactly at s_3 and v. Let K=H-1u-3v+1v+3u.
D is admissible; H is compatible; r_1<d_1,r_3<d_3;
z_1=false,z_3=true,Z_H(u)=false,Z_H(v)=true;
1u,3v,1v,3u all belong to E_H; K is incompatible;
V_K=V_H; E_K={12,23,1v,3u}; the degree vectors in the displayed vertex
order are (3,2,3,2,2) in H and (2,2,2,1,1) in K; |E_H|=6, |E_K|=4.

## SAP.P012a.T10

For every D, assuming admissibility, then every natural i,j, assuming in order
i in S, j in S, t_i<t_j, not (j in N_D and p(j)=i), r_i<d_i, r_j<d_j,
there exist states H,K, in that order, such that both are compatible;
{s_i,s_j} is absent from H and present in K;
E_(I_D(H))=E_R and E_(I_D(K))=E_R union {{s_i,s_j}};
both I_D(H),I_D(K) satisfy InducedCompatible; and there exists
v in U_D(H) with {s_i,v},{s_j,v} both in E_H and
`K=C_true(H-{s_i,v}-{s_j,v}+{s_i,s_j})`.
The quantified H,K,v are chosen witnesses, not arbitrary starting graphs.

## SAP.P012a.T11

Three conjunctions, with independent quantifier blocks:

(1) For every D, assuming admissibility, then every natural i,j, assuming
i in S, j in S, r_i<d_i, r_j<d_j, and z_i!=z_j in that order,
there exist H,K such that both are compatible, H=F+;
{s_i,u_i0},{s_j,u_j0} are present in H and {s_i,u_j0},{s_j,u_i0} absent;
K is H with those two present edges removed and the two absent edges added;
H,K have equal vertex sets, edge counts and total trait functions;
for every vertex v in the whole universe their degrees are equal;
den(H)>0, den(H)=den(K), hval(H)-hval(K)=2/den(H), hval(H)!=hval(K),
and hValues D is not a singleton.

(2) For every D, assuming admissibility, then every natural i,j, assuming
i in S, j in S, r_i<d_i, r_j<d_j, z_i=false, z_j=true;
then for every state H, assuming V_H=V_(F+), E_H=E_(F+),
Z_H(s_k)=z_k for every k in S, Z_H(u_i0)=false, Z_H(u_j0)=true,
let K be the same two-edge swap and Q=sum_(v in V_H)deg_H(v)x_v.
Conclude compatibility of H,K; the same four edge presence/absence facts;
equal vertices, total traits and edge counts; equality of degrees for every
vertex; den(H)=Q-Q^2/(2|E_H|)=Q(2|E_H|-Q)/(2|E_H|);
den(H)=den(K)>0; and, writing j*=s_j and v*=u_j0,

```
hval(H)-hval(K)
 = [2(1-deg_H(j*)deg_H(v*)/(2|E_H|))
     -2(0-deg_H(j*)deg_H(v*)/(2|E_H|))]/den(H)
 = 2/den(H) != 0.
```

The traits of other unsampled vertices in H are arbitrary.

(3) Unconditionally take S={1,2}, B={1}, p constantly 1, t=id,
d constantly 2, and z_i=true exactly when i=2. H has vertices
{s_1,s_2,u_30,u_40}, edges {12,1u,2v}, true traits exactly at s_2,u_40.
K is H-1u-2v+1v+2u. D is admissible; H,K compatible;
|E_H|=3; sum_(v in V_H)deg_H(v)x_v=3; den(H)=den(K)=3/2;
homophily H=some(1/3), homophily K=some(-1);
hval(H)-hval(K)=4/3=2/den(H).

## SAP.P012a.T12

No hypotheses. S={1,2,3}, B={1}, p constantly 1, t(i)=i-1,
d(1)=3 and d(i)=1 otherwise, and z constantly true.
For beta Boolean, H_beta has vertices {s_1,s_2,s_3,u_40}, edges
{12,13,1u}, all s-labels true, and all u-labels of trait beta.
D is admissible and H_true,H_false are compatible; r_1<d_1; p(2)=1;
for every i in S, {s_i,u_40} is an edge of H_true iff i=1;
T_(H_true)(1,2)={s_2,s_3,u_40}, T_(H_true)(1,3)={s_3,u_40};
preferential D H_true=some 0 and preferential D H_false=some(5/12);
pval(D,H_true)=0, pval(D,H_false)=5/12, and their difference is -5/12.
The number of nonseeds is 2. The two expressions
`-1/(|N_D| |T_(H_true)(1,2)|)` and
`-1/(|N_D| |T_(H_true)(1,3)|)` are respectively -1/6 and -1/4;
the difference -5/12 is unequal to each.

## Mathlib semantic checks made for this reading

`Mathlib/Data/Finset/Defs.lean` defines a finite set as a multiset without
duplicates. `Card.lean:47` defines its cardinality. `Filter.lean:52,127`,
`Image.lean:279,293`, `SDiff.lean:58`, `Erase.lean:49,57`, and
`Range.lean:64` give the ordinary filter, set image, set difference, deletion,
and {0,...,n-1} meanings used above. Finite union and finite sums have their
ordinary set-union and sum meanings. In particular insertion does not add a
second copy of an existing edge.

`Mathlib/Order/Bounds/Defs.lean:34-52` defines lower/upper bounds, IsLeast,
IsGreatest and IsGLB (the duals are generated by `to_dual`). Thus an IsLeast
or IsGreatest asserts membership as well as an extremal inequality, whereas
an IsGLB asserts a greatest lower bound, without asserting attainment.
`Mathlib/Logic/Function/Basic.lean:645,669` gives the point-update meaning.
`Mathlib/Algebra/GroupWithZero/Basic.lean:402` states real division by zero is
zero. Raw hval,pval,phi are therefore totalized; the option-valued functionals
and their definedness predicates are separate, substantive conditions.
