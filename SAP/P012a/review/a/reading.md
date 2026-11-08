# Blind reading of the Lean statements

Saved before opening `claims.json` or `record.json`. This reading uses only the
Challenge files, their complete Defs import closure, and the referenced Mathlib
definitions. A Challenge docstring is not treated as a mathematical hypothesis.
There are twelve theorems, all in `SAP/P012a/Challenge/Part1.lean`; the aggregate
Challenge file only imports them. Every theorem has the closed proposition
described below: there are no implicit section parameters.

## Objects and notation, with all definitions expanded

`Vertex` is the disjoint union of the natural numbers and pairs of natural
numbers. Write `s_i` for the left label `i` and `u_{i,k}` for the right label
`(i,k)`. All these labels are distinct as dictated by the disjoint union; in
particular no `s_i` is a `u_{j,k}`. Being sampled is determined by membership,
not by which summand a label occupies.

A datum D consists of finite subsets A (sampled indices) and B (seed indices)
of N, and total functions parent p:N->N, time t:N->N, degree d:N->N, and
binary trait x:N->{false,true}. Values of these functions outside A are
unconstrained. Set N_D=A\B, S_A={s_i:i in A}, and
R={{s_{p(j)},s_j}:j in N_D}. Edges here and everywhere below are finite sets
of vertices, and an edge collection is itself a finite set: duplicate insertions
have no multiplicity. Define r_i as the number of members of R containing s_i,
e_i=d_i-r_i in natural-number subtraction, E=sum_{i in A} e_i,
E_b=sum_{i in A,x_i=b} e_i, and D_b=sum_{i in A,x_i=b} d_i.
Natural subtraction is truncated at zero; `Admissible D` supplies r_i<=d_i
at every sampled index, so it is ordinary subtraction wherever used here.

`Admissible D` means all four of the following, with the displayed universal
quantifiers: B subset A; for every i in A and j in A, t_i=t_j implies i=j;
for every j in N_D, p(j) belongs to A and t_{p(j)}<t_j; and for every i in A,
r_i<=d_i. There is no explicit positive sample size, number of seeds, trait
variation, or positive degree requirement in this predicate. Times record a
strict ordering, rather than durations.

A state H=(V_H,F_H,z_H) consists of a finite vertex set, a finite set of
finite vertex sets, and a total Boolean trait function on all vertex labels.
Write deg_H(v)=#{e in F_H:v in e}. `Simple H` means that for every e in F_H,
e has exactly two elements and e subset V_H. Thus a simple state represents a
finite simple undirected graph with no loops or parallel edges. `Augmented D H`
means simplicity and, for every e in F_H, existence of i in A with s_i in e;
no edge can join two unsampled vertices. `Compatible D H` means:

1. H is augmented;
2. S_A subset V_H and R subset F_H;
3. for every i in A, z_H(s_i)=x_i;
4. for every v in V_H\S_A, there exists i in A with {s_i,v} in F_H;
5. for every i in A, deg_H(s_i)=d_i.

In particular unsampled isolated vertices are forbidden, while sampled isolated
vertices are allowed. There is no separate fixed ambient population size.
`GraphCompatible` is the same predicate with the sampled-trait equality omitted.
It is not an additional hypothesis of any of the twelve theorems.

For a state, put Z_v=1 if z_H(v)=true and 0 otherwise, m=|F_H|, and
A_vw=1 if v!=w and {v,w} in F_H, otherwise 0. Define the real numbers

    Num(H) = sum_{v,w in V_H} (A_vw-deg_H(v)deg_H(w)/(2m)) Z_v Z_w,
    Den(H) = sum_{v,w in V_H} (1_{v=w}deg_H(v)-deg_H(v)deg_H(w)/(2m)) Z_v Z_w,
    h(H) = Num(H)/Den(H).

The sums run over ordered pairs, including diagonal pairs. `HomophilyDefined H`
means m>0 and Den(H)!=0. `homophily H=some q` means this domain condition holds
and h(H)=q; otherwise `homophily H=none`. The unguarded real quotient h is
totalized by Lean's convention a/0=0; the `some` assertions do not use that
convention to assign an undefined functional a value.

For i,j in N, define the susceptible set U_H(i,j) to contain the neighbors v
of s_i in V_H for which either v is unsampled or v=s_k with k in A and
t_j<=t_k. (The actual code treats every right label as unsampled, and a left
label s_k as unsampled if k not in A.) Define M_H(i,j) as the subset whose
trait equals z_H(s_i). The current recruit s_j is eligible at time t_j.
For j in N_D let o_j=1 if x_j=x_{p(j)} and 0 otherwise. Define

    p_D(H) = (1/|N_D|) sum_{j in N_D}
      (1_{z_H(s_j)=z_H(s_{p(j)})} - |M_H(p(j),j)|/|U_H(p(j),j)|).

`PreferentialDefined D H` means |N_D|>0 and, for every j in N_D,
|U_H(p(j),j)|>0. `preferential D H=some q` asserts this domain condition and
p_D(H)=q; otherwise its value is `none`.

Let a_H and b_H count edges all of whose vertices have respectively true and
false traits, and c_H count edges containing both traits. On a simple state
these are the three edge types and partition the edges. The definitions are
finite filters, not counts with multiplicity. Let a,b,c denote these counts
in the recruitment state (S_A,R, with trait x_i on s_i and false on right
labels). `traitDegree H b` sums degrees over vertices of trait b, and
`degreeTraitSum H` is Q_H=sum_{v in V_H}deg_H(v)Z_v.

Define

    phi(x,y,c)=1-c/(2x+c)-c/(2y+c),
    L_h=phi(a,b,c+E),
    U_h=phi(a+E_true,b+E_false,c),
    lowerQuotient=(4ab-(c+E)^2)/((2a+c+E)(2b+c+E)).

For each j, C_j={k in N_D:p(k)=p(j), t_j<=t_k}, n_j=|C_j|, and
q_j=#{k in C_j:x_k=x_{p(j)}}. Set

    L_p=(1/|N_D|)sum_{j in N_D}(o_j-(q_j+e_{p(j)})/(n_j+e_{p(j)})),
    U_p=(1/|N_D|)sum_{j in N_D}(o_j-q_j/(n_j+e_{p(j)})).

All quotients displayed here are real quotients after casting counts to R.
`hValues D`={q in R: there exists a state H compatible with D and
homophily H=some q}; `pValues D` is defined identically using preferential.
`FullHomophilyRegion D L U` says every compatible H has defined homophily,
L belongs to hValues and is <= every member, and U belongs and is >= every
member. `FullPreferentialRegion` has the corresponding meaning for p.
Neither definition says every real number between L and U is attained.
`PointIdentified X` means there exists a real q with X exactly the singleton
{q}. `IsGLB X L` means L<=every member of X and every lower bound of X is <=L;
unlike `IsLeast`, it does not itself assert L belongs to X.

The leaf completion H^+ has V=S_A union {u_{i,k}:i in A,0<=k<e_i},
F=R union {{s_i,u_{i,k}}:i in A,0<=k<e_i}, sampled traits x_i, and trait
x_i on u_{i,k}. H^- has the same vertices and edges and opposite trait on
each such leaf. On *all* left labels their traits are x_i; on *all* right
labels u_{i,k}, including labels outside the vertex set, they use x_i or
its negation. These are `leafCompletion D true/false` respectively.

`induced D H` has vertices S_A, edges {e in F_H:e subset S_A}, and the same
total trait function as H. `InducedCompatible D J` means J is simple,
V_J=S_A, R subset F_J, and for every i in A, deg_J(s_i)<=d_i. This predicate
does not itself demand sampled-trait agreement (the witnesses below have it
through compatibility of their originating augmented states).

## The execution relations, fully expanded

`removeEdge H v w` erases {v,w} from F_H; `addEdge H v w` inserts it.
Neither operation changes vertices or traits. `addVertex H v b` inserts v
into V_H and changes its trait to b, preserving the trait function elsewhere.
`flipTrait H v` negates just the trait at v. Write U_D(H)=V_H\S_A and
P_i(H)={v in U_D(H):{s_i,v} not in F_H}.
Cleanup with flag false retains exactly the vertices of nonzero degree.
Cleanup with flag true retains exactly the sampled vertices already present
and the vertices of nonzero degree. Cleanup leaves the edge and trait data
unchanged; all degree tests use the state before cleanup.

A replacement of endpoint i, relative to the original H and a pending state J,
is either (v,J) for v in P_i(H), or (v,addVertex J v b) for a label v not in
V_J and a freely selected Boolean b. The fresh case has no extra assumption
that P_i(H) is empty. The existing pool is computed in original H, even when
the pending state has already changed.

A graph execution from H, with cleanup flag f, is any output of one of these
four constructors, with all indicated choices existential:

* Choose i in A and j in V_H, s_i!=j, with {s_i,j} in F_H\R and j unsampled.
  Remove that edge and choose a replacement (v,P) at i. For f=true add
  {s_i,v}; for f=false add both {s_i,v} and {j,v}; then clean up with flag f.
* Choose distinct i,j in A with {s_i,s_j} in F_H\R. Remove this edge and
  choose replacement (v,P) at i. Add {s_i,v}, then choose replacement (w,Q)
  at j (still using original H's pool). Add {s_j,w} and clean up with flag f.
* Choose i in A and j in V_H, s_i!=j, with {s_i,j} absent, and choose v,w in
  U_D(H) with {s_i,v} and {j,w} present. Remove those two edges, add {s_i,j},
  and clean up. The constructor does not separately require j sampled or v!=w.
* Choose i in A and j in V_H, s_i!=j, such that neither
  ({s_i,j} present and not recruitment) nor
  ({s_i,j} absent and there exist v,w in U_D(H) with {s_i,v},{j,w} present)
  holds. The output is cleanup of H.

A trait execution either flips a chosen v in U_D(H), or, only if f=true and
U_D(H) is empty, returns H unchanged. `Proposal D f H K` is the disjunction
of a graph execution and a trait execution. These are relations of possible
executions, not probability measures or claims that choices exist in every
state.

## SAP.P012a.T1

This is a conjunction of four concrete assertions, with no external hypotheses.
All unmentioned function values in the following data are the total functions
specified in Defs; only sampled values affect the stated properties.

(a) D has A={1,2}, B={1}, p constantly 1, t_i=i,
d_i=2 if i=1 and 1 otherwise, and x_i true exactly when i=2.
H has V={s_1,s_2,u_{3,0}}, F={{s_1,s_2},{s_1,u_{3,0}}}, and trait true
exactly at s_2. D is admissible, H is compatible, and P_1(H) is empty.
For **each** Boolean b, form K_b by removing {s_1,u_{3,0}}, adding fresh
u_{4,0} with trait b, adding {s_1,u_{4,0}} and {u_{3,0},u_{4,0}}, and
cleaning up with flag false. K_b is a possible flag-false proposal and is
incompatible. Also homophily H=some(-1/3) and preferential D H=some(-1/2).

(b) D has A={1,2,3}, B={1}, p(3)=2 and p(i)=1 otherwise, t_i=i,
d_i=3 if i=2 and 1 otherwise, x_i true exactly when i=2. H has vertices
{s_1,s_2,s_3,u_{4,0}}, edges {{s_1,s_2},{s_2,s_3},{s_2,u_{4,0}}}, and
trait true exactly at s_2. D is admissible, H is compatible, and P_2(H)
is empty. For **each** Boolean b, removing {s_2,u_{4,0}}, adding fresh
u_{5,0} with trait b, adding {s_2,u_{5,0}} and {u_{4,0},u_{5,0}}, then
cleaning up with flag false gives a possible proposal and an incompatible state.

(c) D has A={1,2,3}, B={1,3}, p constantly 1, t_i=i,
d_3=0 and d_i=1 otherwise, and x_i true exactly when i=2. H has
V={s_1,s_2,s_3}, F={{s_1,s_2}}, and trait true exactly at s_2.
D is admissible and H compatible. Flag-false cleanup of H is a possible
flag-false proposal and is incompatible. Homophily H=some(-1) and
preferential D H=some 0.

(d) D has A={1,2}, B={1}, p constantly 1, t_i=i-1 in natural subtraction,
d constantly 1, and x_i true exactly when i=2. H is the single edge
{s_1,s_2}, with trait false at s_1 and true at every other vertex label.
D is admissible and H compatible; V_H\S_A is empty; **there exists no state K**
with a flag-false trait execution H->K. Homophily H=some(-1) and
preferential D H=some 0. This last assertion concerns the trait branch alone.

## SAP.P012a.T2

For **every D, then every H and K**, if D is admissible, H is compatible
with D, and K is a flag-true proposal from H (either relation just defined),
then K is compatible with D. There is no functional definedness hypothesis,
and no conclusion that an execution exists for every compatible starting state.

## SAP.P012a.T3

The conjunction has five components:

1. For **every D**, if D is admissible, |A|=527, |B|=6, and
   sum_{i in A}d_i=4487, then H^- has true-true count a, false-false count b,
   mixed count c+3445, and h(H^-)=lowerQuotient(D).
2. For **every D** under the same hypotheses, H^- is compatible, E=3445,
   a+b+c=521, H^- has defined homophily, h(H^-)=L_h,
   h(H^-)<=-1462/1983 and <=-178409/241987, and it is strictly less than
   each of -7027/10000, -6918/10000, and -7179/10000.
3. For **every real a,b,c**, if a,b,c>=0 and a+b+c=521, then
   (4ab-(c+3445)^2)/((2a+c+3445)(2b+c+3445))<=-1462/1983.
4. For **every natural a,b,c**, if a+b+c=521, the same real quotient is
   <=-178409/241987.
5. The following closed numerical assertions all hold:
   -1462/1983 < -7179/10000 < -7027/10000 < -6918/10000;
   the differences from -1462/1983 to respectively -7027/10000,
   -6918/10000, and -7179/10000 are 685459/19830000,
   450803/9915000, and 384043/19830000;
   phi(260,261,3445)=phi(261,260,3445)=-178409/241987.

No graph or actual paper dataset is supplied as an argument to the numerical
universal inequalities; a,b,c there are independent variables.

## SAP.P012a.T4

This is the conjunction of two universally quantified implications.

First, **for every D**, assuming admissibility, |A|=527, |B|=6, and degree
sum 4487, **for every real L** which is a GLB of hValues(D),

    L<=-1462/1983, L<=-178409/241987,
    -7027/10000-L>=685459/19830000,
    -6918/10000-L>=450803/9915000,
    -7179/10000-L>=384043/19830000.

Second, **for every D and state Hnom**, assume D is admissible, |A|=527,
|B|=6, and sum_{i in A}deg_Hnom(s_i)=4487. There is no simplicity or
compatibility assumption on Hnom and no assumed sum of the reported d_i.
**For every real L**, if L is a GLB of hValues(D) and **there exists** q in
{-7027/10000,-6918/10000,-7179/10000} with |L-q|<=1/20000, then
sum_{i in A}d_i!=4487; **there exists** i in A with
d_i!=deg_Hnom(s_i); and Hnom is incompatible with D.
The theorem does not separately assert existence of a GLB or of such a rounded L.

## SAP.P012a.T5

First, **for every D**, if D is admissible and

    E>0 OR (2a+c>0 AND 2b+c>0),

then L_h is a least member of hValues(D), H^- is compatible,
homophily H^-=some L_h, L_h=lowerQuotient(D), and **for every state H**,
if H is compatible and its homophily is defined, L_h<=h(H).
This does not assert defined homophily for every compatible H on this domain.
Second, **for every D**, if D is admissible, |A|=527, |B|=6, and degree sum
4487, then E=3445, a+b+c=521, L_h<=-1462/1983, and
L_h<=-178409/241987.

## SAP.P012a.T6

First, **for every D**, assume admissibility, D_false>0, and D_true>0.
Then **for every compatible H**, with a_H,b_H,c_H as above,

    Den(H)=((2a_H+c_H)(2b_H+c_H))/(2(a_H+b_H+c_H))>0,
    h(H)=phi(a_H,b_H,c_H),
    a<=a_H<=a+E_true, b<=b_H<=b+E_false, c<=c_H<=c+E,
    L_h<=h(H)<=U_h.

Both H^- and H^+ are compatible; homophily H^-=some L_h and
homophily H^+=some U_h. Every compatible state has defined homophily,
L_h is an attained minimum of hValues(D), and U_h an attained maximum.
Second, **for every real x,y,c**, if 2x+c!=0 and 2y+c!=0,

    phi(x,y,c)=(4xy-c^2)/((2x+c)(2y+c)).

There is no assertion about the time complexity of computing the endpoints.

## SAP.P012a.T7

First, **for every D**, assume admissibility and |B|<|A|. Then **for every
compatible H, then for every j in N_D**, {s_k:k in C_j} subset U_H(p(j),j),
and **there exist naturals y,q** (allowed to depend on D,H,j) with

    y<=e_{p(j)}, q<=y,
    |U_H(p(j),j)|=n_j+y, |M_H(p(j),j)|=q_j+q,
    q_j/(n_j+e_{p(j)}) <= (q_j+q)/(n_j+y)
      <= (q_j+e_{p(j)})/(n_j+e_{p(j)}).

Both H^+ and H^- are compatible; preferential D H^+=some L_p and
preferential D H^-=some U_p. Every compatible state has defined preferential
recruitment, and L_p and U_p are respectively attained minimum and maximum
of pValues(D).
Second, **for every D**, assuming admissibility and |B|<|A|, **for every
j in N_D**, j in C_j and n_j>0. No algorithmic operation count is asserted.

## SAP.P012a.T8

This is closed and concrete. D has A={1,2,3}, B={1}, t_i=i,
p(3)=2 and p(i)=1 otherwise, d_2=2 and d_i=3 otherwise,
and x_i true exactly when i=3. Let w=u_{4,0}. H has

    V_H={s_1,s_2,s_3,w},
    F_H={{s_1,s_2},{s_2,s_3},{s_1,s_3},{s_1,w},{s_3,w}},

with trait true exactly at s_3. K is obtained by erasing {s_1,w} and
{s_3,w}, inserting {s_1,s_3}, then applying flag-true cleanup.
D is admissible, H compatible, 1<3, 3 in N_D, p(3)!=1,
r_1<d_1 and r_3<d_3, and all three edges {s_1,w},{s_3,w},{s_1,s_3}
are in H. K is incompatible. The sampled induced edge sets of H and K
are equal. In addition,

    V_K=S_A,
    F_K={{s_1,s_2},{s_2,s_3},{s_1,s_3}},
    (deg_H(s_1),deg_H(s_2),deg_H(s_3))=(3,2,3),
    (deg_K(s_1),deg_K(s_2),deg_K(s_3))=(2,2,2).

## SAP.P012a.T9

Use exactly the preceding datum D and w=u_{4,0}, v=u_{5,0}. Now H has

    V_H={s_1,s_2,s_3,w,v},
    F_H={{s_1,s_2},{s_2,s_3},{s_1,w},{s_3,v},{s_1,v},{s_3,w}},

with trait true exactly at s_3 and v. K erases {s_1,w},{s_3,v} and
inserts {s_1,v},{s_3,w}, without cleanup. D is admissible and H compatible;
r_1<d_1, r_3<d_3, x_1=false, x_3=true, z_H(w)=false, z_H(v)=true,
and the four selected and cross edges are present. K is incompatible.
Moreover V_K=V_H,

    F_K={{s_1,s_2},{s_2,s_3},{s_1,v},{s_3,w}},
    degrees of H on (s_1,s_2,s_3,w,v)=(3,2,3,2,2),
    degrees of K on that order=(2,2,2,1,1), |F_H|=6, |F_K|=4.

There is no homophily-denominator comparison in the proposition.

## SAP.P012a.T10

**For every D**, assume admissibility; **for every i,j in N**, assume i,j in A,
t_i<t_j, not(j in N_D and p(j)=i), r_i<d_i, and r_j<d_j.
Then **there exist states H,K**, both compatible, for which

    {s_i,s_j} absent in H and present in K,
    F_induced(H)=R, F_induced(K)=R union {{s_i,s_j}},

both induced states satisfy `InducedCompatible`, and **there exists a vertex v**
in V_H\S_A adjacent in H to both s_i and s_j such that K is exactly the
flag-true cleanup of H with those two edges erased and {s_i,s_j} inserted.
H,K and v can depend on D,i,j. There is no assertion that v has no other
neighbors, that it is removed, or that all arbitrary starting H permit this move.

## SAP.P012a.T11

There are three conjuncts.

1. **For every D**, assuming admissibility, **for every i,j in N**, assuming
   i,j in A, r_i<d_i, r_j<d_j, and x_i!=x_j, **there exist states H,K**
   both compatible with D, with H=H^+. Let v=u_{i,0}, w=u_{j,0}.
   H contains {s_i,v},{s_j,w} and does not contain {s_i,w},{s_j,v}.
   K is exactly H with the former two edges erased and the latter two inserted.
   H,K have identical vertex sets, edge counts, and total trait functions;
   **for every vertex label a**, deg_H(a)=deg_K(a). Furthermore
   Den(H)>0, Den(H)=Den(K), h(H)-h(K)=2/Den(H), h(H)!=h(K), and
   hValues(D) is not a singleton. There is no assumed time order or
   non-recruitment relation between i and j.
2. **For every D**, assuming admissibility, **for every i,j**, assuming
   i,j in A, r_i<d_i, r_j<d_j, x_i=false, x_j=true, **for every state H**
   whose vertices and edges equal those of H^+, whose traits agree with x on
   all sampled vertices, and whose traits at u_{i,0},u_{j,0} are respectively
   false,true: let K be the preceding swap, and let
   Q=sum_{v in V_H}deg_H(v)Z_v. Then H,K are compatible; the selected
   edges are present and cross edges absent before the swap; H,K have equal
   vertices, total trait functions, edge counts, and degrees at **every** label;

       Den(H)=Q-Q^2/(2|F_H|)=Q(2|F_H|-Q)/(2|F_H|),
       Den(H)=Den(K)>0,
       h(H)-h(K)=
         [2(1-deg_H(s_j)deg_H(u_{j,0})/(2|F_H|))
          -2(0-deg_H(s_j)deg_H(u_{j,0})/(2|F_H|))]/Den(H)
         =2/Den(H),
       h(H)!=h(K).

   Other unsampled traits are unrestricted, even though the graph is the
   private-leaf graph. Trait values outside the finite vertex sets are also
   unrestricted and unchanged by the swap.
3. A closed instance: D has A={1,2}, B={1}, p constantly 1, t_i=i,
   d constantly 2, x_i true exactly when i=2. H has vertices
   {s_1,s_2,u_{3,0},u_{4,0}}, edges
   {{s_1,s_2},{s_1,u_{3,0}},{s_2,u_{4,0}}}, and trait true exactly at
   s_2 and u_{4,0}. K swaps the two leaf edges as above. D is admissible,
   H,K are compatible, |F_H|=3, Q_H=3, Den(H)=Den(K)=3/2,
   homophily H=some(1/3), homophily K=some(-1), and
   h(H)-h(K)=4/3=2/Den(H).

## SAP.P012a.T12

This is closed and concrete. D has A={1,2,3}, B={1}, p constantly 1,
t_i=i-1 in natural subtraction, d_1=3 and d_i=1 otherwise, and every x_i=true.
For each Boolean b let H_b have vertices {s_1,s_2,s_3,u_{4,0}}, edges
{{s_1,s_2},{s_1,s_3},{s_1,u_{4,0}}}, and trait true at every left label
and b at every right label. D is admissible, H_true and H_false compatible,
r_1<d_1, p(2)=1, and **for every i in A**, {s_i,u_{4,0}} is an edge in
H_true iff i=1. The susceptible sets in H_true are

    U(1,2)={s_2,s_3,u_{4,0}}, U(1,3)={s_3,u_{4,0}}.

Preferential D H_true=some 0 and preferential D H_false=some(5/12);
p_D(H_true)=0, p_D(H_false)=5/12, and their difference is -5/12.
There are exactly two nonseeds. The difference is unequal to both
-1/(|N_D| |U(1,2)|) and -1/(|N_D| |U(1,3)|), and these two expressions
are respectively -1/6 and -1/4. No requirement of defined homophily is imposed
on either state.

## Mathlib meaning checks

The finite-set operations above follow `Mathlib/Data/Finset/Defs.lean`
(a duplicate-free multiset), `Card.lean`, `Filter.lean` (`mem_filter`),
`Image.lean` (`mem_image`, removing duplicates), `SDiff.lean` (`mem_sdiff`),
`Union.lean` (`biUnion`), and `Range.lean` (`mem_range`: k<n).
Finite sums use `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`;
the notation `sum i in A` is a sum once per member of A, not an unrestricted
sum over N. Function modification follows `Mathlib/Logic/Function/Basic.lean`
(`Function.update`). Minimum, maximum, and GLB meanings follow
`Mathlib/Order/Bounds/Defs.lean`: `IsLeast X L` is membership and a lower
bound, `IsGreatest` is its order dual, and `IsGLB X L` is the greatest member
of the set of lower bounds. The real field's zero-division convention is
`Mathlib/Algebra/GroupWithZero/Basic.lean`, `div_zero`. Option `some` and `none`,
Boolean negation, disjoint-union constructors, naturals and real casts have
their ordinary Lean/Mathlib meanings; no SAP predicate further redefines them.
