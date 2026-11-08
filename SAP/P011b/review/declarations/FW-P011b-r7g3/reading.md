# Blind reading

Saved before opening `claims.json` or `record.json`. Sources read: every entry of
`closure.json`, the four Challenge docstrings and statements, and the relevant
declarations in Defs Parts 1, 2, 3, 8, 9 and 10. The generated auxiliary declarations
were also inspected with Lean in `scratch/Blind.lean`. This document records the
elaborated mathematical content, without deciding fidelity to a claim not yet read.

## SAP.P011b.T25

Source: `Challenge/Part1.lean:93–96`; `Defs/Part9.lean:13–32`.

Objects and quantifiers: for every natural number (n>1), every recruitment graph
(R), every function (d:\{0,\ldots,n-1\}\to\mathbb N), and every real vector
(x\in\mathbb R^n), the following conjunction holds. A graph here is a Boolean
matrix on `Fin n` which is symmetric and has false diagonal: a finite, undirected,
simple graph. Write (a_{ij}(A)=1) when its Boolean entry is true and 0 otherwise;
(\deg_A(i)=\sum_j a_{ij}(A)) is a natural number. A graph (A) is feasible when
(a_{ij}(R)\le a_{ij}(A)) for every pair and (\deg_A(i)\le d_i) for every vertex.
Saying (A) maximizes an objective means that (A) is feasible and every feasible
(B) has objective at most that of (A). There is no feasibility hypothesis on
((R,d)), and no graph is asserted to exist in this theorem.

All sums below range over `Fin n`. Put

\[
 \bar x=\frac{\sum_i x_i}{n},\quad z_i=x_i-\bar x,\quad
 S=\sum_i z_i^2,\quad s^2=S/n,\quad
 Q_A=\sum_i\sum_j a_{ij}(A)z_i z_j,
\]
\[
 D_A=\sum_i\sum_j a_{ij}(A),\quad
 t_i=\min(d_i,n-1),\quad T=\sum_i t_i.
\]
Natural degrees and (n) are cast into the reals in real arithmetic. The six
estimators, fully unfolded, are

\[
 V_1(A,x)=(S+Q_A)/n^2,\qquad
 V_2(A,x)=(S/n)/n\,(1+D_A/n),\qquad
 V'_2(d,x)=(S/n)/n\,(1+T/n),
\]
\[
 V_{1R}(A,x)=S/[n(n-1)]+Q_A/n^2,\quad
 V_{2R}(A,x)=S/[n(n-1)](1+D_A/n),\quad
 V'_{2R}(d,x)=S/[n(n-1)](1+T/n).
\]
The conclusion, with its internal quantifier order, is:

1. For every graph (A), (V_1\le V_{1R}) and (V_2\le V_{2R});
   also (V'_2\le V'_{2R}).
2. If (S>0), all these three comparisons are strict, for every graph (A).
3. For every graph (A), (A) maximizes (V_{1R}) iff it maximizes (V_1),
   and (A) maximizes (V_{2R}) iff it maximizes (V_2), over the feasible graphs
   defined above.
4. For all real (\beta,c), if (\forall i, |x_i-\beta|\le c), then for every
   graph (A),
   (0\le n(V_{1R}-V_1)\le4c^2/(n-1)).
5. For every graph (A), splitting the two terms gives exactly
   (S/n^2+Q_A/n^2=V_1), and (S/n^2(1+D_A/n)=V_2).
   Also (S/n^2(1+T/n)=V'_2). These are the displayed formulas obtained by
   correcting the helper's centered-squares divisor.
6. For every graph (A),
   (V_{1R}-V_1=S/[n^2(n-1)]=s^2/[n(n-1)]),
   (V_{2R}=n/(n-1)V_2), and (V'_{2R}=n/(n-1)V'_2).

There are no probability, equal-means, bounded-degree, or homoskedasticity
hypotheses. The bounded-vector condition is local to item 4. The docstring
describes exact discrepancies, ordering, maximizers and a bound; it does not itself
state an asymptotic limit.

Junk-value audit: Lean's real division by zero is total, but (n>1) makes every
displayed denominator positive. The natural subtraction in (t_i) is truncated,
but (n\ge2) makes it ordinary (n-1). The subtraction in the real denominators
is real subtraction. The vertex type is nonempty. A negative (c) cannot satisfy
the bounded-vector hypothesis, because there is a vertex and absolute values are
nonnegative; this creates no hidden assumption in the other clauses. Infeasible
((R,d)) makes the two maximizer equivalences comparisons of two false predicates,
but the other universal identities and inequalities remain substantive. There are
no integrals, logs, roots, real powers, suprema, limits, partial functions or
infinite-valued quantities. The generated `helperCorrection._proof_1` is merely
the numeral typeclass proof that 4 is at least two (needed for notation for powers).

## SAP.P011b.T26

Source: `Challenge/Part1.lean:98–100`; `Defs/Part9.lean:34–83`, together with
the finite probability and family definitions in Defs Parts 1–3.

This theorem has no parameters or hypotheses. It asserts a conjunction of four
fixed propositions, not a universal equality of helper and paper formulas. For
each vector below define (\bar x,z,S,Q_A,D_A,t_i,T) and the six estimators by
the explicit formulas in the T25 section (here every numerical example has (n=3)).
The meanings of graph and feasibility are the symmetric, loopless Boolean
matrices and degree/recruitment inequalities spelled out there. The empty graph
has every Boolean entry false. The complete graph has entry true precisely at
distinct vertices. `edge12` has its sole undirected edge between the first two
coordinates (Lean indices 0 and 1).

The first component asserts all of these fixed examples:

* (x=(0,1,2)), empty recruitment and empty graph, (d=(0,0,0)): feasibility,
  (\bar x=1,S=2), (V_1=V_2=V'_2=2/9),
  (V_{1R}=V_{2R}=V'_{2R}=1/3), and each paper/helper pair is unequal.
* (x=(0,0,3)), empty recruitment, graph consisting of edge12,
  (d=(1,1,0)): feasibility, (\bar x=1,S=6),
  (V_1=8/9,V_2=V'_2=10/9),
  (V_{1R}=11/9,V_{2R}=V'_{2R}=5/3), and each pair is unequal.
* (x=(0,1,2)), empty recruitment, complete graph and (d=(2,2,2)):
  feasibility, (V_1=0,V_{1R}=1/9), and inequality of the two values.

The second component concerns a particular sequence of probability models. At
stage (k\in\mathbb N), (n_k=k+1), and the law on (\mathbb R^{n_k}) is the
pushforward of the uniform probability mass function on the finite, nonempty
set `Fin (k+1) → Fin 3`, by (u\mapsto(i\mapsto\operatorname{real}(u_i))).
Thus coordinates are independent and uniform on (\{0,1,2\}). Every atom in the
image has probability (3^{-n_k}). The model weights are all 1; its dependency
and recruitment graphs are empty and all its degree caps are zero.

Here is the complete meaning of all model/family notions used in this component:

* A model stores a probability measure (\mu) on real vectors, real weights
  (\theta_i), two graphs and natural caps. Its weighted observation is
  (w_i(y)=\theta_i y_i), and its statistic is
  (b(y)=n^{-1}\sum_i w_i(y)). An expectation is the real Bochner integral
  (\int f(y)\,d\mu(y)). The target is (\beta=\int b\,d\mu), variance of
  (f) is (\int(f-\int f\,d\mu)^2d\mu), and covariance entry (i,j) is
  (\int(w_i-\int w_i d\mu)(w_j-\int w_j d\mu)d\mu).
* A family requires positive sizes tending to infinity and a model at each size.
  Nestedness means the sizes are monotone and, for each consecutive pair, an
  injection of the smaller vertex set into the larger one preserves all dependency
  graph entries. It requires no coupling of probability laws across stages.
* Dependency means: for all disjoint finite vertex subsets (U,V), if no dependency
  graph edge joins them, the coordinate vectors (y\mapsto(y_i)_{i\in U}) and
  (y\mapsto(y_j)_{j\in V}) are independent random variables under the model law.
  Independence is Mathlib `IndepFun` on the finite products of real Borel spaces.
* Scaling with four constants means nestedness; strict positivity of all four;
  dependency at every stage; almost surely, for every coordinate,
  (|w_i-\beta|\le c_1); every true degree at most (c_2);
  (n_k\operatorname{Var}(b)\to c_3) in the real topology; and
  (|\theta_i|<c_4) for every stage and coordinate.
* Validity means that each model's true graph contains its recruitment graph and
  respects every degree cap. Homoskedasticity means all diagonal covariance
  entries of the weighted observations are equal. The scaled true variance is
  (n_k\operatorname{Var}(b)).

The theorem asserts scaling for exactly (c_1=c_2=1,c_3=2/3,c_4=2), validity,
and, for every (k), homoskedasticity, (\beta_k=1), and
(n_k\operatorname{Var}(b_k)=2/3). Thus the limit clause has strictly positive
limit. All these assertions are made about the explicit family, not supplied as
hypotheses.

The third component asserts for its size-three model that (\beta=1),
(3\operatorname{Var}(b)=2/3), homoskedasticity, dependency, and probability
exactly (1/27) of the singleton event (y=(0,1,2)). The definition of real
probability is `μ.real E`, namely `ENNReal.toReal (μ E)`.

The fourth component supplies exact auxiliary computations:

* For the first empty-graph example, (Q_A=D_A=T=0).
* For the edge12 example, (z=(-1,-1,2)), (Q_A=D_A=T=2),
  (V_{1R}/V_1=11/8) and (V_{2R}/V_2=V'_{2R}/V'_2=3/2).
* For the complete-graph example, (Q_A=-2) and, for every real (C),
  (C V_1<V_{1R}). This compares (0) with (1/9); it takes no ratio at zero.

The docstring calls the printed claim false and describes three distinguishing
vectors, one with positive probability in an admissible family. The blind
statement alone establishes the computations and family, without specifying the
printed assertion being negated.

Junk-value audit: all helper evaluations have (n=3), hence denominators (n),
(n^2), (n-1), and (n(n-1)) are positive. The two types of ratio in the
second example have positive denominators (8/9) and (10/9). The complete-graph
example deliberately has (V_1=0), but uses multiplication rather than division
by that number. Family sizes start at 1 and have no zero-size averages. The
uniform source sets are nonempty, so uniform PMFs use positive finite
cardinalities. All coordinate statistics and products have finite support, are
measurable and integrable, and all moments used exist. Therefore the Bochner
integral's default zero for nonintegrable functions is irrelevant here. Measures
are probability measures, hence sigma-finite, and no `toReal` is applied to
infinity. Natural casts are the usual exact finite casts; natural subtraction in
truncated degree is ordinary subtraction at size three. Empty subsets in the
dependency condition are allowed and give the ordinary constant empty vector;
they do not eliminate the nonempty-subset independence requirements. The limit
is `Tendsto`, with no `limsup` or order-completeness defaults. No logs, square
roots, real powers, infima, suprema or partial-function defaults occur.

Auxiliary declarations: `Scaling._proof_1` supplies the outer measure instance;
the complete, edge12 and empty graph proof fields verify symmetry and a false
diagonal. `threePointModel._proof_1` proves its finite source type nonempty and
`._proof_2` supplies probability mass one. The reused `signFamily._proof_2` and
`._proof_3` prove positivity of (k+1) and its divergence. The eight
`helperExamples._proof_*` and `threePointWitness._proof_1` are numeral
`AtLeastTwo` instances. None adds an undisclosed mathematical condition.

## SAP.P011b.T27

Source: `Challenge/Part1.lean:102–106`; `Defs/Part10.lean:13–32`, including
`Defs/Part8.lean:34–51`.

Objects and outer quantifier order: for every natural (n>0), every pair of
graphs (R,G), every natural cap vector (d), every proof that (G) is feasible
for (R,d), and every (x\in\mathbb R^n), the following conjunction holds.
Graphs are all symmetric, zero-diagonal Boolean matrices on `Fin n`; adjacency
(a_{ij}) is their entry indicator and degree is the natural count of true entries
in a row. Let

\[
 K=\{A: (\forall i,j, R_{ij}=\mathrm{true}\Rightarrow A_{ij}=\mathrm{true})
             \ \land\ (\forall i,\deg_A(i)\le d_i)\}.
\]
The hypothesis is precisely (G\in K). Define
(\bar x=(\sum_i x_i)/n,z_i=x_i-\bar x,S=\sum_i z_i^2,s^2=S/n),
(Q_A=\sum_{ij}a_{ij}(A)z_i z_j,D_A=\sum_{ij}a_{ij}(A)),
(V_1(A,x)=(S+Q_A)/n^2), and
(V_2(A,x)=(S/n)/n(1+D_A/n)).
An objective maximizer means exactly (A\in K\) and
(\forall B\in K,f(B)\le f(A)).

First, (K) is finite and nonempty. Second, for every function
(f:\operatorname{Graph}(n)\to\mathbb R), there exists (A\in K) maximizing
(f), and for every maximizing (A), (f(G)\le f(A)); if (G) also maximizes
(f), then (f(G)=f(A)). This is an assertion for arbitrary real objectives,
which in particular includes both variance objectives.

Third, the finite matrix programs obey all of the following:

1. For every graph (A), the real row-sum inequalities
   (\sum_j a_{ij}(A)\le d_i), together with every entrywise inequality
   (a_{ij}(R)\le a_{ij}(A)), hold iff (A\in K).
2. For every graph (A), it maximizes (Q_A) over (K) iff it maximizes (V_1).
3. For every graph (A), (n^2V_1(A,x)=n s^2+Q_A).
4. For every graph (A), maximizing (D_A) over (K) implies maximizing (V_2).
5. If (s^2>0), for every graph (A), maximizing (V_2) implies maximizing
   (D_A). The positivity qualification is part of this implication.

Fourth, all eight clauses below assert the equivalence with upper-triangular
binary edge programs, independently universally quantified as indicated:

* The map from Boolean assignments (b:E_n\to\{\mathrm{false},\mathrm{true}\}),
  (E_n=\{(i,j)\in\operatorname{Fin}(n)^2:i<j\}), to graphs is bijective.
  It puts (b(i,j)) in both symmetric positions for (i<j) and false on the
  diagonal. The reverse map reads the entries with (i<j).
* For every assignment (b) and real data vector (u), with
  (v_i=u_i-\sum_j u_j/n),
  (Q_{A(b)}=2\sum_{e=(i,j)\in E_n:b(e)=\mathrm{true}}v_i v_j).
* For every (b) and vertex (i), the matrix degree equals the number of selected
  pairs incident to (i). The edge-based degree explicitly counts each pair once
  when either endpoint equals (i).
* For every recruitment graph, cap vector and assignment, graph feasibility is
  equivalent to selecting each forced upper-triangular edge and obeying those
  incident-edge degree caps.
* For every recruitment graph, cap vector, assignment (b) and data vector (u),
  (A(b)) maximizes (V_1) iff it is feasible and every feasible assignment has
  weighted edge sum at most that of (b), using weights (v_i v_j).
* For every (b,u),
  (n^2 V_1(A(b),u)=n s_u^2+2\sum_{e=(i,j):b(e)=\mathrm{true}}v_i v_j).
* For every (b), (D_{A(b)}=2\sum_{e:b(e)=\mathrm{true}}1).
* The finite cardinality of (E_n) is the natural number (n(n-1)/2), using
  natural subtraction and natural division.

The docstring describes existence, sharp oracle bounds and finite integer
programs. The oracle bound concerns the value at the designated feasible graph
(G). It makes no assertion about true statistical variance or asymptotic
conservativeness. The objects are arbitrary deterministic data, so no stochastic
or homoskedasticity hypotheses are needed.

Junk-value audit: (n>0) excludes zero denominators in all three displayed
quantities involving division. The natural expression (n-1) in the edge count
is ordinary subtraction for (n\ge1), and (n(n-1)) is even, so natural
division by 2 gives the exact cardinality. For (n=1), (E_n) is empty and there
is exactly one graph; the corresponding empty sums are zero and the assertions
retain their stated meaning. Feasibility is nonvacuous because (G\in K) is a
hypothesis. The (s^2=0) case is explicitly excluded from the reverse edge-count
maximization implication, as required when (V_2\) is constant zero. There is no
supremum default: existence is existential quantification over a finite nonempty
set. No integrals, logs, roots, real powers, limit defaults or partial-function
defaults occur. `fromUpper._proof_2` verifies the graph symmetry/diagonal fields;
`correlationIdentity._proof_1` is just the reused numeral instance for 2.

## SAP.P011b.T28

Source: `Challenge/Part1.lean:108–112`; `Defs/Part10.lean:34–38`.

Objects and quantifier order: for every natural (n>0), every three graphs
(R,G,A), every natural cap vector (d:\operatorname{Fin}(n)\to\mathbb N),
every proof that (G) contains (R) and has each degree at most (d_i), every
real vector (x), and every proof that (A) is feasible and maximizes the
specified objective, the following inequalities and conditional equality hold.
Each graph is a symmetric, false-diagonal Boolean matrix. Write (a_{ij}(B))
for its 0/1 real indicator, (\deg_B(i)) for the natural number of true row
entries, and define

\[
 \bar x=\sum_i x_i/n,\quad z_i=x_i-\bar x,\quad
 s^2=\sum_i z_i^2/n,\quad D_B=\sum_i\sum_j a_{ij}(B),
 \quad t_i=\min(d_i,n-1).
\]
The objective is (V_2(B,x)=s^2/n(1+D_B/n)). Specifically, the maximizer
hypothesis is that (A) contains every edge of (R), each of its degrees is at
most (d_i), and every graph (B) with these same properties satisfies
(s^2/n(1+D_B/n)\le s^2/n(1+D_A/n)).

The conclusion is exactly

\[
 \frac{s^2}{n}(1+D_G/n)\le
 \frac{s^2}{n}(1+D_A/n)\le
 \frac{s^2}{n}\left(1+\frac{\sum_i\min(d_i,n-1)}n\right),
\]

and, if (\forall i,\deg_A(i)=\min(d_i,n-1)), the second inequality is an
equality. This is a sufficient condition for equality; there is no converse.
Neither positivity of (s^2) nor a probability model is assumed. The word
homoskedastic in the docstring names the estimator, while the deterministic
inequality itself needs no homoskedastic data-generating assumption.

Junk-value audit: all divisors are positive because (n>0). For (n=1),
natural (n-1=0), every simple graph is empty, and all centered squares and all
three displayed estimates are zero. This is an ordinary boundary case. The
vertex type is nonempty. The truncated caps are exactly (min(d_i,n-1)), with
no negative integer casts. At any size constant data gives (s^2=0), so all
estimates coincide even without cap saturation; the theorem only asserts a
sufficient condition and does not misidentify that case. Feasibility and
maximization are actual hypotheses, with no empty-set supremum convention.
There are no integrals, logs, square roots, real powers, infinite values,
infima, suprema, limit defaults or partial-function defaults.
