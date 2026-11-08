# Blind reading of the Challenge

This file was written after reading only `SAP/P044/Defs.lean`, all eight
`SAP/P044/Defs/Part*.lean` files, the Challenge files, and the referenced
Mathlib definitions. Neither `claims.json` nor `record.json` has been read.
The theorem docstrings have been seen; the readings below follow the types,
not the docstrings. There are eleven theorem stubs, T1–T10 and T13.

## Shared objects and definitions, expanded

Write (I_N=\{0,\ldots,N-1\}). An assignment is any function
(z:I_N\to\{\mathrm{false},\mathrm{true}\}). An adjacency is any Boolean
matrix (A:I_N\times I_N\to\{\mathrm{false},\mathrm{true}\}); the type does
**not** impose symmetry, zero diagonal, or positive degree. Such conditions
must be in an individual clause. A true Boolean represents 1.

The treated-peer count is
(s_i(A,z)=\sum_{j\in I_N}1\{A_{ij}=\mathrm{true},z_j=\mathrm{true}\}).
The four exposures, in the order used below, are (11,10,01,00): own
treatment true/false and treated-peer count positive/zero. This is a finite
type of exactly four distinct constructors.

A `FiniteDesign Ω` consists of a finite type Ω and real weights (P_\omega\ge0)
with \(\sum_\omega P_\omega=1\). It does not require every weight positive.
`expect p T` is exactly the finite sum \(\sum_\omega p_\omega T_\omega\), and
`designVariance p T` is \(\sum_\omega p_\omega T_\omega^2-(\sum_\omega
p_\omega T_\omega)^2\). These two definitions also accept arbitrary weights
and the stated algebraic coefficient types, without themselves imposing a
probability law. They are used with real probability designs or with the
explicit rational masses below.

An outcome schedule is an arbitrary function (y:I_N\times D\to K),
where (D) is an exposure type and (K) is the indicated field. For an
exposure map (f:\Omega\to I_N\to D), observed outcome (i) at \(\omega\)
is (y_i(f_\omega(i))). Set

* \(\tau_y(a,b)=N^{-1}\sum_i(y_i(a)-y_i(b))\).
* \(p_i(a)=\sum_\omega P_\omega1\{f_\omega(i)=a\}\).
* \(p_{ij}(a,b)=\sum_\omega P_\omega
  1\{f_\omega(i)=a,f_\omega(j)=b\}\).
* For supplied weights (w), (H_i(a;\omega)=
  1\{f_\omega(i)=a\}y_i(a)/w_i(a)), with the implementation returning
  exactly zero on the other branch. (H(a)=N^{-1}\sum_iH_i(a)), and
  (T(a,b)=H(a)-H(b)).

For supplied (w,q), define the two total-level estimators

\[
V_a=\sum_{i,j}\left[
1\{q_{ij}(a,a)>0,f_i=a,f_j=a\}y_i(a)y_j(a)
\left(\frac1{w_i(a)w_j(a)}-\frac1{q_{ij}(a,a)}\right)
+1\{i\ne j,q_{ij}(a,a)=0\}
\left(\frac{1\{f_i=a\}y_i(a)^2}{2w_i(a)}+
\frac{1\{f_j=a\}y_j(a)^2}{2w_j(a)}\right)\right],
\]
\[
C_{ab}=\sum_{i,j}\left[
1\{q_{ij}(a,b)>0,f_i=a,f_j=b\}y_i(a)y_j(b)
\left(\frac1{w_i(a)w_j(b)}-\frac1{q_{ij}(a,b)}\right)
-1\{q_{ij}(a,b)=0\}
\left(\frac{1\{f_i=a\}y_i(a)^2}{2w_i(a)}+
\frac{1\{f_j=b\}y_j(b)^2}{2w_j(b)}\right)\right].
\]

The Challenge's variance estimator is \(\widehat V=(V_a+V_b-2C_{ab})/N^2\).
The indicators describe conditional branches, so an unused reciprocal branch
is not evaluated as a mathematical requirement. The structural-zero surplus is

\[
Z_y(q;a,b)=\frac1{N^2}\left[
\sum_{i\ne j:q_{ij}(a,a)=0}\frac{(y_i(a)+y_j(a))^2}{2}
+\sum_{i\ne j:q_{ij}(b,b)=0}\frac{(y_i(b)+y_j(b))^2}{2}
+\sum_{i,j:q_{ij}(a,b)=0}(y_i(a)-y_j(b))^2\right].
\]

All sums over pairs are ordered sums, including the diagonal except where
explicitly excluded. Common support is the finite set
\(S=\{i:p_i(a)>0\text{ and }p_i(b)>0\}\).

For a bank (f:I_R\to I_N\to D), (c_i(a)) and (c_{ij}(a,b)) count the
bank indices giving the indicated exposure(s), and

\[
q_i(a)=\frac{c_i(a)+1}{R+1},\qquad
q_{ij}(a,b)=\begin{cases}
(c_{ij}(a,a)+1\{i=j\})/(R+1),&a=b,\\
c_{ij}(a,b)/R,&a\ne b.
\end{cases}
\]

These are definitions of returned numbers; they do not assert that (q) is
a coherent probability system. `bankWeight R c` is the real number
\((c+1)/(R+1)\). Counting and graph-degree quantities are natural numbers;
natural subtraction is truncated. Division in \(\mathbb R,\mathbb Q\) is
totalized with (x/0=0). Positive-denominator hypotheses and concrete bank
sizes must therefore be checked separately.

`insertOwn i a u` is the full assignment equal to (a) at (i), and equal
to (u(j)) on the subtype (j\ne i). For a full-assignment schedule
\(Y:I_N\to\{0,1\}^{I_N}\to\mathbb R\), `NoInterference Y` means
\(\forall i\,\forall a\,\forall u\,\forall v,
Y_i(\operatorname{insertOwn}(i,a,u))=
Y_i(\operatorname{insertOwn}(i,a,v))\).
`Interference Y` is the corresponding existential inequality, with
quantifiers \(\exists i\,\exists a\,\exists u\,\exists v\).

`completeProfiles N M` is the set of all (M)-element subsets of (I_N),
using Mathlib `Finset.powersetCard`. `completeProbability` is the rational
number of those subsets producing an exposure at (i), divided by the
number of subsets. Thus its denominator is \(\binom NM\), and it denotes
the usual complete-randomization law when (0\le M\le N\).

For any Boolean adjacency,
(d_i=\sum_j1\{A_{ij}\}),
(r_i=\#\{j\ne i:\exists k,A_{ik}=A_{kj}=\mathrm{true}\}\), and
(a_i=d_i+r_i+d_ir_i\).
In particular (r_i) counts distinct reachable vertices, includes adjacent
vertices reachable in two steps, excludes (i), and does not count walks
with multiplicity. `baseline a g e` is (a|g|+e).
`dilatedOutcomes B` assigns multipliers (2,3/2,5/4,1) to (B_i) at
exposures (11,10,01,00), respectively.

Let (G\sim N(0,1)) and (E\sim N(1,1/16)), independently. Mathlib's
`gaussianReal μ v` uses **variance** (v\in\mathbb R_{\ge0}), not standard
deviation. `normalPair` is exactly the product of these two measures.
`baselineLaw a` is its pushforward under ((g,e)\mapsto a|g|+e), and
`halfNormalLaw` is the pushforward of (N(0,1)) under absolute value.
These maps are continuous/measurable. `normalPopulation N` is the finite
product of N copies of `normalPair`; generated (B_i=a_i|G_i|+E_i).
`standardNormalCDF` is \(\Phi\), Mathlib's probability-measure CDF,
equal to the measure of (({-}\infty,x]\) converted to a real number.

Measure-valued probabilities are in \(\mathbb R_{\ge0}\cup\{\infty\}\).
`Measure.real s` means `(μ s).toReal`; on these probability measures it
is ordinary probability. `variance X μ` is the real conversion of
\(\int\|X-\int X\|^2\,d\mu\); without finiteness this conversion can
discard infinity. Here the asserted (L^2) properties address this issue.
`MemLp X 2 μ` means a.e. strong measurability and finite (L^2) norm.
`Integrable` means a.e. strong measurability with finite absolute integral.
`HasLaw X ν μ` includes both a.e. measurability and \(\mu.map(X)=\nu\).
`IndepFun X Y μ` is independence of the sigma algebras generated by (X,Y).
Mathlib's `bernoulliMeasure true false p` has true probability (p), and
`binomial R p` is the law of the count in R independent Bernoulli trials.

For T10 a Mathlib `SimpleGraph` is a symmetric, irreflexive relation.
Its degree counts distinct neighbors. Its `edgeFinset` counts unordered
edges once, represented by `Sym2`; `withinEdges G c` retains exactly edges
whose endpoints have the same community label. For arbitrary real (s,t_i),
`blockEdgeProbability s t c i j` is (s t_i t_j1\{c_i=c_j\}), with no
automatic bound in [0,1] or construction of a random graph.

Mathlib source checks: `Probability/Distributions/Gaussian/Real.lean`
(gaussianReal); `Probability/CDF.lean`; `Probability/Moments/Variance.lean`;
`Probability/HasLaw.lean`; `Probability/Independence/Basic.lean` and
`Probability/Independence/Kernel/IndepFun.lean`;
`Probability/Distributions/Bernoulli.lean` and `Binomial.lean`;
`MeasureTheory/Function/LpSeminorm/Defs.lean`;
`MeasureTheory/Measure/{Map,Prod,Real}.lean`;
`MeasureTheory/Constructions/Pi.lean`; `Data/Finset/Powerset.lean`;
`Data/Fin/SuccPred.lean`; `Combinatorics/SimpleGraph/{Basic,Finite}.lean`.

## SAP.P044.T1

This is an unconditional conjunction about the following rational example.
There are twelve units, partitioned into three complete four-vertex graphs
by the integer quotient (i/4). The 66 assignments are all unordered pairs
(u<v) in lexicographic order, with exactly that pair treated. Exposures
are computed using this adjacency. Outcomes are 1 for every unit and every
exposure. A bank indexed by (t\in I_{66}) consists of all assignments
except assignment (t), each once (Mathlib `succAbove` skips exactly (t)).
Its size is 65, and its returned weights/joints are the smoothing rules
above. Equivalently the marginal count vector before omission is
((3,8,27,28)); a weight is (full count minus the omitted indicator plus
1)/66. A returned same-exposure joint is (full joint count minus its
omitted indicator plus the diagonal indicator)/66; a cross-exposure joint
is (full joint count minus its omitted indicator)/65. These subtractions
are in the natural numbers. The full joint counts at distinct units are
(17/9) for (01,01), (28/6) for (00,00), and (0/15) for (01,00)
according as the units are in the same/different cliques; diagonal counts
are marginal counts for equal exposures and 0 otherwise. Other full joint
counts are defined by direct enumeration.

Let (T(t,z)) and (V(t,z)) be the (01-00) HT contrast and its variance
estimator using this omitted-bank table, evaluated at observation (z).
The two joint rational laws on ((t,z)\in I_{66}^2) are
(P_0(t,z)=1/4356) for every pair, and
(P_1(t,z)=1/4290) when (t\ne z), 0 otherwise. In the second law the
observation is always in the retained bank. T1 asserts all of the following:

1. The explicit exposure formula equals adjacency-derived exposure for
   every assignment and unit. For every Boolean assignment (z), treating
   exactly two units is equivalent to being one of the 66 assignments.
   The assignment list is injective; each assignment treats two units.
   Adjacency is symmetric, loopless, and every vertex has a neighbor.
2. Every unit has exact marginal (p_i(01)=9/22), (p_i(00)=14/33).
   For every omitted (t), the retained list is injective, omits assignment
   (t), and both relevant returned marginal weights are strictly positive
   at every unit. The target contrast is zero.
3. With exact marginal and joint probabilities under the uniform 66-law,
   (E T=0), \(\operatorname{Var}T=6050/11907\), and
   \(E\widehat V=6050/11907\).
4. Under (P_0), the four quantities (ET,\operatorname{Var}T,EV,
   EV-\operatorname{Var}T) respectively equal
   \(-67/53592\), \(113448938731/232640299584\),
   \(1040129476423/2326402995840\), and
   \(-953130413/23499020160\).
5. Under (P_1), those four quantities respectively equal
   \(-67/52780\), \(11375808887/23342482800\),
   \(4673362763/10414338480\), and \(-20161943/522324075\).
6. For each Boolean choice of joint law, (EV<\operatorname{Var}T)
   and (EV<6050/11907).
7. For bank (t=0), under uniform fresh observations, variance and expected
   estimator are \(2810528137/5767941312\) and
   \(267260522663/634473544320\). For bank (t=3), they are
   \(937589375/1922647104\) and \(4830430961/10574559072\).
8. Every unit's full (01,00) counts are 27,28. For every distinct (i,j),
   the three full joint counts are the same/different-clique values given
   above. For every assignment the numbers exposed to (01,00) are 2,8
   when its treated pair is in one clique and 6,4 otherwise. Exactly 18
   treated pairs are within a clique and 48 are between cliques.
9. For **every** omitted (t), variance and expected estimator under uniform
   fresh observations are the corresponding (t=0) values if its treated
   pair shares a clique, and the corresponding (t=3) values otherwise.
   Their differences are respectively \(-1551761941/23499020160\) and
   \(-72513467/2349902016\), and are strictly negative.
10. For every observation with exact weights, the contrast equals
    \(-220/189\) for a within-clique pair and \(55/126\) otherwise.
11. For every omitted bank and unit, both explicit weights equal the general
    smoothed weights. For every (t,i,j,a,b), if each of (a,b) is in
    \(\{01,00\}\), the explicit returned joint equals the general
    smoothed joint.
12. For every omitted assignment (t) there exists a permutation (e) of
    the twelve vertices preserving adjacency for all (i,j), such that
    (z_t(e(i))=z_0(i)) for all (i) if its pair shares a clique, and
    (z_t(e(i))=z_3(i)) otherwise.

There is no assertion here for arbitrary bank size, arbitrary banks,
other sampling/reuse mechanisms, or numerical approximate computation.

## SAP.P044.T2

The first conjunct universally quantifies, in this order: types Ω and D,
natural N, a finite-type structure on Ω, decidable equality on D, a proof
(N>0), a real finite probability design P, an exposure map f, a real
schedule y, exposures a,b, a proof (a\ne b), and proofs
\(\forall i,p_i(a)>0\) and \(\forall i,p_i(b)>0\). It concludes both

\[
E_P\widehat V-\operatorname{Var}_P T=Z_y(p_{ij};a,b),\qquad
\operatorname{Var}_P T\le E_P\widehat V.
\]

The second conjunct, with no hypotheses, says for **each** Boolean choice
of the two explicit T1 joint laws, \(EV<\operatorname{Var}T\).
There is no Gaussian, infinite-population, Hajek, or error-tolerance clause.

## SAP.P044.T3

The concrete design is the four-vertex star with center 0 and the six
assignments treating, respectively, pairs 23,13,12,03,02,01, uniformly.
Schedule A is 1 everywhere. Schedule B is 5 at (center,00) and 1 elsewhere.
All concrete outcomes and probabilities in the first and last blocks are
rational. This unconditional conjunction asserts:

1. Every vertex has a neighbor and each assignment treats two units.
   Center probabilities in exposure order 11,10,01,00 are
   \((1/2,0,1/2,0)\); each leaf's are \((1/6,1/3,1/3,1/6)\).
   Every observed outcome under either schedule is 1.
   \(\tau_A(11,00)=0\), \(\tau_B(11,00)=-1\).
2. The star adjacency is symmetric and loopless. The assignment list is
   injective. For every assignment z, treating two units is equivalent
   to equaling a listed assignment.
3. For **every** real-valued function T of assignment, exposure vector and
   observed real outcome vector, form its random values TA and TB under
   the two schedules. Their expectations under the six-point uniform law
   are equal, and it is impossible for (E TA=0) and (E TB=-1) jointly.
4. Let f be this exposure map and p its exact rational marginal table.
   For **every proof** that \(\forall r,i,a,f_r(i)=a\Rightarrow p_i(a)>0\),
   and then every Boolean flag, set y=A if the flag is true and y=B
   otherwise. Then (EH(11)=1), (EH(00)=3/4), (ET(11,00)=1/4);
   bias is (1/4) for A and (5/4) for B.

The last block is an implication with an explicit support hypothesis;
the earlier blocks do not depend on it.

## SAP.P044.T4

This is a conjunction of seven blocks.

1. Universally quantify Ω,D,N, finiteness of Ω, decidable equality on D,
   (N>0), finite design P, f,y,a,b, (a\ne b), and positive exact
   marginal probabilities for a and b at every unit. Each exact HT term
   for a is unbiased for (y_i(a)), the a and b HT means are unbiased
   for their respective population means, their contrast is unbiased
   for \(\tau_y(a,b)\), and every exact b-term is unbiased for (y_i(b)).
2. Universally quantify Ω,D,N and these finite/decidable structures,
   (N>0), P, an assignment map z, f,y,a,b, (a\ne b), a unit j with
   (p_j(a)=0), a real \(\delta\ne0\), and any estimator function T of
   assignment, exposure vector and observed outcomes. Set
   (y'_i(e)=y_i(e)+\delta1\{i=j,e=a\}\). On every \(\omega\) with
   (P_\omega>0), all observed outcomes of y and y' coincide. The two
   estimator expectations are equal; their target effects differ by
   \(\delta/N\); the estimator cannot be unbiased for both effects.
   No relationship between z and f is imposed.
3. Universally quantify Ω,D,N and finite/decidable structures, P,f,y,a,b,
   (a\ne b), and nonemptiness of their common support S. The mean over
   S of the a-minus-b exact HT terms is unbiased for
   \(|S|^{-1}\sum_{i\in S}(y_i(a)-y_i(b))\). Nonempty S ensures a positive
   denominator and also implies (N>0).
4. For the star, common support for 11,00 is exactly \(\{1,2,3\}\).
   For each of the two schedules (the Boolean flag selects B when true,
   A when false), the restricted true contrast and the expectation of
   its restricted exact HT estimator are zero.
5. For **all** N,M with (N>0), (1\le M\le N-1), symmetric loopless
   Boolean A, and **then each** unit i, let k be its degree. Under uniform
   complete randomization of M treated units,
   \[
   p_i(10)=\binom{N-1-k}{M-1}/\binom NM,\quad
   p_i(00)=\binom{N-1-k}{M}/\binom NM,
   \]
   \(p_i(11)=M/N-p_i(10)\),
   \(p_i(01)=(N-M)/N-p_i(00)\), and
   \[
   (\forall a,p_i(a)>0)\ \Longleftrightarrow\
   2\le M\ \land\ 1\le k\ \land\ k\le N-M-1.
   \]
6. For every symmetric loopless adjacency on 1000 units and then every i,
   all four complete-randomization probabilities at M=100 are positive
   exactly when \(1\le k\le899\).
7. The star center's exact 00 and 10 probabilities are zero; every star
   vertex has a neighbor and the center has degree 3.

## SAP.P044.T5

Write \(m=\sqrt{2/\pi}\), \(v=1-2/\pi\). The unconditional conjunction
asserts the following, with independent G,E as defined above:

1. On the triangle, each unit has degree 2, two-step reachable count 2,
   and scale 8. For vectors (g=(1/64,1,-1/2)) and
   (e=(-3/4,1,5/4)), the baseline vector is \((-5/8,9,21/4)\).
   Its first entry is negative.
2. For every triangle i,j, \(\sum_k1\{i\ne k\}1\{k\ne j\}\) is 2 on
   the diagonal and 1 off it. The analogous count written as a single
   conjunction indicator has the same values.
3. For the baseline vector above, the outcome vectors at 11,10,01,00
   are respectively \((-5/4,18,21/2)\), \((-15/16,27/2,63/8)\),
   \((-25/32,45/4,105/16)\), and \((-5/8,9,21/4)\).
4. For **every real a** and **then a proof (a\ge0)**, the event
   \(|G|<1/[4(a+1)],-1<E<-1/2\) has positive probability. For every
   real pair x in that event, (a|x_1|+x_2<-1/4).
5. For **every (a\ge0)**, `baselineLaw a` gives positive probability
   to \(({-}\infty,0)\); the half-normal gives it probability zero;
   the two probability measures are unequal.
6. The probability of \(-1/32<G<1/32,-1<E<-1/2\) equals
   \([\Phi(1/32)-\Phi(-1/32)][\Phi(-6)-\Phi(-8)]>0\).
   For every g,e in those respective intervals, (8|g|+e<-1/4).
7. \(E|G|=m\), \(\operatorname{Var}|G|=v\), and \(E|G|^2=1\).
8. For **every (a\ge0)**, \(E(a|G|+E)=am+1\) and its variance is
   \(a^2v+1/16\). In particular at a=8 these are (8m+1,64v+1/16);
   the mean and variance shifts from the half-normal are (7m+1) and
   (63v+1/16), both strictly positive.
9. For **every N, Boolean adjacency A with all degrees at least 1, and
   then every unit i**, the mean shift of its scale-(a_i) baseline
   relative to the half-normal is at least 1. No symmetry or looplessness
   is assumed in this block.
10. For **every real a**, (a|G|+E\in L^2(\text{normalPair})\), and
    \(|G|\in L^2(N(0,1))\).
11. For **every (a\ge1)** the mean shift is exactly \((a-1)m+1\).

There is no assertion identifying this ideal Gaussian probability model
with an actual implementation or a pseudorandom generator.

## SAP.P044.T6

This unconditional conjunction states:

1. For **every N, real baseline vector B, and then every i**, outcomes
   at 00,11,10,01 equal \(B_i,2B_i,(3/2)B_i,(5/4)B_i\).
2. For **every (a\ge0)** the baseline mean and variance are (am+1)
   and (a^2v+1/16). Also \(E|G|=m\) and \(E|G|^2=1\).
   For **every real a**, the baseline is in (L^2).
3. For **every (N>0) and every B**, the population effects 11-00,
   10-00,01-00 are respectively \(\bar B,\bar B/2,\bar B/4\), where
   \(\bar B=N^{-1}\sum_i B_i\).
4. For (B=(-5/8,9,21/4)), \(\bar B=109/24\), and these three effects
   are \(109/24,109/48,109/96\).
5. For **every (N>0), Boolean A, and proof its diagonal is false**,
   under the independent `normalPopulation N` law,
   \[
   E\tau(11,00)=1+m\frac{\sum_i a_i}{N}.
   \]
6. With the same quantifier order and the additional hypothesis every
   degree is at least 1, that equality holds, \(E\tau(11,00)\ge1+m\),
   and (m<1).
7. For **every measurable space Ω, N>0, probability measure P, vector-valued
   random B, and proof each coordinate B_i has half-normal law**, the
   expected 11-00 effect is (m), and (m<1). Independence among B_i
   is **not** assumed.
8. For **every (N>0) and Boolean A**, the generated 11-00 effect is
   integrable under `normalPopulation N`, without a diagonal hypothesis.
9. For **every measurable Ω, (N>0), probability measure P, random B
   and coordinate half-normal-law hypotheses**, its 11-00 effect is
   integrable under P.

## SAP.P044.T7

The graph is the undirected cycle on eight vertices; the eight assignments
are cyclic shifts of the treated set \(\{0,1,3\}\). Outcomes are constant
across units, with values (2,3/2,5/4,1) in exposure order.
Let f be its exposure map, p the marginals under the uniform eight-law,
and q the smoothed weights from this entire eight-assignment bank.
All numerical computations here are rational. T7 asserts:

1. The graph has no isolated vertices and the assignment list is injective.
   For **every unit and exposure**, bank counts are \((2,1,3,2)\),
   p is \((1/4,1/8,3/8,1/4)\), q is \((1/3,2/9,4/9,1/3)\).
   At every unit the sum of q over exposures is (4/3).
2. For **every assignment and exposure**, the smoothed-weight HT means
   are \((3/2,27/32,135/128,3/4)\); exact-weight means equal the
   respective potential outcomes.
3. For unit pair (0,1), the sum over b of the returned (q_{01}(11,b))
   is (17/72\ne1/3=q_0(11)). The expected smoothed 11-00 contrast
   is (3/4), whereas its target is 1.
4. Each assignment treats three units. For **every assignment and exposure**
   the numbers of units in the four exposure categories are \((2,1,3,2)\).
5. For **every assignment**, the smoothed 11-00,10-00,01-00 contrasts
   are \(3/4,3/32,39/128\); their differences from the targets are
   \(-1/4,-13/32,7/128\). The latter two targets are (1/2,1/4).
6. For **every assignment**, the three exact-weight contrasts equal
   (1,1/2,1/4). For **every unit and exposure**, p is strictly positive.

## SAP.P044.T8

The first block quantifies, in order, natural R,N, a finite type D with
decidable equality, (R>0,N>0), any bank f, real schedules y,w, an
exposure a, and positive supplied (w_i(a)) for all i. It asserts:

1. For all i,j,b, \(p_i(a)=c_i(a)/R\) and
   \(p_{ij}(a,b)=c_{ij}(a,b)/R\) under the uniform bank law.
2. \(EH_w(a)=N^{-1}\sum_i y_i(a)p_i(a)/w_i(a)\).
3. **If**, additionally, all exact (p_i(a)>0), then exact-weight HT
   mean expectation is \(N^{-1}\sum_i y_i(a)\).
4. With smoothed q, the bias is
   \[
   EH_q(a)-N^{-1}\sum_i y_i(a)
   =N^{-1}\sum_i y_i(a)\frac{c_i(a)-R}{R(c_i(a)+1)}.
   \]
5. For every i, \((c_i(a)/R)/q_i(a)-1\) equals the displayed coefficient,
   which is strictly negative **if** (c_i(a)<R). The subtraction in
   this coefficient is real subtraction, not truncated natural subtraction.
6. **If** \(|D|\ge2\), then for every i,
   \(\sum_b q_i(b)=(R+|D|)/(R+1)>1\).

The second block separately quantifies measurable Ω, probability μ,
**any natural R including zero**, (p\in[0,1]), Boolean random variable D,
natural-valued C, their Bernoulli(p) and Binomial(R,p) laws, independence
of D and C, and then proofs (0<p<1). The random variable
\(1\{D\}/[(C+1)/(R+1)]\) is integrable and has expectation
\(1-(1-p)^{R+1}<1\).

## SAP.P044.T9

This is the conjunction of the following universal statements:

1. For every N and full-assignment real schedule Y,
   `Interference Y` is equivalent to the negation of `NoInterference Y`.
2. For every such N,Y, no interference is equivalent to:
   for every i,z,z', if (z_i=z'_i), then (Y_i(z)=Y_i(z')).
3. For every N,A,z,i, treated-peer count equals the cardinality of
   \(\{j:A_{ij}=\mathrm{true},z_j=\mathrm{true}\}\).
4. For every N,A,i, proof (A_{ii}=\mathrm{false}), assignments z,z',
   and proof \(\forall j\ne i,z_j=z'_j\), the two peer counts at i agree.
5. For every N,A,z,i, each of the four exposure equalities is equivalent
   to its respective own-treatment and positive/zero peer-count condition.
6. For every N,i,z, inserting (z_i) into the restriction of z away from
   i reconstructs z exactly.

The stubs make no statement about matrix shapes of a printed expression.

## SAP.P044.T10

Four independent universal blocks:

1. For every N, type C with decidable equality, real s, real vertex
   weights t, community map c, vertices i,j, and proof (c_i\ne c_j),
   the algebraic expression (s t_i t_j1\{c_i=c_j\}) is zero.
2. For every finite Ω, C with decidable equality, N, real finite design P,
   family of decidable simple graphs G, community maps c, and hypothesis
   that for each i,j the P-probability of adjacency **and** unequal
   communities is zero: for every state \(\omega\) of positive mass,
   and every i,j, adjacency implies equal communities.
3. For every N,C, (N>0), decidable simple graph G, c, proof all degrees
   are positive, and proof all adjacent vertices share a community,
   \(\sum_i\deg(i)=2|E|\), \(N\le2|E|\), \(|E|>0\),
   \(|E_{\rm within}|=|E|\), their ratio is 1, and the ratio minus
   (7/10) is (3/10).
4. For every finite Ω,C,N, (N>0), finite design P, decidable graph
   family G, c, proof **every** graph/state has all degrees positive,
   and proof **every** graph/state has only within-community edges,
   \(E(|E_{\rm within}|/|E|)=1\),
   \(E|E_{\rm within}|/E|E|=1\), and each quantity minus (7/10)
   equals (3/10). The hypotheses here include zero-mass states too.

The algebraic expression in block 1 is not connected by a hypothesis or
construction to a random-graph law in blocks 2–4. No rejection sampling
process, sampling feasibility, or almost-sure termination is stated.

## SAP.P044.T13

For **every natural N**, **every Boolean adjacency A**, and **every proof
its diagonal is false**, if (N>0), then it is not the case that for
**every vertex i** its ideal-Gaussian generated baseline law
\(\mathcal L(a_i|G|+E)\) equals the half-normal law. Equivalently, for
each such nonempty loopless A there exists a vertex with unequal laws.
No symmetry, no-isolate hypothesis, simulation design, effect contrast,
or claim about bias/variance estimators appears. This is solely a
negation of universal baseline-law equality in the supplied ideal model.
