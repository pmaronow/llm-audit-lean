# Blind reading of the Challenge

This file was written from `SAP/P045a/Defs.lean`, all six Defs parts,
`SAP/P045a/Challenge.lean`, and `Challenge/Part1.lean`, before opening
`claims.json` or `record.json`. Each theorem has no external parameters:
`SAP.P045a.Tj` asserts the closed proposition `SAP.P045a.TjStatement`.
The quantifiers below are inside those propositions. The Challenge stubs
contain `sorry`; this audit concerns their types, not their proofs.

## Common definitions and conventions, expanded

All unit and group indices are zero based. `Fin n` is the set of natural
numbers less than n; `Assignment n` is the set {false,true}^n. A finite
`Design Ω` is a function p:Ω→R with p(w)≥0 for every w and Σ_w p(w)=1.
`expect p X` means Σ_w p(w)X(w), `prob p E` means Σ_{w:E(w)}p(w),
`condMean p E X` means Σ_{w:E(w)}p(w)X(w)/prob(p,E), and
`variance p X` means Σ_w p(w)(X(w)−Σ_v p(v)X(v))². The functions alone do
not require p to be a probability law; theorem hypotheses sometimes do.
`average S X` is Σ_{w∈S}X(w)/|S|, and `mean X` is the same expression over
the whole finite index type. `bit true=1`, `bit false=0`.

These are real divisions: Mathlib assigns x/0=0, including 0/0=0.
Thus empty-arm means, empty averages, and singleton sample variances are
totalized real expressions unless the theorem protects their domains.
`none : Option R` explicitly denotes an undefined value, as distinct from
`some 0`. Natural subtraction is truncated at zero; subtraction after
casting to R is ordinary real subtraction. Finite sums over empty sets are
zero and products over empty sets are one.

The Bernoulli mass B_p(z)=Π_i (p if z_i=true, otherwise 1−p).
F(n,k) is the set of assignments with exactly k treated units; CR(n,k)
assigns mass 1/|F(n,k)| to each member and zero outside. Write K(z) for the
treated count. For a schedule Y_i(z), m_i^b(q)=E_q[Y_i(Z)|Z_i=b].
The observed arm ratio A_b(Y,z) is Σ_{i:z_i=b}Y_i(z)/#{i:z_i=b}.
Its existence predicate is ∃i,z_i=b. The overall group mean O(Y,z) is
n^{-1}Σ_iY_i(z). The Bernoulli arm HT mean is
H_b(p,Y,z)=Σ_{i:z_i=b}Y_i(z)/[n(p if b=true, otherwise 1−p)].

A network is a Boolean, symmetric, loopless adjacency matrix A on Fin n.
Its four exposures are d11=(treated, at least one treated neighbor),
d10=(treated, no treated neighbor), d01=(control, at least one treated
neighbor), d00=(control, no treated neighbor). `exposure` itself accepts
any Boolean matrix. π_i(d;q,D)=P_q(D(Z,i)=d). Given exposure-indexed
outcomes y_i(d), the observed outcome is y_i(D(z,i)); HT total for d is
Σ_{i:D(z,i)=d}y_i(d)/π_i(d). `htObserved` uses an arbitrary assignment
schedule Y_i(z) in that numerator instead. `effect y k l` is the unit mean
of y_i(k) minus that of y_i(l). The own-treatment probability e_i(q) is
P_q(Z_i=true). The naive treated mean is
L(q,A,y,z)=n^{-1}Σ_{i:z_i=true}y_i(D_A(z,i))/e_i(q).
The repaired expansion replaces each summand by
1{D_i=d11}y_i(d11)/e_i+1{D_i=d10}y_i(d10)/e_i.

For G groups with sizes n_g, S(G,C) is the set of all C-element subsets
of Fin G. On (H,(z_g)_g), `selectedLaw n C q` is
1{H∈S(G,C)} |S(G,C)|^{-1} Π_g q_g(z_g). This includes independent draws
for unselected groups. `selectedMean C X` is C^{-1}Σ_{g∈H}X_g(z_g).

For a finite subset S, s²_S(x)=Σ_{i∈S}(x_i−average_S x)²/(|S|−1),
where the denominator is real. `popVar x` is s² on all indices (the
finite-population sample-variance normalization, not the divisor |S|).
For treated set T(z), D(a,b,z)=average_T a−average_{Tᶜ}b.
W(a,b,z) is s²_T(a)/|T| if |T|≥2, else zero, plus
s²_{Tᶜ}(b)/|Tᶜ| if |Tᶜ|≥2, else zero. Define
Vhat_C(a,b;H,z)=[(1−C/G)/C]s²_H(g↦D(a_g,b_g,z_g))
+Σ_{g∈H}W(a_g,b_g,z_g)/(CG).
`requiredDirectVariance` returns `some Vhat` only when C≥2, |H|=C,
and both arms have at least two units in every selected group; otherwise
it returns `none`.

The closed neighborhood N_A[i] is {i}∪{j:A_ij=true}; k_i(z) counts its
treated vertices. T_i is k_i=|N_A[i]|, C_i is k_i=0, and B_i (the
defective control event) is k_i<|N_A[i]|. `fullHT correct` is the mean
over i of 1{T_i}Y_i(z)/P(T_i) minus 1{C_i}Y_i(z)/P(C_i) when correct,
and uses B_i instead of C_i otherwise. `allVsNone Y` is
n^{-1}Σ_i[Y_i(all true)−Y_i(all false)].

### Fixed witnesses

The Bernoulli witness space is Bool×Assignment 4×Assignment 4. For w=(s,u,v),
z_H=u,z_L=v if s=true, and z_H=v,z_L=u otherwise. Its mass is
(1/2)B_{1/2}(z_H)B_{1/4}(z_L). Unit i's outcome is
Y_i(z)=Σ_{j≠i}bit(z_j) (`coMembers`). Witness arm means and their
existence events are A_b(Y,z_r) and E_b^r, for r=H,L. Direct contrast
is D_r=A_true^r−A_false^r; indirect I=A_false^H−A_false^L;
total T=A_true^H−A_false^L; overall Q=O(Y,z_H)−O(Y,z_L).

`edge2` is the single edge on two vertices. Its linear schedule is
Y_i(z)=1+z_0+z_1, and its threshold schedule is
Y_i(z)=1+2·1{z_0=z_1=true}.

`upperCells n` lists (i,j) with 0≤i<j<n in column order (j first).
`lowerCells n` lists (i,j) with 0≤j<i<n in the same column order.
For i>j, `faultyCopy n M i j` looks up the position of (i,j) in the
lower list and copies the upper list entry at that position; outside the
lists its lookup defaults to (0,0). For i≤j it retains M_ij.
`correctedCopy M i j` is M_ji for i>j and M_ij otherwise.
`singleEdge4` is the infinite matrix with ones exactly at (0,3),(3,0).
`upperInput4 u` has independent upper entries u_0,…,u_5 in upper-list
order, reflects them below the diagonal, and has zero diagonal (outside
the 4×4 block its list indices are reduced modulo 6). `matrixExposure`
uses Σ_j z_j M_{j,i}>0, so it reads the column, even on asymmetric input.

The printed ten-vertex adjacency has edges
{01,02,04,12,13,19,23,24,25,28,34,35,36,45,47,67,68,78,79,89}.
`deletionMasks d` is all d-element subsets R of these edges;
`deletedAdj R` removes both orientations of every edge in R.
Let g_i(R) be its degree and b_i=5/2 if i=1, else 1. For the unique
treated vertex t, put S_t={i:deletedAdj R t i}, C_t=V\({t}∪S_t).
The deletion Hajek contrast is
[Σ_{i∈S_t}(5b_i/4)/g_i]/[Σ_{i∈S_t}1/g_i]
−[Σ_{i∈C_t}b_i(1+1{printedAdj t i}/4)/(9−g_i)]/
 [Σ_{i∈C_t}1/(9−g_i)].
Deletion bias β_d is the uniform average of this over R and t, minus 23/80.

For an extended natural distance d, an ε-separated set has d(s,t)≥ε
for distinct members. It covers if every vertex outside it is within
ε−1 of a member. `epsilonNet` means both properties. `marked` is the
union of closed radius ε−1 balls about members. A greedy list cs is
admissible iff for every k<length(cs), its kth vertex is outside the
marked set generated by the first k entries. `pathDistance` is |i−j|
as an extended natural. In T11, Mathlib `SimpleGraph.edist` is instead
the infimum of walk lengths, with distance infinity between disconnected
vertices (Metric.lean:55–122); no connectivity is assumed.

The next-center law is uniform on R=V\marked except that, in coded mode
when R={u}, it is uniform on all indices {0,…,u}, including marked ones.
`traceMass` is the product of successive draw probabilities provided all
proper prefixes are nonterminal and the entire list marks all vertices;
otherwise zero. `terminalCentres S` is the real `tsum`, over all lengths
t≥0, of the sum of trace masses of lists of length t whose underlying
set is S. Mathlib's `tsum` is the ordinary unconditional sum if summable,
and zero otherwise (InfiniteSum/Defs.lean); no summability hypothesis is
part of T10. `nearestCentre S v` selects a member of S with least
(distance to v, index), or returns none for empty S, by merge sort.
`clusterProb S p z` is the B_p-probability over center bits c that every
vertex v has a nearest center s and z_v=c_s. Center bits for noncenters
are auxiliary and marginalized. `clusteredTreatment` sums this against
terminal center-set masses, with ε fixed at 3.

`treatmentPairs` is all (u,v) with 0≤u<v<10; the associated assignment
treats exactly u,v. `pairExposureProb` averages the exposure indicator
over these pairs. `pairHT` is its exposure-specific HT total.
`cycle10` is the undirected ten-cycle. `cycleOut` has outcomes
(d11,d10,d01,d00)=(2,1,1,0). `cycleL` is its naive treated mean with
own probability fixed at 1/5. `cycleR` is the sum of its d11 and d10 HT
totals divided by 10. `cancellingOut2` has (d11,d10)=(2,1) at vertex 0
and (1,2) at vertex 1, with zero control outcomes.

`pooledMean a b A B` is none if a+b=0, otherwise some((A+B)/(a+b)).
`printedPool` is none if a=0 or b=0, otherwise some(A/a+B/b).
Six groups are paired by partner(0)=1, partner(1)=0, partner(2)=3,
partner(3)=2, partner(4)=5, partner(5)=4. Each has 75 units.
For H⊆Fin 6, r(H)=#{g∈H:partner(g)∈H} and k_g(H)=50 for g∈H,
25 otherwise. The tract witness assignment treats the first 50 units
in groups 0,1,2 and the first 25 elsewhere. For arbitrary assignments w,
put k=K(w_g)+K(w_partner(g)). A treated unit's tract outcome is 9/4
if k=100, 2 if k=75, and 3/2 otherwise; a control unit's is 11/8,
5/4, and 1 respectively. Tract observed arm means use these outcomes.
The second-stage law is Π_g CR(75,k_g(H)); the two-stage law first
selects H uniformly from the triples of six groups. Its direct estimator
is the average treated arm mean over H minus the average control arm
mean over H. The all-psi law uses k_g=50 everywhere; psi-psi potential
is the unit outcome conditional on own treatment under that law.
The psi-psi target averages its treated-minus-control differences first
over the 150 units of each paired tract, then over the three tracts.
`dilated b` has exposure outcomes (2b,3b/2,5b/4,b).
`printedContrast` is (pairHT_d11−pairHT_d00)/10 for the printed network
and common baseline 1. `pairCellNonempty d e` asserts that at least one
unit has exposure d under pair e.

## SAP.P045a.T1

All of the following hold, with no hypotheses external to the clauses:

* The witness space has 512 outcomes, its mass sums to one, and every
  mass is nonnegative.
* For every real p, if 0<p<1, then for every i∈Fin 4 and b∈Bool,
  m_i^b(B_p)=3p. For every z and then every i, Y_i(z)=K(z)−z_i.
* For every w and regime r, if both its arms exist, D_r(w)=−1.
* P(E_true^H∧E_false^H)=7/8; the analogous low probability is 87/128.
  P(E_false^H∧E_false^L)=3825/4096 and
  P(E_true^H∧E_false^L)=3825/4096.
* E[I|E_false^H∧E_false^L]=224/255;
  E[T|E_true^H∧E_false^L]=37/255.
* The probability that all four arms exist is 609/1024. Conditional on
  that event, E[I]=16/29 and E[T]=−13/29.
* For every z, O(Y,z)=3K(z)/4, and E[Q]=3/4.
* Under B_{1/2}, the treated and control arm means conditional on their
  own existence are 17/15 and 28/15; under B_{1/4} they are 81/175
  and 84/85 respectively.
* For every r∈Bool, its both-arms probability is 7/8 if high, 87/128
  otherwise, and its direct contrast conditional on that event is −1.
* For every p with 0<p<1, the population mean treated marginal minus
  population mean control marginal is zero.

## SAP.P045a.T2

The conjunction, in order, is:

1. For every n>0, p∈R with 0<p<1, schedule Y_i(z), and b∈Bool:
   for every i, E_{B_p}[1{Z_i=b}Y_i(Z)]=(p if b else 1−p)m_i^b;
   and E_{B_p}H_b=mean_i m_i^b.
2. For every G,C with 0<C≤G, every size vector n_g>0, every
   0<p<1, every group-local schedule Y_{g,i}(z_g), and b,
   E_selected[selectedMean_C(H_b)]=mean_g mean_i m_{g,i}^b(B_p),
   with the independent product law defined above.
3. For every n,k with 0<k<n, every schedule Y, and b,
   E_CR(n,k) A_b=mean_i m_i^b(CR(n,k)).
4. For every G,C with 0<C≤G, size and count vectors with
   0<k_g<n_g for every g, schedules Y and b, the analogous selected
   average of A_b has expectation mean_g mean_i m_{g,i}^b(CR(n_g,k_g)).
5. For every k∈Fin 4 with k>0 (hence k=1,2,3), every unit's CR
   treated/control marginals for coMembers are k−1 and k; their direct
   marginal difference is −1. The corresponding direct marginal
   difference under B_{k/4} is zero.
6. For every n>0, Design q on Assignment n, and Y,
   E_q O(Y,Z)=mean_i E_q Y_i(Z).
7. For every 0<C≤G, n_g>0, local Designs q_g, and local schedules Y,
   E_selected[selectedMean_C(O)]=mean_g mean_i E_{q_g}Y_{g,i}.
8. For every 0<p<1 and every z∈Assignment 4,
   H_true=K(K−1)/(4p), and
   H_false=K(4−K)/(4(1−p)).
9. For every 0<p<1, their B_p expectations are each 3p and the
   expectation of their difference is zero.

## SAP.P045a.T3

Let G=6, C=3, n_g=3, x=(1,2,3), q_m be the selected product CR(3,m)
law, point(a,b) the selected average D, and vest(a,b)=Vhat_3.

* For every m∈{1,2}, E point(x+1,x)=1,
  Var point(x+1,x)=1/2, and E vest(x+1,x)=1/3.
* For m=2 and (a,b)=(2x,5x/4), Var point=9/8, E vest=43/48.
* For m=1 and (a,b)=(3x/2,x), Var point=8/9, E vest=19/36.
* For m=2 and (a,b)=(x,0), Var point=1/18, E vest=1/9.
* Separately, for x=(1,2,3) and every m∈{1,2}, under one CR(3,m)
  draw, E D(x+1,x)=1, Var D=3/2, and E W(x+1,x)=1/2.

## SAP.P045a.T4

1. For every G,C with 2≤C≤G, then size and count vectors n,m with
   2≤m_g and m_g+2≤n_g for every g, and then arbitrary real a_g,b_g,
   define θ_g=mean a_g−mean b_g,
   V_g=popVar(a_g)/m_g+popVar(b_g)/(n_g−m_g)
       −popVar(a_g−b_g)/n_g.
   Under the independent CR local laws and uniform group selection:
   every local D has mean θ_g and variance V_g;
   E point=mean θ;
   Var point=[(1−C/G)/C]popVar θ+Σ_g V_g/(CG);
   E Vhat−Var point=Σ_g[popVar(a_g−b_g)/n_g]/G²≥0;
   and equality E Vhat=Var point holds iff for every g and all i,j,
   a_gi−b_gi=a_gj−b_gj.
2. For every 2≤C≤G and arbitrary a,b:Fin G→Fin 3→R, let bias_m be
   E Vhat−Var point under independent CR(3,m) and group selection.
   bias_2=Σ_g[popVar(a_g−b_g)/3−popVar(b_g)]/G² and
   bias_1=Σ_g[popVar(a_g−b_g)/3−popVar(a_g)]/G².
3. For every 2≤C≤G and every x:Fin G→Fin 3→R, the preceding bias
   for m=2,(a,b)=(2x,5x/4) is −11Σ_g popVar(x_g)/(8G²);
   for m=1,(a,b)=(3x/2,x) it is −13Σ_g popVar(x_g)/(6G²).
   If there exist g,i,j with x_gi≠x_gj, both biases are strictly negative.
4. For every m∈{1,2}, a,b:Fin 6→Fin 3→R, H∈S(6,3), and full
   group-assignment vector w such that every selected w_g∈F(3,m),
   requiredDirectVariance_3(a,b;H,w)=none.

## SAP.P045a.T5

On edge2, every closed neighborhood is the full two-vertex set. For
every vertex, assignment (true,false) satisfies B_i but not C_i; under
B_{1/2}, P(T_i)=1/4, P(B_i)=3/4, P(C_i)=1/4.
For the linear schedule the all-versus-none target is 2; the defective
contrast at 00,01,10,11 is respectively −4/3,−8/3,−8/3,12; its
expectation is 4/3 and the corrected contrast expectation is 2.
For the threshold schedule the target is 2 and both defective and
corrected contrast expectations are 2. These are unconditional fixed
finite statements with no external hypotheses.

## SAP.P045a.T6

1. For every n, Network A, assignment z, and vertex i, in that order:
   Σ_j z_j·bit(1{j=i} or A_ji)=k_i and the corresponding row sum of
   the closed-neighborhood adjacency is |N_A[i]|; k_i≤|N_A[i]|;
   T_i iff all neighborhood bits are true; C_i iff all are false;
   B_i iff some is false; C_i implies B_i;
   B_i∧¬C_i iff 0<k_i<|N_A[i]|;
   [for every assignment v, C_i(v) iff B_i(v)] iff |N_A[i]|=1;
   T_i and C_i cannot both hold; T_i iff not B_i.
2. For every finite type Ω, Design p, decidable event E, and Y:Ω→R,
   if P_p(E)>0 then E_p[1_E Y/P_p(E)]=E_p[Y|E].
3. For every n>0, Design p, Network A, and assignment schedule Y,
   assume, for all i,z, T_i(z)⇒Y_i(z)=Y_i(all true) and
   C_i(z)⇒Y_i(z)=Y_i(all false), and assume both extreme-event
   probabilities are positive for every i. Then corrected fullHT has
   expectation allVsNone(Y); defective fullHT has expectation
   mean_i[Y_i(all true)−E(Y_i|B_i)]. Additionally, if for every i,z,
   B_i(z)⇒Y_i(z)=Y_i(all false), defective fullHT has expectation
   allVsNone(Y).

## SAP.P045a.T7

The singleEdge4 matrix is symmetric on all natural indices with zero
diagonal. Faulty copying at n=4 gives entries (0,3)=1, (3,0)=0,
(2,1)=1, (1,2)=0. The upper list is
[(0,1),(0,2),(1,2),(0,3),(1,3),(2,3)] and the lower list is
[(1,0),(2,0),(3,0),(2,1),(3,1),(3,2)]. For every n≥4 their
zero-based entries at position 2 are (1,2) and (3,0); for every n≤3
and every valid upper-list index k, the lower entry is the transposed
upper entry. Among all 64 Boolean upper inputs at n=4 exactly 32 have
an asymmetric faulty output. Under assignment 0001, vertex 0 changes
from d01 to d00; under 0010, vertex 1 changes from d00 to d01.
For every real q with 0≤q<1, a Boolean deletion draw of mass q on true
produces either the zero matrix (true) or faultyCopy(singleEdge4)
(false), and the probability of equality to the latter is 1−q.

## SAP.P045a.T8

The printed graph has 20 edges and mean(b)/4=23/80. For every natural
d≤2, every R∈deletionMasks d, and every vertex i, 1≤g_i(R)≤6.
β_0=890121037/44498644960, 1/50<β_0<1/49,
9/1000<β_1<1/100, −1/800<β_2<−1/900,
|β_2|<|β_1|<|β_0|, and β_0≠0.
Also, for every d∈Fin 3 and R∈deletionMasks d, the degree bounds hold
and both S_t and C_t are nonempty for every t. For every such d,R,
all g_i/10 and (9−g_i)/10 are positive, and for every t the two Hajek
denominator sums Σ_{S_t}1/g_i and Σ_{C_t}1/(9−g_i) are positive.
The deletion-mask counts for d=0,1,2 are 1,20,190 respectively.

## SAP.P045a.T9

1. For every real matrix M on natural indices and i,j, correctedCopy M
   is symmetric.
2. For every n,A,U, assume A is globally symmetric with zero diagonal,
   its n×n block is binary, U has globally zero diagonal, and U's
   strict upper n×n block is binary. Then each of these implications
   holds: upper U≤A implies 0≤correctedCopy U≤A throughout the block;
   upper A≤U implies A≤correctedCopy U≤1 at distinct block indices;
   equality of upper entries implies equality throughout the block.
3. For every n, Networks T,S with S's true edges contained in T's,
   every assignment z, then vertex i: measured d01 implies true d01,
   measured d11 implies true d11, measured d00 implies true d00 or
   d01, and measured d10 implies true d10 or d11.
4. For every n>0, Design p, such Networks T,S, and exposure outcome
   schedule y, assume positive measured d00 and d01 probabilities
   for every i. Put Y_i(z)=y_i(D_T(z,i)), M_d=htObserved(S,Y,d)/n,
   and c_i=P(D_T=d01 | D_S=d00), expressed as a conditional
   indicator mean. Then E M_d00=mean_i[(1−c_i)y_i(d00)+c_i y_i(d01)],
   E M_d01=mean_i y_i(d01), and
   E(M_d01−M_d00)−effect(y,d01,d00)
   =−mean_i[c_i(y_i(d01)−y_i(d00))]. If for every i,
   y_i(d00)≤y_i(d01), the estimated contrast's expectation is at
   most that effect.
5. For the fixed deletion witness, β_0≠0 and |β_1|<|β_0|.

## SAP.P045a.T10

With d=|i−j| on Fin 4, ε=3, the coded terminal-center masses at
{0,1},{0,2},{0,3},{1},{2} are respectively 1/12,1/12,1/3,1/4,1/4.
Their total over all subsets is one; the probability of failure of
3-separation is 1/6. The coded treatment probabilities at
0000,1111,1100,0011,1000,0111 are respectively
3/8,3/8,5/48,5/48,1/48,1/48, and for every other assignment the
probability is zero. For the repaired sampler, the terminal-center
masses at {0,3},{1},{2} are 1/2,1/4,1/4. Its treatment probabilities
at those same six listed assignments are 3/8,3/8,1/8,1/8,0,0.
There are no external hypotheses, and the theorem does not itself
assert summability or a support-exhaustion formula for the repaired law.

## SAP.P045a.T11

For every n>0 and every SimpleGraph G on Fin n:

* For every list cs, if it is an admissible greedy run for G.edist and
  ε=3, then cs has no duplicates, its length is at most n, its center
  set is 3-separated, and if its marked set is all vertices then that
  center set is an epsilonNet (3-separated and radius-two covering).
* For every subset S and then every v outside marked(S), the number
  of unmarked vertices strictly decreases upon adding v to S.
* There exists a list cs which is an admissible greedy run and marks
  all vertices.

## SAP.P045a.T12

There are 45 treatment pairs. For every vertex of the ten-cycle,
(π_d11,π_d10,π_d01,π_d00)=(2/45,7/45,1/3,7/15).
Exactly 10 treatment pairs are adjacent. For every pair e among the 45,
if adjacent, (cycleL(e),cycleR(e))=(2,9), otherwise (1,9/7).
For every pair the two expressions differ. Their uniform expectations
are 11/9 and 3. The uniform expectation of the d11-only HT mean is 2.
The expected cycleL minus the population mean d11 outcome is −7/9.

## SAP.P045a.T13

1. For every n>0, Design p, Network A, exposure-indexed y, assuming
   e_i=P(Z_i=true)>0 for every i: for every i, e_i=π_i(d11)+π_i(d10);
   E L=mean_i[(π_i(d11)/e_i)y_i(d11)+(π_i(d10)/e_i)y_i(d10)];
   E L−mean_i y_i(d11)=−mean_i[(π_i(d10)/e_i)(y_i(d11)−y_i(d10))].
   If every y_i(d10)≤y_i(d11), then E L≤mean_i y_i(d11), with strict
   inequality iff there exists i with π_i(d10)>0 and y_i(d10)<y_i(d11).
   If every y_i(d11)≤y_i(d10), the weak reverse inequality holds.
   If for every i both π_i(d11) and π_i(d10) are positive, then
   E[(HTtotal_d11+HTtotal_d10)/n]=mean_i y_i(d11)+mean_i y_i(d10).
2. Separately, for every n>0, Design p, Network A, y, positive own
   probabilities, and then every assignment z, the naive treated mean
   equals the repaired expansion (both exposure summands use e_i).
3. In the two-unit cancellation schedule, the two treated exposure
   outcomes differ at every unit; the naive treated means at
   00,01,10,11 are 0,2,1,3; its B_{1/2} expectation and the population
   mean d11 outcome both equal 3/2.

## SAP.P045a.T14

The pooled and printed values for (a,b,A,B)=(2,1,9/2,2) are
some(13/6),some(17/4), and for (2,1,11/4,5/4) they are
some(4/3),some(21/8). Their real direct contrasts are 5/6 and 13/8.
For every natural a,b with a>0,b>0 and then all real A,B,
A/a+B/b−(A+B)/(a+b)=bA/[a(a+b)]+aB/[b(a+b)].
There are 20 selected triples; exactly 8 have r(H)=0, and every selected
triple has r(H)=0 or 2. For every real B, printedPool(0,3,0,B)=none,
whereas pooledMean(0,3,0,B)=some(B/3).
There are 450 group-unit indices. H={0,1,2} is a valid triple; its
same-regime groups are {0,1} and other group is {2}. For every group g,
the witness assignment has 50 treated if g<3 and 25 otherwise, and
positive CR mass for that count. For every selected g<3 and b∈Bool,
its observed arm mean is 9/4 (treated) or 11/8 (control) when g<2,
and 2 or 5/4 when g=2. Applying pooled/printed means to the sum of
observed means in {0,1} and the observed mean in group 2 gives exactly
the preceding two treated and two control Option values.

## SAP.P045a.T15

1. For every natural a,b, reals A,B, assuming a+b>0, pooledMean is
   some((A+B)/(a+b)); if additionally a,b>0 that quotient equals
   [a/(a+b)](A/a)+[b/(a+b)](B/b); and if a=0,A=0 the pooled value
   is some(B/b).
2. For every H⊆Fin 6 and then m:Fin 6→R, |H| is the sum of the
   counts of its same-partner and other-partner subclasses, and Σ_H m
   is the sum of m over these two subclasses.
3. The full two-stage tract mass is nonnegative at every outcome and
   sums to one. For every outcome (H,w), its mass is positive iff H is
   a selected triple and every group's treated count is k_g(H).
4. For every selected H and then every w satisfying all these group
   counts: every selected g and either b has a nonempty arm and arm
   mean 9/4 or 11/8 if its partner is selected, 2 or 5/4 otherwise;
   the direct estimator equals Σ_{g∈H}(A_true−A_false)/3 and equals
   [r(H)/3](7/8)+[(3−r(H))/3](3/4).
5. For every group, unit, and b, under the all-psi law the own-arm
   probability is 2/3 if treated, 1/3 if control, and its conditional
   potential outcome is 9/4 or 11/8 respectively. The psi-psi target
   is 7/8. The uniform means of r(H)/3 and (3−r(H))/3 over selected
   triples are 2/5 and 3/5. Under the two-stage law the direct estimator
   has expectation 4/5 and bias relative to that target −3/40.

## SAP.P045a.T16

For every vertex i of the printed graph, let g be its degree. Then its
four pair-exposure probabilities are g/45 for d11, (9−g)/45 for d10,
choose(9−g,2)/45 for d00, and [36−choose(9−g,2)]/45 for d01;
every one is positive. Here 9−g is natural subtraction.
Under treated pair (5,8), no unit has d11, and for every i, exposure
d00 holds iff i=0 or i=1. The d11 HT total with baseline 1 is zero,
the d00 HT total is 15/2, and printedContrast is −3/4.
There are 20 pairs with nonempty d11 and 19 with both d11 and d00
nonempty. The unconditional mean d11 HT total is 20 and its mean
over nonempty-d11 pairs is 45. The unconditional contrast mean is 1,
its mean over nonempty-d11 pairs is 651/200, and over pairs with both
cells nonempty it is 1227/380.
