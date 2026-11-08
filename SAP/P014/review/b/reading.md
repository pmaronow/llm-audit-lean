# Blind reading of SAP.P014

This file was written from `SAP/P014/Defs*.lean`, `SAP/P014/Defs/*.lean`,
`SAP/P014/Challenge*.lean`, `SAP/P014/Challenge/*.lean`, and the relevant Mathlib
definitions, before opening `claims.json` or `record.json`. The mathematical
content below is the expanded proposition, not an inference from a theorem name
or its explanatory comment. All subject indices in this package start at zero.

## Conventions and complete dictionary

For a natural number N the subjects are I = {0,...,N-1} (`Fin N`). A treatment
vector z is a function I → {false,true}; write 0 and 1 for these two Boolean
values. A potential-outcome array y assigns a real number y_i(z) to every
subject and every full treatment vector, including assignments outside the
support. Interference is allowed unless explicitly excluded.

A `FiniteDistribution` L on an arbitrary type consists of a finite set A of
distinct atoms and a real-valued function w on the entire type.
`IsDistribution L` means w(x)>0 for every x in A and Σ_{x∈A} w(x)=1. It says
nothing about w outside A. Without this validity premise the structure alone
does not express a probability distribution. The definitions are

* E_L f = Σ_{x∈A} w(x) f(x);
* P_L(P) = Σ_{x∈A, P(x)} w(x);
* the pushforward under f has atom set f(A), with duplicate values removed,
  and weight at b equal to P_L(f(x)=b).

For S ⊆ I finite, write n=|S|, and define

* W_b(x) = {i : -b ≤ x_i ≤ b}; the endpoints are included;
* H_S(x,t) = #{i∈S : x_i≤t}/n (the empirical CDF);
* Z(x)_i = 1 iff 0≤x_i; a score of exactly zero is treated;
* A_{ia} = {z∈A : z_i=a}; k_{ia}=|A_{ia}|;
* p_{ia} = Σ_{z∈A_{ia}}w(z);
* M_{ia} = Σ_{z∈A_{ia}}w(z)y_i(z);
* U_{ia} = (Σ_{z∈A_{ia}}y_i(z))/k_{ia}, the unweighted average over distinct
  supported full assignments;
* C_{ia} = M_{ia}/p_{ia}, the probability-weighted own-arm average;
* n_a(z)=#{i∈S : z_i=a};
* T_a(z)=Σ_{i∈S,z_i=a}y_i(z);
* D(z)=T_1(z)/n_1(z)-T_0(z)/n_0(z), the difference of observed means;
* Δ_S(f)=(Σ_{i∈S}(f_i(1)-f_i(0)))/n. Thus Δ_S(U) and Δ_S(C) are different
  objects in general.

`PositiveArms L S` is ∀i∈S ∀a, p_{ia}>0.
`ConditionallyUniform L S` is ∀i∈S ∀a ∀z∈A_{ia},
w(z)/p_{ia}=1/k_{ia}. By itself this permits an empty A_{ia}.
`Noninterfering S y` is ∀i∈S ∀z ∀z', z_i=z'_i ⇒ y_i(z)=y_i(z'). It quantifies
over all full assignments, not just atoms. `DistinctNoTies L X S` is
∀i∈S ∀j∈S, i≠j ⇒ P_L(X_i=X_j)=0.

The five clauses of `PrintedLocalConditions L X b S`, in order, are:

1. For every atom ω of L, W_b(X(ω))=S.
2. There exists a single real-valued F on ℝ such that, for every atom ω and
   every real t, H_S(X(ω),t)=F(t).
3. For every atom ω, P_L(X(η)=X(ω))=1/n!. Equality here is equality of the
   **entire N-coordinate vector**, not just its restriction to S.
4. DistinctNoTies L X S.
5. For every atom ω, 0<n_1(Z(X(ω)))<n.

This definition does not itself include validity of L or b>0.

For a measurable space Ω and a Mathlib measure μ, define
P_μ(P)=(μ{ω:P(ω)}).toReal. Mathlib measures evaluate every set via their outer
measure extension. Infinite measure would be mapped to zero by `toReal`, but
every measure used in the theorem statements below has μ(Ω)=1, so that case
cannot occur. A statement holding μ-almost everywhere means its exceptional
set has outer measure zero. Measurability means that preimages of Borel sets
are measurable.

Given v:S→ℝ, `CorrectedLocalConditions μ X b S v` means precisely:

1. Every coordinate function ω↦X_i(ω), for i∈I, is measurable.
2. For every i∈I, P_μ(-b≤X_i≤b)=1 if i∈S and =0 otherwise.
3. For every permutation σ:S≃S,
   P_μ(∀i∈S, X_i=v_{σ(i)})=1/n!.

In particular the permutation probabilities specify only the local
coordinates. Injectivity of v, its inclusion in the window, b>0, and interior
treated count are separate hypotheses when used. `FiniteLocalConditions` is
the finite-law version: W_b(X(ω))=S at every atom, together with the same
permutation-event probabilities computed with P_L. It is defined but is not
used by any theorem statement.

For i∈I an other-subject assignment u assigns a Boolean to every j≠i, including
subjects outside S. `removeOwn i z` restricts z to these subjects;
`insertOwn i a u` puts a at i and u at each j≠i. The latter follows Mathlib's
`Equiv.funSplitAt` inverse, so it is the genuine inverse reconstruction.
Define

q_{ia}(u)=P_L(z_i=a and z_{-i}=u)/p_{ia},
B_{ia}=Σ_{u∈{0,1}^{I\{i}}}y_i(a,u)q_{ia}(u),
d_i=B_{i0}-B_{i1}.

The sum defining B includes every other-subject Boolean vector and gives
unsupported ones their probability zero. The direct effect d uses
**control minus treatment**.

All displayed sums in these definitions are finite Mathlib `Finset.sum`s;
finset image removes repetitions and finset cardinality counts distinct
elements. Finset subtypes, such as S in v:S→ℝ or σ:S≃S, contain exactly the
elements of S. All fractions above are divisions in ℝ. Lean assigns value zero
to a fraction with denominator zero; the relevant nonzero premises are stated
below. Natural-number subtraction in (n-m)! and (n-1)! is truncated, but the
theorems that use it require 0<m<n, hence n≥2 and no truncation occurs.
Factorial and choose are the ordinary recursive Mathlib natural factorial and
binomial coefficient. Their values in real fractions are cast to ℝ.

Mathlib source points checked: `Data/Finset/{Defs,Card,Filter,Image}.lean`,
`Logic/Equiv/Prod.lean` (`piSplitAt`, `funSplitAt`),
`MeasureTheory/MeasurableSpace/Defs.lean` (`Measurable`),
`MeasureTheory/Measure/MeasureSpaceDef.lean` (`Measure`, `Measure.real`),
`MeasureTheory/Measure/Typeclasses/Probability.lean` (`IsProbabilityMeasure`),
`MeasureTheory/OuterMeasure/AE.lean` (`ae`),
`Basic/ENNReal/Basic.lean` (`toReal`), and
`Data/Nat/{Factorial,Choose}/Basic.lean`.

## Concrete objects shared by T1, T4, T5, T6, T7, T9, T10

There are four subjects, S={0,1,2}, and a six-point sample space r=0,...,5,
each point having weight 1/6 (`uniformSix`). The following are full score
vectors; listed coordinates are in order 0,1,2,3.

| r | scores1 | scores5 | scores9 | allocations z(r) |
|---|---|---|---|---|
|0|(-2,-1,1,3)|(1,-1,-2,3)|(-1,-1/2,1/2,2)|(0,0,1,1)|
|1|(-2,1,-1,-3)|(-1,1,-2,3)|(-1,1/2,-1/2,-2)|(0,1,0,0)|
|2|(-1,-2,1,-3)|(-1,-2,1,3)|(-1/2,-1,1/2,-2)|(0,0,1,0)|
|3|(-1,1,-2,-3)|(-1,-2,1,4)|(-1/2,1/2,-1,-2)|(0,1,0,0)|
|4|(1,-2,-1,-3)|(-1,-2,1,5)|(1/2,-1,-1/2,-2)|(1,0,0,0)|
|5|(1,-1,-2,-3)|(-1,-2,1,6)|(1/2,-1/2,-1,-2)|(1,0,0,0)|

`localCoordinates` selects the first three coordinates (Mathlib's
`Fin.castSucc` embeds Fin 3 into Fin 4 without changing the index).
Let A be the pushforward of the uniform six-point law by the listed
allocations (`assignmentDistribution`). Let A5 be the pushforward by
Z(scores5) (`assignmentDistribution5`).

The three potential-outcome arrays are, on **all** assignments:

* y1_i(z)=z_3 for i∈{0,1,2} and y1_3(z)=0, with Booleans converted to 0 or 1.
* y5_0(z)=z_0 and y5_i(z)=0 for i≠0.
* y9_0(z)=z_3 and y9_i(z)=0 for i≠0.

`AssignmentMasses` states that A has exactly the four distinct atoms
(0,0,1,1), (0,1,0,0), (0,0,1,0), (1,0,0,0), with respective weights
1/6, 1/3, 1/6, 1/3. `CommonWitnessCounts` states that every atom of A has
exactly one treated member of S and that p_{i1}=1/3 for each i∈S.

The extended sample space is {0,...,5}×{0,1}. Every (r,1) has weight 1/9
and every (r,0) weight 1/18. Its scores are the first three coordinates of
scores1(r), followed by 3 when the Boolean is 1 and -3 when it is 0.

## SAP.P014.T1

There are no hypotheses or universal object parameters. This is a conjunction
of the following assertions about the fixed objects above (y=y1 and L=A):

1. The uniform six-point law and A are valid probability distributions.
2. PrintedLocalConditions holds for scores1, b=2, S={0,1,2}.
3. |S|=3 and the score pushforward has exactly six distinct atoms.
4. Z(scores1(r))=z(r) for every r (equality of these two functions of r).
5. For every permutation σ of {0,1,2}, the probability that the first three
   scores equal the σ-reordering of (-2,-1,1) is 1/6.
6. AssignmentMasses, CommonWitnessCounts, and PositiveArms A S all hold.
7. The own-arm averages have these exact values:

|i|U_i1|U_i0|C_i1|C_i0|
|---|---|---|---|---|
|0|0|1/3|0|1/4|
|1|0|1/3|0|1/4|
|2|1/2|0|1/2|0|

8. For every r∈{0,...,5}, D(z(r))=0; also E_A D=0.
9. Δ_S(U)=-1/18 and Δ_S(C)=0.
10. E_A D-Δ_S(U)=1/18 and E_A D≠Δ_S(U).

## SAP.P014.T2

For every natural N, every finite assignment law L, **if** L is valid,
then for every finite subject set S⊆I, every full potential-outcome array y,
and every natural m, **if**, in order,

1. 0<m;
2. m<n;
3. every supported assignment z has n_1(z)=m;
4. for every i∈S, p_{i1}=m/n;

then all of the following hold:

1. PositiveArms L S.
2. For every i∈S and both a, p_{ia}=P_L(z_i=a).
3. For every i∈S, p_{i0}=(n-m)/n.
4. For every supported z, n_0(z)=n-m and
   D(z)=T_1(z)/m-T_0(z)/(n-m).
5. For every i∈S and a,
   E_L(1_{z_i=a}y_i(z))=M_{ia} and M_{ia}=p_{ia}C_{ia}.
6. For every i∈S, M_{i1}=(m/n)C_{i1} and
   M_{i0}=((n-m)/n)C_{i0}.
7. E_L D=(Σ_{i∈S}M_{i1})/m-(Σ_{i∈S}M_{i0})/(n-m).
8. E_L D=(1/m)(m/n)Σ_{i∈S}C_{i1}
   -(1/(n-m))((n-m)/n)Σ_{i∈S}C_{i0}.
9. E_L D=Δ_S(C).
10. Δ_S(C)=(Σ_{i∈S}C_{i1}-Σ_{i∈S}C_{i0})/n.

Here n-m in real fractions is real subtraction. No running variables,
probability measure μ, local-score law, or transfer from such a law are
quantified in this theorem.

## SAP.P014.T3

This is the conjunction of five separately universally quantified statements;
their objects need not be the same across the five statements.

### Conditional-uniformity part

For every N, L, validity of L, and then every S,y,m, assume 0<m<n,
n_1(z)=m at every atom, p_{i1}=m/n for every i∈S, and finally
ConditionallyUniform L S. Then:

* for every i∈S and a, A_{ia} is nonempty and U_{ia}=C_{ia};
* E_L D=Δ_S(U);
* Δ_S(U)=(Σ_{i∈S}U_{i1}-Σ_{i∈S}U_{i0})/n.

### Uniform-law part

For every N,L, if L is valid, then for every S, if each atom has weight
1/|A|, ConditionallyUniform L S holds. There is no positive-arm or fixed-count
premise in this part; an empty individual arm satisfies the resulting
conditional-uniformity predicate vacuously.

### Corrected local randomization with fixed outside treatments

For every measurable space Ω (in universe u), every N, every probability
measure μ on Ω, every X:Ω→I→ℝ, real b, finite S⊆I, v:S→ℝ,
and finite assignment law A, assume A is valid. Then for every fixed full
assignment c, every potential-outcome array y, and every natural m, assume,
in order:

1. b>0;
2. v is injective;
3. -b≤v_i≤b for all i∈S;
4. 0<m<n;
5. #{i∈S:0≤v_i}=m;
6. CorrectedLocalConditions μ X b S v;
7. for every full assignment z,
   P_μ(Z(X)=z)=w_A(z) if z∈A.atoms and 0 otherwise;
8. μ-almost surely, for every i∉S, Z(X)_i=c_i.

Define z(σ) to equal 1_{0≤v_{σ(i)}} at i∈S and c_i outside S, for every
permutation σ of S. The conclusions are:

* |A.atoms|=choose(n,m).
* For every atom z of A, #{σ:z(σ)=z}=m!(n-m)! and
  w_A(z)=m!(n-m)!/n!=1/choose(n,m).
* Every atom has n_1(z)=m.
* Every i∈S has p_{i1}=m/n.
* ConditionallyUniform A S.
* E_A D=Δ_S(U), with U and D built from A,y,S.
* For **every** full assignment z, if z_i=c_i for all i∉S and n_1(z)=m,
  then z is an atom of A, #{σ:z(σ)=z}=m!(n-m)!, and
  w_A(z)=1/choose(n,m).

Only outside treatments are fixed; the outside scores themselves are not
assumed fixed. The assignment-law representation in premise 7 is explicit.

### No-interference alternative

For every N,L, validity of L, then every S,y,m, assume 0<m<n, n_1(z)=m
at every atom, p_{i1}=m/n for all i∈S, and Noninterfering S y. Then for
every i∈S, a, and **every** full assignment z satisfying z_i=a,
U_{ia}=y_i(z) and C_{ia}=y_i(z). Also E_L D=Δ_S(U).
No conditional-uniformity hypothesis is imposed here.

### Necessity for agreement for every outcome

For every N,L, validity of L, and then every i∈I and a, assume p_{ia}>0.
If for every potential-outcome array y one has U_{ia}=C_{ia}, then for every
z∈A_{ia}, w(z)/p_{ia}=1/k_{ia}. This part concerns a single specified
subject and arm and makes no fixed-count assumption. Agreement for every y
is the premise of a necessity implication, not a premise of the sufficiency
parts above.

## SAP.P014.T4

There are no hypotheses or free object parameters. This asserts, for the fixed
uniform six-point scores1 example and y1, the conjunction:

* uniformSix and A are valid;
* PrintedLocalConditions uniformSix scores1 2 S;
* the threshold assignments are exactly the listed z(r);
* for every permutation of {0,1,2}, the local arrangement of (-2,-1,1)
  has probability 1/6;
* CommonWitnessCounts and PositiveArms A S;
* E_A D=0, Δ_S(U)=-1/18, and E_A D≠Δ_S(U).

Thus the formal conclusion is an explicit counterexample package, not the
universally quantified positive unbiasedness assertion named in its comment.

## SAP.P014.T5

There are no hypotheses or free object parameters. For scores5 with b=2,
S={0,1,2}, A5, and y5, the theorem asserts:

1. uniformSix and A5 are valid, PrintedLocalConditions holds, and the score
   pushforward has six distinct full vectors.
2. The probabilities of the six possible local permutations are:

|local vector|probability|
|---|---|
|(1,-1,-2)|1/6|
|(-1,1,-2)|1/6|
|(-1,-2,1)|2/3|
|(-2,-1,1)|0|
|(-2,1,-1)|0|
|(1,-2,-1)|0|

   In particular the mass of (-1,-2,1) is not 1/6.
3. The probabilities that subjects 0,1,2 are treated are respectively
   1/6,1/6,2/3.
4. PositiveArms A5 S holds. Its atoms are precisely (1,0,0,1),
   (0,1,0,1), (0,0,1,1) with respective weights 1/6,1/6,2/3.
5. At every atom z, n_1(z)=1 and D(z)=z_0.
6. For every i∈S and a, both U_{ia} and C_{ia} equal a when i=0,
   and equal zero otherwise (Boolean a interpreted numerically).
7. Noninterfering S y5.
8. E_A5 D=1/6, Δ_S(U)=1/3, and E_A5 D≠Δ_S(U).

## SAP.P014.T6

This is a conjunction of a general implication and a concrete example.

### General implication

For every measurable Ω (universe u), N, probability measure μ, X,b,S,v,m,
assume in order b>0, n≥2, injective v, all v_i∈[-b,b], 0<m<n,
#{i∈S:v_i≥0}=m, and CorrectedLocalConditions μ X b S v. Then
`LocalConsequences μ X b S v m` holds, meaning exactly:

1. μ-almost surely, **jointly**:
   n_1(Z(X))=m, 0<n_1(Z(X))<n, W_b(X)=S, |W_b(X)|=n, and
   for every t∈ℝ,
   H_S(X,t)=(Σ_{i∈S}1_{v_i≤t})/n.
2. For every i∈S,
   P_μ(Z_i=1)=m(n-1)!/n!=m/n and P_μ(Z_i=0)=(n-m)/n.
3. For every i,j∈S with i≠j, P_μ(X_i=X_j)=0.

In addition, for every function g:(S→ℝ)→I→ℝ, **if** μ-almost surely
X_j=g(X|_S)_j for all j∉S, **then** there exists a finite distribution A
on full real score vectors I→ℝ such that:

* A is valid;
* |A.atoms|=n!;
* every atom has weight 1/n!;
* for every full score vector x,
  P_μ(X=x)=w_A(x) if x∈A.atoms and 0 otherwise.

g need not be separately measurable; the given X coordinates are measurable.
There is no converse implication from the full-vector mass condition to the
existence of g in the formal proposition.

### Outside-score example

For the fixed twelve-point extended design described above, the following all
hold, without premises:

1. The extended distribution is valid.
2. For every sample point, W_2(X)=S.
3. For every r∈{0,...,5}, P(X|_S=scores1(r)|_S)=1/6.
4. For every permutation σ of {0,1,2},
   P(∀i∈S, X_i=(-2,-1,1)_{σ(i)})=1/6.
5. At every sample point, n_1(Z(X))=1, and |S|=3.
6. The score pushforward has twelve distinct atoms.
7. For every ω=(r,t), P(X=X(ω)) is 1/9 if t=1 and 1/18 if t=0;
   in either case it is not 1/6.
8. P(X_3=-3)=1/3 and P(X_3=3)=2/3.
9. For every r∈{0,...,5} and every Boolean t, the joint probability of
   X|_S=scores1(r)|_S and X_3=(3 if t=1, -3 if t=0) is the product of
   the two marginal probabilities.

## SAP.P014.T7

This conjunction has a general probability statement, a corrected-local-law
statement, and four assertions about fixed finite objects.

For every measurable Ω (universe u), N, probability measure μ, X and S,
without any measurability hypothesis on X, all the following hold:

1. [∀i∈S ∀j∈S, P_μ(X_i=X_j)=0] iff S is empty.
2. For every i∈S, P_μ(X_i=X_i)=1.
3. [∀i∈S ∀j∈S, P_μ(X_i=X_j)=0] iff the conjunction of
   [∀i∈S ∀j∈S, i≠j ⇒ P_μ(X_i=X_j)=0] and
   [∀i∈S, P_μ(X_i=X_i)=0].
4. For every natural m, if 0<m<n, then n≥2, S is nonempty, and
   it is false that ∀i∈S ∀j∈S, P_μ(X_i=X_j)=0.

Separately, for every measurable Ω,N,probability μ,X,b,S,v,m, assume b>0,
n≥2, injective v, all v_i∈[-b,b], 0<m<n, exactly m nonnegative v_i,
and CorrectedLocalConditions μ X b S v. Then for all distinct i,j∈S,
P_μ(X_i=X_j)=0.

Finally, |{0,1,2}|=3 and DistinctNoTies holds under uniformSix for each
of scores1, scores5, and scores9 on that set. The first general statement
uses outer measure on any possibly nonmeasurable pair-equality event; its
diagonal equality event is always the whole sample space.

## SAP.P014.T8

For every N, every S⊆Fin N, and every real-valued f:I→{0,1}→ℝ, if S is
nonempty, then

(Σ_{i∈S}(f_i(1)-f_i(0)))/n
  = (Σ_{i∈S}f_i(1)-Σ_{i∈S}f_i(0))/n.

There are no probability or outcome assumptions. Nonemptiness ensures n>0,
although the finite-sum algebraic identity also survives Lean's totalized
division when n=0.

## SAP.P014.T9

There are no hypotheses or free object parameters. For scores9, b=1,
S={0,1,2}, A and y9, the conjunction asserts:

1. uniformSix and A are valid; PrintedLocalConditions holds; the full-score
   pushforward has six distinct atoms; and Z(scores9(r))=z(r) for every r.
2. Every permutation of local values (-1,-1/2,1/2) has probability 1/6.
3. AssignmentMasses, CommonWitnessCounts and PositiveArms A S.
4. U_{00}=1/3, C_{00}=1/4, U_{01}=C_{01}=0.
5. For every i∈S and a, B_{ia}=C_{ia}.
6. For every i∈S with i≠0 and every a, U_{ia}=C_{ia}=0.
7. Δ_S(U)=-1/9, Δ_S(C)=-1/12, and (Σ_{i∈S}d_i)/n=1/12.
8. Δ_S(U) differs from both (Σd_i)/n and -(Σd_i)/n.
9. At every atom z, D(z)=-1/2 when z=(0,0,1,1) and D(z)=0 otherwise.
10. E_A D=-1/12 and E_A D-Δ_S(U)=1/36.

## SAP.P014.T10

This is the conjunction of a general statement and a concrete failure package.

For every N,L, if L is valid, then for every S,y, assume S is nonempty
and for every i∈S, 0<p_{i1}<1. Then:

1. For every i∈S and a,
   B_{ia}=Σ_{z∈A_{ia}}y_i(z)(w(z)/p_{ia})=C_{ia}.
2. Δ_S(C)=-(Σ_{i∈S}d_i)/n.
3. For every natural m, if 0<m<n, every atom has n_1(z)=m, and
   every i∈S has p_{i1}=m/n, then E_L D=-(Σ_{i∈S}d_i)/n.

Separately, without hypotheses, for A,S={0,1,2},y9 the theorem asserts:

* A is valid and PositiveArms A S;
* U_{00}≠B_{00};
* Δ_S(U)≠(Σ_{i∈S}d_i)/n;
* Δ_S(U)≠-(Σ_{i∈S}d_i)/n.

The marginal positivity premise of the general part also implies positive
control-arm probabilities, since a valid finite Boolean law has
p_{i0}=1-p_{i1}.
