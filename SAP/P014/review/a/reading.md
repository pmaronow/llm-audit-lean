# Blind reading of the Challenge statements

This file was written from `SAP/P014/Defs*.lean`, `SAP/P014/Defs/*.lean`,
`SAP/P014/Challenge.lean`, and `SAP/P014/Challenge/Part1.lean`, before opening
`claims.json` or `record.json`. The readings below describe the theorem types,
including the propositions hidden behind `T*Statement`; the `sorry` bodies are
not evidence for their truth.

## Objects and fully expanded common notation

All subjects are indexed from zero: `Fin N` is the finite set
`{0,...,N-1}`. A treatment vector is an arbitrary map `z : Fin N → Bool`;
write 1 for `true` and 0 for `false`. A potential-outcome schedule is an
arbitrary real function `y(i,z)` of the subject and the **entire** treatment
vector. There is no implicit noninterference assumption.

A `FiniteDistribution α` is just a finite set `D` of distinct elements of α
and a real function `p` on α. `IsDistribution` adds `p(x)>0` for every
`x∈D` and `Σ[x∈D]p(x)=1`. Values of `p` off D have no meaning in any sum.
Write `P_L(E)=Σ[x∈D, E(x)]p(x)` and `E_L f=Σ[x∈D]p(x)f(x)`.
`pushforward L f` has support `f(D)` with duplicates removed, and weight
`P_L(f(x)=b)` at b. Thus repeated rows are combined, not counted as separate
assignment-support elements.

For a finite subject set S, let n=|S|. For an assignment distribution L set

* `D_ia={z∈D:z_i=a}`, `p_ia=Σ[z∈D_ia]p(z)`;
* `M_ia=Σ[z∈D_ia]p(z)y(i,z)`;
* `U_ia=Σ[z∈D_ia]y(i,z)/|D_ia|` (`supportAverage`);
* `C_ia=M_ia/p_ia` (`conditionalAverage`);
* `Δ_S(f)=Σ[i∈S](f(i,1)-f(i,0))/n` (`windowContrast`);
* `n_a(z)=Σ[i∈S]1{z_i=a}` (`armSize`, valued in the reals);
* `T_a(z)=Σ[i∈S]1{z_i=a}y(i,z)` (`observedArmTotal`);
* `d(z)=T_1(z)/n_1(z)-T_0(z)/n_0(z)` (`differenceOfMeans`).

All divisions are real division: Lean makes `r/0=0`. This convention is part
of these definitions even when a later hypothesis rules out zero denominators.
Natural cardinalities and factorials appearing in real expressions are cast
to the reals. Natural subtractions in `(n-m)!` and `(n-1)!` are truncated;
the general results using them assume m<n and m>0, so they have their usual
integer meaning there.

`PositiveArms L S` means `∀i∈S, ∀a∈{0,1}, p_ia>0`.
`ConditionallyUniform L S` means
`∀i∈S, ∀a, ∀z∈D_ia, p(z)/p_ia=1/|D_ia|`.
`Noninterfering S y` means
`∀i∈S, ∀z,z', z_i=z'_i ⇒ y(i,z)=y(i,z')`, including vectors outside D.

For scores x, `z(x)_i=1{0≤x_i}` (zero is treated). The window is the closed
interval [-b,b], and `W_b(x)={i:-b≤x_i≤b}`. The empirical window CDF on S is
`F_S(x,t)=Σ[i∈S]1{x_i≤t}/n`.

For a finite score-sample distribution L on Ω,
`PrintedLocalConditions L X b S` is exactly the following conjunction:

1. `∀ω∈D, W_b(X(ω))=S`;
2. `∃F:ℝ→ℝ, ∀ω∈D, ∀t∈ℝ, F_S(X(ω),t)=F(t)`;
3. `∀ω∈D, P_L(X(η)=X(ω))=1/n!`, where equality is of the **full N-vector**;
4. `∀i∈S, ∀j∈S, i≠j ⇒ P_L(X_i=X_j)=0` (`DistinctNoTies`);
5. `∀ω∈D, 0<n_1(z(X(ω)))<n`.

In particular the SAP definition called "printed" has already inserted the
distinct-subject qualification in its no-ties clause.

For a measure μ, `eventProbability μ E=(μ{ω:E(ω)}).toReal`. In general
`ENNReal.toReal ∞=0`; in every general theorem here that uses this definition
μ is a probability measure (`μ Ω=1`), so all its set measures are finite.
On arbitrary sets μ is the measure's associated outer measure; score
measurability is explicitly imposed in the corrected conditions below.

`CorrectedLocalConditions μ X b S v`, for `v:S→ℝ`, means:

1. `∀i:Fin N`, the real coordinate map `ω↦X_i(ω)` is measurable;
2. `∀i:Fin N`, `P_μ(-b≤X_i≤b)=1` if i∈S, and 0 otherwise;
3. `∀σ:S≃S`, `P_μ(∀i:S, X_i=v(σ(i)))=1/n!`.

Injectivity of v, its membership in [-b,b], and the number of its nonnegative
entries are **not** part of this definition; the relevant theorems add them.
`FiniteLocalConditions` is defined but unused by every Challenge statement;
it asserts fixed window membership on every supported ω and the same
permutation-event probabilities in a finite law.

For i, an `OtherTreatments i` vector u is a Boolean function on the N-1
subjects j≠i. `removeOwn i z` restricts z to these subjects;
`insertOwn i a u` is the unique full vector with own coordinate a and other
coordinates u. Define
`q_ia(u)=P_L(z_i=a, z_{-i}=u)/p_ia` and
`H_ia=Σ[u]y(i,(a,u))q_ia(u)` (`otherSubjectsAverage`).
`directEffect_i=H_i0-H_i1`, using control minus treatment.

`permutationAssignment S v c σ` gives subject i∈S treatment
`1{v(σ(i))≥0}` and gives i∉S treatment c_i.

Mathlib foundations followed: `Finset.sum` is the ordinary finite sum
(`Algebra/BigOperators/Group/Finset/Defs.lean`, including its sum-notation
documentation); `Finset.card` is multiset cardinality
(`Data/Finset/Card.lean:47`); `filter` selects satisfying members
(`Data/Finset/Filter.lean:52`); `image` deduplicates the mapped multiset
(`Data/Finset/Image.lean:279`); `Equiv.Perm S` means a bijection S≃S
(`Logic/Equiv/Defs.lean:96`); `Equiv.funSplitAt` and its inverse split and
insert the own coordinate (`Logic/Equiv/Prod.lean:487-501`). `Nat.choose` and
`Nat.factorial` are the usual recursions (`Data/Nat/Choose/Basic.lean:50`,
`Data/Nat/Factorial/Basic.lean:37`). `IsProbabilityMeasure` means μ(univ)=1
(`MeasureTheory/Measure/Typeclasses/Probability.lean:64`); `Measurable` means
measurable preimages (`MeasureTheory/MeasurableSpace/Defs.lean:493`);
`∀ᵐ ω ∂μ` means outside a set of μ-measure zero
(`MeasureTheory/OuterMeasure/AE.lean:49-60`). `ENNReal.toReal` and its value
at infinity are in `Basic/ENNReal/Basic.lean:228,284`.

## Shared concrete data

Let Ω={0,...,5} with every row of probability 1/6 (`uniformSix`). Let
N=4 and S={0,1,2} (`localThree`). The score arrays, in row order, are:

| row | scores1 | scores5 | scores9 |
|---|---|---|---|
| 0 | (-2,-1,1,3) | (1,-1,-2,3) | (-1,-1/2,1/2,2) |
| 1 | (-2,1,-1,-3) | (-1,1,-2,3) | (-1,1/2,-1/2,-2) |
| 2 | (-1,-2,1,-3) | (-1,-2,1,3) | (-1/2,-1,1/2,-2) |
| 3 | (-1,1,-2,-3) | (-1,-2,1,4) | (-1/2,1/2,-1,-2) |
| 4 | (1,-2,-1,-3) | (-1,-2,1,5) | (1/2,-1,-1/2,-2) |
| 5 | (1,-1,-2,-3) | (-1,-2,1,6) | (1/2,-1/2,-1,-2) |

The six vectors `allocations` are respectively
`(0,0,1,1),(0,1,0,0),(0,0,1,0),(0,1,0,0),(1,0,0,0),(1,0,0,0)`.
Let A be the pushforward of the uniform row law through allocations.
Let B be the pushforward through the thresholded scores5.
The schedules are:

* y1(i,z)=z_3 as a real number for i=0,1,2, and y1(3,z)=0;
* y5(i,z)=z_0 for i=0, and 0 for every other i;
* y9(i,z)=z_3 for i=0, and 0 for every other i.

`localCoordinates X ω` is `(X_0(ω),X_1(ω),X_2(ω))`.
`AssignmentMasses` asserts that A has precisely the following support and weights:
`(0,0,1,1):1/6`, `(0,1,0,0):1/3`, `(0,0,1,0):1/6`, `(1,0,0,0):1/3`.
`CommonWitnessCounts` means `∀z∈supp A, n_1(z)=1` and
`∀i∈S, p_i1=1/3`.

The extended law is on Ω×Bool: each `(r,0)` has weight 1/18 and each
`(r,1)` has weight 1/9. Its scores equal scores1(r) on subjects 0,1,2;
subject 3 has score -3 for Boolean 0 and +3 for Boolean 1.

## SAP.P014.T1

There are no variables or hypotheses: this is a conjunction of facts about
the concrete data. It asserts all of the following:

1. The uniform row law and A are valid probability distributions.
2. `PrintedLocalConditions uniformSix scores1 2 S` holds, with all five
   clauses expanded above.
3. |S|=3 and the full scores1 pushforward has six distinct score vectors.
4. The thresholded scores1 row function equals allocations, as functions.
5. For **every** permutation σ of {0,1,2}, the probability that the local
   scores equal `(-2,-1,1)∘σ` is 1/6.
6. `AssignmentMasses`, `CommonWitnessCounts`, and `PositiveArms A S` hold.
7. For y1, `(U_i1,U_i0)` equals `(0,1/3)` for i=0, `(0,1/3)` for i=1,
   and `(1/2,0)` for i=2.
8. For y1, `(C_i1,C_i0)` equals `(0,1/4)` for i=0, `(0,1/4)` for i=1,
   and `(1/2,0)` for i=2.
9. `∀r∈Ω, d(allocations(r))=0`; `E_A d=0`; `Δ_S(U)=-1/18`;
   `Δ_S(C)=0`; `E_A d-Δ_S(U)=1/18`; and `E_A d≠Δ_S(U)`.

## SAP.P014.T2

For every natural N, then every finite assignment law L, assuming it is a
valid distribution, for every S⊆Fin N, every schedule y, and every natural m,
assume in this order: `0<m`, `m<n`, `∀z∈supp L, n_1(z)=m`, and
`∀i∈S, p_i1=m/n`. The conclusion is the conjunction:

1. `PositiveArms L S`.
2. `∀i∈S, ∀a, p_ia=P_L(z_i=a)`.
3. `∀i∈S, p_i0=(n-m)/n` (real subtraction).
4. `∀z∈supp L`, `n_0(z)=n-m` and
   `d(z)=T_1(z)/m-T_0(z)/(n-m)`.
5. `∀i∈S, ∀a`, `E_L(1{z_i=a}y(i,z))=M_ia` and `M_ia=p_ia C_ia`.
6. `∀i∈S`, `M_i1=(m/n)C_i1` and `M_i0=((n-m)/n)C_i0`.
7. `E_L d=(Σ[i∈S]M_i1)/m-(Σ[i∈S]M_i0)/(n-m)`.
8. `E_L d=(1/m)(m/n)Σ[i∈S]C_i1
   -(1/(n-m))((n-m)/n)Σ[i∈S]C_i0`.
9. `E_L d=Δ_S(C)` and
   `Δ_S(C)=(Σ[i∈S]C_i1-Σ[i∈S]C_i0)/n`.

There is no score randomization premise or conclusion in this theorem.

## SAP.P014.T3

This is a conjunction of five independently universally quantified results.

1. **Conditional uniformity.** For every N,L, assume L valid; then for every
   S,y,m assume `0<m<n`, fixed supported treated count m, common treated
   propensity m/n, and `ConditionallyUniform L S`. Conclude
   `∀i∈S, ∀a, D_ia≠∅` and `U_ia=C_ia`; also
   `E_L d=Δ_S(U)` and `Δ_S(U)=(Σ U_i1-Σ U_i0)/n`.
2. **Full uniformity implies conditional uniformity.** For every N,L,
   assume L valid; for every S assume
   `∀z∈supp L, p(z)=1/|supp L|`; conclude `ConditionallyUniform L S`.
   This clause does not assume interior counts or positive arms.
3. **Fixed outside treatments.** For every measurable space Ω (in the
   theorem's arbitrary universe), every N, every measure μ, assume μ is a
   probability measure; for every X,b,S,v, finite assignment law A, assume A
   valid; for every outside template c, schedule y, and natural m, assume:
   `b>0`; v is injective; every v_i∈[-b,b]; `0<m<n`;
   exactly m entries of v are nonnegative; corrected local conditions hold;
   for every full assignment z,
   `P_μ(z(X)=z)=p_A(z)` if z∈supp A and is zero otherwise; and
   almost surely `∀i∉S, z(X)_i=c_i`.
   Conclude:
   * `|supp A|=binom(n,m)`;
   * `∀z∈supp A`, exactly `m!(n-m)!` permutations σ satisfy
     `permutationAssignment(S,v,c,σ)=z`, and
     `p_A(z)=m!(n-m)!/n!=1/binom(n,m)`;
   * `∀z∈supp A, n_1(z)=m`; `∀i∈S, p_A,i1=m/n`;
     `ConditionallyUniform A S`; and `E_A d=Δ_S(U_A)`;
   * `∀z:Fin N→Bool`, if `∀i∉S,z_i=c_i` and `n_1(z)=m`, then z∈supp A,
     its permutation-fiber cardinality is `m!(n-m)!`, and its mass is
     `1/binom(n,m)`.
4. **Noninterference.** For every N,L, assume L valid; for every S,y,m
   assume `0<m<n`, fixed supported treated count m, common propensity m/n,
   and `Noninterfering S y`. Conclude
   `∀i∈S, ∀a, ∀z` (not just supported z), `z_i=a ⇒ U_ia=y(i,z)` and
   `C_ia=y(i,z)`; also `E_L d=Δ_S(U)`.
5. **Necessity for all schedules.** For every N,L, assume L valid; for
   every subject i and arm a, assume `p_ia>0`, then assume
   `∀y:PotentialOutcomes N, U_ia=C_ia`. Conclude
   `∀z∈D_ia, p(z)/p_ia=1/|D_ia|`.

## SAP.P014.T4

No hypotheses or free objects. The uniform row law and A are valid;
`PrintedLocalConditions uniformSix scores1 2 S` holds; thresholded scores1
equals allocations; every local permutation of (-2,-1,1) has probability
1/6; `CommonWitnessCounts` and `PositiveArms A S` hold; and for y1,
`E_A d=0`, `Δ_S(U)=-1/18`, and `E_A d≠Δ_S(U)`.
This proves a concrete counterexample, rather than asserting the universal
unbiasedness assertion that its docstring calls false.

## SAP.P014.T5

No hypotheses or free objects. It asserts:

1. The uniform row law and B are valid, and
   `PrintedLocalConditions uniformSix scores5 2 S` holds.
2. The full scores5 pushforward has six distinct vectors. The probabilities
   of the local arrangements `(1,-1,-2)`, `(-1,1,-2)`, `(-1,-2,1)`,
   `(-2,-1,1)`, `(-2,1,-1)`, `(1,-2,-1)` are respectively
   `1/6,1/6,2/3,0,0,0`; in particular the third probability is not 1/6.
3. The treatment probabilities for subjects 0,1,2 are respectively
   `1/6,1/6,2/3`. All own-arm probabilities for S in B are positive.
4. The support of B is precisely `(1,0,0,1),(0,1,0,1),(0,0,1,1)`, with
   masses `1/6,1/6,2/3` respectively.
5. `∀z∈supp B`, `n_1(z)=1` and `d_y5(z)=z_0` as a real number.
6. `∀i∈S, ∀a`, `U_ia=C_ia=a` if i=0 and both equal zero otherwise.
7. y5 is noninterfering on S, `E_B d=1/6`, `Δ_S(U)=1/3`, and
   `E_B d≠Δ_S(U)`.

## SAP.P014.T6

The conjunction of a general result and one concrete extended-law example.

**General part.** For every measurable Ω, N, μ with μ a probability measure,
then every X,b,S,v,m, assume in order: `b>0`; `2≤n`; v injective; each
v_i∈[-b,b]; `0<m`; `m<n`; exactly m values v_i are nonnegative; and
`CorrectedLocalConditions μ X b S v`. Conclude:

1. Almost surely, simultaneously: `n_1(z(X))=m`, `0<n_1(z(X))<n`,
   `W_b(X)=S`, `|W_b(X)|=n`, and **for every real t**,
   `F_S(X,t)=Σ[i:S]1{v_i≤t}/n`.
2. `∀i:S`, `P_μ(z(X)_i=1)=m(n-1)!/n!=m/n` and
   `P_μ(z(X)_i=0)=(n-m)/n`.
3. `∀i,j:S, i≠j ⇒ P_μ(X_i=X_j)=0`.
4. For **every** function `g:(S→ℝ)→Fin N→ℝ`, if almost surely
   `∀j∉S, X_j=g(X|S)_j`, then there **exists** a finite distribution A on
   full real N-vectors such that A is valid, `|supp A|=n!`, every supported
   vector has mass 1/n!, and **for every full vector x**,
   `P_μ(X=x)=p_A(x)` on supp A and zero off supp A.

There is no converse from a full-vector mass condition to existence of g.

**Concrete part.** The extended law above is valid; every one of its 12
rows has window S at b=2; every local vector `localCoordinates scores1 r`
has probability 1/6 (for each r); every permutation of (-2,-1,1) likewise
has probability 1/6; every row has local treated count 1; n=3; the full
score pushforward has 12 distinct vectors; for **each** `(r,t)` the mass of
its full vector is 1/9 if t=1 and 1/18 if t=0, and in either case is not
1/6. The outside score has probabilities `P(X_3=-3)=1/3` and
`P(X_3=3)=2/3`. For **every** r and Boolean t, the joint event of local
vector r and outside score `(if t then 3 else -3)` has probability equal
to the product of its two marginal probabilities.

## SAP.P014.T7

The conjunction of:

1. For every measurable Ω,N, probability measure μ, score function X and
   S (no measurability of X is assumed in this part), the literal assertion
   `∀i∈S,∀j∈S,P_μ(X_i=X_j)=0` is equivalent to `S=∅`.
   Also `∀i∈S,P_μ(X_i=X_i)=1`. The literal assertion is equivalent to
   the conjunction of its distinct-subject restriction and
   `∀i∈S,P_μ(X_i=X_i)=0`. Finally, for **every natural m**, if `0<m<n`,
   then `2≤n`, S is nonempty, and the literal assertion is false.
2. For every measurable Ω,N, probability measure μ, X,b,S,v,m, under the
   same assumptions as the T6 general part, for **every** i,j:S with i≠j,
   `P_μ(X_i=X_j)=0`.
3. The concrete S has cardinality 3 and the three finite designs scores1,
   scores5, scores9 have zero tie probability for every pair of distinct
   subjects in S.

## SAP.P014.T8

For every natural N, every S⊆Fin N, every real function
`f:Fin N→Bool→ℝ`, if S is nonempty, then
`Σ[i∈S](f(i,1)-f(i,0))/n = (Σ[i∈S]f(i,1)-Σ[i∈S]f(i,0))/n`.
There is no probability law, outcome schedule, or unbiasedness conclusion.

## SAP.P014.T9

No hypotheses or free objects. It asserts:

1. The uniform row law and A are valid;
   `PrintedLocalConditions uniformSix scores9 1 S` holds; the full scores9
   pushforward has six vectors; thresholded scores9 equals allocations;
   every permutation of (-1,-1/2,1/2) has probability 1/6;
   `AssignmentMasses`, `CommonWitnessCounts`, `PositiveArms A S` hold.
2. For y9, `U_00=1/3`, `C_00=1/4`, `U_01=C_01=0`.
   `∀i∈S,∀a,H_ia=C_ia`; and for **every** i∈S with i≠0 and **every** a,
   `U_ia=C_ia=0`.
3. `Δ_S(U)=-1/9`; `Δ_S(C)=-1/12`;
   `Σ[i∈S]directEffect_i/n=1/12`; and `Δ_S(U)` differs from both this
   average and its negative.
4. `∀z∈supp A`, `d_y9(z)=-1/2` if z=(0,0,1,1) and zero otherwise;
   `E_A d=-1/12`; `E_A d-Δ_S(U)=1/36`.

## SAP.P014.T10

Conjunction of two parts:

1. For every N,L, assume L valid; for every S,y assume S nonempty and
   `∀i∈S,0<p_i1<1`. Conclude for **every** i∈S and **every** a,
   `H_ia=Σ[z∈D_ia]y(i,z)(p(z)/p_ia)=C_ia`; also
   `Δ_S(C)=-(Σ[i∈S]directEffect_i)/n`. Finally, for **every natural m**,
   if `0<m<n`, fixed supported treated count m, and common treated
   propensity m/n, then `E_L d=-(Σ[i∈S]directEffect_i)/n`.
2. A is valid and has positive arms on S; for y9,
   `U_00≠H_00`; and `Δ_S(U)` differs from both
   `Σ[i∈S]directEffect_i/n` and its negative.

