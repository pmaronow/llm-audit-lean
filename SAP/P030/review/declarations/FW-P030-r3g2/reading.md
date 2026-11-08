# Blind reading of P030-T6 through P030-T10

This file was written before opening `claims.json` or `record.json`. It describes
the statements, not a verdict against the canonical claims. Sources read:
`Challenge/Part1.lean`, `Defs/Part1.lean` through the relevant parts of
`Defs/Part5.lean`, `Defs/WholeW1.lean`, the import files, and every entry of
`closure.json`. The 49 distinct generated `_proof_` declarations in the closures
were also printed by Lean in `scratch/PrintClosure.lean`; the output is in
`scratch/PrintClosure.out`. There are 101 distinct closure declarations overall.
The generated declarations establish literal numeral typeclass instances,
nonzero finite index sizes, the bound `r.val + 1 < 10`, or that the four listed
fixed indices satisfy the fixed indicator. They add no substantive hypotheses.

All indices below are zero based unless a unit is explicitly described in
one-based paper notation. Function equality is pointwise equality. Finite sets
have no duplicate elements, while ranks count indices, so tied observations
retain multiplicity. Decimal literals in these statements denote exact rational
real numbers.

## SAP.P030.T6

Source: `SAP/P030/Challenge/Part1.lean:27-30`; statement definition:
`SAP/P030/Defs/Part5.lean:10-21`.

### Universal part, including all definitions

For every natural number N, finite set Ω of Boolean functions `Fin N → Bool`,
Boolean function S on `Fin N`, and Boolean function obs on `Fin N`, assume
`obs ∈ Ω`. Then, for every real potential-outcome schedule
`Y : Fin N → (Fin N → Bool) → ℝ` and every real-valued function

`g : (({i : Fin N | S i = true} → ℝ)) → (Fin N → Bool) → ℝ`,

the following two implications hold. Write

`C = {z ∈ Ω | ∀ i, S i = true → z i = obs i}`,

and write `y(z)` for the function on the subtype of fixed units that takes i to
`Y i.val z`. The functions called statistic and reference statistic are exactly
`t(z) = g(y(z), z)` and `t_ref(obs,z) = g(y(obs), z)`.

1. If, for every i and every z,z' in Ω, `z i = z' i` implies
   `Y i z = Y i z'`, then, for every fixed i and every z,z' in C,
   `Y i z = Y i z'`.
2. If the latter fixed-outcome condition on C holds, then `y(z)=y(obs)` for
   every z in C; `t_ref(obs,z)=t(z)` for every z in C; and, for every real x,

   `#{z ∈ C | t_ref(obs,z) ≤ x}/#C = #{z ∈ C | t(z) ≤ x}/#C`.

The two implications are conjoined; the second assumes the fixed-outcome null,
not the stronger no-interference null. The threshold x is universally quantified
inside the second conclusion. No distribution, smoothness, or restriction on g
is imposed. Its actually attainable outcome inputs and assignment inputs are
finite, so usual statistical measurability poses no obstacle.

### Explicit ten-unit conjunct, fully unfolded

Independently of the universal inputs above, the theorem asserts all the
following facts about fixed, explicitly defined data:

- Units are `Fin 10`. Position of unit i is the real number `i.val+1`.
  The fixed units are indices 0,7,8,9 (paper units 1,8,9,10).
- For j in `Fin 10`, e_j is the assignment treating exactly j:
  `e_j(i) = decide(i=j)`. Ω10 is the image of all ten indices under this map.
  For r in `Fin 6`, j_r is the index with value r.val+1, and C10 is the image
  `{e_(j_r) | r ∈ Fin 6}`.
- The potential outcome at i, for every assignment, is entry i of
  `[1,2,2,2,2,3,2,3,2,1]`. In particular this schedule has no effects:
  `∀ i, ∀ z,z' ∈ Ω10, Y i z = Y i z'`. It also has no interference in the
  implication form stated above.
- Conditioning Ω10 on agreement with e_6 at the fixed units gives exactly
  C10; all outcomes of fixed units agree between every two assignments in C10;
  and e_(j_0), e_(j_3) both belong to C10.
- Let f enumerate the fixed indices in the order `[0,7,8,9]`. For any z,
  V(z) is the finite set of indices j with S(j)=false and z(j)=true.
  Distance at fixed index f(k) is the minimum of `|x(f(k))-x(j)|` over
  j in V(z), if V(z) is nonempty, and is zero otherwise.
- The fixed outcome vector y is `[1,3,2,1]`. The six distance vectors D_r are,
  in order,
  `[1,6,7,8]`, `[2,5,6,7]`, `[3,4,5,6]`, `[4,3,4,5]`, `[5,2,3,4]`,
  `[6,1,2,3]`. For each row its treated-variant set is nonempty.
- For a real vector a indexed by `Fin n`, its midrank at k is

  `R_a(k) = #{l | a(l)<a(k)} + (#{l | a(l)=a(k)}+1)/2`.

  Put `U_a(k)=R_a(k)-(n+1)/2`,
  `Q(a)=Σ_k U_a(k)^2`, and `C(a,b)=Σ_k U_a(k)U_b(k)`.
  Its Spearman expression is `C(a,b)/sqrt(Q(a)Q(b))`.
- For every row Q(D_r)>0, and Q(y)=9/2. The six Spearman expressions are
  `[-1/sqrt(90), -1/sqrt(90), -1/sqrt(90), -5/6, -3/sqrt(10), -3/sqrt(10)]`.
  The strict inequalities are
  `-3/sqrt(10) < -5/6 < -1/sqrt(90) < 0`; every row is negative.
  The errors in displaying these three distinct values as -0.105, -0.833,
  and -0.949 are respectively less than 0.0005.
- For the actual statistic, g takes a function h on the fixed-unit subtype
  and assignment z to the Spearman expression of its four nearest-variant
  distances and the four-vector `k ↦ h(f(k))`. With the constant potential
  schedule above, the actual statistic at e_(j_0) differs from that at e_(j_3).

Thus the explicit counterexample establishes outcome invariance together with
statistic variation. It does not assume an actual statistic is constant.

### Junk and boundary conventions

Real division sends division by zero to zero. The universal count ratios avoid
this: obs belongs to C, hence C is nonempty. The finite minimum has an explicit
zero fallback for empty V; every concrete distance row asserts nonempty V and
indeed has its unique treated variant j_r. Spearman's real-valued definition
would assign zero to a zero denominator; its concrete uses have positive rank
square sums. `Real.sqrt` is zero on nonpositive inputs, but its inputs here are
positive. Rank sums and cardinalities are finite; natural-number cardinalities
are cast into ℝ before the additions and divisions in the rank definition, so
there is no truncated subtraction. `Fin` numeral construction can reduce modulo
the type size, but all the fixed and treatment indices here are in range.

N may be zero, and the fixed-unit subtype may be empty in the universal part;
there is still one empty assignment when N=0. Fixed-unit assertions then can be
vacuous, but the nonempty reference support and count ratios remain sound.
There are no integrals, infinite extended reals, logarithms, real powers,
unbounded infima/suprema, sequence limsups/liminfs, or partial-function default
values in this closure. The generated numeral and index proofs described above
do not create additional junk cases.

## SAP.P030.T7

Source: `SAP/P030/Challenge/Part1.lean:32-35`; statement definition:
`SAP/P030/Defs/Part5.lean:23-35`.

For every N : ℕ, finite set Ω of assignments `Fin N → Bool`, fixed indicator
S : `Fin N → Bool`, and assignment obs, assume obs belongs to Ω. Define
`C = {z ∈ Ω | ∀ i, S i=true → z i=obs i}`. The conclusion is the conjunction of:

1. For every z in C, every z' in C, and every i, if S i=true then z i=z' i.
2. For every real schedule `Y : Fin N → (Fin N → Bool) → ℝ`, if
   `∀ i, ∀ z,z' ∈ Ω, z i=z' i → Y i z=Y i z'`, then
   `∀ i, S i=true → ∀ z,z' ∈ C, Y i z=Y i z'`.
3. For every such Y, if there exist i, z, z' with S i=true, z,z' in C,
   and `Y i z ≠ Y i z'`, then the no-interference property on Ω from item 2
   does not hold.
4. For every pair of functions c,τ : `Fin N → ℝ`, the schedule
   `Y(i,z)=c(i)+τ(i) * (if z i then 1 else 0)` has both the no-interference
   property on Ω and the fixed-outcome property on C. Thus τ need not be zero.
5. For every Y, the condition
   `∀ i, ∀ z,z' ∈ Ω, Y i z=Y i z'` implies no interference on Ω.

The Y-quantifiers in items 2, 3, and 5 are separate. The c,τ-quantifiers in item 4
are universal. There is no statistic, p-value, or probabilistic independence
assertion. No interference is defined on the allowed assignment support Ω,
not on assignments outside Ω.

### Junk and boundary conventions

All operations are finite filtering, Boolean equality, real addition and
multiplication, and pointwise schedule equalities. There is no division,
square root, logarithm, real exponentiation, integration, `toReal`, extremum,
limit, or partial-function fallback. Casting a Boolean treatment through the
explicit if returns exactly 0 or 1. Natural N specifies a finite type without
an integer cast or subtraction. obs∈Ω makes C nonempty. N=0 or an empty fixed
subtype makes some component assertions vacuous; it does not render the theorem
vacuous for nonempty populations. A singleton support makes no interference
trivial on that support, but larger supports are included.

## SAP.P030.T8

Source: `SAP/P030/Challenge/Part1.lean:37-38`; statement definition:
`SAP/P030/Defs/WholeW1.lean:142-148`, which includes
`SAP/P030/Defs/Part5.lean:37-51` and the explicit detail predicates at
`Defs/WholeW1.lean:93-131`.

This is a closed conjunction of numerical facts plus one universal positive
divisor identity. It has no top-level hypotheses. All its SAP notions unfold as
follows.

For a real vector a : `Fin n → ℝ`, let
`R_a(k)=#{l | a(l)<a(k)}+(#{l | a(l)=a(k)}+1)/2`,
`U_a(k)=R_a(k)-(n+1)/2`,
`C(a,b)=Σ_k U_a(k)U_b(k)`, and `Q(a)=Σ_k U_a(k)^2`.
Define the correct rank correlation
`ρ(a,b)=C(a,b)/sqrt(Q(a)Q(b))`, the divisor-m covariance
`Cov_m(a,b)=C(a,b)/m`, and the printed expression

`P_m(a,b)=(C(a,b)/m)/((Q(a)/m)*(Q(b)/m))`.

The explicit vectors come from positions x(i)=i.val+1 on `Fin 10`, fixed
indicator S true exactly at 0,7,8,9, fixed enumeration `[0,7,8,9]`, and one-hot
assignment e_j treating j only. The r-th assignment treats index r.val+1,
for r in `Fin 6`. Its distance at a fixed index i is the minimum of |x(i)-x(j)|
over nonfixed treated indices j, with zero fallback if there are none. The
outcome schedule is entry i of `[1,2,2,2,2,3,2,3,2,1]`, independently of z;
the fixed outcome vector y is its values at the fixed enumeration and e_6.
Consequently y and the six D_r are asserted to be:

`y=[1,3,2,1]`,

`D=([1,6,7,8], [2,5,6,7], [3,4,5,6], [4,3,4,5], [5,2,3,4], [6,1,2,3])`.

The theorem includes every clause of the following list:

1. The above y and D equalities; nonemptiness of the treated-variant set for
   every row; Q(D_r)>0 for every row and Q(y)=9/2; the exact values
   `ρ(D_r,y)=[-1/sqrt(90),-1/sqrt(90),-1/sqrt(90),-5/6,-3/sqrt(10),-3/sqrt(10)]`;
   the strict order `-3/sqrt(10)<-5/6<-1/sqrt(90)<0`; negativity of each row;
   and error <0.0005 for displays -0.105, -0.833, and -0.949.
2. For all r, the six P_4 values are
   `[-4/45,-4/45,-4/45,-20/27,-4/5,-4/5]`, and the six P_3 values are
   `[-1/15,-1/15,-1/15,-5/9,-3/5,-3/5]`.
   Both -4/5 and -3/5 differ from -3/sqrt(10), and -4/5 differs from -3/5.
3. At the observed row r=5,
   `R_y=[3/2,4,3,3/2]`, `U_y=[-1,3/2,1/2,-1]`,
   `R_D=[4,1,2,3]`, `U_D=[3/2,-3/2,-1/2,1/2]`,
   `C(D_5,y)=-9/2`, `Q(D_5)=5`, and `Q(y)=9/2`.
4. Its divisor-4 moments are `Cov_4=-9/8`, `Q(D_5)/4=5/4`, `Q(y)/4=9/8`;
   its divisor-3 moments are `Cov_3=-3/2`, `Q(D_5)/3=5/3`, `Q(y)/3=3/2`.
   For every row r and every real m>0,

   `(C(D_r,y)/m)/sqrt((Q(D_r)/m)*(Q(y)/m)) = ρ(D_r,y)`.

5. The squares of the observed P_4, P_3, and correct correlations are 16/25,
   9/25, and 9/10, respectively; both 16/25 and 9/25 are less than 9/10.
6. For a=`[1,2,1,1]` and b=`[0,2,1,1]`, Q(a)>0 and Q(b)>0,
   `ρ(a,y)=sqrt(6)/3`, `ρ(b,y)=5/6`, `P_4(a,y)=8/9`, `P_4(b,y)=20/27`,
   `sqrt(6)/3<5/6`, and `20/27<8/9`.
   Also `R_a=[2,4,2,2]`, `R_b=[1,4,5/2,5/2]`, their correct squared
   correlations are 2/3 and 25/36, `2/3<25/36`, and `8/9=24/27`.
7. For v=`[1,2,3]` and w=`[0,0,1]`,
   `∀ i,j ∈ Fin 3, v(i)≤v(j) → w(i)≤w(j)`;
   `Q(v)=2`, `Q(w)=3/2`, `ρ(v,w)=sqrt(3)/2`, and this last value differs
   from both 1 and -1. Their midranks are `[1,2,3]` and `[3/2,3/2,3]`,
   centered ranks `[-1,0,1]` and `[-1/2,-1/2,1]`, and C(v,w)=3/2.
   Both vectors are nonconstant, meaning each has two unequal entries.
   Finally `|sqrt(3)/2-0.866|<0.0005`.

Thus the first numerical pair falsifies the covariance-over-product-of-variances
formula as an identity for rank correlation; the second pair reverses its
ordering; the weakly monotone pair does not achieve ±1.

### Junk and boundary conventions

Every concrete vector is indexed by a nonempty finite type; every numerical
index is in range, despite `Fin` literals generally being modular. The nearest
treated minimum has a zero fallback for an empty set, but each used assignment
has its unique nonfixed treated index. All actual correlation denominators have
positive Q factors. P_m uses only m=4 or 3, and the corrected divisor identity
assumes m>0. Thus real division by zero and the zero value of sqrt on
nonpositive arguments are unused. Rank cardinalities are cast to reals before
arithmetic, ties count indices, and all subtractions are real. All decimals are
exact rational tolerances, not floating-point rounding operations. No Bochner
integrals, undefined moments, ∞ conversions, logarithms, real powers,
unbounded extrema, limsups/liminfs, or unspecified defaults occur. In particular
the weakly monotone counterexample has two nonconstant vectors and defined
correlation, so it does not exploit a constant-vector convention.

## SAP.P030.T9

Source: `SAP/P030/Challenge/Part1.lean:40-43`; statement definition:
`SAP/P030/Defs/Part5.lean:53-67`.

For every natural n, assume 2≤n. Then, for every pair of functions
a,b : `Fin n → ℝ`, assume `∃ i,j, a(i)≠a(j)` and independently
`∃ i,j, b(i)≠b(j)`. Let

`R_a(k)=#{l | a(l)<a(k)}+(#{l | a(l)=a(k)}+1)/2`,
`U_a(k)=R_a(k)-(n+1)/2`, `Q(a)=Σ_k U_a(k)^2`,
`C(a,b)=Σ_k U_a(k)U_b(k)`, and `ρ(a,b)=C(a,b)/sqrt(Q(a)Q(b))`.

The conclusion is:

1. `Σ_k R_a(k)=n(n+1)/2` and `Σ_k R_b(k)=n(n+1)/2`, with n cast to ℝ.
2. Q(a)>0 and Q(b)>0.
3. For every real m>0,
   `ρ(a,b)=(C(a,b)/m)/sqrt((Q(a)/m)*(Q(b)/m))`.
4. -1≤ρ(a,b)≤1.
5. `|ρ(a,b)|=1` if and only if there exists real c≠0 such that, for every k,
   `U_a(k)=c U_b(k)`. The existential c is inside the equivalence, after a,b.
6. For every c≠0 satisfying this equality, c>0 implies ρ=1 and c<0 implies
   ρ=-1.
7. If `∀ k,l, a(k)<a(l) ↔ b(k)<b(l)`, then the two midrank functions are
   equal and ρ=1.
8. If `∀ k,l, a(k)<a(l) ↔ b(l)<b(k)`, then
   `∀ k, R_a(k)=n+1-R_b(k)` and ρ=-1.

There are two additional, independently conjoined closed examples, not
hypotheses on a and b:

- For v=`[1,2,3]` and w=`[0,0,1]` on `Fin 3`, all v-order comparisons
  `v(i)≤v(j)` imply `w(i)≤w(j)`, Q(v)=2, Q(w)=3/2,
  `ρ(v,w)=sqrt(3)/2`, and that value differs from 1 and -1.
- The six-row table is defined from positions x(i)=i.val+1 on `Fin 10`, fixed
  indices 0,7,8,9 (enumerated in that order), and the r-th one-hot assignment
  treating index r.val+1 for r in `Fin 6`. At a fixed unit, distance is the
  minimum absolute position difference to a nonfixed treated unit (zero if
  there is none). Fixed outcomes are entries 0,7,8,9 of
  `[1,2,2,2,2,3,2,3,2,1]`, independent of assignment.
  The outcome vector is `[1,3,2,1]` and the distance vectors are
  `[1,6,7,8]`, `[2,5,6,7]`, `[3,4,5,6]`, `[4,3,4,5]`, `[5,2,3,4]`,
  `[6,1,2,3]`.
  Every row has a nonempty treated-variant set and positive Q(D_r), Q(y)=9/2,
  and the exact correlations are
  `[-1/sqrt(90),-1/sqrt(90),-1/sqrt(90),-5/6,-3/sqrt(10),-3/sqrt(10)]`.
  They have the strict order `-3/sqrt(10)<-5/6<-1/sqrt(90)<0`, every row is
  negative, and the three respective displays -0.105, -0.833, and -0.949
  have errors less than 0.0005.

### Junk and boundary conventions

The nonconstancy hypotheses and explicit n≥2 exclude empty and singleton
index types in the universal part; positive Q is itself a proved conclusion,
not an assumed equality case. The m-identity requires m>0. The concrete weak
example has positive rank squares, and all table Q values are positive.
Thus Spearman's totalized division never supplies an undefined correlation.
All sqrt inputs are positive in correlations and are positive constants in
numerical examples. The minimum's empty-set zero fallback is excluded by the
concrete treated-variant nonemptiness assertion. Natural cardinals are embedded
in ℝ before subtraction; no Nat/Int truncated subtraction is used. Every `Fin`
literal is in range. There are no integrals, ∞ conversions, logarithms, rpow,
unbounded set extrema, limsups/liminfs, or partial-function defaults.

## SAP.P030.T10

Source: `SAP/P030/Challenge/Part1.lean:45-48`; statement definition:
`SAP/P030/Defs/Part5.lean:69-86`.

The closed statement is a conjunction of six parts. Its only SAP functions are
Boolean assignments, `treatment(z,i)=if z i then 1 else 0`,
`q(a,b)=none` if b=0 and `some(a/b)` otherwise,
`h(d)=1/((3/2)*d)^2`,

`I(d,z,i)=Σ_{j ∈ (univ : Finset (Fin N)).erase i} treatment(z,j)*h(d(i,j))`,

and

`S(d,i)=Σ_{j ∈ (univ : Finset (Fin N)).erase i} h(d(i,j))`.

1. For every N, real function d on `Fin N × Fin N`, Boolean assignment z,
   and i : Fin N, assume d(i,i)=0. The self numerator
   `(1-(if i=i then 1 else 0))*treatment(z,i)` is zero, the denominator
   `((3/2)*d(i,i))^2` is zero, and q of these numerator and denominator
   is `none`.
2. For every N and real function d on `Fin N × Fin N`, assume
   `∀ i,j, i≠j → 0<d(i,j)`. Then every j in `univ.erase i` has
   `((3/2)*d(i,j))^2 ≠ 0`. Also, for every z,i the function I is equal to
   the displayed off-diagonal treatment-weighted sum, and for every i the
   function S is equal to the displayed off-diagonal unweighted sum.
   These last two equalities unfold their definitions; no diagonal condition,
   symmetry, or triangle inequality is assumed in this part.
3. For every real d>0,
   `h(d)=4/(9*d^2)`, `h(2*d)/h(d)=1/4`, `h(2/3)=1`, `h(1)=4/9`,
   and `h(2)=1/9`. The last three equalities are inside, but independent of,
   the d-quantifier.
4. There do not exist real constants A,c such that for every real d>0,
   `h(d)=A*Real.exp(-c*d)`.
5. For all real B,d, if B>0, d>0, and `d<2/(3*sqrt(B))`, then `B<h(d)`.
6. For all real A,c, the real function `d ↦ A*Real.exp(-c*d)` tends to A
   as d tends to zero within the open half-line (0,∞). In filter notation
   the source is `nhdsWithin 0 (Set.Ioi 0)` and the target `nhds A`.

No limit at infinity is asserted. No relation between the d used in the finite
population and a geometric metric is required beyond the stated positivity.
Excluding self is part of the two sum definitions, not an assumption about
Lean's value for an unexcluded self term.

### Junk and boundary conventions

The total real function h takes h(0)=0 because Lean real division by zero is
zero. The statement deliberately does not interpret that as a valid real
self contribution: its separate Option-valued quotient sends a zero denominator
to `none`, including 0/0. Every contribution in the off-diagonal sums has a
nonzero denominator by the strict-positivity assumption. Scalar identities and
divergence require d>0. The ratio h(2d)/h(d) also has a positive denominator.
The threshold sqrt(B) has B>0, so it and its denominator are positive; there is
no use of sqrt's value zero on nonpositive arguments. Constants 3/2, 2/3, 4/9,
and 1/9 are real rational numbers.

For N=0 there is no i, so indexed assertions are vacuous. For N=1 the
off-diagonal sums are empty and equal zero, which is the correct empty sum.
Both cases coexist with all larger N and do not defeat the nontrivial scalar
parts. `Finset.erase` removes i exactly; no natural truncated subtraction or
modular index is used in these formulas. `Real.exp` is defined on all real
inputs. The source filter at zero from the positive side is nontrivial. There
are no Bochner integrals, ∞ conversions, logarithms, rpow, empty/unbounded
set extrema, sequence limsups/liminfs, or hidden partial-function defaults.
