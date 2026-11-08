# Blind reading

This file was written before opening `claims.json` or `record.json`.
The five theorem docstrings, all entries of `closure.json`, all source
declarations in those closures, and all 24 generated `_proof_` declarations
were read. `scratch/Blind.lean` prints the generated declarations; they are
only proofs that small numeral bases are at least two or finite-index types
are nonempty. They add no statistical assumptions. Lean also confirms that
T6 is universe-polymorphic, rather than restricted to the bottom universe.

## Shared mathematical expansion of the finite definitions

This notation is used in each section below. It expands the SAP definitions
to finite sets, functions, finite sums, and real division; no SAP predicate is
left uninterpreted.

* `FiniteDistribution α` is a pair `(A,w)` with `A : Finset α` and
  `w : α → ℝ`. `IsDistribution` means `w(x)>0` for every `x∈A` and
  `Σ(x∈A) w(x)=1`. There is no condition on weights outside A.
* `E_L f = Σ(x∈A) w(x)f(x)` and `P_L(Q)=Σ(x∈A) if Q(x) then w(x) else 0`.
  The pushforward under f has atom set `A.image f` and weight
  `b ↦ Σ(x∈A) if f(x)=b then w(x) else 0`. Equal images are merged.
* The subjects are `I=Fin N`, treatments are functions `z:I→Bool`, and
  potential outcomes are arbitrary real functions `y:I→(I→Bool)→ℝ`.
  Bool `true` means treatment and `false` means control. `binaryValue(a)` is
  1 for true and 0 for false. Thresholding is `z_i=decide(0≤x_i)`.
* A score lies inside the window exactly when `-b≤x≤b`, with both endpoints
  included. `W_b(x)={i∈I | -b≤x_i≤b}`.
* For a finite subject set S, write `n=|S|` and
  `F_S(x,t)=Σ(i∈S) 1{x_i≤t}/n`.
* For an assignment law L=(A,w),
  `A_ia={z∈A | z_i=a}`, `p_ia=Σ(z∈A_ia)w(z)`,
  `M_ia=Σ(z∈A_ia)w(z)y_i(z)`,
  `U_ia=Σ(z∈A_ia)y_i(z)/|A_ia|`, and `C_ia=M_ia/p_ia`.
  These are respectively `armAssignments`, `armProbability`, `armMoment`,
  `supportAverage`, and `conditionalAverage`. U counts supported assignments
  equally; C uses their probability weights.
* `B_S(f)=Σ(i∈S)(f_i(true)-f_i(false))/n` is `windowContrast`.
  `n_a(z)=Σ(i∈S)1{z_i=a}` is the **real** number `armSize`.
  `D_S(y,z)=Σ(i∈S,z_i=true)y_i(z)/n_true(z)
              -Σ(i∈S,z_i=false)y_i(z)/n_false(z)` is `differenceOfMeans`.
  `observedArmTotal` is the appropriate numerator of this expression.
* `PositiveArms` means `∀i∈S, ∀a:Bool, p_ia>0`.
  `Noninterfering` means `∀i∈S, ∀z,z':I→Bool,
  z_i=z'_i → y_i(z)=y_i(z')`; it ranges over all assignments, including
  unsupported ones.
* `DistinctNoTies(L,X,S)` means `∀i∈S, ∀j∈S, i≠j →
  Σ(ω∈A)1{X_ωi=X_ωj}w(ω)=0`.
* `PrintedLocalConditions(L,X,b,S)` is precisely the conjunction:
  (1) `∀ω∈A, W_b(X_ω)=S`;
  (2) `∃F:ℝ→ℝ, ∀ω∈A, ∀t:ℝ, F_S(X_ω,t)=F(t)`;
  (3) `∀ω∈A, P_L{η | X_η=X_ω}=1/(n!)` for the **full N-vector**;
  (4) the distinct-subject no-ties condition just given; and
  (5) `∀ω∈A, 0<n_true(threshold(X_ω))<n`.
  The no-ties docstring invokes R6; this reading records its literal
  distinct-subject content without consulting the record.
* `OtherTreatments(i)` is the finite function type
  `{j:Fin N // j≠i}→Bool`. `removeOwn(i,z)` restricts z to that subtype.
  `insertOwn(i,a,u)` is the unique full vector with coordinate i equal to a
  and every other coordinate equal to u. Mathlib's `Equiv.funSplitAt` is a
  total equivalence, not a partial insertion with a default.
  Put `q_ia(u)=P_L{z | z_i=a ∧ z|_{I\{i}}=u}/p_ia`.
  `H_ia=Σ(u:OtherTreatments(i))y_i(insertOwn(i,a,u))q_ia(u)` is
  `otherSubjectsAverage`; the sum includes all binary vectors of the other
  subjects. `directEffect_i=H_i,false-H_i,true` uses control minus treatment.

All counts used as real denominators are natural counts cast to ℝ. All these
casts preserve the exact nonnegative integer value. Sums over empty sets
are zero and real division is total, with `r/0=0`. These conventions can
matter for the bare definitions. Each theorem's actual guards are checked
below. None of these definitions uses log, sqrt, rpow, sInf/sSup,
liminf/limsup, an integral, or a partial-function default.

## SAP.P014.T1

Location: `SAP/P014/Challenge/Part1.lean:9–12`; expanded statement:
`SAP/P014/Defs/Part3.lean:10–37`.

There are **no universally quantified input parameters or hypotheses**.
The theorem asserts the following complete conjunction about fixed data.
The sample space is `Fin 6`, every row has weight 1/6, the subjects are
`Fin 4`, S={0,1,2}, b=2, and the score and threshold vectors are:

| row | full score vector | full threshold vector |
| --- | --- | --- |
| 0 | (-2,-1,1,3) | (0,0,1,1) |
| 1 | (-2,1,-1,-3) | (0,1,0,0) |
| 2 | (-1,-2,1,-3) | (0,0,1,0) |
| 3 | (-1,1,-2,-3) | (0,1,0,0) |
| 4 | (1,-2,-1,-3) | (1,0,0,0) |
| 5 | (1,-1,-2,-3) | (1,0,0,0) |

Here 0 and 1 in a threshold vector denote Bool false and true. The outcome
is `y_i(z)=1{z_3=true}` for i≠3, and `y_3(z)=0`.
Let L be the pushforward of the six-row law under the threshold-vector
column. The assertions are:

1. Both the six-row law and L have positive atom weights summing to one.
2. All five expanded printed clauses above hold for these scores, b, and S.
3. `|S|=3`; the full-score pushforward has six distinct atoms; thresholding
   the full score function equals the displayed threshold function.
4. For every permutation σ of `Fin 3`, the event
   `∀i:Fin 3, X_ω,i=(-2,-1,1)_(σi)` has probability 1/6.
5. L has exactly the four atoms
   A=(0,0,1,1), B=(0,1,0,0), C=(0,0,1,0), D=(1,0,0,0),
   with weights 1/6, 1/3, 1/6, 1/3, respectively (`AssignmentMasses`).
6. Every atom has exactly one treated subject in S, every i∈S has
   `p_i,true=1/3` (`CommonWitnessCounts`), and both arm probabilities are
   positive for every i∈S.
7. The unweighted means `(U_i,true,U_i,false)` for i=0,1,2 are respectively
   `(0,1/3)`, `(0,1/3)`, `(1/2,0)`.
8. The weighted means `(C_i,true,C_i,false)` are respectively
   `(0,1/4)`, `(0,1/4)`, `(1/2,0)`.
9. `∀ω:Fin 6, D_S(y,threshold-vector(ω))=0`; `E_L D_S=0`;
   `B_S(U)=-1/18`; `B_S(C)=0`; `E_L D_S-B_S(U)=1/18`; and
   `E_L D_S≠B_S(U)`.

The docstring describes precisely this specified example and its printed
and weighted targets. It calls the local conditions both printed and
intended; the actual statement separately asserts the full-vector clauses
and all six local permutation probabilities.

Junk-value audit: n=3, n_true=1, n_false=2 on every supported assignment;
both own-arm probabilities are positive, hence their finite atom sets are
nonempty. All denominators in all asserted numbers are strictly positive.
The factorial denominator is 3!=6. No zero division is used to obtain any
claimed discrepancy. The outcomes are real values on a finite domain, so
all expectations exist without an integrability convention. All indexing
is checked `Fin` indexing; none can wrap an out-of-bounds index here.

## SAP.P014.T9

Location: `SAP/P014/Challenge/Part1.lean:62–65`; expanded statement:
`SAP/P014/Defs/Part3.lean:84–112`.

Again there are **no input parameters or hypotheses**. The sample space,
row weights, S, L, and threshold vectors A,B,C,D are exactly those explicitly
listed in the T1 section. Here b=1 and the six full-score rows are:

`(-1,-1/2,1/2,2)`, `(-1,1/2,-1/2,-2)`,
`(-1/2,-1,1/2,-2)`, `(-1/2,1/2,-1,-2)`,
`(1/2,-1,-1/2,-2)`, `(1/2,-1/2,-1,-2)`.

The outcome is `y_0(z)=1{z_3=true}`, and `y_i(z)=0` for i≠0.
The complete conjunction says:

1. The row law and L are positive normalized distributions, all five
   expanded printed clauses hold, the full-score pushforward has six atoms,
   and thresholding equals the displayed T1 threshold function.
2. For every permutation σ of `Fin 3`,
   `P{∀i:Fin 3, X_ω,i=(-1,-1/2,1/2)_(σi)}=1/6`.
3. The four assignment masses are 1/6,1/3,1/6,1/3; every supported assignment
   has one local treated subject; every local propensity is 1/3; all local
   own-arm probabilities are positive.
4. `U_0,false=1/3`, `C_0,false=1/4`, `U_0,true=C_0,true=0`.
   For each i∈S different from 0, and each a:Bool, `U_ia=C_ia=0`.
5. `∀i∈S, ∀a:Bool, H_ia=C_ia`, with H expanded in the shared notation.
6. `B_S(U)=-1/9`, `B_S(C)=-1/12`,
   `Σ(i∈S)(H_i,false-H_i,true)/3=1/12`, and B_S(U) differs from both that
   last number and its negative.
7. `∀z∈L.atoms, D_S(y,z)=-1/2` if z=A and 0 otherwise;
   `E_L D_S=-1/12`; and `E_L D_S-B_S(U)=1/36`.

The docstring claims this comparison design satisfies local randomization
and gives these target, direct-effect-average, and bias values. The sign
convention for the direct effect is explicitly control minus treatment.

Junk-value audit: n=3, arm sizes 1 and 2 on support, positive conditioning
probabilities 1/3 and 2/3, and nonempty own-arm support sets rule out every
zero denominator occurring in an asserted mean. All sums are finite;
the sum defining H is over all 2^3 assignments of other subjects and has
no missing or default outcomes. Unattained other-subject patterns get
probability zero, not undefined values. The fractional score literals are
real numbers, and their denominators are 2. No domain extension is used.

## SAP.P014.T5

Location: `SAP/P014/Challenge/Part1.lean:36–39`; expanded statement:
`SAP/P014/Defs/Part3.lean:52–82`.

This is another **closed conjunction**, with no input parameters or
hypotheses. There are six rows with weight 1/6, four subjects, b=2,
S={0,1,2}, and scores

`(1,-1,-2,3)`, `(-1,1,-2,3)`, `(-1,-2,1,3)`,
`(-1,-2,1,4)`, `(-1,-2,1,5)`, `(-1,-2,1,6)`.

The outcome is `y_0(z)=1{z_0=true}`, and `y_i(z)=0` for i≠0. L5 is the
pushforward of the six-row distribution under score thresholding.
`localCoordinates` is exactly restriction to coordinates 0,1,2 by
`Fin.castSucc : Fin 3 → Fin 4`. The asserted conjunction is:

1. The row law and L5 are valid positive normalized distributions. The five
   expanded printed clauses hold. The full-score pushforward has six atoms.
2. The six local arrangement probabilities, in the order
   `(1,-1,-2)`, `(-1,1,-2)`, `(-1,-2,1)`, `(-2,-1,1)`,
   `(-2,1,-1)`, `(1,-2,-1)`, are
   `1/6,1/6,2/3,0,0,0`, respectively; `2/3≠1/6` is also asserted.
3. The treatment propensities of subjects 0,1,2 are respectively
   `1/6,1/6,2/3`, and both own-arm probabilities are positive for all i∈S.
4. L5 has exactly the atoms `(1,0,0,1)`, `(0,1,0,1)`, `(0,0,1,1)`, with
   weights `1/6,1/6,2/3`.
5. Every atom z has `n_true(z)=1` and `D_S(y,z)=1{z_0=true}`.
6. For every i∈S and every a:Bool,
   `U_ia=C_ia= if i=0 then 1{a=true} else 0`.
7. For every i∈S and all z,z', `z_i=z'_i → y_i(z)=y_i(z')`.
8. `E_L5 D_S=1/6`, `B_S(U)=1/3`, and these numbers differ.

The docstring's nonuniform-arrangement, unequal-propensity, and
no-interference descriptions refer to these explicit assertions.

Junk-value audit: the printed full-score mass uses six distinct vectors
even though four have identical local coordinates; it is not a division
by a duplicate count. The local size is 3, supported arm sizes are 1 and 2,
and conditioning probabilities and support cardinalities are all positive.
Thus no zero-division convention enters the estimator, U, C, or contrast.
The full score 6 in the last row is a real score, not a finite index.
All expectations are finite sums of finite real numbers.

## SAP.P014.T10

Location: `SAP/P014/Challenge/Part1.lean:67–71`; expanded statement:
`SAP/P014/Defs/Part6.lean:10–34`.

The statement is a conjunction of a universally quantified implication and
a closed failure example. The quantifier order of the general part is:

For every natural N, every finite law L=(A,w) on `Fin N→Bool`, **if**
all its supported weights are positive and sum to one, **then**, for every
finite S⊆Fin N and every real potential-outcome function y, **if**
S is nonempty and `∀i∈S, 0<p_i,true<1`, **then** all of:

1. `∀i∈S, ∀a:Bool`,
   `Σ(u:{j:Fin N // j≠i}→Bool)
      y_i(insertOwn(i,a,u))
        [Σ(z∈A)1{z_i=a ∧ z|_{I\{i}}=u}w(z)/p_ia]
    = Σ(z∈A_ia)y_i(z)[w(z)/p_ia]
    = [Σ(z∈A_ia)w(z)y_i(z)]/p_ia`.
2. `Σ(i∈S)(C_i,true-C_i,false)/n
    = -Σ(i∈S)(H_i,false-H_i,true)/n`.
3. For every natural m, if `0<m<n`, every supported z has n_true(z)=m,
   and every i∈S has `p_i,true=m/n`, then
   `Σ(z∈A)w(z)D_S(y,z)=-Σ(i∈S)(H_i,false-H_i,true)/n`.

The second conjunct specializes to L and y from the T9 section. It asserts
L is a valid distribution, all local arms have positive probability,
`U_0,false≠H_0,false`, and `B_S(U)` differs from both
`Σ(i∈S)(H_i,false-H_i,true)/3` and its negative. It does not include the
numeric values, the score-law hypotheses, or an estimator expectation in
this conjunct; those are supplied by other declarations but are not
assumed here.

The docstring describes weighted averages as the conditional sum over other
subjects, the reverse sign for the corrected target and estimator, and
the failed unweighted identifications in this example.

Junk-value audit: validity makes the atom set nonempty; S.Nonempty gives
n>0. Validity plus `0<p_i,true<1` yields `p_i,false=1-p_i,true>0`,
so U's failure example and all conditional means have positive denominators.
In the estimator clause, `0<m<n` and the fixed count give both arm sizes
strictly positive on support. For N=0 no nonempty S exists, which simply
excludes a nonexistent window; for N=1 the first two identities can have
genuine data, and the other-subject index type has exactly one function
on the empty set. That convention gives the usual one-subject sum.
There are no expectations of non-integrable functions: outcomes are real
functions on a finite assignment space. All subtraction here is real;
no truncated natural subtraction occurs.

## SAP.P014.T6

Location: `SAP/P014/Challenge/Part1.lean:41–50`; expanded statement is
`T6GeneralPart ∧ T6PrintedForwardPart ∧ T6OutsideExample`, at
`SAP/P014/Defs/WholeW1.lean:154–155`.

For the two general parts, independently quantify, in order: an arbitrary
type Ω in the theorem's universe, a measurable-space structure on Ω,
a natural N, a measure μ on Ω with `IsProbabilityMeasure μ`, a function
`X:Ω→Fin N→ℝ`, b:ℝ, a finite S⊆Fin N, a function `v:S→ℝ`, and m:ℕ.
Here S as a type is the subtype `{i:Fin N // i∈S}`. The common premises are:

* b>0, n=|S|≥2, v is injective, and every v_i lies in [-b,b];
* `0<m<n` and exactly m elements of the finite subtype S have v_i≥0;
* every coordinate `ω↦X_ωi` is measurable;
* for **every** subject i, `(μ{ω | -b≤X_ωi≤b}).toReal` equals 1 if i∈S
  and 0 otherwise;
* for **every** permutation σ of S,
  `(μ{ω | ∀i:S, X_ωi=v_(σi)}).toReal=1/(n!)`.

The last three items are the full expansion of `CorrectedLocalConditions`.
Write P(E)=(μ E).toReal in the following. This is a usual real probability
because μ is a probability measure.

The first general part concludes the following expanded `LocalConsequences`:

1. For μ-almost every ω, all of:
   `n_true(threshold(X_ω))=m`, `0<n_true<n`, `W_b(X_ω)=S`,
   `|W_b(X_ω)|=n`, and, **for every real t**,
   `Σ(i∈S)1{X_ωi≤t}/n=Σ(i:S)1{v_i≤t}/n`.
   The ∀t is inside the almost-everywhere assertion, so a single conull
   event works for all t.
2. For every i:S, the treatment probability is
   `m (n-1)!/(n!)=m/n`, and the control probability is `(n-m)/n`.
   In the factorial expression n-1 is natural subtraction; in `(n-m)/n`
   subtraction is in ℝ.
3. For every distinct i,j:S, `P{X_i=X_j}=0`.

It also concludes: **for every** total function
`g:(S→ℝ)→Fin N→ℝ`, **if**
`∀ᵐω, ∀j∉S, X_ωj=g((i:S↦X_ωi),j)`, **then there exists** a finite
law A=(B,w) on full real score vectors `Fin N→ℝ` such that:
the supported weights are positive and sum to one, `|B|=n!`,
`∀x∈B,w(x)=1/(n!)`, and **for every full vector x**,
`P{X=x}=if x∈B then w(x) else 0`.
There is no measurability premise on g. Its values are only used on a finite
set of local arrangements, and the required relation to the measurable X
is almost sure.

The second general part has the same quantified objects and common
premises. It **additionally assumes**:

* `∀ᵐω, 0<P{η | X_η=X_ω}` (`DiscreteScoreLaw`); and
* `∀x:Fin N→ℝ, 0<P{X=x} → P{X=x}=1/(n!)`.

It concludes that **there exists** a finite set B of full score vectors with:
`∀x, x∈B ↔ 0<P{X=x}`; `|B|=n!`;
for **every** permutation σ:S≃S, there exists **exactly one full vector x**
with `x∈B ∧ ∀i:S,x_i=v_(σi)`; and **there exists** a total function g
of the above type with `∀ᵐω, ∀j∉S, X_ωj=g((i:S↦X_ωi),j)`.
These are all clauses of `FullScoreReconstruction`. The g is chosen after
B. Discreteness is almost-sure positive point mass, not an assumption that
the score space itself is finite.

The third part is a closed conjunction about Ω=Fin 6×Bool with every
pair (r,false) of weight 1/18 and every pair (r,true) of weight 1/9.
The first three scores are row r of `scores1` listed in the T1 section,
and the fourth is -3 for false and 3 for true. The statement asserts:

1. These twelve weights form a valid distribution.
2. For every pair ω, `W_2(X_ω)=S={0,1,2}`.
3. For each a:Fin 6, the local vector equals row a's first three coordinates
   with probability 1/6; for every permutation σ:Fin 3≃Fin 3, it equals
   the corresponding permutation of (-2,-1,1) with probability 1/6.
4. For every ω the local treated count is 1; |S|=3; the full-score
   pushforward has twelve atoms.
5. For every ω, `P{η | X_η=X_ω}` is 1/9 or 1/18 according to ω's Bool,
   and is different from 1/6.
6. `P{X_3=-3}=1/3` and `P{X_3=3}=2/3`.
7. For every a:Fin 6 and t:Bool, the probability that the local vector
   equals local row a **and** X_3 equals (3 if t else -3) is the product
   of those two marginal probabilities. Thus independence is stated for
   every possible local and outside value, rather than merely asserted
   in a name.

The docstring describes all three components, including discreteness in
the forward implication and almost-sure outside reconstruction.

Junk-value audit: `eventProbability` uses `ENNReal.toReal`, which sends ∞
to 0, but every set has measure at most μ(Ω)=1, so this convention is
unreachable here. Coordinate measurability and finite products make all
point, permutation, threshold, tie, and reconstruction events measurable
(or equal to finite Boolean combinations of such events). All windows and
CDFs in the general parts have n≥2; n! is a positive natural number before
its real cast. `n-1` is the sole truncated subtraction and n≥2 prevents
truncation from changing its intended meaning. `0<m<n` makes all asserted
arm sizes and real propensity denominators positive. The outside example
has n=3 and arm sizes 1 and 2. The possible null exceptional states in
the general parts are explicitly excluded by almost-everywhere quantifiers;
the definitions do not assign them an inferential role. There are no
Bochner integrals, empty infima, suprema, limsups, logs, roots, powers with
domain issues, default partial values, or integer casts in this closure.
The finite-set existential conclusions assert nonempty normalized laws,
not arbitrarily chosen empty supports. No usual moment hypothesis is
needed for the probabilities and finite real CDFs in this theorem.
