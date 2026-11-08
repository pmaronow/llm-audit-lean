# Blind reading

This file was written before opening `claims.json` or `record.json`.
I read the Challenge docstrings and statements, every source definition in the
five closures in `closure.json`, and used `scratch/ClosurePrint.lean` to inspect
the types of the generated auxiliary declarations and the `FiniteLaw`
constructor/projections. The auxiliaries only supply numeral instances, valid
`Fin` bounds, or membership of the four enumerated fixed units. They introduce
no mathematical assumptions.

## SAP.P030.T1

The theorem is an unconditional conjunction about the following specific data.
An assignment is a function `Fin 5 → Bool`; an assignment set is a `Finset` of
such functions. In one-based unit order, positions are `(0,4,8,-1,-2)`, the
fixed-unit indicator is `(true,true,true,false,false)`, and the potential
outcomes are `(0,1,2,0,0)` independently of the assignment. For `a : Fin 2`,
`z_a(i)` is true exactly when the zero-based index of `i` is `a+3`.
The support is the image of these two assignments, with uniform probability.
The enumerated fixed units are indices `0,1,2`. Their outcome vector is
`y=(0,1,2)` and their distance vector `d_a` is distance on the real line to
the nearest treated nonfixed unit.

Here and below, for a finite support `E` and predicate `P`, uniform probability
means exactly `|{z ∈ E : P(z)}| / |E|`, with natural cardinalities cast to real
numbers. Conditioning an assignment set on an observed assignment means
filtering it for agreement with that assignment at every fixed unit. No effects
means `∀ i, ∀ z ∈ E, ∀ z' ∈ E, Y(i,z)=Y(i,z')`. No interference adds the
antecedent `z(i)=z'(i)` to this equality.

For any `a : Fin n → ℝ`, its midrank at `k` is
`R_a(k)=#{l : a(l)<a(k)} + (#{l : a(l)=a(k)}+1)/2`.
Its centered rank is `C_a(k)=R_a(k)-(n+1)/2`. The cross product is the finite
sum `Q(a,b)=Σ_k C_a(k)C_b(k)`; the rank square sum is
`V(a)=Σ_k C_a(k)^2`; Spearman correlation is
`Q(a,b)/sqrt(V(a)V(b))`. These formulas, rather than a name for an unspecified
statistic, define `fiveStatistic(a)=rho(d_a,y)`.

The conjuncts assert all of the following:

* For each unit and **all** binary assignments `z,z'`, its outcome is unchanged;
  also no effects and no interference hold on the specified support.
* The support has two assignments, conditioning on `z_0` preserves the support,
  each assignment has probability `1/2`, every fixed unit is untreated on the
  support, and each `z_a` treats exactly one unit.
* `y=(0,1,2)`, `d_0=(1,5,9)`, and `d_1=(2,6,10)`.
  The ranks of each of these vectors are `(1,2,3)` and the centered ranks are
  `(-1,0,1)`. For each `a`, the cross product is `2`, both square sums are `2`,
  and `rho(d_a,y)=1`. Both square sums are strictly positive and each treated
  nonfixed-unit set is nonempty.
* For every `a : Fin 2`, both inclusive tail probabilities, counted over all
  `b : Fin 2`, are `1`.
* For **every real** `alpha`, if `0<alpha<1`, the probability over `a : Fin 2`
  of `p_L(a)<alpha/2 OR 1-alpha/2<p_L(a)` is `1`; the probability of
  `p_L(a)<alpha/2 OR p_U(a)<alpha/2` is `0`; and `alpha<1` is reiterated as
  a conjunct of the conclusion. Here `p_L(a)=P(rho_b≤rho_a)` and
  `p_U(a)=P(rho_a≤rho_b)`, including ties.
* At `alpha=1/20`, the two thresholds are `1/40` and `39/40`, the latter is
  less than `1`, and the printed rule rejects `p=1`.

The docstring describes this finite example and its two rejection probabilities.

Junk-value audit: real division by zero is defined as zero in Lean, and
`Real.sqrt` is zero on nonpositive inputs. The Spearman denominator here is
`sqrt(4)=2`, so neither convention is used. `nearestDistance` is the finite
minimum of absolute real coordinate differences over treated nonfixed units,
but returns **0** when that set is empty. Each distance used here has a
nonempty treated set, explicitly asserted as well as directly inspectable.
All probability supports have cardinality two, and all numeric denominators
are nonzero. Every `Fin` index is in range. Natural-to-real casts are exact;
there is no natural subtraction, `toReal`, integral, logarithm, real power,
infinite supremum, or limit in this closure.

## SAP.P030.T2

This is also an unconditional conjunction for fixed data, followed by explicitly
bounded real threshold quantifiers. Assignments are now `Fin 10 → Bool`.
Unit `i` has position `i+1` (one-based positions 1 through 10).
`tenAssignment(j)` treats just unit `j`; `tenOmega` is the image of all ten such
assignments. Fixed units have zero-based indices `0,7,8,9`, or one-based labels
`1,8,9,10`. The potential outcome schedule is the vector
`(1,2,2,2,2,3,2,3,2,1)` for **every** binary assignment. The observed treated
index is `6` (unit 7). Row `r : Fin 6` treats index `r+1`, so the six conditional
assignments treat units 2 through 7. Their image is `tableOmega`.

The four fixed outcomes, in the order just given, form `y=(1,3,2,1)`.
The six distance rows to the nearest treated nonfixed unit are

```
(1,6,7,8) (2,5,6,7) (3,4,5,6)
(4,3,4,5) (5,2,3,4) (6,1,2,3).
```

Midranks, centered ranks, cross products, square sums, Spearman correlation,
uniform probability, conditioning, no effects, and no interference mean the
explicit finite formulas in the T1 section. In addition, for any assignment
`z`, the actual statistic is `g((Y(i,z))_{i fixed},z)`, where `g` correlates
the distances at fixed units with its four supplied outcome values. The
reference statistic at observation `obs` and reference assignment `z` instead
uses `g((Y(i,obs))_{i fixed},z)`. Thus outcomes are held at the observation
while distances are recomputed. `p_L(z)` counts reference statistics less than
or equal to the actual statistic at `z`, over `tableOmega`; `p_U(z)` reverses
that inclusive comparison.

Unfolding all conjuncts gives:

* The outcome schedule is invariant under all binary assignments, and no effects
  and no interference hold on `tenOmega`.
* There are ten unconditional and six conditional assignments. Filtering at
  the observed fixed treatments gives exactly `tableOmega`. The conditioning
  event has probability `3/5`; each unconditional singleton has probability
  `1/10`; each conditional singleton has probability `1/6`; each conditional
  singleton probability equals its unconditional probability divided by `3/5`.
  Every unconditional assignment treats exactly one unit.
* The fixed outcomes and all six distances equal the displayed vectors. Each
  row has a treated nonfixed unit and strictly positive distance rank square
  sum. The outcome rank square sum is `9/2`.
* The six correlations equal
  `(-1/sqrt(90),-1/sqrt(90),-1/sqrt(90),-5/6,-3/sqrt(10),-3/sqrt(10))`.
  The three distinct values have strict order
  `-3/sqrt(10)<-5/6<-1/sqrt(90)<0`; every row is negative; the respective
  displayed approximations `-0.949,-0.833,-0.105` have error less than `0.0005`.
* Outcome midranks and centered ranks are `(3/2,4,3,3/2)` and
  `(-1,3/2,1/2,-1)`. Distance midranks are `(1,2,3,4)` for rows 0,1,2,
  `(5/2,1,5/2,4)` for row 3, and `(4,1,2,3)` for rows 4,5. Subtracting
  `5/2` gives, respectively, `(-3/2,-1/2,1/2,3/2)`, `(0,-3/2,0,3/2)`,
  and `(3/2,-3/2,-1/2,1/2)`.
  The cross products are `(-1/2,-1/2,-1/2,-15/4,-9/2,-9/2)`, the distance
  square sums are `(5,5,5,9/2,5,5)`, and the squared correlations are
  `(1/90,1/90,1/90,25/36,9/10,9/10)`, with `1/90<25/36<9/10`.
* For each row the actual statistic equals the row correlation; for all row
  pairs the observed-data reference statistic equals the reference row's
  correlation. More strongly, the fixed outcomes equal `y` at **every** binary
  assignment, and the reference statistic equals the actual statistic for
  **all** `obs,z : Assignment 10`.
* The row lower tails, both by direct row counting and actual reference
  statistics on `tableOmega`, are `(1,1,1,1/2,1/3,1/3)`. The inclusive upper
  tails are `(1/2,1/2,1/2,2/3,1,1)`. The image of the six actual statistics
  has cardinality exactly three (ties do not discard assignments in tails).
* For every real `alpha` with `0<alpha≤2/3`, printed rejection probability
  is `1/2` and corrected rejection probability is zero. For every such alpha
  and every row, printed rejection is equivalent both to its lower tail being
  `1` and to `r.val<3`, and corrected rejection fails. For every real
  `0<alpha<1/2`, printed rejection probability strictly exceeds alpha.
  The numeric inequality `1/20<1/2` is also asserted.

The docstring describes precisely these finite population and numeric clauses.

Junk-value audit: finite minima use a fallback of 0 on an empty treated set;
Spearman uses total real division and square root. The six conditional rows
explicitly have nonempty treated sets and positive square sums, and have
nonzero Spearman denominators. The universal equality of reference and actual
statistics for **all** binary assignments also covers assignments outside the
randomization support, including the all-false assignment: there, distances
can use the fallback and correlations can use `0/0=0`. That equality is an
equality of total extensions; the six-row probability calculation never uses
these extensions. Uniform supports have sizes ten or six, conditioning mass
is `3/5`, and fixed numeric square roots have positive arguments 90 and 10.
All other fractions have positive denominators; decimals are exact reals
specified by decimal notation. No out-of-range indexing, truncated subtraction,
infinite extrema, integral, or limit is involved.

## SAP.P030.T3

This is a universal finite-law theorem conjoined with **all** of the concrete
T1 statement above. For any type `A` (universe polymorphic), a `FiniteLaw A`
consists of a finite set `E : Finset A`, a real-valued mass function `m : A→ℝ`,
proof that `m(z)≥0` for `z∈E`, and proof `Σ_{z∈E} m(z)=1`. Its probability
of `P` is the finite sum `Σ_{z∈E} (if P(z) then m(z) else 0)`. Values of the
mass function outside `E` are ignored, and zero masses inside `E` are allowed.
Given **any** such law and **any** function `f : A→ℝ`, put
`L(x)=Σ_{z∈E, f(z)≤x}m(z)` and `U(x)=Σ_{z∈E, x≤f(z)}m(z)`.
The quantifier order is `∀ A, ∀ μ, ∀ f`, then the following conjunction:

* For every real `x`, `U(x)=1-L(x)+P(f=x)` and `1-L(x)≤U(x)`.
* For every real `u`, if `0≤u≤1`, both `P(L(f(z))≤u)≤u` and
  `P(U(f(z))≤u)≤u`.
* For every real `alpha`, if `0<alpha<1`, all the following hold:
  the probability of `L(f(z))<alpha/2 OR U(f(z))<alpha/2` is at most
  `P(L(f(z))≤alpha/2)+P(U(f(z))≤alpha/2)`; that sum is at most alpha;
  the rejection probability is at most alpha; for every real `x`,
  `U(x)<alpha/2` implies `1-alpha/2<L(x)`; for every real `x`, corrected
  rejection implies printed rejection `L(x)<alpha/2 OR 1-alpha/2<L(x)`.
* For every pair of **arbitrary real numbers** `pL,pU`, still within the
  alpha quantifier, `min(1,2 min(pL,pU))≤alpha` if and only if
  `pL≤alpha/2 OR pU≤alpha/2`. The probability that this conventional
  two-tailed value evaluated at `(L(f(z)),U(f(z)))` is at most alpha is
  at most alpha.

The final T1 conjunct supplies a genuine strict-inclusion example: the printed
rule rejects every assignment of that experiment and the corrected rule
rejects none for `0<alpha<1`. T3 has no hypothesis demanding a continuous law,
no no-interference hypothesis, and no generic imputation theorem in its type.
It applies to any finite probability law and real statistic.

Junk-value audit: nonnegativity and total mass one force `E` to be nonempty
and `A` to be inhabited; no `FiniteLaw` exists on an empty type. Empty tail
events give empty sums, correctly zero. Finite sums require no integrability
or `toReal` convention, and no probability division occurs in this general
part. The only division is by 2. Arbitrary off-support masses, even negative,
have no effect. `min` on real numbers has its ordinary order meaning.
All T1 distance, square-root, and division checks are as in the T1 section:
they have nonzero denominators and nonempty sets. There is no infinite-support
or asymptotic assertion in this statement.

## SAP.P030.T4

The theorem asserts the **negation** of the following universal proposition,
called `PrintedTwoTailedExactness`. The quantifiers, in order, are:

1. For every natural `N`, every finite set `Omega` of functions `Fin N→Bool`,
   every fixed indicator `S : Fin N→Bool`, and every observation assignment
   `a : Fin N→Bool`, assume the filtered support
   `E={z∈Omega : ∀ i, S(i)=true → z(i)=a(i)}` is nonempty.
2. For every potential outcome schedule `Y : Fin N → (Fin N→Bool) → ℝ`
   and every real statistic function
   `g : (({i : Fin N // S(i)=true}→ℝ) → (Fin N→Bool) → ℝ)`, assume
   `∀ i, ∀ z∈Omega, ∀ z'∈Omega, z(i)=z'(i) → Y(i,z)=Y(i,z')`.
3. For every real `alpha`, assume `0≤alpha≤1`. Define the actual statistic
   `t(z)=g((Y(i,z))_{i fixed},z)` and the reference statistic
   `t_ref(z,w)=g((Y(i,z))_{i fixed},w)`. Then the claimed bound is
   `#{z∈E : p(z)<alpha/2 OR 1-alpha/2<p(z)}/|E| ≤ alpha`, where
   `p(z)=#{w∈E : t_ref(z,w)≤t(z)}/|E|`.

T4 denies that universal bound. Classically this supplies some finite design,
nonempty conditional support, no-interference outcome schedule, statistic,
and alpha in `[0,1]` for which that exact displayed bound fails. It does not
state that an inclusive lower tail alone is invalid, or negate validity of a
rule based on two separately computed inclusive tails. It does not itself
identify a particular witness.

The Challenge docstring explicitly says “The printed claim is false” and says
the printed two-tailed rule fails universal conditional Type I control. At this
blind stage I record that description without comparing it to any source claim.

Junk-value audit: the two cardinality divisions have the **same explicitly
nonempty** support; thus neither uses `0/0`. An empty fixed-unit subtype and
`N=0` are allowed by the universal definition, but there is then an ordinary
unique empty outcome vector, and `g` still has a well-defined real output.
The observation need not be in `Omega`, although agreement defines the same
nonempty event for some assignments in `Omega`. No minima, square roots,
integrals, infinite extrema, logarithms, or partial functions occur in this
closure. The strict rejection inequalities and alpha endpoints are literal.

## SAP.P030.T5

This is an unconditional conjunction using the ten-unit positions, assignment
functions, fixed indices, null potential outcomes, distance statistic, uniform
counting probabilities, and all table numeric definitions spelled out in the
T2 section. Those descriptions are part of this section's unfolding as well.
There are no extra inputs or design hypotheses to instantiate.

In full, it asserts:

* For every unit and **all** binary assignments, `tenYnull` is unchanged.
  No effects and no interference hold on the ten-assignment support.
* Every clause of `TableDesign` holds: sizes ten and six, the exact conditional
  set, conditioning probability `3/5`, one treated unit per assignment,
  unconditional masses `1/10`, conditional masses `1/6`, and their ratio
  formula.
* Every clause of `TableNumerics` holds: fixed outcomes `(1,3,2,1)`, all six
  distance rows, the six exact Spearman values, nonempty treated sets, positive
  distance square sums and outcome square sum `9/2`, the three strict value
  comparisons and negativity, and the three error bounds below `0.0005`.
* The corrected fixed-outcome null says
  `∀ fixed i, ∀ z∈tableOmega, ∀ z'∈tableOmega, Y(i,z)=Y(i,z')`.
  This holds. The assignments treating units 2 and 5 belong to `tableOmega`,
  but their **actual** statistics differ. Thus this is outcome constancy
  together with statistic nonconstancy, with actual assignment witnesses.
* For all six rows, the actual statistic equals its table correlation.
  The row-count inclusive lower tail at row 5 is `1/3`.
* For every type `A` (at the theorem's universe), every finite `E : Finset A`,
  if `E` is nonempty, then for every `t : A→ℝ`, if
  `∀ z∈E, ∀ z'∈E, t(z)=t(z')`, then for **every** `z∈E`,
  `#{w∈E : t(w)≤t(z)}/|E|=1`.
* All clauses of `TableRankDetails` hold: the exact outcome and distance
  midranks, centered ranks, cross products, square sums, rational squared
  correlations and their strict comparisons given in the T2 section.
* All clauses of `NullReferenceDetails` hold: the fixed outcomes equal the
  table vector at every binary assignment; for every `obs,z` the imputed
  reference statistic equals the actual statistic; the six actual lower
  and upper tails are the same inclusive vectors as in T2; and the image
  of the actual six conditional statistics has cardinality three.
* The actual observed-data inclusive lower tail for treatment at unit 7
  (index 6, row 5) is `1/3`, and `|1/3-0.333|<0.0005`.
* Finally, with exactly the same order of quantifiers and constancy hypotheses
  as the generic finite-support assertion above, for every `z∈E`,
  `#{w∈E : t(w)=t(z)}/|E|=1`. This is the point mass at the observed statistic
  mentioned in the docstring.

The two universal constancy assertions require the observed point to belong
to the support. No rule is asserted for an unrelated observed value. A
finite-support statistic may be otherwise arbitrary outside that support.

Junk-value audit: as in T2, all six correlations have positive rank variances,
all reference supports have positive cardinality, and all treated sets used
in them are nonempty. The generic point-mass/p-value conclusions explicitly
require a nonempty support. The equality of imputed and actual statistics at
all binary assignments includes the total extensions outside the experiment
(nearest-distance fallback 0 and zero-denominator correlation 0), but the
nonconstant witnesses, exact image cardinality, and observed p-value all lie
inside the genuine six-assignment support and avoid them. Midrank denominators
are 2, the conditioning ratio has denominator `3/5`, fixed square roots have
positive arguments, casts are exact, and every fixed-unit/index proof is
in range. No infinite extremum, integral, partial-function default, logarithm,
truncated subtraction, or asymptotic limit occurs.
