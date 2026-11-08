# Blind reading

Saved before opening `claims.json`, `record.json`, `earlier.json`, or
`architect-report.md`. Sources: all entries in `closure.json`, the five
Challenge docstrings, and their defining source declarations. Generated
auxiliaries were also inspected with `scratch/PrintClosure.lean`.

## Common mathematical dictionary (used, fully expanded, in the sections below)

All unit indices are elements of `Fin n`, i.e. integers 0 through n-1.
`TreatmentVector n` is the entire Boolean cube {false,true}^n. Write z_i as
the real number 0 or 1 when used in arithmetic; this is `treatmentValue`.
An experiment E consists of arbitrary real functions y_i on this cube and a
function p from the cube to nonnegative real numbers satisfying sum_z p(z)=1.
There is no separate measure or measurability structure: this is a finite
probability model. For any real function f and event A on the cube, write

* E_p f = sum_z p(z) f(z), P_p(A)=sum_z p(z) 1_A(z);
* M_A(f)=E_p(1_A f)/P_p(A);
* Cov_p(f,g)=E_p[(f-E_p f)(g-E_p g)], Var_p(f)=Cov_p(f,f);
* Cov_A(f,g)=M_A[(f-M_A f)(g-M_A g)].

These expand `expectation`, `probability`, `conditionalMean`, `covariance`,
`variance`, and `conditionalCovariance`. All sums use the complete finite
index type. Let p_i(a)=P_p(z_i=a), the definition of `armProbability`, and
p_i=p_i(true). `Function.update z i a` replaces exactly coordinate i. Put
y_i(a;z)=y_i(z[i:=a]) (`potentialResponse`) and
tau_i(z)=y_i(true;z)-y_i(false;z) (`individualEffect`).

Define I(i,j) to mean i=j OR there exist two full-cube assignments differing
only possibly at i with unequal y_j values. Thus the first index is the
treatment source and the second the outcome receiver; the diagonal is forced
even for constant outcomes. This is `Affects`. Set H_ij=1 if I(i,j), and 0
otherwise (`interferenceIndicator`). Define D_ij=1 if there exists an index l
with I(l,i) AND I(l,j), and 0 otherwise (`SharesCause`,
`dependenceIndicator`). Set

    d_i = sum_j D_ij,
    d = (sum_i d_i)/n,
    c_i = sum_j H_ij,
    c = (sum_i c_i)/n.

These are `dependenceDegree`, `averageDependence`, `outgoingCount`, and
`averageOutgoing`. For n>0, 1<=c<=d<=n since self-interference is included.

`ProductDesign E` means (i) every p_i is strictly between 0 and 1, AND
(ii) for EVERY full-cube z, p(z)=product_i [p_i if z_i=true, else 1-p_i].
It therefore means independent nondegenerate Bernoulli coordinates, not just
specified marginals. It gives full support and positive joint probabilities
for any distinct pair's assignments.

`Regularity E k q s`, where k,q,s are REAL numbers, is exactly:

    k>0, q>=2, s>=1;
    for every i, 1/k <= p_i <= 1-1/k;
    for every i, E_p |y_i(z)|^q <= k^q;
    for every i and Boolean a, E_p |y_i(a;z)|^s <= k^s.

Powers here are `Real.rpow`. `SequenceRegularity` uses the SAME k,q,s at
every index of the sequence; it does not choose them separately at each size.

The quantities in the bias statements expand to the following finite sums:

    T = (sum_i (E_p tau_i)^2)/n                 (`meanSquaredEffect`),
    xi_ij(a) = E_p[y_i(z[i:=a][j:=true])-y_i(z[i:=a][j:=false])],
    xibar_ij = (1-p_i) xi_ij(true) + p_i xi_ij(false),
    ybar_i = (1-p_i) M_{z_i=true}(y_i) + p_i M_{z_i=false}(y_i),
    B1 = (1/(n*d)) sum_{i,j, j!=i}
           [xibar_ij*xibar_ji + 2*ybar_j*(xi_ij(true)-xi_ij(false))],
    B2 = (1/(n*d)) sum_{i,j, j!=i} sum_{a,b in {false,true}}
           (1-2a)(1-2b) Cov_{z_i=a AND z_j=b}(y_i,y_j).

Here a,b in arithmetic denote their real Boolean values. These respectively
expand `expectedSpillover`, `weightedSpillover`, `weightedOutcome`,
`directBias`, and `indirectBias`. The receiver is the FIRST index of xi,
which reverses the orientation of I. Updates are in the displayed order;
the theorems use off-diagonal pairs where needed. T is the mean of the
SQUARES OF EXPECTED individual effects, not the mean expected squared
individual effect. This distinction is retained in all sections.

An `ExperimentSequence` S has N:Natural->Natural with N(t)>0 at EVERY t,
N(t)->infinity, and an experiment E_t on `Fin (N t)` for every t. Its
`sampleSize` is the exact real cast n_t=N(t). `SparseDependence` means
d_t/n_t->0. All sequence limits are as natural t->infinity (`Filter.atTop`);
a real limit is `Filter.Tendsto ... (nhds ...)`. An eventual assertion means
there exists a natural threshold after which it holds. `vanishingRelativeTo
f g` means f_t/g_t->0. `boundedRelativeTo f g` means there exists a REAL C>0
such that eventually |f_t|<=C|g_t|.

`fairDistribution n` is p(z)=1/2^n for EVERY z, including when n=0;
`fairPopulation n y` combines this law with the given y.
`cancellingPopulation` is n=3 under this law, with

    y_1(z)=z_0(2z_2-1), and y_0(z)=y_2(z)=0.

Subscripts here are Lean's zero-based indices. `identityPopulation n` uses
this law and y_i(z)=z_i. `sparseSequence` has N(t)=t+1 and outcomes z_0 for
unit 0 and zero elsewhere; `identitySequence` keeps only its N, positivity,
and growth proofs and replaces all outcomes by identity outcomes. Thus the
identity sequence has E_t=`identityPopulation (t+1)`; its outcomes are NOT
those of the sparse sequence.

## SAP.P009a.T11

The theorem is exactly the NEGATION of this ordered universal statement:
for every S:ExperimentSequence, then every real k,q,s, if (1) uniform
regularity as expanded above holds, (2) q>=4, (3) each E_t has independent
nondegenerate Bernoulli assignment, (4) d_t/n_t->0, and (5) d_t/c_t->infinity,
then eventually BOTH |T_t/d_t|<=|B2_t| AND |B1_t|<=|B2_t|.

Equivalently there exist S,k,q,s satisfying ALL five hypotheses, with
arbitrarily late indices where at least one comparison fails. There is no
assertion of a named witness, of B2 being identically zero, of a formula for
B1, or of failure at every index. All quantities T,B1,B2,d,c and all their
constituents are precisely the finite-cube formulas in the dictionary.

The docstring says this defeats only the eventual-largest-absolute-value
reading of dominance, and expressly discloses omission of the square-size
block witness, its formulas, and its extension to all n>=4. It expressly
preserves the printed big-O bounds and Proposition 7.

Junk-value audit: real division/inversion gives zero at denominator zero.
Here n_t>0 and d_t,c_t>=1. Regularity gives positive single-arm probabilities;
ProductDesign gives positive two-arm events for distinct i,j. B2 skips the
diagonal, so inconsistent same-coordinate arm events are never evaluated in
its summands. Thus all conditional means used have ordinary meaning. The
rpow bases |y| and k are nonnegative and positive respectively, with q>=4,
s>=1; zero-to-positive-power is zero. No other real-power domain is used.
The natural-to-real casts are exact. No empty unit indices occur along S;
an off-diagonal sum may be empty at n=1, in which case zero is the correct
sum. There are no suprema, infima, logs, roots, integrals, extended-real
conversions, limsup/liminf, natural subtractions, or partial functions in
this statement's mathematical closure. Constructor/projection auxiliaries
add no assumptions: the printed generated proofs here certify natural
numerals are at least two.

## SAP.P009a.T12

This theorem is a conjunction of THREE statements, with fresh quantifiers
in each part.

1. For every natural n>0, experiment E on its Boolean cube, and real k,q,s,
   if Regularity E k q s, q>=4, and ProductDesign E, then ALL of:

       |B1| <= 12 k^4 (c-1)/d,
       |B2| <= 4 k^4 (d-1)/d,
       4 k^4 (d-1)/d <= 4 k^4,
       0 <= T <= 4 k^4.

2. For every S and real k,q,s, if SequenceRegularity S k q s, q>=4,
   ProductDesign E_t for every t, and d_t/c_t->infinity, then ALL of:

       T_t/d_t -> 0;
       B1_t -> 0;
       there exists C>0 such that eventually |B2_t|<=C;
       IF eventually B2_t!=0 AND c_t/(d_t |B2_t|)->0, THEN
         1/(d_t |B2_t|)->0,
         (T_t/d_t)/|B2_t|->0,
         B1_t/|B2_t|->0;
       for EVERY real c0>0, IF eventually c0<=|B2_t|, THEN
         eventually B2_t!=0,
         c_t/(d_t |B2_t|)->0,
         and the same three limits just listed hold.

   The three final limits expand `WholeBiasDominance` completely. There is
   NO SparseDependence hypothesis in this universal part.

3. There EXISTS S such that uniform Regularity with (k,q,s)=(2,4,1),
   ProductDesign at every t, d_t/n_t->0, and d_t/c_t->infinity all hold,
   AND for EVERY t, B2_t=0, B1_t>0, and T_t/d_t>0.

All quantities use the full finite-sum definitions in the dictionary.
No named witness or exact witness formulas occur. The docstring describes
finite bounds, the unconditional limits and boundedness, a zero-B2 witness,
and sufficient extra conditions for relative dominance.

Junk-value audit: all n,d,c and conditional-mean denominators in the first
two universal antecedent domains are positive, for the same reasons as T11.
The quotient involving |B2| would be defined as zero at B2=0, but the
dominance implication explicitly requires eventual nonzero B2; its lower-
bound alternative implies that requirement. Finitely many exceptional
initial denominators do not change limits. The existential part never uses
B2 as a divisor. Boundedness is eventual, with a positive constant.
Subtractions c-1 and d-1 are REAL, not truncated natural subtraction.
Powers k^4 are natural powers; the moment powers are rpow on the valid
domain described above. No infinity conversion, integral, log, root,
supremum/infimum, limsup/liminf, or partial function is present. Generated
proof declarations certify numeral typeclass facts only.

## SAP.P009a.T13

The theorem asserts ALL of the following about the SPECIFIED experiment
C=`cancellingPopulation` (n=3, p(z)=1/8, y_1=z_0(2z_2-1), others zero):

* ProductDesign C; p(z)=1/8 for every z; the complete outcome formula for
  every unit i and every z; |y_i(z)|<=1 for every i,z.
* For EVERY real q,s, q>=2 and s>=1 imply Regularity C 2 q s.
* `WholeRegularity C 2 top top`: k=2>0, top>=2, top>=1,
  1/2<=p_i<=1-1/2 for every i, and for every positive-mass assignment z,
  |y_i(z)|<=2 and |y_i(a;z)|<=2 for each i,a.
* For EVERY Boolean a and EVERY full-cube z, changing z_0 from false to
  true while setting z_1=a changes y_1 by 2z_2-1; this quantity is -1 OR 1,
  and is nonzero.
* I(0,1), xi_10(false)=0, xi_10(true)=0, xibar_10=0.
* It is NOT the case that for every natural n and experiment E,
  ProductDesign E AND Regularity E 2 4 1 imply, for every i,j with i!=j,
  I(i,j) -> xibar_ji!=0.

The receiver/source reversal in the last formula is intentional. This is
an explicit refutation of the nonzero-expected-weighted-spillover implication
for a regular independent Bernoulli experiment. The docstring calls it a
refutation of the printed assertion itself; that attribution remains to be
checked after the blind stage.

`ExtendedOrder` is `WithTop Real`: finite real orders plus a greatest
element top. `OrderBound p X k q` at q=top is |X(z)|<=k for every z of
positive p-mass. At finite q it is E_p |X|^r<=k^r where r is the real
coordinate of q (`untopD 0`). `WholeRegularity` uses this OrderBound for
observed and forced-coordinate outcomes, with the SAME marginal bounds
as Regularity. Thus it expresses essential boundedness at the top endpoint;
fair full support here makes that ordinary full-cube boundedness.

Junk-value audit: n=3, p_i=1/2, p(z)=1/8 are all nonzero. Expectations
are finite sums and xi has no conditional mean. Weighted spillovers use
only ordinary p_i. All finite rpow exponents satisfy q>=2,s>=1 with
nonnegative bases and positive k. At top, `untopD 0` is NOT used: the
top branch gives the boundedness assertion directly. Indices 0,1,2 are
literal `Fin 3` elements; the generated `NeZero 3` proof ensures those
numerals do not conceal an empty type. No infinity-to-real conversion,
supremum/infimum, unbounded limit, root, log, integral, truncated subtraction,
or partial function appears. The negated universal's n=0 cases have empty
unit quantifiers, but the concrete n=3 witness makes the refutation
nonempty and substantive.

## SAP.P009a.T14

`T14WholeStatement` is precisely `T14Statement`, a conjunction of FOUR
separately quantified assertions:

1. For every natural n, experiment E, and i,j in Fin n with i!=j and
   NOT I(i,j): for EVERY Boolean a and assignment z,
   y_j(z[j:=a][i:=true])=y_j(z[j:=a][i:=false]); ALSO
   xi_ji(false)=xi_ji(true)=xibar_ji=0.
2. For every natural n>0 and experiment E, if `NoSpillovers E`, meaning
   for every i,z,z' equality z_i=z'_i implies y_i(z)=y_i(z'), and if for
   every i both p_i(true)>0 and p_i(false)>0, then for every distinct i,j
   xi_ij(false)=xi_ij(true)=0, AND B1=0.
3. In C (the explicit n=3 fair cancellation experiment, formula as above),
   I(0,1) AND xibar_10=0.
4. For every natural n, experiment E, and distinct i,j,
   xibar_ji!=0 -> I(i,j).

The I, xi, xibar, B1 and other components expand exactly to the dictionary's
finite events, coordinate updates and sums. There is no independence,
moment, or support hypothesis in parts 1 and 4. Part 2 imposes positivity
of conditional-mean events, but no independence. The docstring's converse
failure refers to the implication from interference to nonzero weighted
spillover, falsified by part 3.

Junk-value audit: xi is a finite unconditional expectation and xibar has
no divisions. Therefore parts 1,3,4 do not depend on choices of a
conditional expectation at zero-mass events. B1 in part 2 uses positive
single-arm probabilities, n>0, and d>=1; no undefined conditional mean
or normalization occurs. The off-diagonal requirement handles distinct
coordinate updates and excludes forced diagonal interference. `NoSpillovers`
requires invariance on the FULL cube, including zero-mass assignments.
When n=0, the unit-quantified portions of 1 and 4 are empty, but n=3 is
an explicit nonempty instance and part 2 requires n>0. No rpow, extended
order, supremum, limsup/liminf, integral, log, root, truncated natural
subtraction, or partial function affects this statement. The numeral
auxiliaries specify natural numerals and `Fin 3` literals only.

## SAP.P009a.T15

This theorem conjoins `T15Statement`, a universal finite identity-family
calculation, and a concrete n=4 calculation. In all cases the experiment
has independent fair Boolean assignments and y_i=z_i.

First, for S=`identitySequence`, N(t)=t+1:

* SequenceRegularity S 2 4 1 AND `MaximalOrders S top top`.
* For EVERY t, ProductDesign E_t, NoSpillovers E_t, d_t=1.
* d_t/n_t->0; externalMixing(E_t,1)/n_t->0;
  internalMixing(E_t,1)/n_t->0.
* For EVERY t, 4 sum_{i,j} Cov_p(z_i,z_j)=n_t,
  4 sum_{i,j,j!=i} alpha(z_i,z_j)=0, AND n_t>0.

Here the remaining definitions unfold as follows. For functions X,Y on a
finite probability space,

    alpha_p(X,Y) = sup { |P_p(X in A AND Y in B)
                           -P_p(X in A)P_p(Y in B)| : sets A,B }.

This is `mixingCoefficient`, a REAL supremum. Let R_i(z) be the complete
Boolean vector with entry z_j if I(j,i), else false (`relevantTreatments`).
Let Rminus_i(z)=R_i(z)[i:=false] (`relevantOtherTreatments`). Define
m(a,theta)=0 if a=0, else `Real.rpow a theta` (`mixingPower`). Then

    externalMixing(E,theta) = (1/n) sum_{i,j}(1-D_ij)
                                 m(alpha_p(R_i,R_j),theta),
    internalMixing(E,theta) = sum_i m(alpha_p(z_i,Rminus_i),theta).

`ObservedOrderAdmissible S q` means q>=2 AND there exists a SINGLE real
k>0 such that for every t,i, OrderBound(p_t,y_i,k,q).
`PotentialOrderAdmissible S s` means s>=1 AND there exists a SINGLE k>0
such that for every t,i,a, OrderBound(p_t,y_i(a;.),k,s).
`MaximalOrders S q s` asserts both admissibilities AND that every admissible
observed order r satisfies r<=q AND every admissible potential order r
satisfies r<=s. At q=s=top the upper-bound clauses follow from top being
greatest, but admissibility still requires uniform essential boundedness.
OrderBound, including its top branch, is expanded in the T13 section.

Second, for EVERY natural n>0, for E=`identityPopulation n`, ALL of:

* ProductDesign E; NoSpillovers E; for EVERY real q>=2,s>=1,
  Regularity E 2 q s;
* for EVERY i,j, H_ij=D_ij=1 if i=j, else 0; d=1;
* for EVERY REAL theta, externalMixing(E,theta)=internalMixing(E,theta)=0;
* for EVERY i,j, Cov_p(z_i,z_j)=A_ij=alpha_p(z_i,z_j)=1/4 if i=j,
  else 0, where A_ij=P_p(z_i=true AND z_j=true)-p_i p_j
  (`assignmentCovariance`);
* F(E)=1/n, G(E)=0, and NOT F(E)<=G(E), where

      F(E)=4/n^2 sum_{i,j} A_ij                 (`fullAssignmentSum`),
      G(E)=4/n^2 sum_{i,j,j!=i} alpha_p(z_i,z_j) (`offDiagonalMixingSum`);

* Var_p[(sum_i 1_{z_i=true}/p_i(true))/n]=1/n. The numerator is
  `estimatedArmSize E true`; both it and the variance are finite formulas.

Third, at n=4, F(E)=1/4, G(E)=0, and NOT (1/4<=0).

The docstring attributes this to a false bound that omitted diagonal terms,
and asserts the example satisfies regularity and the three asymptotic
restrictions. The statement actually gives every positive size, not just
the displayed n=4 example.

Junk-value audit: the set whose real supremum defines alpha is nonempty
(empty events give 0) and bounded (indeed alpha<=1/4 for probabilities),
so `sSup` is an ordinary finite supremum. The domains may be presented as
arbitrary codomain types and arbitrary sets, but every pullback is an event
on the finite sample space. No nonmeasurable expectation is being used.
The explicit m(0,theta)=0 convention is substantive: in particular this
sets zero-mixing to exponent zero to ZERO rather than Real.rpow 0 0=1,
and also defines zero mixing at negative theta as zero. The theorem
quantifies over every real theta; both mixing averages still vanish since
all relevant nondependent/internal alpha entries are exactly zero. Nonzero
mixing bases are positive, so rpow has its ordinary real-exponent meaning.
All divisions are safe: n>=1, p_i=1/2, and 2^n>0. Covariances, arm sizes,
and moments are finite sums, hence integrable in the finite model. top in
MaximalOrders uses boundedness, not `untopD 0`; at finite admissible order
the untop fallback is unused and exponents are >=2 or >=1. Natural casts
are exact; t+1 avoids n=0. Off-diagonal sums can be empty at n=1 and then
are correctly zero, while F(E)=1 remains positive. The definition named
sparseSequence supplies only the size sequence and its proofs, with its
outcomes overwritten. No natural truncated subtraction, log, square root,
Bochner integral, infinity-to-real map, limsup/liminf, or partial function
is used. All generated proof dependencies were printed: they are numeral
instances, positivity and normalization of the fair distribution, and
the facts t+1>0 and t+1 tends to infinity, not extra hypotheses.
