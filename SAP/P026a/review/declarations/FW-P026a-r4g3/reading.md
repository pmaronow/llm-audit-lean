# Blind statement reading

Saved before opening `claims.json` or `record.json`. This reading uses only the
Challenge declarations, their dependency closures, and inspection of the three
generated proof declarations with `scratch/Blind.lean`.

## SAP.P026a.T11

Source: `SAP/P026a/Challenge/Part1.lean:136-138`, expanding
`SAP/P026a/Defs/Part15.lean:13-37`.

The docstring describes restored cluster-indicator formulas for exact arm
variance, conservative bounds, unbiased estimation of the bounds, and unbiased
equation [31] when same-arm joint support holds. The statement is a conjunction
of three separately universally quantified propositions.

### Objects and all underlying definitions

In each proposition, U and C are arbitrary finite types with decidable equality
and an inhabitant each. E consists of a map c: U -> C, a proof that c is
surjective, and a probability law on the finite set W = {w: C -> Bool}. Thus the
clusters are the nonempty fibers of c. The law consists of real weights p(w)
such that p(w) >= 0 for every w, sum_w p(w) = 1, and for every cluster k both
sum_w p(w) 1{w(k)=true} > 0 and sum_w p(w) 1{w(k)=false} > 0. There is no
independence requirement, no fixed treatment count, and no requirement that each
allocation have positive weight.

Here is a complete expansion of the SAP notation used in the statement. All
sums are finite Mathlib `Finset.univ` sums; a sum over k != l means
sum_k sum_{l in univ.erase k}, hence ordered pairs, with no diagonal.

* `AssignmentDesign` is just a pair of maps (weight, treatment). The constructor
  and its projections impose no conditions themselves. Here
  `UnitLaw.assignmentDesign` and `ClusterLaw.clusterAssignmentDesign` give
  weight p and treatment (w,k) -> w(k). The `ClusterLaw` constructor and its
  cluster, assignment, and totals fields have exactly the meanings just stated.
* Write J_a(w,k) = 1 if w(k)=a, and 0 otherwise. This is `armIndicator`.
  `mean` of f is M(f) = sum_w p(w) f(w).
* `inclusion` is pi_a(k) = M(J_a(-,k)). `jointInclusion` is
  q_ab(k,l) = M(J_a(-,k) J_b(-,l)).
* `disagreementProbability` is sum_w p(w) 1{w(k) != w(l)}.
* `ClusterLaw.totals` sends unit outcomes y: U -> R to
  Y(k) = sum_{u in univ.filter (c(u)=k)} y(u).
* `htSum` is H_a(Y)(w) = sum_k J_a(w,k) Y(k)/pi_a(k).
* `designCovariance` is Cov(f,g) = M(w -> f(w)g(w)) - M(f)M(g), and
  `designVariance` is V(f) = M(w -> f(w)^2) - M(f)^2.
* `orderedOffDiagonalSum` is the ordered sum over k != l described above.
  `unavailablePairSum` of F at arms a,b is
  U_ab(F) = sum_{k != l, q_ab(k,l)=0} F(k,l).
* `armPopulationVariance` is

      A_a(Y) = sum_k pi_a(k)(1-pi_a(k))(Y(k)/pi_a(k))^2
             + sum_{k != l} (q_aa(k,l)-pi_a(k)pi_a(l))
                            (Y(k)/pi_a(k))(Y(l)/pi_a(l)).

* `armPopulationBound` is

      B_a(Y) = sum_k pi_a(k)(1-pi_a(k))(Y(k)/pi_a(k))^2
             + sum_{k != l, q_aa(k,l)>0}
                 (q_aa(k,l)-pi_a(k)pi_a(l))(Y(k)/pi_a(k))(Y(l)/pi_a(l))
             + U_aa((k,l) -> Y(k)^2/2 + Y(l)^2/2).

* For cluster-total vectors X,Z, `response` is r(w,k) = X(k) if w(k)=true,
  and Z(k) otherwise. `zeroAdjustment` is delta(q)=1 if q=0, and 0 otherwise.
  `estimatedPairTerm`, at general arms a,b, is

      P_ab(w,k,l) = J_a(w,k)J_b(w,l)/(q_ab(k,l)+delta(q_ab(k,l)))
                   * (q_ab(k,l)-pi_a(k)pi_b(l))
                   * (r(w,k)/pi_a(k)) * (r(w,l)/pi_b(l)).

* `armVarianceEstimate` is the following random variable (X,Z are suppressed
  on the left):

      S_a(w) = sum_k J_a(w,k)(1-pi_a(k))(r(w,k)/pi_a(k))^2
             + sum_{k != l, q_aa(k,l)>0} P_aa(w,k,l)
             + U_aa((k,l) -> J_a(w,k)r(w,k)^2/(2*pi_a(k))
                             + J_a(w,l)r(w,l)^2/(2*pi_a(l))).

* `fullSupportArmEstimate` is

      F_a(w) = sum_k J_a(w,k)(1-pi_a(k))(r(w,k)/pi_a(k))^2
             + sum_{k != l} J_a(w,k)J_a(w,l)/q_aa(k,l)
                   * (q_aa(k,l)-pi_a(k)pi_a(l))
                   * (r(w,k)/pi_a(k)) * (r(w,l)/pi_a(l)).

The closure also contains `T11Statement._proof_1` and
`repairedBias._proof_1`. Both were printed: each proves the numerical
typeclass fact `(1+1).AtLeastTwo` by `Nat.instAtLeastTwoHAddOfNat 1`.
These are support for the real numeral 2, with no mathematical assumptions or
additional definitions hidden in them. The declaration `repairedBias` itself
is not in the statement closure.

### Quantifiers, hypotheses, and conclusions

1. For every U,C and E as above, then every proof h that
   sum_w p(w)1{w(k)!=w(l)} > 0 for every distinct k,l, then every Boolean arm a
   and every y: U -> R, the conclusion is V(H_a(Y)) = A_a(Y).
2. Independently, for every U,C,E, then such an h, then every Boolean a and
   every pair x,z: U -> R, form cluster totals X,Z and let Y=X if a=true,
   otherwise Y=Z. The conclusion is the conjunction

       B_a(Y) - V(H_a(Y)) = (1/2) U_aa((k,l) -> (Y(k)+Y(l))^2),
       M(S_a) = B_a(Y),
       V(H_a(Y)) <= M(S_a),
       [for all distinct k,l, q_aa(k,l)>0] -> M(S_a) = V(H_a(Y)).

3. Independently, for every U,C,E, then such an h, then every Boolean a,
   every x,z: U -> R, and then a proof that q_aa(k,l)>0 for every distinct
   k,l, the conclusion is M(F_a) = V(H_a(Y)), with Y selected as in (2).

These are variances of unnormalized cluster arm totals. No division by number
of units or number of clusters occurs. The separation hypothesis is present in
all three propositions, including the first exact-variance identity. It does
not assert independence, same-arm support, or directed cross-arm support.
All outcomes are arbitrary real numbers. There is no positivity restriction on
outcomes and no sharp-null requirement.

### Totalization and junk-value audit

Real division in Lean uses 0 inverse = 0. Here pi_true(k) and pi_false(k) are
strictly positive by E's law, so all marginal and twice-marginal denominators
are nonzero. The number 2 is nonzero in R. The denominator q+delta(q) is 1 at
q=0 and q otherwise, so it is always nonzero. Moreover S_a only evaluates its
pair contribution in the branch q_aa>0. The population bound treats the omitted
zero-joint pairs explicitly. Its strict-positive test and its zero-joint test
cover all possibilities because q_aa >= 0 follows from the law.

F_a has literal q_aa denominators without a guard in its definition, so outside
the final proposition's support hypothesis it can use Lean's value for division
by zero. In its sole occurrence in this theorem, the support hypothesis rules
this out on every ordered off-diagonal term; there are no diagonal pair
denominators. Allocation points with p(w)=0 are retained in the finite mean,
but all statistic values are finite real values with valid denominators under
the relevant hypotheses, so there is no undefined product on null points.

The finite sum called `mean` would be a mere weighted sum for a general
`AssignmentDesign`, but every design here comes from a normalized nonnegative
`UnitLaw`; covariance and variance thus have their usual meanings. All types
of units and clusters are nonempty, every cluster fiber is nonempty by
surjectivity, and the allocation type is nonempty. An off-diagonal or unavailable
pair sum can be empty and is then the genuine mathematical empty sum 0.
The single-cluster case makes the separation and same-arm pair hypotheses
vacuous but leaves a real, nontrivial Bernoulli arm-variance assertion.

There is no truncated subtraction, problematic natural/integer cast, integral,
non-integrable mean, infinity-to-real conversion, logarithm, square root,
real power outside its domain, infimum, supremum, limsup/liminf, partial
function, or arbitrary default in this closure. Squares are ordinary integer
powers and all subtraction is real subtraction. Measurability and finiteness
of moments are automatic for these finite real-valued models.

## SAP.P026a.T12

Source: `SAP/P026a/Challenge/Part1.lean:140-142`, expanding
`SAP/P026a/Defs/Part16.lean:13-50`.

The docstring says equations [20]-[24] hold, retaining both intermediate
arm-covariance expansions and terms for unavailable directed pairs. The
statement is a conjunction of five separately universally quantified
propositions; none is an existential claim or a counterexample.

### Objects and all underlying definitions

Each proposition quantifies over an arbitrary finite inhabited type I with
decidable equality and a `UnitLaw` E on W = {w: I -> Bool}. This means real
weights p(w)>=0 summing to 1 and strictly positive treatment and control
marginals for every i. Zero-weight allocations are allowed. There are no
independence, cluster, pair-support, separation, outcome-size, or fixed-count
assumptions.

The `AssignmentDesign` constructor and its weight and treatment projections,
and `UnitLaw` constructor and weight projection, are the underlying data just
described. `UnitLaw.assignmentDesign` has weight p and treatment (w,i)->w(i).
In full finite-sum notation, set

    J_a(w,i) = if w(i)=a then 1 else 0,
    M(f) = sum_w p(w)f(w),
    pi_a(i) = sum_w p(w)J_a(w,i),
    q_ab(i,j) = sum_w p(w)J_a(w,i)J_b(w,j),
    H_a(y)(w) = sum_i J_a(w,i)y(i)/pi_a(i),
    Cov(f,g) = sum_w p(w)f(w)g(w) - (sum_w p(w)f(w))(sum_w p(w)g(w)),
    V(f) = Cov(f,f),
    N = |I|,
    D(x,z)(w) = (H_true(x)(w)-H_false(z)(w))/N.

These respectively expand `armIndicator`, `mean`, `inclusion`,
`jointInclusion`, `htSum`, `designCovariance`, `designVariance`, and
`htContrast`. N in `htContrast` is a natural number coerced to R.
`orderedOffDiagonalSum` always means sum_i sum_{j in univ.erase i}.

The remaining two numerical SAP definitions in the closure are

    A_a(y) = sum_i pi_a(i)(1-pi_a(i))(y(i)/pi_a(i))^2
           + sum_{i != j} (q_aa(i,j)-pi_a(i)pi_a(j))
                          (y(i)/pi_a(i))(y(j)/pi_a(j)),

    K(x,z) = sum_{i,j: q_true,false(i,j) != 0}
                (q_true,false(i,j)-pi_true(i)pi_false(j))
                (x(i)/pi_true(i))(z(j)/pi_false(j))
             - sum_{i,j: q_true,false(i,j)=0} x(i)z(j).

A is `armPopulationVariance`. K is `splitPopulationCovariance`; both of
its sums are over all ordered pairs, including the diagonal. In particular,
q_true,false(i,i)=0, so the second sum includes sum_i x(i)z(i) and also every
unavailable directed off-diagonal pair. No unordered-pair identification or
extra factor of 1/2 is used.

The closure's `T12Statement._proof_1` was printed and is just the typeclass
proof `(1+1).AtLeastTwo` by `Nat.instAtLeastTwoHAddOfNat 1`. It introduces
no data, assumptions, or hidden mathematical claim beyond the numeral 2.

### Quantifiers, hypotheses, and conclusions

1. For all I and E as above and then all x,z: I -> R,

       V(D(x,z)) = [V(H_true(x)) + V(H_false(z))
                    - 2 Cov(H_true(x),H_false(z))]/N^2.

2. Independently, for all I,E, then every Boolean a and every y: I -> R,
   the following three equalities all hold:

       V(H_a(y)) = sum_i sum_j Cov(J_a(-,i),J_a(-,j))
                                  (y(i)/pi_a(i))(y(j)/pi_a(j)),
       V(H_a(y)) = sum_i V(J_a(-,i))(y(i)/pi_a(i))^2
                    + sum_{i != j} Cov(J_a(-,i),J_a(-,j))
                                     (y(i)/pi_a(i))(y(j)/pi_a(j)),
       V(H_a(y)) = A_a(y).

3. Independently, for all I,E, then every ordered pair of Boolean arms a,b,
   then every x,z: I -> R,

       Cov(H_a(x),H_b(z)) = sum_i sum_j (q_ab(i,j)-pi_a(i)pi_b(j))
                                           (x(i)/pi_a(i))(z(j)/pi_b(j)).

4. Independently, for all I,E, then every x,z: I -> R,

       V(D(x,z)) = [A_true(x)+A_false(z)-2 K(x,z)]/N^2.

5. Independently, for all I,E, then every x,z: I -> R,

       Cov(H_true(x),H_false(z)) = K(x,z).

The variables x,z,y are fixed, arbitrary real-valued population vectors, not
functions of the allocation. The law and marginal requirements are bundled
in the universally quantified E rather than written as separate arrows.

### Totalization and junk-value audit

Lean defines division by zero to be zero, but no denominator is zero here.
Every pi_a(i)>0 by the `UnitLaw` fields, for either Boolean arm. I is finite
and nonempty, so N>0, its real cast is positive, and N^2>0. No natural
subtraction appears. `splitPopulationCovariance` divides by marginal
probabilities only, never by a joint probability; its q=0 case is an explicit
algebraic contribution -x(i)z(j), rather than a disguised use of 0/0.
Joint probabilities can vanish, and that case is intentionally covered.

The weighted finite mean is an actual probability expectation for every law
allowed here. Every random variable has a finite real value at each of finitely
many allocations. There are no integrals or integrability defaults. I and W
are nonempty; an off-diagonal sum for a singleton or a sum selected by an
empty predicate is the mathematical empty sum 0. There is no logarithm,
square root, real power outside its domain, `toReal` of infinity, truncated
subtraction, infimum/supremum, limsup/liminf, partial-function default, or
other junk-value convention relevant to this theorem. All powers are ordinary
squares and all differences are in R. The usual finite-space measurability
and moment conditions hold automatically.
