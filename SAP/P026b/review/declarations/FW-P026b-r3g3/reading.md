# Blind reading

This document was written before opening `claims.json` or `record.json`.
I read the Challenge statements/docstrings and every declaration listed in their
`closure.json` entries. `scratch/Blind.lean` also prints the three generated
auxiliary proofs and checks the structure constructors. No claim or architect
decision is used below.

## SAP.P026b.T23

Location: `SAP/P026b/Challenge/Part1.lean:71–74`, expanding
`SAP/P026b/Defs/Part5.lean:72–92`.

### Objects and definitions

A `Design Ω I R` is simply a pair consisting of weights `p : Ω → R` and a
Boolean treatment map `t : Ω → I → Bool`. By itself it imposes no probability
conditions. In the general clause here, `I` is any finite, decidably equal,
nonempty type (in Lean's `Type` universe), the scalar field is the reals, and
the assignment set is the finite set `W = (I → Bool)` of all binary vectors.
The data `E : UnitExperiment I` consist of weights `p : W → ℝ` satisfying:

1. `p(w) ≥ 0` for every `w ∈ W`;
2. `Σ_w p(w) = 1`;
3. for every `i ∈ I`, both `Σ_w p(w) 1{w(i)=true}` and
   `Σ_w p(w) 1{w(i)=false}` are strictly positive.

`E.design` has weight `p(w)` and treatment `t(w,i)=w(i)`.
All sums below are ordinary Mathlib finite sums over the entire indicated
finite type. Write

* `n = |I|`, a natural number, cast to `ℝ` when used in a real expression;
* `B_a(w,i) = 1` when `w(i)=a`, and `0` otherwise;
* `π_a(i) = Σ_w p(w) B_a(w,i)`;
* `H_a(y;w) = Σ_i B_a(w,i) y(i) / π_a(i)`;
* `H(x,z;w) = [H_true(x;w) − H_false(z;w)]/n`;
* `G_a(y,f;w) = Σ_i [B_a(w,i)y(i)/π_a(i)
  − B_a(w,i)f(w,i)/π_a(i) + f(w,i)]`;
* `G(x,z,f;w) = [G_true(x,f;w) − G_false(z,f;w)]/n`.

These respectively unfold `indicator`, `marginal`/`expectation`, `htTotal`,
`ht`, `generalizedTotal`, and `generalized`. The same prediction function
`f` is used in both arms. In particular, its two unweighted population sums
cancel in the generalized contrast; the predictions may depend arbitrarily
on the assignment.

`probabilityDesign D` means that all weights of `D` are nonnegative and their
sum is one. `positiveMarginals D` means the two `π_a(i)` above are positive
for every unit. Neither predicate includes an independence condition.

### Quantifiers and conclusion

The statement is a conjunction of a universally quantified assertion and
concrete facts about a rational-valued example.

First, for every finite decidably equal nonempty `I`, every `UnitExperiment I`
as above, every `x,z : I → ℝ`, every `f : W → I → ℝ`, every pair of real
numbers `b0,b1`, and every assignment `w ∈ W`, all three conclusions hold:

1. With `S_a(w) = Σ_i B_a(w,i)/π_a(i)`,
   `H(b0+b1*x, b0+b1*z;w)
     = (b0/n)[S_true(w)−S_false(w)] + b1 H(x,z;w)`.
2. `H(b0+b1*x, b0+b1*z;w) = b1 H(x,z;w)` if and only if
   `b0=0` or `S_true(w)=S_false(w)`.
3. `G(b0+b1*x, b0+b1*z, (v,i) ↦ b0+b1*f(v,i);w)
     = b1 G(x,z,f;w)`.

The quantifier order is exactly `I`, its three typeclass instances, `E`,
`x`, `z`, `f`, `b0`, `b1`, `w`, followed by the conjunction. There is no
condition on `b1`, no fixed arm count, no balance hypothesis, and no condition
that `p(w)>0` for these identities.

Second, define `asymmetricTwo` on `Ω=Fin 3`, `I=Fin 2`, with rational weight
`1/3` at each point and treatment vectors `(false,false)`, `(false,true)`,
and `(true,true)` at the three successive points. `singleAsymmetric` keeps
these three weights but keeps only the first unit, producing a design on
`Fin 3 × Fin 1` with successive assignments `false,false,true`. Thus its
treatment marginal is `1/3` and its control marginal is `2/3`. The statement
asserts all of:

* this is a probability design with positive marginals;
* assignment point `2` has strictly positive weight;
* for population denominator `1`, `H(1,1;2)=3`;
* `(-1) H(0,0;2)=0`;
* `H(1,1;2) ≠ (-1) H(0,0;2)`.

This is the affine transformation `b0=1,b1=-1` of zero outcomes, at an
actual positive-probability assignment. It is not a claim that HT lacks
scale homogeneity when the intercept is zero.

### Junk values and boundary conventions

* Division in `ℝ` and `ℚ` is total, with `u/0=0`. The abstract `Design`
  definitions permit zero marginals, but every marginal used by this theorem
  is nonzero: positivity is a field of `UnitExperiment` or is asserted and
  true for the explicit design. No denominator divides by a joint
  probability or by an assignment weight.
* The population denominator is exactly `|I|`, and `[Nonempty I]` makes it
  positive. It casts faithfully to `ℝ`. In the witness it is the literal
  positive integer `1` in `ℚ`. There is no natural-number subtraction.
* `I` cannot be empty; `W` is nonempty even without that condition and is
  finite. The concrete finite types are nonempty. There are no empty sums
  serving as population or probability laws.
* Zero assignment weights and assignments with an empty treatment or
  control arm are allowed. HT sums use fixed marginal denominators, not
  random arm sizes, so such assignments cause no undefined means.
* All finite-vector accesses are inside their finite index types, including
  index `2` in `Fin 3` and index `0` in `Fin 2`. The printed auxiliary
  proofs are `NeZero (2+1)` and `NeZero (1+1)`, used for finite numerals;
  there is no out-of-range default selected here.
* There are no integrals, partial functions, `toReal`, logarithms, roots,
  real powers, infima/suprema, or limits. Arbitrary real-valued finite
  functions have all the finite expectations used here.

### Closure coverage

Read: `Design`, `Design.mk`, `Design.weight`, `Design.treatment`;
`UnitExperiment`, `UnitExperiment.mk`, `UnitExperiment.weight`,
`UnitExperiment.design`; `expectation`, `probabilityDesign`, `indicator`,
`marginal`, `positiveMarginals`, `htTotal`, `ht`, `generalizedTotal`,
`generalized`; `asymmetricTwo`, `singleAsymmetric`,
`singleAsymmetric._proof_1`; `T23Statement`, `T23Statement._proof_1`.
The constructors/projections have exactly the fields described above; the
generated proofs only supply finite-numeral instances.

## SAP.P026b.T24

Location: `SAP/P026b/Challenge/Part1.lean:76–80`, expanding
`SAP/P026b/Defs/Part6.lean:12–43`.

### Objects and definitions

A `Design Ω I ℝ` consists of a real weight function `p` and Boolean treatment
map `t`, with no axioms in this raw structure. For finite `Ω,I`, define:

* `B_a(w,i)=1{t(w,i)=a}`;
* `E_p[h]=Σ_w p(w)h(w)` (`expectation`);
* `π_a(i)=Σ_w p(w)B_a(w,i)` (`marginal`);
* `q_ab(i,j)=Σ_w p(w)B_a(w,i)B_b(w,j)` (`joint`);
* `Cov_p(h,k)=Σ_w p(w)h(w)k(w)
    − (Σ_w p(w)h(w))(Σ_w p(w)k(w))` (`covariance`);
* `Var_p(h)=Cov_p(h,h)` (`variance`);
* `Y(x,z;w,i)=x(i)` if `t(w,i)=true`, otherwise `z(i)` (`observed`);
* `H_a(y;w)=Σ_i B_a(w,i)y(i)/π_a(i)` (`htTotal`);
* `H_N(x,z;w)=[H_true(x;w)−H_false(z;w)]/N` (`ht`);
* `G_a(y,f;w)=Σ_i [B_a(w,i)y(i)/π_a(i)
    − B_a(w,i)f(w,i)/π_a(i)+f(w,i)]` (`generalizedTotal`);
* `G_N(x,z,f;w)=[G_true(x,f;w)−G_false(z,f;w)]/N`
  (`generalized`);
* `R_N(x,z,f;w)=[Σ_i B_true(w,i)(Y(x,z;w,i)−f(w,i))/π_true(i)
    − Σ_i B_false(w,i)(Y(x,z;w,i)−f(w,i))/π_false(i)]/N`
  (`residualContrast`).

`offSum k` is the ordered sum `Σ_i Σ_{j∈I, j≠i} k(i,j)`. In particular,
off-diagonal pairs are directed, and both `(i,j)` and `(j,i)` appear.
The three displayed expression definitions expand as follows:

`A_a(y) = Σ_i π_a(i)(1−π_a(i))(y(i)/π_a(i))²
          + Σ_i Σ_{j≠i} [q_aa(i,j)−π_a(i)π_a(j)]
             (y(i)/π_a(i))(y(j)/π_a(j))`

(`armVarianceExpression`),

`S(x,z) = Σ_i Σ_j (if q_true,false(i,j)≠0 then
             [q_true,false(i,j)−π_true(i)π_false(j)]
             (x(i)/π_true(i))(z(j)/π_false(j)) else 0)
          − Σ_i Σ_j (if q_true,false(i,j)=0 then x(i)z(j) else 0)`

(`splitCovarianceExpression`), and

`K(x,z) = Σ_i Σ_{j≠i}
             [q_true,false(i,j)−π_true(i)π_false(j)]
             (x(i)/π_true(i))(z(j)/π_false(j)) − Σ_i x(i)z(i)`

(`clusterCovarianceExpression`). No term in these definitions divides by `q`.

For the first conjunct, `I` is finite, decidably equal, and nonempty.
`UnitExperiment I` is a weight function on all Boolean assignment vectors
`W=I→Bool` with nonnegative weights summing to one and strictly positive
`π_true(i),π_false(i)` for every unit. `E.design` uses those weights and
`t(w,i)=w(i)`.

For the second conjunct, `U,C` are finite, decidably equal, nonempty types.
A `ClusterExperiment U C` consists of a map `c:U→C`, a proof that it is
surjective, and `assignment : UnitExperiment C`. Thus each labeled cluster
has at least one unit, each unit belongs to exactly one cluster, and the
cluster assignment law has positive treatment/control marginals.
`E.clusterDesign` is the assignment design on `W_C=C→Bool`, with weight
`E.assignment.weight` and treatment `w(k)` at cluster `k`.
`E.totals x(k)=Σ_{i∈U, c(i)=k} x(i)` is an actual sum of unit potential
outcomes within that cluster, and likewise for `z`.
Finally `disagreement(k,l)=Σ_w p(w)1{w(k)≠w(l)}`.

### Quantifiers and conclusion

The statement has two independent universal conjuncts.

1. For every `I` and the three instances above, then every `E`, every
   `x,z:I→ℝ`, and every arbitrary assignment-dependent
   `f:W→I→ℝ`, the following conjunction holds, with `n=|I|`:
   * For every assignment `w`,
     `G_n(x,z,f;w)=H_n(x−f(w),z−f(w);w)` and
     `G_n(x,z,f;w)=R_n(x,z,f;w)`.
   * For every deterministic `r:I→ℝ`,
     `Var_p(G_n(x,z,(w,i)↦r(i)))
       = [A_true(x−r)+A_false(z−r)−2 S(x−r,z−r)]/n²`.
   The assignmentwise identities apply even at zero-weight assignments.
   The variance formula concerns fixed predictions only; no such formula
   is asserted for arbitrary random fits.

2. For every `U,C` and their finite/decidable/nonempty instances, then every
   `E:ClusterExperiment U C`, assume
   `∀k,l∈C, k≠l → disagreement(k,l)>0`. For every `x,z:U→ℝ`,
   write `X(k)=Σ_{c(i)=k}x(i)` and `Z(k)=Σ_{c(i)=k}z(i)`. All four
   conclusions hold for the cluster assignment law:
   * For every Boolean arm `a`,
     `Var_p(H_a(if a then X else Z))=A_a(if a then X else Z)`.
   * `Cov_p(H_true(X),H_false(Z))
       =Σ_k Σ_l [q_true,false(k,l)−π_true(k)π_false(l)]
          (X(k)/π_true(k))(Z(l)/π_false(l))`.
   * The same covariance equals `S(X,Z)`.
   * The same covariance equals `K(X,Z)`.

The cluster hypothesis requires each pair of distinct cluster indicators
to differ with positive probability. It does not require every directed
event `{w(k)=true,w(l)=false}` to have positive probability, nor any
independence, equal cluster sizes, equal marginals, or fixed treated count.
The cluster arm quantities are totals, without population normalization.

### Junk values and boundary conventions

* Real division is total with `u/0=0`. All marginal denominators are
  strictly positive by `UnitExperiment` fields, including for every cluster.
  In the generalized variance formula, `n=|I|>0`, so `n²>0` as a real.
  No random arm size is used as a denominator.
* Joint probabilities may be zero. The split expression handles them by
  explicit equality tests, replacing their covariance contribution with
  `−x(i)z(j)`. This uses nonzero marginal denominators; it does not use a
  junk inverse of the joint probability. In the binary setting diagonal
  cross-arm joints are zero. The off-diagonal expression retains every
  other zero-joint term and subtracts the diagonal products explicitly.
* `[Nonempty I]`, `[Nonempty U]`, and `[Nonempty C]` exclude empty
  populations in the respective clauses. Assignment types are nonempty.
  Surjectivity makes each cluster sum a sum over at least one unit.
  If there is just one cluster, the pairwise-disagreement hypothesis is
  empty and `offSum` is the legitimate empty sum `0`; the diagonal
  cross-covariance term remains. This is a valid one-cluster experiment
  with two positive-marginal assignment possibilities, not an empty law.
* Finite-set erasure excludes the diagonal using decidable equality. It
  involves no truncated subtraction of indices or cardinals. Natural
  cardinals are cast to reals; there is no integer coercion or overflow.
* The generated auxiliary proof printed from `T24Statement._proof_1`
  is `(1+1).AtLeastTwo` for the exponent `2`; it supplies no statistical
  hypothesis or conclusion.
* All expectations and covariance/variance definitions are finite real
  sums. There are no nonintegrable integrals, infinite measures, `toReal`,
  logarithms, square roots, real powers, infima/suprema, limits, partial
  functions, or defaults in these formulas.

### Closure coverage

Read: `ClusterExperiment`, `ClusterExperiment.mk`, `ClusterExperiment.cluster`,
`ClusterExperiment.assignment`, `ClusterExperiment.clusterDesign`,
`ClusterExperiment.totals`; `Design`, `Design.mk`, `Design.weight`,
`Design.treatment`; `UnitExperiment`, `UnitExperiment.mk`,
`UnitExperiment.weight`, `UnitExperiment.design`; `expectation`, `indicator`,
`marginal`, `joint`, `observed`, `htTotal`, `ht`, `generalizedTotal`,
`generalized`, `covariance`, `variance`, `disagreement`, `offSum`,
`armVarianceExpression`, `clusterCovarianceExpression`,
`splitCovarianceExpression`, `residualContrast`; `T24Statement`,
`T24Statement._proof_1`. Structure constructors and projections have the
fields described above, and the generated proof only supplies the numeral
instance for squaring.
