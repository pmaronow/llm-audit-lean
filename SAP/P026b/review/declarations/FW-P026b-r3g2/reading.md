# Blind reading

This file was written before opening `claims.json` or `record.json`. It records the elaborated declarations and all unit declarations in their `closure.json` entries, including the generated proof auxiliaries printed in `scratch/BlindCheck.lean`. No canonical-claim or architect information is used here.

## Common expansions used below

A `Design Ω I R` consists only of a weight function `q : Ω → R` and a Boolean allocation `t : Ω → I → Bool`. The structure itself imposes no probability conditions. All index and sample spaces used in the statements are finite; the scalar field is the reals except the explicitly rational portions of T19. A probability design means `q(w) ≥ 0` for every `w` and `Σ_w q(w) = 1`. Write

* `E h = Σ_w q(w) h(w)`;
* `A_ai(w) = 1` when `t(w,i)=a`, and `0` otherwise;
* `p_ai = Σ_w q(w) A_ai(w)` and `p_abij = Σ_w q(w) A_ai(w) A_bj(w)`;
* `o_i(w) = y1_i` when `t(w,i)=true`, and `y0_i` otherwise;
* `S(y) = Σ_i y_i`, `Δ_N(y1,y0) = (Σ_i y1_i-Σ_i y0_i)/N`;
* `H_a(y,w) = Σ_i A_ai(w)y_i/p_ai`, and `H_N(y1,y0,w) = (H_true(y1,w)-H_false(y0,w))/N`;
* `C(h,k) = Σ_w q(w)h(w)k(w) - (Σ_w q(w)h(w))(Σ_w q(w)k(w))`, and `V(h)=C(h,h)`.

These are finite sums in an ordered field, not measure-theoretic integrals. In particular they involve no integrability or measurability defaults. Natural numbers in denominators are cast to the scalar field. Later uses of these mathematical abbreviations stand for the displayed sums, not for additional SAP primitives.

## SAP.P026b.T18

Source: `SAP/P026b/Challenge/Part1.lean:37–40`, `SAP/P026b/Defs/Part4.lean:72–78`, with the indicated Part1/Part2 closure.

There are no externally quantified data or hypotheses: this is a conjunction about a specified example. The sample space is `Fin 4`, the units are `Fin 3`, scalars are real, and every sample has weight `1/4`. In sample order `0,1,2,3`, the three allocations are the rows

```
0 0 0
0 1 1
1 0 1
1 1 0
```

The fitting set is `{1,2}` (`Finset.univ.erase 0`). Potential outcomes at all three units are `y1=1`, `y0=0`, so the observed outcomes equal their treatment indicators. A fitting outcome is the function on the subtype `{j // j∈{1,2}}` returning `o_j(w)`. The fit maps such a function `y` to `y(1)+y(2)-2y(1)y(2)`.

The conclusion asserts, in order:

1. The four weights are nonnegative and sum to one.
2. For every unit `i`, both `Σ_w q(w) A_true,i(w)>0` and `Σ_w q(w) A_false,i(w)>0`.
3. For each `j∈{1,2}`, the Boolean focal allocation `t(w,0)` and the Boolean allocation `t(w,j)` are independent in this exact sense: for **every** function `u : Bool → ℝ` and **every** function `v : Bool → ℝ`, `Σ_w q(w)u(t(w,0))v(t(w,j)) = (Σ_w q(w)u(t(w,0)))(Σ_w q(w)v(t(w,j)))`.
4. `C(A_true,0, w ↦ o_1(w)+o_2(w)-2o_1(w)o_2(w)) ≠ 0`.

The fit is exactly the focal treatment indicator on these four samples, so its covariance with that indicator is `1/4`. The independence clause is individual/pairwise independence, not independence of the focal allocation from the joint vector of fitting outcomes. Indeed the joint vector determines the focal allocation. The docstring describes this as falsity of a printed general rule; the mathematical statement itself is the concrete conjunction above and includes no universal rule in its syntax.

Junk/default audit: all scalar denominators here are the positive constant `4`; marginal positivity is asserted; there are no empty index sets, partial function defaults, logs, roots, infinities, extrema, limits, or truncated subtractions with numerical consequences. Finite-vector indexing is justified by `Fin` proofs; the subtype arguments `1,2` have explicit membership proofs. The generated auxiliaries are only numeral nonzeroness/at-least-two instances and membership proofs. The `independent` definition quantifies over all real test functions; because its random arguments are Boolean, this causes no measurability issue.

## SAP.P026b.T19

Source: `SAP/P026b/Challenge/Part1.lean:42–45`, `SAP/P026b/Defs/Part4.lean:80–97`, with its entire Part1/Part2 closure.

This is again a closed conjunction about fixed data, with no externally imposed hypotheses. There are 16 units, 10 clusters, and 90 equiprobable allocations. Clusters `0,1,2,3` have exactly two treated, uniformly over their six pairs, and clusters `4,…,9` have exactly two treated, uniformly over their fifteen pairs. The sample space is `Fin 6 × Fin 15` and each weight is `1/90`. The listed rows enumerate all six and all fifteen pairs exactly once, so this is the independent product of these two uniform choices. In the rational design all arithmetic is rational; `realTableDesign` casts its weights to reals and leaves the allocations identical.

The arrays, indexed from zero, are:

```
unit i:    0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15
cluster:   0 0 1 1 2 3 4 4 4 5  5  6  6  7  8  9
y:         1 1 1 1 1 0 1 1 0 1  1  1  1  0  0  0
x:         4 0 4 1 4 2 4 1 2 5  4  1  4  2  2  3
```

Unit allocations are those of their clusters. Define stratum `L={0,…,5}`, `R={6,…,15}`. Centered covariates are `Xc_i=x_i-5/2` on L and `x_i-14/5` on R; centered outcomes are `Yc_i=y_i-5/6` on L and `y_i-3/5` on R. Let `Tbar_L(w)=Σ_{i∈L} A_true,i(w)/6`, `Tbar_R(w)=Σ_{i∈R} A_true,i(w)/10`, and `Tc_i(w)=A_true,i(w)-Tbar_stratum(i)(w)`. The residualized treatment is

`r_i(w)=Tc_i(w)-[Σ_j Xc_j Tc_j(w)/Σ_j Xc_j²]Xc_i`,

and the FE estimate is `F(w)=Σ_i r_i(w)Yc_i/Σ_i r_i(w)²`.

The fixed cluster-level linear residual vector is

`l=(1,7/8,1/4,-1/2,-15/31,19/93,1/3,-76/93,-76/93,-79/93)`.

For the logistic portion, `s(z)=1-1/(1+exp(z))`. For a Boolean `b`, let `J_false=L`, `J_true=R`. The objective at real coefficients `(a,d)` is

`L_b(a,d)=Σ_{i∈J_b} [y_i log(s(a+d x_i))+(1-y_i)log(1-s(a+d x_i))]`.

A maximizer is a pair `(a,d)` with `∀(a',d')∈ℝ², L_b(a',d')≤L_b(a,d)`. The selected coefficients `β_b` are a classically chosen maximizer if one exists; otherwise they are `(0,0)`. **Prediction uses `β_true` for `i<6` and `β_false` for `i≥6`.** This reverses the fitting objective's stratum selector. Cluster-level logistic residuals are `z_c=Σ_{i:cluster(i)=c}(y_i-s(β_selected,1+β_selected,2 x_i))`.

For either residual vector, the ATE estimator is `H_16(residual,residual,w)` on the **cluster** design, with the sum over ten clusters but divisor 16. Its variance estimate, denoted `Q(residual,w)` here, unfolds as follows. Set `ε(p)=1` if `p=0`, otherwise `0`; let

`B_abij(w)= A_ai(w) A_bj(w)/(p_abij+ε(p_abij)) ·(p_abij-p_ai p_bj)·(o_i(w)/p_ai)·(o_j(w)/p_bj)`.

For the variance estimate the potential cluster outcomes are both the residual vector, so `o_i(w)` is that fixed residual. Then `Q` is `1/16²` times

* `Σ_i [A_true,i(o_i/p_true,i)²+A_false,i(o_i/p_false,i)²]`;
* plus `Σ_i Σ_{j≠i}(B_true,true,ij+B_false,false,ij-2B_true,false,ij)`;
* plus `Σ_i Σ_{j≠i:p_true,true,ij=0}[A_true,i o_i²/(2p_true,i)+A_true,j o_j²/(2p_true,j)]`;
* plus the same last sum with both arms false.

The two off-diagonal sums are over ordered pairs. `clusterTotal` is precisely the filtered finite sum displayed in the definition of `z_c`; it is not an average.

The theorem first asserts `∀w, Σ_i r_i(w)²>0`, then existence and uniqueness of a maximizer for each of `L_false` and `L_true`. Finally it negates the following entire conjunction (it does **not** individually negate each numeric row):

* unique maximizers for both strata, again;
* `E F` rounds to `-0.012` and `V(F)` rounds to `0.036`;
* `V(F)` and `V(F)+(EF)²` have square roots rounding to `0.191`;
* `V(H_16(l,l))` has square root rounding to `0.162`, and itself rounds to `0.026`;
* `E Q(l)` rounds to `0.026`, and `V(Q(l))` has square root rounding to `0.007`;
* each of `sqrt(V(H_16(z,z)))`, `V(H_16(z,z))`, `E Q(z)`, `sqrt(V(Q(z)))` is within `0.0005` inclusive of `0.170`, `0.029`, `0.029`, `0.007`, respectively.

For the rational rows, “rounds to r” means `r-1/2000≤x<r+1/2000`. “Has square root rounding to r” is actually the predicate `(r-1/2000)²≤v<(r+1/2000)²`. All the specific SD targets are positive. The real rows instead use a closed absolute-value tolerance on both ends. The generated `correctedLogitColumn`, `printedLogitColumn`, and `roundsTo` proof auxiliaries occurring in the closure prove only that fixed positive numerals are at least two; their parent column definitions are not terms of T19's assertion.

Junk/default audit: finite sums are always defined. Rational and real division by zero is totalized to zero. The FE covariate denominator is a fixed positive sum of squares; the theorem explicitly asserts strict positivity of the treatment residual denominator at all 90 allocations. Stratum mean denominators 6 and 10 and population denominator 16 are positive. All cluster treatment/control marginals are positive in this enumerated design. The `ε` convention replaces a zero joint denominator by one; for the table design all off-diagonal joint probabilities used are positive, so the correction terms selected by zero joints are empty. The `i.val-4` natural subtraction is used only under `i.val≥4`, with a bound proof, so it is exact subtraction here. Indexing Fin vectors is total with valid indices. Real logarithms would be totalized even at nonpositive arguments (`log 0=0`), but `0<s(z)<1` for finite real z, so both log arguments are strictly positive. The coefficient selector's `(0,0)` fallback is present in the definition, but the outer existence/uniqueness assertions rule it out in this theorem. The selected maximizers have no specified tie-breaking, but uniqueness also rules that ambiguity out. `Real.sqrt` is totalized for negative arguments, but the normalized nonnegative table law makes these variances nonnegative. No Bochner integrals, infinities, empty/unbounded extrema, limsups, or partial function defaults occur. The reversed stratum selector can affect the substantive meaning independently of any junk-value convention.

## SAP.P026b.T20

Source: `SAP/P026b/Challenge/Part1.lean:47–50`, `SAP/P026b/Defs/Part5.lean:12–19`, and the Part1 closure.

Quantifier order: for every small type `I`, every finite enumeration and decidable equality on it, every witness that `I` is nonempty, every `UnitExperiment I`, and every pair of real functions `y1,y0 : I→ℝ`, the following conjunction holds.

A `UnitExperiment I` is a real weight function on the complete binary allocation space `Ω=(I→Bool)`, together with proofs of `q(w)≥0` for all allocations, `Σ_w q(w)=1`, and, for every unit, strictly positive sums of weights of allocations assigning it true and false. The associated design has allocation `t(w,i)=w(i)`. Thus all substantive probability and marginal hypotheses are structure fields, not omitted assumptions. Set `N=|I|`.

The conclusions are:

1. For every Boolean arm `a` and every binary allocation `w` (including those of weight zero), `Σ_i A_ai(w) y^a_i/p_ai = Σ_i A_ai(w)o_i(w)/p_ai`, where `y^true=y1` and `y^false=y0`.
2. `Σ_w q(w)Σ_i A_true,i(w)y1_i/p_true,i = Σ_i y1_i`.
3. The same equality for false and `y0`.
4. `Σ_w q(w)[(Σ_i A_true,i(w)y1_i/p_true,i - Σ_i A_false,i(w)y0_i/p_false,i)/N] = (Σ_i y1_i-Σ_i y0_i)/N`.

There is no independence assumption between units, no fixed treated count, and no equal-marginal requirement.

Junk/default audit: every inverse marginal is genuinely positive by the structure's fields; `I` nonempty implies its finite cardinal `N>0`. The natural cardinal casts exactly to the real cardinal. No other subtraction than real subtraction is used; there are no empty population averages, integrals, log/root/rpow defaults, infinity conversions, extrema, limits, or partial values. Some allocations may have an empty arm even with positive mass, but the formulas divide by positive inclusion probabilities and N, never by realized arm sizes.

## SAP.P026b.T21

Source: `SAP/P026b/Challenge/Part1.lean:52–64`, `SAP/P026b/Defs/WholeW1.lean:12–93`, and its complete Part1 closure. The target is `T21WholeStatement`, **not** the unused older `T21Statement` in Part5.

The full statement is a conjunction of two universally quantified assertions and one existential assertion. Define the observed unit arm total `O_a(w)=Σ_i A_ai(w)o_i(w)`, and the actual difference of unit means `D(w)=O_true(w)/Σ_i A_true,i(w)-O_false(w)/Σ_i A_false,i(w)`.

First universal assertion, quantifiers and conditions in order: take any finite sample type `Ω`, finite unit type `I` with decidable equality, and real design `D`; assume nonnegative normalized weights. Take any natural `n` with `0<n<|I|`. Assume every true marginal is `n/|I|`, every false marginal is `(|I|-n)/|I|`, and every positive-weight allocation has `Σ_i A_true,i(w)=n`. Then for **every** real potential outcome pair `x,z`, writing `N=|I|`,

* at every positive-weight allocation, `Σ_i A_false,i(w)=N-n`, and both `H_N(x,z,w)` and `D(w)` equal `O_true(w)/n-O_false(w)/(N-n)`;
* the expectation of this fixed-denominator contrast equals `(Σ_i x_i-Σ_i z_i)/N`;
* the expectation of the actual difference of means equals the same quantity.

Second universal assertion: take any nonempty finite unit type `U` with decidable equality, naturals `M,m` satisfying `0<m<M`, and a `ClusterExperiment U (Fin M)`. This structure consists of a surjection `c:U→Fin M` (each cluster nonempty), and a `UnitExperiment (Fin M)` (nonnegative normalized weights on all cluster allocation maps and strictly positive treatment/control cluster marginals). Its cluster design is that assignment law; its unit design gives unit i allocation `w(c(i))` and the identical weight function. Assume distinct clusters c,d have `Σ_w q(w)1_{w(c)≠w(d)}>0`. Assume each cluster has true marginal `m/M` and false marginal `(M-m)/M`. For **every** real outcome pair `x,z : U→ℝ`, with `N=|U|`,

* at **every** cluster allocation, including mass-zero allocations, the unit HT estimate equals `K(w)=(M/N)[O_true(w)/m-O_false(w)/(M-m)]`, where O sums observed outcomes over original units;
* `Σ_w q(w)K(w)=Δ_N(x,z)`;
* `Σ_w q(w)H_N(x,z,w)=Δ_N(x,z)`.

There is no assumption that a realized cluster allocation has exactly m treated clusters. The distinct-cluster disagreement condition is explicit even though the displayed algebraic identities do not need it. The contrast divisors m and M-m are fixed constants, not realized arm sizes.

Existential assertion: there exists a `ClusterExperiment (Fin 4) (Fin 3)` with the exact unit-to-cluster map `(0,1,2,2)` and the following exact assignment law. Let `onehot_j(c)` be the Boolean equality test `j=c`. At an allocation w, `q(w)=Σ_{j=0}² [1/3 if w=onehot_j, else 0]`; thus the three one-hot allocations have weight `1/3`, all others zero. This experiment has:

* cluster and unit true marginals `1/3` and false marginals `2/3`;
* disagreement probability `2/3` for every distinct cluster pair;
* exactly one treated cluster at every positive-weight allocation and a strictly positive treated unit count there;
* a strictly positive control unit count at every positive-weight allocation;
* with real sharp-null outcomes `x=z=(1,1,0,0)`, `E D=1/9`, `E H_4=0`, `Δ_4=0`, and explicitly `E D≠Δ_4`.

Junk/default audit: the first assertion's `0<n<N` makes N,n,N-n strictly positive; the second's `0<m<M` and nonempty U make M,m,M-m,N positive. All relevant marginals are consequently positive. The displayed natural subtractions are truncated by Lean, but their strict inequalities ensure ordinary positive differences here. The first assertion's difference-in-means denominator is nonzero on positive support. The existential witness also asserts both arm counts positive on positive support. On allocations of weight zero, actual means may use division by zero (giving zero), but this affects neither supported claims nor their expectations. The second assertion's contrast has fixed positive divisors even when a realized arm is empty. `Fin M` is nonempty under m<M. Surjectivity and positive U prevent empty clusters. All Fin indexing, equality tests, and one-hot allocation weights are total. The generated proof auxiliaries establish only nonzero/at-least-two numeral instances. No log/root/rpow, integral defaults, infinity conversions, unbounded/empty extrema, or limit conventions occur.

## SAP.P026b.T22

Source: `SAP/P026b/Challenge/Part1.lean:66–69`, `SAP/P026b/Defs/Part5.lean:53–70`, and the complete Part1 closure.

Quantifier order: for every nonempty finite small type I with decidable equality, every `UnitExperiment I` as expanded in T20, every real potential outcome pair y1,y0, and every real assignment-dependent prediction function `f : (I→Bool)→I→ℝ`, the following conjunction holds. Set `N=|I|`. The generalized arm total and contrast are exactly

`G_a(y,f,w)=Σ_i [A_ai(w)y_i/p_ai - A_ai(w)f(w,i)/p_ai + f(w,i)]`,

`G_N(y1,y0,f,w)=[G_true(y1,f,w)-G_false(y0,f,w)]/N`.

1. **If**, for every i, `Σ_w q(w)A_true,i(w)f(w,i) - (Σ_w q(w)A_true,i(w))(Σ_w q(w)f(w,i))=0`, then `E G_true(y1,f)=Σ_i y1_i`, `E G_false(y0,f)=Σ_i y0_i`, and `E G_N=Δ_N(y1,y0)`. The covariance condition is only an antecedent for this first component; it is not a global assumption for the identity in component 3.
2. For **every** fixed real function `g:I→ℝ`, the covariance in component 1 with `f(w,i)=g_i` is zero at every unit, both generalized arm totals are unbiased, and the generalized contrast is unbiased.
3. At **every** allocation w, with arbitrary f and without the covariance condition, `G_N(y1,y0,f,w)=H_N(y1,y0,w)-[Σ_i A_true,i(w)f(w,i)/p_true,i-Σ_i A_false,i(w)f(w,i)/p_false,i]/N`.

The same prediction f is used for both arms. The statement imposes no accuracy, linearity, or statistical fitting assumption on it. It is a function of the full allocation, not an additional independently randomized quantity.

Junk/default audit: all marginals and N are positive by `UnitExperiment` and nonempty I, so every division is in its intended domain. All sums are finite, all outcomes and predictions are finite real values, and covariance is the displayed finite moment expression. Zero covariance for both arms follows from the true-arm condition and the normalized binary law; the false-arm condition is not an extra assumption. There is no truncated subtraction, logarithm, square root, real-power convention, infinity conversion, extremum, limit, integral of a nonintegrable function, or partial/default value in this closure. Empty realized arms are allowed, with no division by their realized sizes.
