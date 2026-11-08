# Blind reading

Saved before opening `claims.json` or `record.json`. This reading uses only the Challenge,
its source definitions, `closure.json`, and Lean's printed declarations.
All 44 distinct line-zero auxiliary declarations in the five closures were printed in
`scratch/ClosureChecks.lean` (successful compilation; output in `scratch/closure-checks.log`).
They certify nonzero finite index types, natural numeral base conditions, singleton
nonemptiness, finite-dimensional/Borel instances, or the scalar tower for measures.
They impose no statistical hypotheses. In particular an auxiliary name referring to T8,
T9, or angular coordinates does not import that other theorem's assertion.

## SAP.P004a.T11

Source: `Challenge/Part1.lean:116-120`; statement: `Defs/Part4.lean:41-52`.

Let `N` be a natural number, `I={0,...,N-1}`, and `Z={false,true}^I`.
A circle table here is **any** real function `R:I×Z→ℝ`; it is not required to be
obtained by integration. Put `b(true)=1`, `b(false)=0`,
`c_i(true)=p_i`, `c_i(false)=1-p_i`, and
`q_p(z)=∏_{i∈I}c_i(z_i)`. All expectations mean the literal finite sum
`E_p F=∑_{z∈Z}q_p(z)F(z)`.
For each arm `a`, put
`μ_i(a)=[∑_z q_p(z) 1{z_i=a} R(i,z)]/c_i(a)`,
`τ_i=μ_i(true)-μ_i(false)`, and `τ=N^{-1}∑_i τ_i`.
These are conditional means under the independent Bernoulli assignment distribution
when `0<p_i<1`.

Define
`H(z)=N^{-1}∑_i [b(z_i)R(i,z)/p_i-(1-b(z_i))R(i,z)/(1-p_i)]`
and
`H_print(z)=N^{-1}∑_i [b(z_i)R(i,z)/p_i-(1-b(z_i))R(i,z)/p_i]`.
The theorem is the conjunction of the following:

1. For **every** natural `N`, then every vector `p:I→ℝ`, then every table `R`,
   if `N>0` and `0<p_i<1` for every `i`, then all three statements hold:
   `E_p H=τ`;
   `E_p H_print=N^{-1}∑_i [μ_i(true)-(1-p_i)μ_i(false)/p_i]`;
   and `E_p H_print=τ` if and only if
   `N^{-1}∑_i [(1-2p_i)/p_i]μ_i(false)=0`.
2. For **every** natural `N>0`, with all `p_i=1/4` and all `R(i,z)=1`,
   `τ=0`, `E_p H_print=-2`, and `E_p H=0`.

There is no independence hypothesis on outcomes and assignments; arbitrary interference
is allowed. Independence of the assignments themselves is built into `q_p`.
The docstring asserts exactly unbiasedness, the printed expectation and criterion,
and the constant-outcome example.

Junk conventions: real division by zero is defined as zero, but `N>0` and strict
propensity overlap exclude it in every asserted formula. The finite spaces are nonempty;
`Fin 0` and its empty node sum are excluded by `N>0`. All natural casts are exact,
all sums finite, and all real expectations exist. There is no integral, log, square
root, real power, infimum, supremum, or partial-function default in this closure.

## SAP.P004a.T12

Source: `Challenge/Part1.lean:122-131`; statement: `Defs/Part4.lean:55-69`.

There are exactly eight nodes in the Euclidean plane with locations
`a_i=(3(i+1),0)`, `i=0,...,7`. Each node is the singleton `{a_i}`.
The spatial measure is `ζ=∑_{i=0}^7 δ_{a_i}`. The outcome field is
`Y(x,z)=∑_i 1{x=a_i} 2^i/128`, independent of the Boolean assignment `z`.
The radius band at parameter `d` is `[0,d]`; the region for node `i` consists
of points whose distance to `{a_i}` is in that interval. Distance to a node is
Mathlib's `Metric.infDist` (the infimum of distances to points in the node).
At `d=0`, the region is `{a_i}` and its mass is one. The circle table is
`R(i,z)=[∫_{region_i}Y(x,z)dζ]/ζ(region_i)`.
The sharp null means `Y(x,z)=Y(x,all-false)` for **every** plane point and assignment.
Well-definedness at `d=0` means, for every node, its region is measurable with
strictly positive finite ζ mass and every assignment's outcome is Bochner integrable
on it. The theorem explicitly asserts both conditions.

Let `q(z)=∏_{i=0}^7 (1/2)=1/256`. For a real statistic `T` on the 256 assignments
and a draw array `z_0,...,z_P`, define
`B_T=card{r∈{0,...,P}:r≠0 and |T(z_0)|≤|T(z_r)|}` and
`p_+=(1+B_T)/(P+1)`. The array weight is `∏_{r=0}^P q(z_r)`;
it is the joint probability of independent assignments, including the observation.
Here `T(z)=H(z)=8^{-1}∑_i [2 b(z_i)R(i,z)-2(1-b(z_i))R(i,z)]`.

The first conjunct asserts sharp null and well-definedness and then the following
facts about a **specific possible realization** of 101 independent draws:
`z_0=all-false`, and every `z_r`, `r=1,...,100`, treats nodes 0 through 6 and
leaves node 7 untreated. Its observed statistic is `-255/512`, its replicate
statistic is `-1/512`, its array weight is `256^{-101}>0`, the printed
signed-observation comparison
`100^{-1}card{r≠0:H(z_0)≤|H(z_r)|}` equals one, the absolute exceedance count
`B_H` is zero, and `p_+=1/101`.
Repeated values in this one realized array do not assert dependence of the draws:
the positive probability is computed under the product law.

The second conjunct again asserts sharp null and well-definedness. For **all**
arrays in the finite sum, with `P=100`, it asserts
`∑_{arrays} (∏_{r=0}^{100}q(z_r)) 1{B_H/100≤1/20}=S>1/20`, where
`S=128^{-101}∑_{m=0}^{127}∑_{b=0}^{5} C(100,b)(m+1)^b(128-(m+1))^{100-b}`.
Thus this is an exact unconditional size assertion for a raw Monte Carlo test of
**absolute HT**, not the printed signed-observation rule's size.
The docstring explicitly restricts to these two witnesses and omits other universal,
signed-statistic, decimal, and seventeen-node assertions.

Junk conventions: integrals of nonintegrable real functions are totalized by zero,
and `ENNReal.toReal(∞)=0`; `circleAverage` itself would also divide by zero for
zero-mass regions. The asserted `WellDefined` properties prevent these cases here.
Nodes are nonempty singletons, so `infDist`'s empty-set convention is irrelevant.
The exponent `-101` in `256^{-101}` is an integer power of a strictly positive real.
The natural subtractions in `128-(m+1)` and `100-b` are truncated, but the explicit
ranges make them ordinary nonnegative differences. Exponent zero uses `0^0=1`,
which is the appropriate combinatorial convention at binomial endpoints. The count
is a natural cast exactly to ℝ. All denominators (8,128,256,100,101,512) are positive;
there is no empty draw type, since it is `Fin 101`.

## SAP.P004a.T13

Source: `Challenge/Part1.lean:133-136`; statement: `Defs/Part4.lean:72-91`.

For **every** natural `N` and `P`, every real function `w` on the finite assignment
space `Z={false,true}^{Fin N}`, every real statistic `T:Z→ℝ`, if every `w(z)≥0`,
`∑_z w(z)=1`, and `P>0`, then for **every** real `0<α<1`:

* Under the joint law `Pr(z_0,...,z_P)=∏_{r=0}^P w(z_r)`,
  `Pr((1+B)/(P+1)≤α)≤α`, where
  `B=card{r≠0:|T(z_0)|≤|T(z_r)|}`.
* Under the same law, `Pr(B/P≤α)≤(floor(αP)+1)/(P+1)`.
* `(floor(αP)+1)/(P+1)≤α+(1-α)/(P+1)`.

Separately, for **every** `N,P,T` and **every** deterministic array of `P+1`
assignments with `P>0`, the theorem asserts
`(1+B)/(P+1)-B/P=(1-B/P)/(P+1)`, with that difference between zero and
`1/(P+1)`. Finally it asserts the numerical inequality
`(floor((1/20)100)+1)/101>1/20`.
There is no requirement that `w` factor over nodes, and it need not have full support.
The product over draw indices explicitly models independent identically distributed
draws. `T` is fixed while the array is drawn; ties are counted as exceedances.
The docstring calls this the plus-one absolute-statistic finite-sample level theorem,
raw bound, and exact size of the correction.

Junk conventions: `P>0` excludes the raw denominator zero. `P+1>0` always, and its
`Fin` type contains index 0. `N=0` is allowed: the node type is empty but there is
exactly one assignment, so this is a meaningful degenerate sampling space.
`Int.floor` is the genuine integer floor of the finite real `αP` and its cast is
exact. No truncated subtraction occurs in these formulas. Expectations are finite
sums, and no integrability, `toReal`, log, root, power, infimum, or partial default arises.

## SAP.P004a.T14

Source: `Challenge/Part1.lean:138-151`; statement: `Defs/WholeW2.lean:226-335`.
The theorem has no external hypotheses; it conjoins three fixed Euclidean witnesses.
For all populations below, assignments have independent Bernoulli(1/2) coordinates.
For any band `D⊆ℝ`, a node region is `{x:infDist(x,node_i)∈D}`;
`R_D(i,z)=∫_{region_i}Y(x,z)dζ/ζ(region_i).toReal`.
For each node its effect is the difference of the conditional means
`[∑_z q(z)1{z_i=true}R_D(i,z)]/(1/2)` and
`[∑_z q(z)1{z_i=false}R_D(i,z)]/(1/2)`, where `q(z)=(1/2)^N`.
The AME is the arithmetic mean of these `N` node effects.
Each asserted `WellDefined` means measurable positive finite mass for every node
and integrability of every potential outcome over its region.

**One node, atomic measure.** The node is `{(0,0)}`. There are unit atoms at
`u_0=(1,0)`, `u_1=(0,2)`, `u_2=(-2,0)`. The outcome at `u_1,u_2` is `b(z_0)`
and is zero everywhere else. For every `D` in the four-element collection
`{ {1},{2},[0,2],[1,2] }`, well-definedness is asserted. Outcomes are globally
bounded in absolute value by 2. The three atom distances are explicitly 1,2,2.
The radius-1 AME is 0, radius-2 AME is 1, their arithmetic mean is 1/2, and both
band AMEs are 2/3. Actual shell masses divided by the `[1,2]` band mass are 1/3
and 2/3, and this weighted radius AME sum equals the band AME.
Here “uniform-radius mean” in the docstring denotes the arithmetic mean over the
two supported radii, not a Lebesgue integral over the intervening zero-mass circles.

**Two nodes, atomic measure.** Nodes are `{(0,0)}` and `{(3,0)}`; the unit atoms
are `v_0=(0,4)`, `v_1=(3,4)`, `v_2=(3,-4)`. Let
`δ_0=(0,1,1)` and `δ_1=(-1,0,0)` on these three atoms. The field is
`Y(v_x,z)=1+∑_{i=0}^1 b(z_i)δ_i(x)` and equals 1 at other plane points.
For `D={4},{5},[4,5],[0,5]` all averages are well-defined, and globally `|Y|<3`.
Node 0 distances are (4,5,5); node 1 distances are (5,4,4).
At radius 4 the individual effects are (0,0); at radius 5 they are (1,-1);
on each band they are (2/3,-1/3). Thus the circle AMEs are zero at both radii,
and both band AMEs are 1/6. Radius-4 normalized shell masses are (1/3,2/3),
and radius-5 masses are (2/3,1/3).
For **every** pair of real coefficients `(w4,w5)`, the weighted sum of the two
circle AMEs differs from the `[4,5]` AME and also from the `[0,5]` AME.

**One node, planar area.** Node `{0}` lies in ℝ², `ζ` is two-dimensional volume
restricted to the closed unit disk, and `Y(x,z)=b(z_0)‖x‖` for `‖x‖≤1`, zero
outside. This is globally bounded by 2 in absolute value. At every point inside
the disk the marginalized point effect, defined by the same conditional finite
sum for `Y(x,z)`, is `‖x‖`. The function `g(r)=r` is continuous and is asserted
to be a version of its conditional mean given radius: `g` is measurable, the
point effect and `x↦g(‖x‖)` are integrable under ζ, and for **every** measurable
`B⊆ℝ`, their integrals over `{x:‖x‖∈B}` agree.

For **every** real `a,b` with `0≤a<b≤1`, the `[a,b]` region is well-defined and
has mass `π(b²-a²)`. The pushforward of ζ restricted to this region by `x↦‖x‖`,
scaled by `1/[π(b²-a²)]`, is one-dimensional volume with density
`1{a≤r≤b}2r/(b²-a²)` (using `ENNReal.ofReal` to express nonnegative densities).
The function `r↦r·2r/(b²-a²)` is integrable on `[a,b]`, and the band AME equals
its integral, which is `2(b³-a³)/[3(b²-a²)]`.
Also `r↦r` is integrable there and its uniform-radius mean
`(∫_[a,b] r dr)/(b-a)` is `(a+b)/2`.
For the disk, the means are explicitly 1/2 and 2/3 and are unequal; for
`[1/2,1]` they are 3/4 and 7/9 and are unequal.
The docstring describes all three as counterexamples to a uniform-radius
band identity and explicitly uses conditional means for zero-area circles.

Junk conventions: atomic shell denominators are positive and finite by explicit
well-definedness. Area singleton circles have mass zero; their normalized set
integrals would totalize to zero, so the theorem instead uses the conditional-mean
moment certificate and never identifies those zero-over-zero averages with `g`.
All positive-area bands have `b-a>0`, `b²-a²>0`, and π>0. Their masses have finite
positive `toReal`; `ofReal` does not truncate any positive band normalization or
any density on `[a,b]`. Density zero outside is intentional. Finite atomic node
sets avoid the empty-set `infDist` convention. All assignment spaces and node
counts here are nonempty. No unbounded/empty `sInf`, `sSup`, limits, log, root,
real power, partial inverse, or truncated natural subtraction occurs.

## SAP.P004a.T15

Source: `Challenge/Part1.lean:153-162`; statement: `Defs/WholeW1.lean:35-166`.
This conjoins five statements, with separate universal quantifiers for each.

**Band averaging and conditional circles.** For **every** natural `N`, every
metric and measurable space `X`, every population consisting of nonempty node
sets `A_i⊆X`, a measure ζ, a real potential-outcome field `Y(x,z)`, and arbitrary
real distance bands `D_d`, then every `p:Fin N→ℝ` and `d∈ℝ`, assume `N>0`,
`0≤p_i≤1` for all nodes, each `C_i={x:infDist(x,A_i)∈D_d}` measurable with
`0<ζ(C_i)<∞`, every `Y(·,z)` integrable on every `C_i`, and all node-distance
functions measurable. Let `q_p(z)=∏_j[p_j if z_j=true else 1-p_j]`.
Define the forced marginal
`m_i^a(F)=∑_z q_p(z)F(i,z with coordinate i overwritten by a)`.
For point outcomes put
`δ_i(x)=∑_z q_p(z)[Y(x,z[i:=true])-Y(x,z[i:=false])]`;
for region means `R_i(z)=∫_{C_i}Y(x,z)dζ/ζ(C_i).toReal`, put
`τ_i=m_i^true(R)-m_i^false(R)` and `τ=N^{-1}∑_i τ_i`.
The conclusions, jointly, are:

* Every `δ_i` is integrable on `C_i`, and
  `τ_i=∫_{C_i}δ_i dζ/ζ(C_i).toReal` for every `i`, with the analogous formula
  `τ=N^{-1}∑_i ∫_{C_i}δ_i dζ/ζ(C_i).toReal`.
* For **every** node `i` there **exists** a real function `t_i` on radii.
  Write `μ_i=ζ|C_i`, `r_i(x)=infDist(x,A_i)`, and `ν_i=(r_i)_*μ_i`.
  It satisfies all three parts of the radial-density predicate:
  `t_i` is Bochner integrable under `ν_i`;
  for **every** measurable `B⊆ℝ`,
  `∫_B t_i dν_i=∫_{r_i^{-1}(B)}δ_i dμ_i`;
  for **every** `s` with `ν_i({s})>0`,
  `t_i(s)=∫_{r_i^{-1}({s})}δ_i dμ_i/ν_i({s}).toReal`.
  Further, `τ_i=∫ t_i dν_i/ζ(C_i).toReal`.
* If in addition `0<p_i<1` for every node, the forced effects and AME equal
  the conditional effects from
  `μ_i(a)=∑_z q_p(z)1{z_i=a}R_i(z)/[p_i if a=true else 1-p_i]`.

The existential density need only be integrable (thus a.e. measurable), not a
pointwise continuous or everywhere measurable chosen representative. Its moment
property is the signed pushforward/conditional-mean definition. No RN density or
conditional law is defined by assuming the desired band-averaging equality.

**Finite shells.** For **every** finite type `A`, natural `m,N`, mass array
`a_i(x)∈ℝ`, shell labels `s_i(x)∈Fin m`, and real profiles `δ_i(x)`, assume
`N>0`, every `a_i(x)≥0`, and `M_i=∑_x a_i(x)>0` for every node.
Put `M_ik=∑_{x:s_i(x)=k}a_i(x)` and
`U_ik=∑_{x:s_i(x)=k}a_i(x)δ_i(x)`. For every node,
`∑_x a_i(x)δ_i(x)/M_i=∑_{k:M_ik>0}(M_ik/M_i)(U_ik/M_ik)`;
the same holds after averaging over nodes.
For **every** vector `w:Fin m→ℝ`, if `M_ik/M_i=w_k` for every `i,k`, then
each `w_k>0` implies `M_ik>0` for every node and the node-average effect equals
`∑_{k:w_k>0}w_k[(∑_i U_ik/M_ik)/N]`.
Thus zero-mass labels are explicitly omitted, including from the common-weight sum.

**Universal common-kernel characterization.** For **every** natural `N>0`,
every family of probability measures `P_i` on ℝ and probability measure `U`,
the following are equivalent:
(i) for **every** family `f_i:ℝ→ℝ`, if each `f_i` is measurable and for each
`i` there exists a finite real `C_i` bounding `|f_i(r)|` for **all** real `r`,
then `N^{-1}∑_i∫f_i dP_i=∫[N^{-1}∑_i f_i]dU`;
(ii) `P_i=U` for **every** node.
No conclusion is assumed in a hypothesis: (i) is one side of an equivalence.

**Nonidentifiability.** The two-node atomic population, its regions, effects,
product design, positive finite integrals, and the conclusion stated in the T14
section above are included literally as a conjunct. In addition, for **every**
node `i∈Fin 2` and real `r`, its shell has positive ζ mass if and only if `r=4`
or `r=5`. A second population has the same nodes, atoms, and bands but outcome
zero everywhere. For every `D` among `{4},{5},[4,5],[0,5]` it is well-defined
and its AME is zero. There is **no** function `F:(Fin 2→ℝ)→ℝ` that maps the
vector of radius-4 and radius-5 AMEs to the `[4,5]` band AME for **both**
populations. The two input vectors are both `(0,0)`, but the required outputs
are 1/6 and 0. This prohibits arbitrary recovery functions, not only linear ones.

**Planar area.** For **every** center `c∈ℝ²`, reals `a,b`, and ambient subset
`X⊆ℝ²`, assume `0≤a<b` and `closedBall(c,b)⊆X`. Define the radial measure
`P=[π(b²-a²)]^{-1}(x↦dist(x,c))_*[(volume|X)|{a≤dist(x,c)≤b}]` and
`U=(b-a)^{-1}(volume|[a,b])`, using `ENNReal.ofReal` for the scalars.
Then `P` equals volume with density `1{a≤r≤b}2r/(b²-a²)`;
`P((−∞,(a+b)/2])=[((a+b)/2)²-a²]/(b²-a²)`;
`U((−∞,(a+b)/2])=1/2`;
the former ratio is strictly less than 1/2; and `P≠U`.
The ambient set need not be measurable: the contained measurable annulus makes its
extra restriction immaterial there. The center is a point, so this area statement
addresses full point-centered annuli, including disks when `a=0`.

Junk conventions: all band masses are explicitly positive finite, eliminating
`toReal(∞)=0` and zero-divisor artifacts in region averages. Forced marginals use
coordinate update and finite sums rather than division by endpoint probabilities;
`p_i=0` and `p_i=1` therefore have ordinary marginal-over-other-coordinates meaning.
Conditional means are compared only under strict overlap. Positive radial atoms
of the finite restricted measure have positive finite real masses. Continuous
zero-mass shells receive density versions, not zero-over-zero shell averages.
`Measure.map` can totalize nonmeasurable maps to the zero measure, but measurable
node distances are an explicit hypothesis; radial distance in the area clause is
continuous. Bochner integral totalization is excluded by the integrability hypotheses,
conclusions, and bounded functions under probability measures. The finite-shell
positive-mass filters exclude all zero denominators actually summed. If `A` or
`Fin m` is empty the positive-mass premises cannot be met for `N>0`, but there
are ordinary nonempty instances; those empty cases do not trivialize the theorem.
All node means require `N>0`. In the area clause `b-a`, `b²-a²`, and π are positive,
and `ofReal` agrees with their nonnegative normalizations and densities.
Node sets are nonempty, so empty-set distance defaults do not arise; an unclosed
node merely has distance zero on its closure, as `infDist` specifies. There is no
real log, root, real exponent, unbounded order infimum/supremum, limsup/liminf,
truncated subtraction, or partial-function default in the mathematical statements.
