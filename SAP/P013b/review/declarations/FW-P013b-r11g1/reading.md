# Blind reading

Saved before opening either `claims.json` or `record.json`. Sources read: every
entry of `closure.json`; `Defs/Part1.lean` in full, `Defs/Part2.lean` in full,
`Defs/Part5.lean` (including all five statement definitions), and the five
docstrings and declarations in `Challenge/Part1.lean`. The generated
`correctionA2._proof_1` and `normalCritical._proof_1` were also printed in
`scratch/Blind.lean`: both merely certify that the numeral 2 is at least two.
Structure constructors and projections were checked by printing the structures.
No Solution or proof implementation was read.

## Common fully unfolded finite notation

This notation is mathematical shorthand for explicit finite sums, not additional
assumptions. A design consists of a finite type Ω and real numbers p(z)>0 for
every z∈Ω with Σ_z p(z)=1. Thus Ω cannot be empty. A population consists of
natural numbers N,K, an arbitrary map D:Ω×{0,…,N−1}→{0,…,K−1}, and real fixed
potential outcomes y(i,a). Set I(i,a,z)=1 if D(z,i)=a and 0 otherwise. Write

* E[X]=Σ_z p(z)X(z), P(A)=Σ_z (if A(z) then p(z) else 0);
* Cov(X,Y)=Σ_z p(z)X(z)Y(z)−(Σ_z p(z)X(z))(Σ_z p(z)Y(z)),
  Var(X)=Σ_z p(z)X(z)^2−(Σ_z p(z)X(z))^2;
* q(i,a)=Σ_z p(z)I(i,a,z),
  q(i,j,a,b)=Σ_z p(z)I(i,a,z)I(j,b,z);
* Y(a)=Σ_i y(i,a), μ(a)=Y(a)/N,
  τ(a,b)=(Y(a)−Y(b))/N;
* T(a,z)=Σ_i I(i,a,z)y(i,a)/q(i,a),
  H(a,b,z)=(T(a,z)−T(b,z))/N.

All unit indices range over `Fin N`, exposure indices over `Fin K`; all real
divisions have Lean's convention x/0=0. `Positivity` means **both**
0<q(i,a) and q(i,a)<1 for every unit. The observed outcome is y(i,D(z,i)).
No other constraint on D or y is imposed by `Population`; fixed exposure-specific
outcomes and the observed-outcome definition encode consistency and exposure
sufficiency. Finite sums and conditional branches have their usual Mathlib
meanings. Empty sums equal zero.

For the variance statements introduce the following further explicit sums:

* B(i,j,a,b,z)=I(i,a,z)I(j,b,z)
  ·(q(i,j,a,b)−q(i,a)q(j,b))/q(i,j,a,b)
  ·(y(i,a)/q(i,a))·(y(j,b)/q(j,b)).
* V(a,z)=Σ_i I(i,a,z)(1−q(i,a))(y(i,a)/q(i,a))²
  +Σ_i Σ_{j≠i} B(i,j,a,a,z).
* A(a,z)=Σ_i Σ_{j≠i:q(i,j,a,a)=0}
  [I(i,a,z)y(i,a)²/(2q(i,a))+I(j,a,z)y(j,a)²/(2q(j,a))].
* C_HT(a,b,z)=Σ_i Σ_{j≠i}B(i,j,a,b,z)
  −Σ_i[I(i,a,z)y(i,a)²/(2q(i,a))
  +I(i,b,z)y(i,b)²/(2q(i,b))].
* C_A(a,b,z)=Σ_i Σ_{j≠i:q(i,j,a,b)>0}B(i,j,a,b,z)
  −Σ_i Σ_{j:q(i,j,a,b)=0}
  [I(i,a,z)y(i,a)²/(2q(i,a))+I(j,b,z)y(j,b)²/(2q(j,b))].
  This last zero-joint sum includes diagonal pairs.
* W(a,b,z)=[V(a,z)+A(a,z)+V(b,z)+A(b,z)−2C_A(a,b,z)]/N².

The double sums are over ordered pairs. `univ.erase i` means exactly j≠i;
there is no subtraction of natural numbers in that expression.

## SAP.P013b.T15

For every finite Ω, every N,K∈ℕ, every design p and population (D,y), if N>0,
then for every a,b∈Fin K, if a≠b and 0<q(i,a),q(i,b)<1 for all i, the following
four assertions hold together:

1. If q(i,j,a,b)>0 for every distinct i,j, then
   E[C_HT(a,b)]≤Cov(T(a),T(b)).
2. If that same off-diagonal positivity holds, and y(i,a)=y(i,b) for every i,
   then E[C_HT(a,b)]=Cov(T(a),T(b)).
3. E[C_A(a,b)]≤Cov(T(a),T(b)), without an off-diagonal positivity condition.
4. Var(H(a,b))≤E[W(a,b)], also without that condition.

Every term in these conclusions is exactly the finite sum in the common
notation above. The hypotheses preceding the four-way conjunction are shared;
the two off-diagonal positivity antecedents apply only to their own conjuncts.
The docstring describes these four inequalities/equality.

Junk-value audit: marginal denominators are strictly positive. Cross-joint
denominators may vanish outside the first two conditional conjuncts; B then
uses x/0=0. Since all support weights are positive, q(i,j,a,b)=0 implies the
indicator product is zero at every supported z, so this realizes the omitted-pair
convention in V and C_A. The first two conjuncts eliminate this issue for C_HT.
N>0 eliminates the population-size zero division. K must have at least two
elements once a≠b is supplied; N=0 is excluded. No logarithm, rpow, square root,
integral, `toReal`, supremum, infimum, limit, partial function or integer cast
is used. Natural casts and powers are ordinary nonnegative integer casts/powers.

## SAP.P013b.T16

For every finite Ω, every N,K∈ℕ, design p and population (D,y), if N>0, then
for every a∈Fin K with 0<q(i,a)<1 for all units and **every fixed numerical vector**
g:Fin N→ℝ, define

* Δ_g(a,z)=T(a,z)−Σ_i I(i,a,z)g(i)/q(i,a)+Σ_i g(i);
* C(a,z)=Σ_i I(i,a,z)/q(i,a);
* R(a,z)=T(a,z)/C(a,z).

The conclusion is the conjunction

1. E[Δ_g(a)]=Y(a);
2. for every z, Δ_g(a,z)=Σ_i I(i,a,z)
   [y(i,D(z,i))−g(i)]/q(i,a)+Σ_i g(i);
3. E[C(a)]=N;
4. |E[R(a)]−μ(a)|≤sqrt(Var(C(a)/N)·Var(R(a))).

E, Var, T, Y, μ, q, I are the explicit finite sums above. There is no distribution
over g and no conditional fitting/training assertion. The docstring explicitly
calls this a fixed-prediction result and mentions the zero-convention ratio.

Junk-value audit: N and marginal probabilities are positive. C(a,z) is a sum
of nonnegative terms and can be zero (no unit receives a); T(a,z) is then zero
as well. R(a,z)=0/0=0 in that event, and this convention affects the expectation
and variance in the asserted bound. No hypothesis excludes the event. Square
root is Mathlib's real sqrt, which is zero on negative arguments; its argument
here is nonnegative because each variance is the genuine finite-law variance.
No nonintegrable integral, infinity conversion, extremum, logarithm, rpow,
limit or partial function is involved. Empty populations are excluded; the
chosen exposure exists. Natural casts do not truncate.

## SAP.P013b.T17

For every finite Ω, N,K∈ℕ, design p and population (D,y), if N>0, then for
every arbitrary array r:Fin N×Ω→ℝ and a,b∈Fin K, assume a≠b,
0<q(i,a),q(i,b)<1 for all i, and

    ∃ i,z,z′, D(z,i)=D(z′,i) and r(i,z)≠r(i,z′).

This last condition is `Misspecified`: at least one unit's assignment-specific
outcome fails to be a function of its declared exposure. The population's y
field has no role in the assertion. Define

* T_r(a,z)=Σ_i I(i,a,z)r(i,z)/q(i,a);
* w(i,z)=p(z)/q(i,D(z,i));
* Y_r(a)=Σ_i Σ_{z:D(z,i)=a}w(i,z)r(i,z).

Then the conjunction is

    E[T_r(a)]=Y_r(a),
    E[(T_r(a)−T_r(b))/N]=(Y_r(a)−Y_r(b))/N.

The first equality is explicitly asserted for a; universal quantification and
swapping the two chosen exposures also give it for b. All expectations, q and I
are the finite sums above. The docstring describes weighted expectations under
misspecified exposures, not equality to the old fixed y totals.

Junk-value audit: the two marginal-probability hypotheses protect selected
exposure divisions. Even w(i,z) is protected at every supported z: the event
D(·,i)=D(z,i) contains z, whose weight is positive. Consequently its conditional
normalizing sum is positive. The conditionally included sum over a is an ordinary
finite sum; no regular conditional law or unspecified version is used. N>0;
distinct exposures exist; misspecification requires genuine units and at least
two assignments. All quantities are finite real arrays. No square root,
logarithm, rpow, integral, `toReal`, limit, extremum or partial function occurs.

## SAP.P013b.T18

A sequence S has, for each n∈ℕ, population size N=n+1, a finite support
Ω_n=Fin M_n with positive real weights summing to one, exposure alphabet
Fin K_n, map D_n and array y_n. It contains chosen exposures a_n≠b_n and proofs
0<q_n(i,a_n),q_n(i,b_n)<1 for every n,i. M_n cannot be zero. In addition:

* Nesting: there exist injections ℓ_n:Fin K_n→ℕ, global labels a≠b∈ℕ,
  and an array y:ℕ×ℕ→ℝ, with ℓ_n(a_n)=a, ℓ_n(b_n)=b and
  y_n(i,c)=y(i.val,ℓ_n(c)) for every n,i,c. This fixes the outcomes of old
  units under consistently labelled exposures; it imposes no coupling of designs.
* Standing positivity: 0<q_n(i,c)<1 for every n,i,c, including unselected exposures.
* Condition 3: there exist constants c₁,c₂∈ℝ with c₁≥0,c₂>0 such that for
  every n,i,c, |y_n(i,c)|≤c₁ and |1/q_n(i,c)|≤c₂.
* Printed Condition 5: there exist one m∈ℕ and Boolean matrices
  h_n:Fin N×Fin N→Bool such that for every n every row has at most m entries
  equal to true, and for all finite unit sets A,B, disjointness and the following
  no-edge predicate imply vector independence. The predicate is literally

      ¬∃ i,j, h_n(i,j)=true and
        [(i∈A and j∉B) or (j∈A and i∉B) or
         (i∉A and j∈B) or (j∉A and i∈B)].

  Vector independence here means that for every two full exposure assignments
  u,v:Fin N→Fin K_n, the probability of
  (∀i∈A,D_n(z,i)=u(i)) and (∀j∈B,D_n(z,j)=v(j)) equals the product of
  the probabilities of these two events. Each probability is a weighted finite
  sum. There is no requirement that h be symmetric, have zero diagonal or
  be the minimal graph. The displayed no-edge predicate differs from the usual
  absence of edges between A and B: for disjoint A,B it allows edges across
  A and B but forbids edges within or leaving either set in the other directions.
  In particular, true diagonal entries can force both A and B empty.
* Condition 6: there exist a real c>0 such that
  (n+1)Var_n(H_n(a_n,b_n)) tends to c as n→∞.

For α∈ℝ, define Φ(x)=(Gaussian(0,variance 1))((−∞,x]); Mathlib's
`ProbabilityTheory.cdf (gaussianReal 0 1)` gives precisely this real probability.
Let z_α=inf{x∈ℝ:1−α/2≤Φ(x)}. Define

    c_n(α)=Σ_{z∈Ω_n} p_n(z) · 1{
      W_n(a_n,b_n,z)≥0 and
      |H_n(a_n,b_n,z)−τ_n(a_n,b_n)|≤z_α sqrt(W_n(a_n,b_n,z)) }.

Here W,H,τ,Var and all ingredients are the explicit finite sums above applied
separately at n. The complete theorem is the negation of:

    For every S, if nesting, standing positivity, Conditions 3, printed 5 and 6
    hold, then for every real α with 0<α<1,
    1−α≤liminf_{n→∞}c_n(α).

Thus classically it asserts existence of some such S and some α∈(0,1) with
liminf c_n(α)<1−α. S is chosen before α. The theorem does not specify a witness.
The docstring says the printed claim is false and describes a source paired
witness with asymptotically negligible negative estimated variances along an
even-size subsequence; that description is not a clause of the theorem.

Junk-value audit: N=n+1 always positive; standing positivity protects marginal
denominators and the reciprocal in Condition 3 (without positivity, 1/0=0
would spuriously meet that bound). Zero joint probabilities in W use the same
omitted-pair convention as T15; positive support makes it harmless. W may be
negative: sqrt then equals zero, but the explicit W≥0 conjunct forces
noncoverage, so no negative-variance interval is counted as defined. This
convention can affect the coverage number and must be kept visible.
For 0<α<1, 1−α/2∈(1/2,1), so the Gaussian quantile set is nonempty and bounded
below; its real infimum is not an empty/unbounded-set default. Outside that
range the definition is total and can use real sInf defaults, but such levels
are excluded. Mathlib's real liminf is
sup{r∈ℝ: eventually r≤c_n(α)}; real sSup has default 0 on empty/unbounded-above
sets. Since 0≤c_n(α)≤1 and atTop on ℕ is nontrivial, the lower-bound set is
nonempty and bounded above, so this is the ordinary bounded liminf.
The Gaussian CDF can internally use measure-to-real conversions; it is a
probability measure, so no ∞ is converted. No expectation here is a Bochner
integral of potentially nonintegrable data. No log, rpow, truncated natural
subtraction, `Int` cast or partial function is used. Finset row counts are
natural numbers; the denominator 2 and all natural casts are positive where
used. No assumption across n of stochastic independence is present or required
by the statement itself.

## SAP.P013b.T19

For every sequence S of the exact type described in T18 (positive weights,
N=n+1, arbitrary exposure maps, fixed arrays, distinct selected exposures and
selected marginal positivity), assume the same nesting, standing positivity and
uniform Condition 3. Assume Condition 4, defined as existence of Boolean matrices
g_n on the N units such that:

* for every n,i,j, if g_n(i,j)=false, then for every c,e∈Fin K_n,
  q_n(i,j,c,e)=q_n(i,c)q_n(j,e);
* (Σ_i Σ_j 1{g_n(i,j)=true})/(n+1)² tends to zero.

No symmetry, diagonal convention, rate, minimum variance or vector independence
is separately imposed on g. The conclusion is: for every real ε>0,

    Σ_{z∈Ω_n} p_n(z) · 1{ ε <
      |[(Σ_i I_n(i,a_n,z)y_n(i,a_n)/q_n(i,a_n)
          −Σ_i I_n(i,b_n,z)y_n(i,b_n)/q_n(i,b_n))/(n+1)
        −(Σ_i y_n(i,a_n)−Σ_i y_n(i,b_n))/(n+1)]−0| }

tends to zero as n→∞. This is convergence in probability of the HT effect
estimation error to zero with possibly different finite probability spaces at
each n. Quantifiers over ε follow S and all its hypotheses. The docstring states
this consistency result under uniform Condition 3 and Condition 4.

Junk-value audit: N=n+1 and all marginal probabilities are positive. The count
in Condition 4 is a real finite sum of real 0/1 values, divided by a positive
real square. There are no joint-probability denominators in T19. The limit is
ordinary real `Tendsto` to a specified real number, not liminf or limsup;
no extrema or default infinite-limit values occur. All random variables have
finite support, so finite moments and measurability are automatic (with the
discrete sigma-algebra). Global nesting labels use `Fin.val` and injections;
no invalid natural subtraction or integer cast occurs. There is no square root,
log, rpow, Bochner integral, `toReal` or partial function in the conclusion or
its other assumptions. The empty support cannot carry a design, populations are
nonempty, and selected distinct exposures preclude an empty alphabet.
