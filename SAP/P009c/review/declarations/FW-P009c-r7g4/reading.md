# Blind reading

This file was saved before opening either `claims.json` or `record.json`.
The source statements, docstrings, every declaration listed in `closure.json`,
and the generated auxiliary declarations were read. Formulae below use ordinary
real arithmetic and finite sums. No claim or architect decision is used here.

## SAP.P009c.T50

The declaration at `SAP/P009c/Challenge/Part1.lean:104–107` asserts
`T50Statement` (`Defs/Part4.lean:38–46`). Its docstring describes SR inflation
under two alternatives and bounds on the maximum Rayleigh value.

### Objects and definitions, unfolded

For a natural number n, `Assignment n` is the finite set of all functions
`Fin n → Bool`, i.e. all binary vectors, including assignments of probability
zero. A `Law Ω` on a finite type Ω consists of real masses w(ω) ≥ 0 whose
finite sum is 1. `Law.mk` constructs exactly this data; `Law.mass` projects
the weights. In particular this is a genuine finite probability law, not an
arbitrary weighting. Define

* E_w f = Σω w(ω) f(ω) (`mean`);
* P_w(A) = Σω w(ω) 1_A(ω) (`prob`);
* Cov_w(f,g) = Σω w(ω)(f(ω)−E_w f)(g(ω)−E_w g) (`cov`);
* Var_w(f) = Σω w(ω)(f(ω)−E_w f)² (`var`).

`Experiment n` consists of such a law on binary assignments and arbitrary real
outcome functions y_i(z), i ∈ Fin n. Its constructor and projections carry no
additional assumptions. Write p_i(b) = Σz w(z)1_{z_i=b} (`marginal`).
The modified potential outcome `potential E i b z` is y_i(z with its ith
coordinate replaced by b), where replacement is Mathlib's `Function.update`.
The direct `effect` is the difference between replacement by true and false.
Define

* μ̂_b(z) = n⁻¹ Σi 1_{z_i=b} y_i(z)/p_i(b) (`muHat`);
* H(z) = μ̂_true(z)−μ̂_false(z) (`ht`);
* B(z) = n⁻² Σi [1_{z_i=true} y_i(z)²/p_i(true)²
  +1_{z_i=false} y_i(z)²/p_i(false)²] (`vBER`);
* M = n⁻¹ Σi [Σz w(z)(y_i(z with i=true)−y_i(z with i=false))]² (`msq`).

`Interferes E i j` says i=j OR there exist two binary vectors differing only
possibly at coordinate i for which y_j differs. The vectors range over the
entire cube, without restricting to the support of w. `Dependent E i j` says
there is an ℓ that interferes with both i and j. The real matrix D has entry
D_ij=1 if this holds and 0 otherwise (`d`). Thus D is symmetric, has entries
in {0,1}, and has diagonal entries 1 for nonempty populations.

`degree E i` is Σj D_ij; `dAvg E` is a = (Σi Σj D_ij)/n; `dMax E` is
m = sup {Σj D_ij : i ∈ Fin n}. `quadD E v` is Σi Σj v_i D_ij v_j.
`lambdaMax E` is

  λ = sup {Σi Σj v_i D_ij v_j : v : Fin n → ℝ, Σi v_i²=1}.

This is the largest Rayleigh value of the real symmetric matrix D. There is
no positive-semidefinite hypothesis. The inflated estimator `vSR E z` is
λ B(z).

`Bernoulli E` requires 0 < p_i(true) < 1 for every i, and, for every z,
w(z)=∏i (p_i(true) if z_i=true, otherwise 1−p_i(true)). This is mutual
independence of all assignments, not just pairwise independence.

`Regular E k q s` requires, in order:

1. k>0, q≥2, and s≥1, all real;
2. k⁻¹ ≤ p_i(true) ≤ 1−k⁻¹ for every i;
3. Σz w(z)|y_i(z)|^q ≤ k^q for every i;
4. Σz w(z)|y_i(z with i=b)|^s ≤ k^s for every i and Boolean b.

Powers in the last two conditions are `Real.rpow`, with real exponents.
The same k bounds probabilities and both kinds of moments.

A `Study` has a natural size N(t)>0 at every natural time t, N(t)→∞, and
an experiment E_t of that size. `Study.mk` constructs precisely these fields;
the projections appearing in the closure have their literal meanings.
`size S t` is the real cast n_t of N(t). `RegularSequence S k q s` means
the preceding four conditions hold for every t with the same k,q,s.
`Restricted S` means a_t/n_t → 0.
`LittleO f g` means f_t/g_t → 0 using total real division.
`PositiveLiminf f` means ∃c>0, ∀ sufficiently large natural t, c≤f_t; it
does not evaluate a real-valued `Filter.liminf`.

`Conservative S V` means there exists a real function L on ℝ such that:

* for EVERY real ε>0, the limit as t→∞ of
  Σz w_t(z)1_{(n_t/a_t)(V_t(z)−Var_{w_t}(H_t))≤−ε}
  exists and equals L(ε);
* lim_{ε→0, ε>0} L(ε)=0.

The first limit is ordinary `Filter.Tendsto` on naturals with `atTop`; the
second uses `nhdsWithin 0 (Set.Ioi 0)`. The definition demands existence of
each positive-threshold inner limit, not merely a limsup bound.

### Quantifiers, hypotheses, and conclusions

The statement is the conjunction of two independent assertions:

1. For EVERY Study S and EVERY real k,q,s, if it is a RegularSequence, q≥4,
   every E_t is Bernoulli, and EITHER
   (i) λ_t/(sqrt(n_t)sqrt(a_t))→0, OR
   (ii) a_t/n_t→0 and ∃c>0 eventually M_t≥c,
   then the sequence V_t(z)=λ_t B_t(z) is Conservative in precisely the
   iterated-limit/existence sense above. The outer quantifiers precede all
   the hypotheses. The c in alternative (ii) is existential inside that
   hypothesis. The function L is existential only in the conclusion.
2. For EVERY natural n>0 and EVERY Experiment E of size n, a≤λ≤m.
   This second assertion assumes no design independence, regularity or
   moment bounds.

### Junk values and domains

Real division and inversion are total: division by zero would return zero.
The hypotheses exclude its use as a substitute for a defined quantity here:
all n_t and the separately quantified n are positive; finite-cube
probabilities satisfy p_i(false)=1−p_i(true); Bernoulli and regularity keep
both marginals positive. The mandatory diagonal implies degree_i≥1,
a_t≥1, and λ_t≥1 (use a coordinate unit vector). Thus the scaling by a_t
and by sqrt(n_t)sqrt(a_t) has positive denominators. k>0 prevents k⁻¹
from being the junk inverse of zero.

`Real.sqrt` is defined to be zero on negative reals, but its arguments here
are positive n_t and a_t. `Real.rpow` is a total extension (including its
0^0=1 convention); all moment bases are absolute values or positive k,
and the exponents satisfy q≥4 and s≥1, so only ordinary nonnegative-base
powers, including 0 to a positive power, are used.

Real `sSup` has a default value of zero for empty or unbounded sets. For
positive n the degree range is nonempty and finite. The Rayleigh set is
nonempty (coordinate unit vectors) and bounded (finite dimension and
|D_ij|≤1, e.g. |vᵀDv|≤n on the unit sphere). Its supremum is the usual
real supremum; continuity on the unit sphere also makes it a maximum.
Empty `Fin 0` sums and empty Rayleigh/degree ranges would change the
definitions for n=0, but neither assertion applies at n=0.

All means are literal finite sums of real numbers. There is no Bochner
integral default, nonintegrability convention, infinity, `toReal`, log,
infimum, liminf or limsup in this closure. No truncated subtraction occurs;
the subtractions used here are real. Natural sizes are cast to ℝ without
rounding. Function updates are total. Classical decidability of predicates
only supplies the indicators. The generated `Paired._proof_1` and
`T47Statement._proof_1` were printed: they certify `(1+1).AtLeastTwo` and
`(3+1).AtLeastTwo`, respectively, for ordinary real numeral notation;
they impose no substantive Paired or T47 premise.

## SAP.P009c.T51

The declaration at `SAP/P009c/Challenge/Part1.lean:109–112` asserts
`T51Statement` (`Defs/Part4.lean:48–65`). Its docstring describes construction
of outcomes for each regular Bernoulli design sequence, a three-point weak
limit, interference bounds, and finite Chebyshev equality.

### Objects and definitions, unfolded

Here too an assignment is z : Fin n → Bool, an Experiment is a normalized
nonnegative real law w on that finite cube and arbitrary full-cube outcomes
y_i(z), and a Study has positive sizes N(t) tending to infinity. Its
constructors and projections introduce exactly these fields. Expectations
are Σz w(z)f(z); probabilities are Σz w(z)1_A(z); covariance and variance
are their finite centered product and square sums. The `marginal`,
`potential`, `muHat`, `ht`, `Regular`, `RegularSequence`, `Bernoulli`,
`Interferes`, `Dependent`, `d`, `degree`, `dAvg`, `dMax`, `size`, and
`Restricted` definitions are the explicit formulae given in T50's section:
in particular a_t=(Σij D_t,ij)/n_t, m_t=max_i Σj D_t,ij, H_t is the
inverse-probability weighted treatment/control difference, regularity
requires uniform finite real q≥2 and s≥1 moment bounds and uniform
interior marginals, and restricted interference means a_t/n_t→0.
These definitions are applied to the REPLACEMENT outcomes, not the
original outcomes, wherever S' occurs.

`BigO f g` means ∃C>0 such that |f_t|≤C|g_t| for every sufficiently
large natural t. Its constant and starting time may depend on all data
outside that existential. Powers n_t^x are `Real.rpow`.

For a real α with 0<α<1, `sharpLaw α hα` is a Law on `Fin 3`, with
weights (α/2,1−α,α/2). `sharpValue` maps its indices 0,1,2 to −1,0,1.
`sharpCDF α x` is the explicitly defined real function

* 0 for x<−1;
* α/2 for −1≤x<0;
* 1−α/2 for 0≤x<1;
* 1 for x≥1.

For a Study S and a family of real random variables X_t on its finite
assignment spaces, `InDistribution S X G` means: for EVERY real x,
if the real function G is continuous at x, then
Σz w_t(z)1_{X_t(z)≤x} → G(x) as t→∞. Applied to the displayed CDF,
this is ordinary convergence in distribution to the three-point law.

### Quantifiers, hypotheses, and conclusions

There are again two independent universally quantified assertions.

1. For EVERY Study S and EVERY real k,α,x, assume, in the written order:
   k>0; for every t and i, k⁻¹≤p_t,i(true)≤1−k⁻¹; every original
   E_t is Bernoulli; 0<α<1; and 0≤x<1. There then EXISTS a family
   y_t : Fin (N(t)) → (Fin (N(t)) → Bool) → ℝ. Form S' by keeping
   exactly S's sizes, growth proof, positivity proof and design laws,
   and replacing just its outcome functions by y_t. All of the
   following are required jointly for this one family:
   * ∃ real K,q,s, RegularSequence S' K q s;
   * a'_t/n_t→0;
   * ∃C>0 eventually |a'_t|≤C|n_t^x|;
   * IF x=0, ∃C>0 eventually |m'_t|≤C|sqrt(n_t)|;
   * the random variables
     sqrt(n_t)/sqrt(a'_t) · [H'_t(z)−Σu w_t(u)H'_t(u)]
     converge in distribution to the preceding CDF with parameter α.
   The same chosen outcome family satisfies every bullet. K,q,s and
   all BigO constants may depend on S,k,α,x. No property of the
   original outcomes is assumed beyond being real-valued functions.
   Centering uses the expectation of the replacement HT estimator.
2. For EVERY real α and EVERY proof hα of 0<α<1, for the separate
   finite law above, its mean is 0, its variance is α,
   P(|sharpValue|≥1)=α, and
   P(|sharpValue−mean|≥sqrt(variance/α))=α.
   In the latter equality the threshold is 1, since variance=α>0.
   The finite-law assertion concerns this explicit three-point law;
   it does not itself assert equality for any finite-population HT
   distribution or any inequality for other distributions.

### Junk values and domains

All finite-sum expectations and variances exist. No measure, conditional
law, Bochner integral or partial expectation appears. The construction
keeps n_t>0; the mandatory interference diagonal gives a'_t≥1, so the
normalized HT variable divides by a positive square root. The input
Bernoulli laws have strictly positive marginals in each arm, and keeping
the designs keeps these true for the replacement HT estimator. Both
regularity constants k and K are positive when used inversely. The last
Chebyshev expression divides by α>0. Other denominators are positive
population sizes and the constant 2. No conclusion exploits division
by zero.

Square roots are only used for positive sizes/degrees and nonnegative
variance/α. All `Real.rpow` bases in moment conditions are absolute
values or positive constants, all moment exponents are ≥1, and n_t^x
has strictly positive base even for x=0. Thus 0^0, negative-base powers,
and negative-root conventions have no effect. As in T50, dMax is a
supremum over a nonempty finite range, so its default value is unused.
Empty index types, infinite or nonintegrable quantities, real liminf/
limsup defaults, logs, infinities cast to reals, rounding, truncated
natural subtraction and default values of partial functions do not
occur. The finite tuples are total functions on Fin 3. Their arbitrary
extensions outside Fin 3 are not part of any expression.

The generated `Paired._proof_1` and `B1._proof_1` are certificates of
`(1+1).AtLeastTwo`, not assumptions about pairings or B1.
`sharpLaw._proof_1` proves all three weights nonnegative using 0<α<1;
`sharpLaw._proof_2` proves their sum is 1. Their source proof bodies
and printed declarations were inspected. There are no hidden
hypotheses or conclusion-encoding data in these proof fields.
