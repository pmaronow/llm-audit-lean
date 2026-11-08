# Blind reading

Saved at stage 1, before opening `claims.json` or `record.json`. Sources read:
`closure.json`, `SAP/P001b/Challenge/Part1.lean`, the relevant definitions in
`Defs/Part1.lean`, `Defs/Part3.lean`, and `Defs/WholeW1.lean`, and both import
aggregators. `scratch/Blind.lean` prints all 57 distinct declarations named in
the five closures; its successful output is `scratch/blind-print.txt`.
Generated proof declarations were read as well: they prove numeral
`Nat.AtLeastTwo` facts (for the numerals 2, 3, 4, 5, 8, 12, 20, 24, 25, 30,
40, 55, 60, 65, 100, as applicable) or the usual scalar-tower instance for
extended nonnegative reals. They add no statistical assumptions or definitions.

Throughout, for a measure μ write P(H) = (μ(H)).toReal, a real number. Every
general probability assertion assumes μ is a probability measure, so every set
has finite measure and this conversion preserves its value. Set complements
are relative to the whole sample space. All subtractions in the conclusions are
real subtractions. Integrals are Mathlib Bochner integrals. Real infinite sums
are unconditional limits of finite subsums, when they exist. Universes are
arbitrary; type and typeclass binders are universally quantified.

## SAP.P001b.T20

Source: `Challenge/Part1.lean:9–20`, `Defs/WholeW1.lean:23–155`, and
`Defs/Part1.lean:12–14`. There are four conjoined assertions, in this order.

1. General measurable covariates. For every measurable sample space Ω,
   measurable covariate space E, probability measure μ on Ω, X : Ω → E and
   D : Ω → ℝ, assume, in order: X measurable; D measurable; for every ω,
   D(ω) = 0 or D(ω) = 1; P(D = 0) > 0; P(D = 1) > 0. Then for every
   p : E → ℝ assume: p measurable; D integrable; p ∘ X integrable; and for
   every measurable H ⊆ E,
   ∫[X⁻¹(H)] D dμ = ∫[X⁻¹(H)] p(X) dμ. This is the integral characterization
   of a conditional expectation of D given X.

   Define the marginal law Q = μ.map X and, for d = 0,1, define
   Q_d = μ(D = d)⁻¹ • ((μ.restrict {D = d}).map X), with inverse and scalar
   multiplication in the extended nonnegative reals. The conclusions are:

   - If there exists a real ε > 0 such that ε < p(X(ω)) < 1 − ε for μ-almost
     every ω, then Q_1 ≪ Q, Q ≪ Q_1, Q_0 ≪ Q, and Q ≪ Q_0. Here ≪ means
     every set null for the second measure is null for the first.
   - For every measurable H ⊆ E with P(X ∈ H) > 0, both implications hold:
     if p(X) = 0 almost everywhere for μ restricted to {X ∈ H}, then
     P(X ∈ H, D = 1) = 0 and P(X ∈ H, D = 0) > 0; if p(X) = 1 almost
     everywhere on that restriction, then P(X ∈ H, D = 0) = 0 and
     P(X ∈ H, D = 1) > 0. These two implications have no uniform-positivity
     hypothesis.

2. Discrete covariates. For every Ω,E,μ,X,D as above, assume in addition
   that E is countable and every singleton of E is measurable. The hypotheses
   are measurability of X,D, binary D at every point, and positive mass in
   both arms. Write q(x) = P(X = x), j_d(x) = P(X = x,D = d), r_d = P(D = d),
   a_d(x) = j_d(x)/r_d, and
   p(x) = j_1(x)/q(x) if q(x) > 0, and 1/2 otherwise.
   Put S = {x : q(x) > 0} and S_d = {x : a_d(x) > 0}. Then all five clauses hold:

   - S_1 = {x ∈ S : p(x) > 0}.
   - S_0 = {x ∈ S : p(x) < 1}.
   - S_1 = S_0 if and only if, for every x ∈ S, 0 < p(x) < 1.
   - If there exists ε > 0 with ε < p(x) < 1 − ε for every x ∈ S, then S_1 = S_0.
   - If S is finite and S_1 = S_0, there exists ε > 0 with those same bounds
     for every x ∈ S. Finiteness is an antecedent of this last clause only.

3. Explicit infinite law. On Ω = ℕ × Bool with the full powerset sigma algebra,
   let t_k = (1/3)^(k+1), c_k = (1/2)^(k+2). Define μ as the countable sum,
   over (k,b), of a Dirac measure at (k,b) multiplied by
   ENNReal.ofReal(t_k) if b = true and ENNReal.ofReal(c_k) if b = false.
   Let X(k,b) = k and D(k,b) = 1 for true and 0 for false. The assertion is
   an unconditional conjunction of all of the following:

   - Both t and c are summable, and each has sum 1/2.
   - μ is a probability measure and every subset of Ω is measurable.
   - For every k, P(X = k,D = 1) = t_k and P(X = k,D = 0) = c_k.
   - P(D = 0) = P(D = 1) = 1/2.
   - {k : P(X = k) > 0}, {k : P(X = k,D = 1)/P(D = 1) > 0}, and
     {k : P(X = k,D = 0)/P(D = 0) > 0} are all ℕ.
   - There does not exist ε > 0 such that, for every k,
     ε < p(k) < 1 − ε, where p(k) is the positive-cell ratio defined above
     (and 1/2 on any zero-mass cell).

   In ordinary arithmetic p(k) = t_k/(t_k+c_k); t_k/c_k = (4/3)(2/3)^k,
   so the absence of a uniform lower bound has a genuine limiting mechanism.
   The theorem does not itself state that limit.

4. Coherent support algebra. For every type E, nonnegative real functions
   t,c : E → ℝ, and real a,b > 0, equality of {x : t(x)/a > 0} and
   {x : c(x)/b > 0} is equivalent to
   ∀x, t(x)+c(x) > 0 → 0 < t(x)/(t(x)+c(x)) < 1.
   Also, existence of a real ε > 0 with ε < t(x)/(t(x)+c(x)) < 1 − ε on
   every positive-total point implies that support equality. This is a
   universal algebraic assertion: it does not assume t,c integrate to a,b,
   or that they arise from a measure. It applies to such density versions
   when those relations are supplied externally.

The docstring describes a theorem about overlap modulo null sets for general
covariates, exact positive-mass supports for discrete covariates, the finite
converse, the infinite counterexample to the uniform-bound converse, and exact
support identities for coherent density versions. It explicitly assumes the
usual measure-theoretic conditions.

Junk-value audit:

- `toReal ∞ = 0` cannot affect the quantified probability laws, and the
  explicit infinite law is itself asserted to be a probability measure.
- Real division by zero returns zero. Arm-PMF denominators are positive by
  hypothesis (and equal 1/2 in the fixed example). The propensity divides only
  on q(x) > 0 and explicitly assigns 1/2 elsewhere. Support and positivity
  statements test the propensity only on S. The coherent algebra tests its
  t/(t+c) ratio only when t+c > 0; a and b are positive.
- The extended-real inverse in the conditional arm law would be ∞ at zero;
  here its argument is finite and positive. No ambiguous zero/infinity
  normalization is used.
- `ENNReal.ofReal` clips negative inputs to zero. The explicit weights t_k,c_k
  are strictly positive ordinary geometric powers; clipping changes nothing.
- Bochner integrals are zero for nonintegrable inputs, but the conditional
  expectation characterization requires integrability explicitly, including
  the candidate version. Restricted integrals inherit integrability.
- A real `tsum` defaults to zero for a nonsummable family; explicit summability
  is a conjunct for both geometric sums. All powers have natural exponents
  and positive real bases. There is no real-power domain issue.
- General probability spaces cannot be empty. E cannot be empty when X
  exists on such a space. The purely algebraic assertion allows empty E
  or t = c = 0, yielding harmless tautological special cases without making
  its other instances vacuous. The geometric index type is infinite.
- No truncated subtraction, logarithm, square root, real `rpow`, infimum,
  supremum, limsup/liminf, or default-valued partial function occurs.

## SAP.P001b.T21

Source: `Challenge/Part1.lean:22–26`, `Defs/Part3.lean:27–56`, and the finite
probability/voting definitions in `Defs/Part1.lean:30–66`.

There are no external hypotheses and no existentially chosen model: this
theorem asserts facts about the following fixed four-atom probability table.
The index i ranges over Fin 4, with atoms 0,1,2,3. The weights w, latent
electorate types U, displayed binary gender D, potential percentage shares
Y_0,Y_1, and observed share Y are:

| i | w_i | U_i | D_i | Y_0(i) | Y_1(i) | Y(i) |
|---|---|---|---|---|---|---|
| 0 | 3/8 | 0 | 0 | 20 | 25 | 20 |
| 1 | 1/8 | 0 | 1 | 20 | 25 | 25 |
| 2 | 1/8 | 1 | 0 | 60 | 65 | 60 |
| 3 | 3/8 | 1 | 1 | 60 | 65 | 65 |

For any real d, Y_d(i) = 20 + 40 U_i + 5d, and Y(i) = Y_{D_i}(i).
For any predicate H on these four atoms, P_w(H) = Σ_i 1_H(i)w_i;
E_w(Z) = Σ_i w_i Z_i; and
M_w(Z,V,v) = [Σ_i 1_{V_i=v}w_i Z_i]/P_w(V=v).
The covariate used for conditional independence is X_i = 0.
For displayed treatment b : Bool, the leaflet is the triple (0,b,false).
For voter k : Fin 100, that voter casts the counted vote exactly when
(k.val : ℝ)+1 ≤ 20+40U_i+5·(if b then 1 else 0).
The counted percentage is the real cast of the cardinality of the voters
satisfying that inequality. Because the electorate has 100 voters, this
count is numerically its percentage.

The theorem is the conjunction, in order, of:

1. Every w_i ≥ 0 and Σ_i w_i = 1.
2. For every b, the leaflet has first component zero, second component b,
   and third component false.
3. For every i,b, the counted vote equals Y_{1}(i) for true and Y_{0}(i)
   for false.
4. For every i, Y(i) = Y_1(i)D_i + Y_0(i)(1−D_i).
5. For every i, Y_0(i),Y_1(i) ∈ [0,100], and Y(i) ∈ [0,100].
6. For every i, Y_1(i)−Y_0(i) = 5.
7. P_w(D=1) = 1/2 and P_w(D=0) = 1/2.
8. M_w(D,X,0) = 1/2 for constant X=0.
9. P_w((Y_0,Y_1)=(60,65),D=1) = 3/8;
   P_w((Y_0,Y_1)=(60,65)) = 1/2; and
   P_w((Y_0,Y_1)=(60,65))P_w(D=1) = 1/4.
10. The following universal factorization property fails for Z=(Y_0,Y_1),
    V=D, and X=0:
    for every x : ℝ, z : ℝ×ℝ, v : ℝ with P_w(X=x)>0,
    P_w(X=x,Z=z,V=v)P_w(X=x) = P_w(X=x,Z=z)P_w(X=x,V=v).
    Since the underlying support is finite, factorization for all singleton
    values is the usual finite conditional independence.
11. M_w(Y,D,1)=55 and M_w(Y,D,0)=30; their difference is 25.
12. E_w(Y_1−Y_0)=5 and the real numbers 25 and 5 are unequal.

The docstring calls this a counterexample to a reading of complete information
coding as forcing ignorability. It describes fully coded leaflets, positivity,
conditional dependence, contrast 25, and average effect 5. The formal leaflet
triple is explicit; the information/coding interpretation is not a separate
predicate. The false component is the representation available for the stated
no-acquaintance condition; all voter responses use only b and U_i.

Junk-value audit:

- The weights are actual nonnegative normalized real probabilities, not signed
  formal weights. Fin 4 and Fin 100 are nonempty concrete finite types.
- Every used conditional-mean denominator is 1 (constant X) or 1/2 (the
  treatment arms), so totalized real division introduces no null-cell value.
- Failure of the factorization property is meaningful: its positive-mass
  conditioning cell is X=0, with mass one. No empty or zero-mass cell is used.
- The voter index and vote-count casts are ordinary injections from naturals
  to reals; `(k.val + 1 : ℝ)` is real addition after casting, not a truncated
  natural subtraction. Counts lie between 0 and 100.
- The formula for Y_d is defined for every real d and can leave [0,100] for
  nonbinary d. All vote-share range claims use d=0 or d=1 only.
- There are no integrals, infinite sums, `toReal`, partial functions, or
  problematic transcendental/extremum/limit operations in this closure.

## SAP.P001b.T22

Source: `Challenge/Part1.lean:28–42`, `Defs/WholeW1.lean:157–203`, the full
T21 closure just unfolded above, and the conditional-expectation factorization
definition at `Defs/WholeW1.lean:25–36`. It has three conjoined clauses.

1. An explicit model with a latent electorate variable. It asserts every
   numerical, voter-counting, range, and independence-failure assertion of
   T21 above, using exactly the four-row table w=(3/8,1/8,1/8,3/8),
   U=(0,0,1,1), D=(0,1,0,1), Y_d=20+40U+5d, X=0, leaflet (0,b,false),
   and voter rule k+1≤20+40U+5·1_b. In addition:
   - There exists a function R : ℝ → ℝ → ℝ → ℝ such that for every i : Fin 4
     and every real d, Y_d(i)=R(0,d,U_i).
   - 1/4 < E_w[D | X=0] < 1−1/4, with conditional expectation evaluated by
     the finite weighted-sum ratio. No measurability constraint is placed on
     the existential R, although the affine R(x,d,u)=20+40u+5d is available.

2. Response determined by the covariate. For every measurable Ω,E,
   probability measure μ, X : Ω→E with a proof hX of measurability, and
   D : Ω→ℝ, assume D measurable. Then for every R : E→ℝ→ℝ, assume both
   x↦R(x,0) and x↦R(x,1) are measurable. Put Z(ω)=(R(X(ω),0),R(X(ω),1)).
   For every measurable A⊆ℝ×ℝ and B⊆ℝ, the conclusion is
   E_μ[1_{Z∈A,D∈B} | σ(X)] = E_μ[1_{Z∈A} | σ(X)] ·
   E_μ[1_{D∈B} | σ(X)] almost everywhere under μ. Here σ(X) is literally
   the comap of E's sigma algebra under X. Conditional expectation is
   Mathlib's conditional expectation relative to that sub-sigma algebra.
   There is no binary-D or positivity hypothesis in this clause, and none
   is needed for the stated independence of a function of X.

3. Discrete identification. For every measurable Ω,E with E countable and
   all its singletons measurable, probability measure μ, measurable X:Ω→E,
   and real functions Y_0,Y_1,D on Ω, assume, in order: Y_0 measurable;
   Y_1 measurable; D measurable; Y_0 integrable; Y_1 integrable;
   ∀ω, D(ω)=0 or D(ω)=1; existence of ε>0 such that for every x with
   q(x)=P(X=x)>0,
   ε < p(x) < 1−ε, where p(x)=P(X=x,D=1)/q(x) when q(x)>0 and 1/2
   otherwise; and conditional independence of Z=(Y_0,Y_1) and D given X.
   This last hypothesis means exactly the indicator conditional-expectation
   factorization in clause 2, for every measurable A⊆ℝ×ℝ and B⊆ℝ.

   Define the observed response Y=Y_1D+Y_0(1−D), the cell
   C_{d,x}={ω:X(ω)=x and D(ω)=d}, and
   m_d(x)=[∫[C_{d,x}] Y dμ]/P(C_{d,x}) if P(C_{d,x})>0, and zero otherwise.
   The conclusion is summability of x↦m_0(x)q(x) and x↦m_1(x)q(x), and
   ∫(Y_1−Y_0)dμ = Σ'_x m_1(x)q(x) − Σ'_x m_0(x)q(x).

The docstring explicitly promises all three canonical clauses (without yet
consulting the canonical source), states the usual measure-theoretic conditions,
and describes genuine positive-cell observed means and absolute convergence.

Junk-value audit:

- Clause 1 inherits all the safe finite conventions described for T21.
  Its new ratio has denominator one; R need not use any partial operation.
- Every use of P has a probability-measure hypothesis. Thus `toReal ∞=0`
  cannot alter probabilities or positivity tests.
- The propensity explicitly chooses 1/2 on null X-cells and the arm mean
  explicitly chooses zero on null joint cells. Positivity guarantees both
  arm cells have positive mass on every positive marginal cell. Elsewhere
  the marginal weighting q(x)=0 removes the chosen version from the sums.
- The integrals in m_d and the ATE are defined as actual integrals:
  integrable Y_0,Y_1 and measurable binary D imply integrable Y and
  integrable difference. Their restrictions remain integrable.
- Mathlib conditional expectation defaults to zero when the proposed sigma
  algebra is not a sub-sigma algebra, the trimmed measure is not sigma-finite,
  or its argument is not integrable. Measurable X supplies the sub-sigma
  algebra, probability measures give finite trimmed measures, and every
  indicator being conditioned is measurable and bounded. Thus none of the
  defaults can manufacture the independence hypothesis or conclusion.
- The two real `tsum`s have explicit `Summable` conclusions, so they cannot
  rely on the default zero for divergent sums. For real families this is
  unconditional/absolute convergence.
- The probability space and a covariate type receiving X cannot be empty.
  A countable E may have unused/null values, handled by the stated versions.
  The separate universal response clause permits arbitrary measurable D.
- All subtraction is real. No log, sqrt, real power, infimum/supremum,
  limsup/liminf, or default-valued partial function occurs.

## SAP.P001b.T23

Source: `Challenge/Part1.lean:44–47`, `Defs/Part3.lean:61–70`, and
`Defs/Part1.lean:12–14`. For every measurable space Ω, probability measure μ,
and sets A,B⊆Ω, assume A measurable, then B measurable. The conclusion is the
conjunction, in order, of:

1. A⊆B if and only if for every ω, ω∈A implies ω∈B.
2. If A⊆B then (μ A).toReal≤(μ B).toReal.
3. If A⊆B then (μ(B\A)).toReal=(μ B).toReal−(μ A).toReal.
4. (μ ∅).toReal=0.
5. 0≤(μ A).toReal≤1.
6. (μ(Aᶜ)).toReal=1−(μ A).toReal.
7. (μ(A∪B)).toReal=(μ A).toReal+(μ B).toReal−(μ(A∩B)).toReal.
8. If A⊆B and A≠B then it is false that for every ω, ω∈B implies ω∈A.

The docstring describes the corrected direction of the subset gloss, basic
probability rules, inclusion-exclusion, and failure of the reversed implication
for every proper subset. The first clause unfolds the definition of subset;
the final clause asserts the genuine set-theoretic failure of reverse inclusion,
not a positive-probability gap. Proper subsets can have equal probability.

Junk-value audit: μ is a probability measure, so `toReal ∞=0` never applies.
Differences are in ℝ rather than truncated subtraction; the subset condition
ensures the difference in clause 3 is nonnegative. Complements and empty sets
are ordinary measurable events. The sample space cannot be empty. Empty A or B,
null strict set differences, and A=B are legitimate special cases; the proper
subset antecedent in clause 8 is satisfiable on a two-point space. There are no
divisions, integrals, infinite sums, casts, partial functions, transcendental
operations, infima/suprema, or limits.

## SAP.P001b.T24

Source: `Challenge/Part1.lean:49–52`, `Defs/Part3.lean:72–91`, and
`Defs/Part1.lean:12–14,76–78`. The theorem conjoins these three assertions.

1. For every measurable space Ω, probability measure μ on Ω, countable type
   ι, and family A:ι→Set Ω, assume, in order, that every A_i is measurable;
   every A_i is nonempty; A_i,A_j are disjoint whenever i≠j; and ⋃_i A_i=Ω.
   Then for every measurable B⊆Ω, all four clauses hold:
   - P(B)=Σ'_i P(B∩A_i).
   - If every P(A_i)>0, then
     P(B)=Σ'_i [P(B∩A_i)/P(A_i)]P(A_i).
   - For every measurable C⊆Ω, P(C)≥0;
     [C and Cᶜ both nonempty] iff [C≠∅ and C≠Ω]; and
     P(B)=P(B∩C)+P(B∩Cᶜ).
   - P(∅)≥0 and it is not true that P(∅)>0.
   The latter two clauses are syntactically under the family hypotheses,
   although the identities themselves do not need that family.
2. For every type Ω and every A⊆Ω, define a family F of subsets C⊆Ω by
   C∈F iff C is nonempty and (C=A or C=Aᶜ). Then every member of F is
   nonempty; any two distinct members are disjoint; and ⋃₀F=Ω. This is a
   set of subsets, not an indexed pair; empty members and repeated sets
   are discarded. No probability or measurable-space hypothesis is used
   in this purely set-theoretic clause.
3. The real-number equality 1/8+1/12=5/24.

The docstring claims countable total probability using conditional ratios on
positive cells and a repaired event/complement partition after removing empty
members. It does not describe any particular probability model realizing the
last arithmetic equality.

Junk-value audit:

- Every probability is `(μ H).toReal` with μ a probability measure, so infinity
  does not get converted to zero.
- The conditional ratios occur only after a hypothesis that all denominators
  are positive. Real division by zero therefore cannot affect that clause.
  Nonempty cells are not assumed to have positive mass in the first sum.
- The real sums default to zero if nonsummable. Here nonnegative disjoint-cell
  probabilities have finite partial sums bounded by one, hence are summable;
  positive-cell cancellation makes the second family termwise the first.
  No divergence is being used, although summability is not separately stated.
- An empty ι cannot satisfy the covering hypothesis on a probability space.
  A one-cell family can, and two or countably many positive cells can as well.
  In the second, purely set-theoretic clause Ω may be empty: F is then empty
  and its union is empty=Ω, which is correct.
- The sum in clause 3 is ordinary rational arithmetic in ℝ with fixed nonzero
  denominators. There is no integrability convention, truncated subtraction,
  log, sqrt, real power, infimum/supremum, limsup/liminf, cast, or partial
  function default in this statement.

Stage-2 technical supplement to T20's junk-value audit: the installed Mathlib's
`Measure.map` (`MeasureTheory/Measure/Map.lean:91–106`) uses a measurable
representative for an almost-everywhere measurable map. For a map that is not
almost-everywhere measurable, it returns zero when the source measure is zero,
and an arbitrary Dirac mass otherwise. Every X passed to a map in T20 is
measurable, also for the restricted source measure, so this fallback cannot be
reached. This additional implementation check does not change the blind
mathematical reading or the claim comparison.
