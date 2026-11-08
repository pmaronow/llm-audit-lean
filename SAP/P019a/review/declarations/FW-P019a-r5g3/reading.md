# Blind reading

Saved before opening `claims.json` or `record.json`.

## SAP.P019a.T11

The declaration at `SAP/P019a/Challenge/Part1.lean:86–96` asserts
`T11WholeStatement`, defined at `SAP/P019a/Defs/WholeW2.lean:157–191`.
Its docstring describes three corrected population identities and asymptotic
coverage of the printed Wald interval, under their respective assumptions. It
also describes a correction to the label of negative responders as having no
independent mathematical assertion.

### Objects, definitions, and quantifiers

For every type Ω (in the theorem's arbitrary universe), every measurable-space
structure on Ω, every natural number J, and every population S, the following
four implications/conjunctions hold. A population consists of a probability
measure P on Ω and a measurable observation map

    O : Ω → {0,…,J} × {false,true}³ × {0,…,J+1}.

The coordinates, in order, are W, X, Y, Z, V: W and V are natural-valued
counts; X, Y, Z are Boolean. `T11Observation` uses `Fin (J+1)` and
`Fin (J+2)` for the counts. The projections W and V take the `Fin.val`
natural numbers, and X, Y, Z take the corresponding Boolean coordinates.
Write b(false)=0 and b(true)=1 in ℝ (`bitVal`). Every count used in an
expectation or sample mean is cast from ℕ to ℝ.

For any function f on this finite observation range and any predicate D on
that range, the definitions unfold to

    E[f] = ∫Ω f(O(ω)) dP(ω),
    p(D) = (P{ω : D(O(ω))}).toReal,
    E[f | D] = E[1_D f] / p(D),
    Var(f) = E[f²] − E[f]²,
    Var(f | D) = E[f² | D] − E[f | D]².

Here the integral is Mathlib's real Bochner integral and probabilities are
Mathlib measure values in ℝ≥0∞ converted to ℝ. The observable range has its
finite discrete measurable structure; therefore every f and D here is
measurable, and every such integrand has finite range and is integrable under
P. Define μ=p(X=true), and C_zy={Z=z,Y=y} (`T11Observation.cell`).

The assumptions are separate predicates:

* `monotone`: P-almost surely, Y=true implies X=true.
* `noLiarsDesign`: P-almost surely, V=W+b(X)b(Z), as an equality in ℝ.
* `treatmentIndependent`: for every f:ℕ→Bool→Bool→ℝ and every Boolean z,
  E[1_{Z=z} f(W,X,Y)] = p(Z=z) E[f(W,X,Y)]. This is independence of Z
  and the entire finite-valued triple (W,X,Y).
* `nondegenerate`: for every Boolean z,y, both p(C_zy)>0 and
  Var(V | C_zy)>0, and additionally Var(b(Z))>0 and Var(b(Y))>0.
* `standing`: the conjunction of these four predicates, in the order above.

The finite-law machinery in the closure does not restrict Ω to be finite.
`FiniteLaw A` is a real mass function m on a finite type A, with m(a)≥0 and
Σ_a m(a)=1. `wholeFiniteLaw P O` puts m(t)=P.real(O⁻¹{t}); its proofs
use nonnegativity and the fact that the finitely many measurable fibers
partition Ω. `Study A` packages such a law with natural-valued W,V and
Boolean-valued X,Y,Z functions. `finiteStudy S` takes A to be the finite
observation range and uses its coordinate projections and this exact
pushforward mass. Its sample calculations below depend only on those
coordinate functions, not on any unspoken population hypothesis.

For each n∈ℕ the sampling measure is the finite product

    P_n = ⨂_{i∈Fin n} P

on functions s:Fin n→Ω (`sampleLaw`). Thus all n respondents are independent
and identically distributed with law P. `sampleObservations s` is the
coordinatewise map i↦O(s(i)). For such a sample define

    N_zy = Σ_{i∈Fin n} 1_{Z_i=z,Y_i=y} ∈ ℕ,
    A_z  = Σ_{i∈Fin n} 1_{Z_i=z} ∈ ℕ,
    ybar = (Σ_i b(Y_i))/n,
    gammahat = A_true/n.

`Study.cell` is the conjunction Z=z and Y=y; `cellCount` and `armCount`
are these natural-valued sums. `cellMean` is

    vbar_zy(c) = c                         if N_zy=0,
                (Σ_i 1_{C_zy}(i) V_i)/N_zy otherwise.

`muHat` (`estimate` after applying `sampleObservations`) is

    muhat = ybar + (1−ybar)(vbar_true,false(c1)−vbar_false,false(c0)).

`cellVariance` is zero if N_zy<2, and otherwise is

    s²_zy = [Σ_i 1_{C_zy}(i)(V_i−vbar_zy(0))²]/(N_zy−1).

The subtraction in its denominator is in ℝ. The domain D_n (`T11FiniteDomain`,
then `intervalDomain`) is exactly

    n>0, N_true,false≥2, N_false,false≥2,
    ybar<1, 0<gammahat<1.

`muVarianceHat` (`varianceEstimate`) equals, when the last five conditions
(all except explicit n>0) hold,

    vhat = (1/n) [ ((1−muhat)²/(1−ybar)) ybar
                 +(1−ybar)(s²_true,false/gammahat
                           +s²_false,false/(1−gammahat)) ],

and equals cV otherwise. Its conditions imply n>0. On D_n all denominators
in these formulas are positive and all completions c1,c0,cV are unused.

Let G be Mathlib `gaussianReal 0 1`, the probability measure on ℝ with density
the centered Gaussian density of variance 1 with respect to Lebesgue measure.
`normalCDF(t)` is (G(−∞,t]).toReal. `normalQuantile(u)` is the real infimum
of {x∈ℝ : u≤normalCDF(x)}. Thus for u∈(0,1) it is the usual standard-normal
quantile. No assumption about that set is present in T11.

The constructors and generated declarations in `closure.json` have also been
read, including by `#print` in `scratch/Check.lean`: `FiniteLaw.mk`,
`Study.mk`, `T11Population.mk`, and the listed coordinate projections merely
construct/project the fields described above. `instIsProbabilityMeasureLaw`
returns S's probability proof. `finiteStudy._proof_1` supplies the finite
product's measurable-singleton instance; `T11WholeStatement._proof_1` supplies
the numeral-two `AtLeastTwo` instance; `wholeFiniteLaw._proof_1` proves fiber
mass nonnegative and `._proof_2` proves its total is one. They introduce no
additional propositions to assume.

### The four conclusions, in their precise order

The universal quantifiers Ω, its measurable structure, J, S are outside the
conjunction of the following four clauses. Each clause has its own assumptions;
the assumptions of one clause are not implicitly required by another.

1. If `noLiarsDesign`, then `treatmentIndependent`, then p(Z=false)>0,
   then p(Z=true)>0, the following three identities all hold:

       E[V | Z=true] = E[W] + μ,
       E[V | Z=false] = E[W],
       E[V | Z=true] − E[V | Z=false] = μ.

2. If `monotone`, then p(Y=true)>0, then E[b(X) | Y=true]=1.

3. If `standing`, both of these conclusions hold:

       P_n(D_n) → 1 as n→∞;

   and, for every real α with 0<α<1, and then every three fixed real
   completions c1,c0,cV,

       P_n{ s : D_n(s) and
                  |muhat(s;c1,c0)−μ|
                   ≤ q(1−α/2) sqrt(vhat(s;c1,c0,cV)) }
         → 1−α as n→∞.

   Both probabilities are `.real` values, and both limits mean Mathlib
   `Filter.Tendsto` from the natural-number `atTop` filter to the indicated
   real neighborhood filter. This is coverage of the closed symmetric
   interval after excluding samples outside D_n. It is not finite-n exact
   coverage. The completion quantifiers are inside α's quantifier, but each
   completion is fixed as n varies.

4. If `monotone`, then `noLiarsDesign`, then `treatmentIndependent`, then
   p(C_false,true)>0, then p(C_true,true)>0, then

       E[V | Z=true,Y=true] = E[V | Z=false,Y=true] + 1.

No additional conjunct expresses the label-only correction mentioned in the
docstring.

### Totalization and junk-value audit

* Real division has 0⁻¹=0. Thus an event conditional mean at a zero-probability
  event is defined as zero. Every population conditional mean or conditional
  variance used in a conclusion is protected by positive event probabilities,
  directly or through `nondegenerate`. The predicates themselves are total
  even for zero-probability events, but positivity excludes those cases when
  the predicate is assumed.
* Empty-sample `ybar` and `gammahat` are 0/0=0. Empty cell means are the supplied
  c1/c0 (or zero where `cellVariance` internally supplies zero). Variances in
  cells of size 0 or 1 are explicitly zero. The whole variance estimate is cV
  outside its formula's domain. D_n excludes every such denominator failure;
  n=0 fails D_n and affects no limit at infinity. On D_n the three arbitrary
  completions have no effect.
* `Real.sqrt` is total and equals zero on nonpositive real arguments. On D_n,
  the displayed vhat is a sum of nonnegative terms divided by a positive n,
  so negative-square-root totalization cannot affect the coverage event.
  vhat can equal zero in a particular sample; sqrt(0)=0 is mathematically
  legitimate and defines a zero-width interval.
* An unrestricted real `sInf` can take its totalized fallback on an empty or
  unbounded-below set. The only quantile arguments here are 1−α/2∈(1/2,1),
  for which the standard-normal CDF's quantile set is nonempty and bounded
  below. Hence no fallback value is used in this theorem, despite the old
  `normalQuantile` definition's docstring mentioning an explicit premise.
* `ENNReal.toReal ∞=0` would corrupt an infinite measure value. P and every
  finite product P_n are probability measures, as is G, so all converted
  values and fiber masses are finite; this convention is never used at ∞.
* A real Bochner integral of a nonintegrable function is totalized to zero.
  Every integrand here is a measurable function of a finite observation, or
  an indicator of such a predicate, under a probability measure, so all are
  integrable. There is no nonintegrability loophole.
* J and n are natural numbers. J+1 and J+2 give nonempty observable coordinate
  types even at J=0. Natural counts are cast exactly into ℝ. No natural or
  integer truncated subtraction occurs: every “−1”, “1−ybar”, and
  “1−gammahat” in a denominator is real subtraction. Negative-response cell
  sizes required by D_n are natural inequalities.
* `Fin 0` is empty and the unique empty sample has the usual zero sums; its
  product measure is the probability law on that singleton function space.
  A population probability measure precludes an empty underlying Ω. J=0
  makes `standing` impossible because the control-cell count is then
  constant, but J is universally quantified and may be positive; that
  endpoint alone does not make the theorem globally vacuous.
* No `Real.log`, real noninteger power, `sSup`, `limsup`, `liminf`, partial
  function default, or other relevant totalization occurs in the closure.
  All finite projections are defined on genuine finite types.
