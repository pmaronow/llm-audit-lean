# Blind mathematical reading

Written from the Defs and Challenge files and Mathlib definitions before opening
`claims.json` or `record.json`. The Challenge contains exactly two theorem stubs,
`SAP.P021.T1` and `SAP.P021.T2`.

## Shared objects and definitions

For a real number B and a natural number K the state space is

    X(B,K) = [-B,B] × ({0,...,K-1} × {false,true}).

The first coordinate is a subtype of the real line with its usual subspace
topology and Borel sigma algebra. The finite degree-index and Boolean spaces
have their discrete topology and full sigma algebra. Products have the product
topology and product sigma algebra. A state x=(y,(k,s)) has outcome Y(x)=y,
numerical degree d(x)=k+1, and sampling indicator S(x)=1 if s=true and 0 otherwise.
Thus degrees are positive integers at most the single fixed K; there are no
zero-degree states. The outcome bound is the single fixed finite B. X is compact.

For a measure F on X define, for every k in {0,...,K-1},

    mu = integral Y dF,
    p_k = integral 1_{degree-index=k} dF,
    s_k = integral 1_{degree-index=k} S dF,
    m_k = integral 1_{degree-index=k} Y dF,
    t_k = integral 1_{degree-index=k} S Y dF,
    h   = integral S dF,
    pi_k = s_k / p_k,
    u_k  = m_k / p_k,
    v_k  = t_k / s_k,
    q_k  = s_k / h,
    A = {k : p_k > 0},
    C = {k : q_k > 0}.

Here `populationMean=mu`, `degreeMass=p`, `sampledMass=s`,
`degreeMoment=m`, `sampledMoment=t`, `sampleFraction=h`,
`samplingProbability=pi`, `degreeMean=u`, `sampledMean=v`,
`observedDegreeMass=q`, `degreeSupport=A`, and `observedSupport=C`.
The support sets are finite subsets of Fin K, not new infinite index types.

All integrals are Mathlib real Bochner integrals. Mathlib assigns zero to a
nonintegrable function, and real division is total with x/0=0. In these theorems
F is a probability measure, which means F(X)=1. The displayed integrands are
bounded Borel functions, hence integrable; continuous test functions are also
bounded and integrable because X is compact. Positive-mass conditions determine
where the ratios have a conditional-probability or conditional-mean meaning.
They are not assertions about conditionals on null events.

`Ignorability F` means exactly

    for every k, p_k>0 implies (v_k=u_k and pi_k>0).

It asserts equality of conditional outcome means, not conditional independence
of the entire outcome and the sampling indicator. `KnownSampling F c f` means

    for every k, p_k>0 implies pi_k=c f(k),

where c is real and f maps Fin K to the reals. There is no additional sign,
nonzero, or normalization hypothesis on c or f.

For N a natural number and z:Fin N -> X, put

    E_z(g) = (sum_{j=0}^{N-1} g(z(j))) / N,
    J_z = {j in Fin N : the sample mark of z(j) is true},
    V(z) = (sum_{j in J_z} Y(z(j))/d(z(j))) /
           (sum_{j in J_z} 1/d(z(j))).

These are `empiricalAverage`, `sampleSet`, and `vhEstimator`. Repeated states
are allowed: units are indexed, and z need not be injective. A zero N or empty
J_z would give a totalized value, but T2 excludes both possibilities in its
applicable instances.

`TendstoInMeasure P U atTop W` is Mathlib convergence in measure: for every
positive extended-real epsilon, the P measure of
{omega : epsilon <= edist(U_r(omega),W(omega))} tends to zero as r tends to
infinity. For real-valued functions on a probability space this is convergence
in probability, equivalently the usual condition for every real epsilon>0.
`Tendsto ... atTop (nhds L)` is ordinary convergence of a sequence to L.
`almost every` uses the measure's almost-everywhere filter (null exceptional
set). No independence is part of either definition.

## SAP.P021.T1

In the following exact quantifier order: for every real B, every natural K,
every measure F on X(B,K), if F(X)=1, then for every real c and every function
f:Fin K -> R, if Ignorability F and KnownSampling F c f, all the following hold
as one conjunction:

1. h>0.
2. A=C.
3. c != 0.
4. For every k in A, all five statements hold:
   s_k>0; c f(k)>0; f(k)!=0;

       p_k = q_k h / pi_k;
       p_k = (h/c) (q_k/f(k)).

5. sum_{k in A} q_k/f(k) = c/h.
6. sum_{k in A} q_k/f(k) != 0.
7. mu = (sum_{k in A} v_k (q_k/f(k))) /
        (sum_{k in A} q_k/f(k)).
8. mu = (sum_{k in A} u_k (h/c) (q_k/f(k))) /
        (sum_{k in A} (h/c) (q_k/f(k))).
9. (sum_{k in A} u_k (h/c) (q_k/f(k))) /
   (sum_{k in A} (h/c) (q_k/f(k)))
   equals (sum_{k in A} u_k (q_k/f(k))) /
          (sum_{k in A} q_k/f(k)).

There are no separately supplied hypotheses B>=0 or K>0 in T1. Existence of
a probability measure on X forces X to be nonempty, and thus forces both.
For a probability measure the finite degree strata partition X, so A is
nonempty. The conclusions explicitly justify every division on a supported
stratum and the inverse-profile denominator; they do not require c or f to
be positive individually.

## SAP.P021.T2

The theorem is universally polymorphic in a type Omega and an arbitrary
measurable-space structure on Omega. For each such fixed Omega it asserts a
conjunction of the following random and deterministic implications.

### Random implication, in quantifier order

For every real B, natural K, and measure P on Omega, assume P(Omega)=1,
B>=0, and K>0. For every measure F on X(B,K), assume F(X)=1. For every
function N:N->N, assume N(r)>0 for every r. For every family

    z : (r:N) -> Omega -> Fin(N(r)) -> X(B,K),

assume all three of the following:

* For every r and every j:Fin(N(r)), omega -> z(r,omega,j) is measurable.
* For every r, J_{z(r,omega)} is nonempty for P-almost every omega.
  The exceptional null set can be presented separately at each r. Since r
  is countable, this also gives one full-measure set on which all stages
  have nonempty samples.
* For every continuous real function g on X, E_{z(r,omega)}(g) converges
  in P-probability to the constant integral g dF.

Then for every pair of real numbers c,a, if a!=0, Ignorability F holds, and

    for every k with p_k>0, pi_k = c (a (k+1)),

the real random variables V(z(r,omega)) converge in P-probability to the
constant mu. This is the entire random conclusion.

### Deterministic implication, in quantifier order

For every real B and natural K, assume B>=0 and K>0. For every measure F on
X(B,K), assume F(X)=1. For every N:N->N, assume N(r)>0 for every r. For every
family

    z : (r:N) -> Fin(N(r)) -> X(B,K),

assume (i) J_{z(r)} is nonempty for every r, and (ii) for every continuous
real g on X, E_{z(r)}(g) converges ordinarily to integral g dF. Then for
every pair of real numbers c,a, if a!=0, Ignorability F holds, and
pi_k=c(a(k+1)) for every k with p_k>0, V(z(r)) converges ordinarily to mu.

This branch does not depend on Omega or P. Both branches use one common
bounded outcome and finite-degree state space throughout their sequence.
There is no hypothesis N(r)->infinity, no fixed relation between r and N(r),
no graph or recruitment process, no independent sampling hypothesis, and no
assumption that the estimator already converges. Convergence of the joint
empirical laws is the test-function premise. All sampled inverse-degree
denominators are positive on the specified nonempty-sample events.

## Mathlib sources followed

* `MeasureTheory/MeasurableSpace/Instances.lean`: Fin and Bool have the full
  sigma algebra.
* `MeasureTheory/MeasurableSpace/Constructions.lean`: subtype sigma algebra
  is the pullback by inclusion; product sigma algebra is generated by the
  coordinate projections.
* `MeasureTheory/Constructions/BorelSpace/Basic.lean`: the real sigma algebra
  is Borel, and the subtype/finite factors have the corresponding Borel
  instances.
* `MeasureTheory/Measure/Typeclasses/Probability.lean`: probability means
  measure of the whole space is one; this implies a nonempty underlying type.
* `MeasureTheory/Function/L1Space/Integrable.lean`: integrability means
  almost-everywhere strong measurability and finite norm integral.
* `MeasureTheory/Integral/Bochner/Basic.lean`: the real Bochner integral uses
  the L1 integral for integrable functions and zero otherwise.
* `MeasureTheory/Function/ConvergenceInMeasure.lean`: the positive-threshold
  exceptional-set definition, including its equivalent real-distance form.
* `Order/Filter/Defs.lean` and `Order/Filter/AtTopBot/Defs.lean`: Tendsto is
  the map-filter comparison and atTop on N is generated by upper tails.
