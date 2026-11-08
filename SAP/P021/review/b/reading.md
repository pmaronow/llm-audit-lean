# Blind reading of the Challenge statements

This file was written from `SAP/P021/Defs.lean`, `Defs/Part1.lean`,
`Defs/Part2.lean`, `Challenge.lean`, and `Challenge/Part1.lean`, before reading
`claims.json` or `record.json`.

## Common objects and all SAP definitions

For a real number B and natural number K, the state space is

    X(B,K) = [-B,B] × ({0,...,K-1} × {false,true}).

The first factor is a subtype of the real numbers, with its subspace topology
and measurable structure. The other two factors have discrete topologies and
all subsets measurable; products carry their usual product structures. Write a
state as x=(y,(k,b)). Its outcome is Y(x)=y, its numerical degree is d(k)=k+1,
and its sample mark is S(x)=1 if b=true and 0 otherwise. Write
I_k(x)=1 if the degree index of x is k and 0 otherwise, and
J_k(x)=I_k(x)S(x). In particular all numerical degrees are positive integers,
at most K. The outcome is bounded by B in absolute value whenever a state
exists. The space is compact, including when it is empty.

For a measure F on this space, the definitions are the following real Bochner
integrals and real quotients:

    mu = populationMean F = integral Y dF,
    p_k = degreeMass F k = integral I_k dF,
    t_k = sampledMass F k = integral J_k dF,
    u_k = degreeMoment F k = integral I_k Y dF,
    v_k = sampledMoment F k = integral J_k Y dF,
    s = sampleFraction F = integral S dF,
    pi_k = samplingProbability F k = t_k/p_k,
    m_k = degreeMean F k = u_k/p_k,
    mS_k = sampledMean F k = v_k/t_k,
    q_k = observedDegreeMass F k = t_k/s.

`degreeSupport F` is the finite set H={k : p_k>0}.
`observedSupport F` is the finite set Hobs={k : q_k>0}.

`Ignorability F` means: for every k, if p_k>0, then BOTH
mS_k=m_k and pi_k>0. This is equality of conditional means, with strict
positivity of conditional sampling, rather than full conditional independence.
`KnownSampling F c f`, for c real and f:{0,...,K-1}->R, means: for every k,
if p_k>0, then pi_k=c f(k). There is no independent positivity or nonzero
assumption on c or f, and nothing is required on zero-mass strata.

Mathlib `IsProbabilityMeasure F` means F(X)=1. Its real Bochner integral
is defined to be zero if the integrand is not integrable; here, under the
probability hypotheses, all the displayed coordinate and indicator integrands
are measurable and bounded and hence genuinely integrable. Real division is
totalized, so division by zero is zero. Conditional quantities on null strata
are thus formally defined but the hypotheses and sums involving them are
restricted as specified above. Under ignorability and a probability law,
H is nonempty, s>0, and t_k>0 on H, so the conditional expressions actually
used have nonzero denominators.

For a finite population z:{0,...,N-1}->X and any real function g on X,

    empiricalAverage z g = (sum_{j=0}^{N-1} g(z(j)))/N.

`sampleSet z` consists precisely of indices j whose sample mark is true.
Writing A for that set, the estimator is

    VH(z) = (sum_{j in A} Y(z(j))/d(z(j))) /
            (sum_{j in A} 1/d(z(j))).

For a measurable space Omega, a measure P on Omega, a law F on X, a sequence
N_r of natural numbers, and populations z_r(omega):Fin(N_r)->X,
`EmpiricalWeakInProbability P F N z` means: for EVERY continuous real function
g on X, the random variables empiricalAverage(z_r(omega),g) converge in
P-measure to the constant integral g dF as r tends to infinity. This means
for every epsilon>0, the P-measure of the set where the absolute error is
at least epsilon tends to zero. All continuous test functions are bounded
because X is compact. Mathlib `TendstoInMeasure` is defined using extended
distance thresholds; on real-valued functions under a probability measure this
has exactly the preceding usual meaning. It does not itself assert measurability;
the random population coordinates are separately assumed measurable in T2.
`Tendsto ... atTop (nhds L)` is ordinary sequential convergence to L.

Sources followed in Mathlib include
`MeasureTheory/Measure/Typeclasses/Probability.lean:64`,
`MeasureTheory/Integral/Bochner/Basic.lean:155`,
`MeasureTheory/Integral/Bochner/Basic.lean:204`,
`MeasureTheory/Function/ConvergenceInMeasure.lean:57`,
`MeasureTheory/MeasurableSpace/Instances.lean:26,34`,
`Topology/Defs/Induced.lean:76`, and `Topology/Order.lean:575,584`.

## SAP.P021.T1

Quantifiers, in order: for every real B, every natural K, every measure F on
X(B,K), if F is a probability measure, then for every real c and every real
function f on Fin K, if Ignorability F and KnownSampling F c f hold, ALL the
following conclusions hold:

1. s>0.
2. H=Hobs.
3. c is nonzero.
4. For every k in H, all of these hold:
   t_k>0; c f(k)>0; f(k) is nonzero;

       p_k = q_k s / pi_k,
       p_k = (s/c)(q_k/f(k)).

5. With W=sum_{k in H} q_k/f(k), W=c/s and W is nonzero.
6. The population mean is identified by the inverse-profile ratio:

       mu = (sum_{k in H} mS_k (q_k/f(k))) / W.

7. The further weighted-mean equality holds:

       mu = (sum_{k in H} m_k (s/c)(q_k/f(k))) /
            (sum_{k in H} (s/c)(q_k/f(k))).

8. The common scalar cancels from that ratio:

       (sum_{k in H} m_k (s/c)(q_k/f(k))) /
       (sum_{k in H} (s/c)(q_k/f(k)))
       = (sum_{k in H} m_k (q_k/f(k))) / W.

There are no other hypotheses. In particular B>=0 and K>0 are not explicitly
assumed in T1, but existence of the probability law on X forces them. The
theorem does not assume c>0 or f>0: c and all supported f(k) may instead
be negative, provided their products are positive.

## SAP.P021.T2

The theorem is universally quantified over an arbitrary type Omega and its
measurable-space structure. For every such Omega it asserts the conjunction
of the following random and deterministic statements.

### Random statement

Quantifiers and hypotheses, in order:

* For every real B, natural K, and measure P on Omega, assume P is a
  probability measure, B>=0, and K>0.
* For every measure F on X(B,K), assume F is a probability measure.
* For every sequence N:N->N, assume N_r>0 for every r.
* For every array z assigning to r and omega a population
  z_r(omega):Fin(N_r)->X(B,K), assume that, for every r and j, the map
  omega -> z_r(omega)(j) is measurable.
* Assume that for every r the sampleSet(z_r(omega)) is nonempty for
  P-almost every omega. The null set may initially depend on r.
* Assume EmpiricalWeakInProbability P F N z, expanded above.
* For every pair of real numbers c,a, assume a is nonzero,
  Ignorability F holds, and KnownSampling F c (k -> a d(k)) holds.
  Thus on each positive-mass degree, pi_k=c a d(k), with equality of
  sampled and population conditional outcome means and pi_k>0.

Conclusion: VH(z_r(omega)) converges in P-probability to the constant mu.
Explicitly, for every epsilon>0,

    P{omega : |VH(z_r(omega))-mu| >= epsilon} -> 0.

### Deterministic statement

Quantifiers and hypotheses, in order:

* For every real B and natural K, assume B>=0 and K>0.
* For every measure F on X(B,K), assume F is a probability measure.
* For every sequence N:N->N, assume N_r>0 for every r.
* For every deterministic array z_r:Fin(N_r)->X(B,K), assume the sample
  at every r is nonempty.
* Assume for every continuous g:X(B,K)->R that
  empiricalAverage(z_r,g) -> integral g dF.
* For every real c,a, assume a is nonzero, Ignorability F holds, and
  pi_k=c a d(k) on every k with p_k>0.

Conclusion: VH(z_r) -> mu in the ordinary topology on the real numbers.

Neither branch assumes independence, identical distribution, a stochastic
sampling mechanism for the finite arrays, increasing populations, N_r ->
infinity, an increasing K, or a rate of convergence. A single common B and K
apply to the whole sequence. The empirical laws include the actual binary
sample marks, not just outcome and degree. The nonempty-sample hypothesis
makes each estimator denominator strictly positive (almost surely in the
random branch); each d(k) is positive without any separate hypothesis.
