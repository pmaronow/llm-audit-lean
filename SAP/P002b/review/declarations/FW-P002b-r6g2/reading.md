# Blind reading

This file was written before opening either `claims.json` or `record.json`.
Sources read: all five target statements and docstrings, all entries of their
`closure.json` closures, and the source bodies of those entries. Generated
constructors/projections were checked against their structures. The generated
matchers and proof entries were also printed by
`scratch/BlindChecks.lean` (successful compilation).

The notation below is an expansion into finite real sums, finite sets, real
matrices, extended reals and Mathlib filters. It is shared between sections to
avoid repeating identical definitions. No mathematical conditions are implicit
in a structure constructor.

## Shared expansions used in the five sections

For natural numbers n,k, the unit set is I={0,...,n-1} (`Fin n`), and the
covariate coordinate set is K={0,...,k-1}. `Population n` is exactly a triple
(y,d,n1), where y:I×{false,true}→ℝ, d:I×{false,true}→{false,true}, and n1:ℕ.
`CovPopulation n k` adds x:I×K→ℝ. The `.mk` declarations are the constructors
of these records; `.pop`, `.y`, `.d`, `.n1`, `.x` are their field projections.
There are no positivity, rank or stochastic assumptions in the records.

Write b(false)=0, b(true)=1 (`binary`). Put C={i:d(i,false)=false and
d(i,true)=true} (`compliers`). `MonotoneReceipt` means, for every i,
d(i,false)=true implies d(i,true)=true. `ValidDesign` means n≥2 and
0<n1<n. Write n0=(n:ℝ)-(n1:ℝ), rP=(n1:ℝ)/(n:ℝ). `controlSize` and
`fraction` are precisely these real expressions; there is no natural-number
subtraction here. The assignment support A_P is the set of all subsets S⊆I
with |S|=n1 (`assignments`, `Finset.univ.powersetCard n1`). For any predicate E,
p_P(E)=|{S∈A_P:E(S)}|/|A_P|, with both cardinalities cast to ℝ
(`probability`). This is complete randomization, uniform on the finite support.

For q:I→ℝ, write bar(q)=Σ_i q_i/n (`mean`) and
bar_S(q)=Σ_{i∈S}q_i/|S| (`groupMean`). The arm mean `armMean q S true`
is bar_S(q), and the false arm mean is bar_{Sᶜ}(q). All complements are in I.
Write

    V(q)=Σ_i(q_i-bar(q))²/(n-1),
    Cov(q,t)=Σ_i(q_i-bar(q))(t_i-bar(t))/(n-1).

These are `popVar` and `popCov`; n-1 is subtraction in ℝ. `late` is
bar_C(i↦y(i,true)-y(i,false)). `w P a β i` is
y(i,d(i,a))-β b(d(i,a)). The observed receipt under any subset S is
d_S(i)=d(i,decide(i∈S)) (`observedD`), observed outcome is
Y_S(i)=y(i,d_S(i)) (`observedY`), and observed transformed response is
W_{β,S}(i)=Y_S(i)-β b(d_S(i)) (`observedW`). Exclusion is encoded by the
receipt-indexed outcome y, rather than a separate assignment-indexed outcome.

Here are all the regression expansions. Indices of a coefficient vector are
`Option (Fin k)`: one intercept coordinate none, and slope coordinates some(j).
Let u_i=(1,x_i) (`augmented`), and let the Euclidean scalar product mean the
finite sum of coordinate products (Mathlib `dotProduct`). For a subset R,

    G_R(s,t)=bar_R(i↦u_i(s)u_i(t)),
    h_R(q)(s)=bar_R(i↦u_i(s)q_i),
    RSS_R(q,c)=Σ_{i∈R}(q_i-Σ_s u_i(s)c(s))².

These are `gram`, `score`, `rss`. `ols x R q`, denoted c_R(q), is
G_R⁻¹ h_R(q) when det(G_R)≠0. If det(G_R)=0, it is the vector chosen by
`Classical.choose` from {c:∀b,RSS_R(q,c)≤RSS_R(q,b)}, if such a vector exists,
and is the zero vector otherwise. Thus it is not the zero nonsingular inverse
on a singular design. A real finite-dimensional least-squares minimizer always
exists, including on an empty arm, so the last fallback is mathematically
unreachable. The choice on a singular design is unspecified but fixed by the
definition. `fitted P q S a` is c_S(q) for a=true, and c_{Sᶜ}(q) for a=false.
`slopeDot x c` is Σ_{j∈K}x(j)c(some(j)), excluding the intercept.

For arbitrary coefficient vectors c1,c0, `adjustedWith` is

    bar_S(i↦q_i-Σ_j x_i(j)c1(some(j)))
      -bar_{Sᶜ}(i↦q_i-Σ_j x_i(j)c0(some(j))).

Denote this by L(q,S,c1,c0), and put

    T_x(q,S)=L(q,S,c_S(q),c_{Sᶜ}(q)),
    H_x(q,S)=RSS_S(q,c_S(q))/n1²+RSS_{Sᶜ}(q,c_{Sᶜ}(q))/n0².

These are `adjustedTau` and `adjustedSigma2`.

The raw versions are

    T_0(q,S)=Σ_i q_i(1_{i∈S}-rP)/n,
    H_0(q,S)=rP²(1-rP)² [Σ_{i∈S}(q_i-bar_S(q))²/n1²
                              +Σ_{i∈Sᶜ}(q_i-bar_{Sᶜ}(q))²/n0²].

These are `rawTau` and `rawSigma2` (the raw contrast is scaled by rP(1-rP)
relative to the arm-mean difference on a valid assignment).

For real t,h, `absStudent` takes values in [0,∞] (`ℝ≥0∞`): it is 0 if h=0=t,
∞ if h=0≠t, and otherwise `ENNReal.ofReal(|t|/Real.sqrt h)`.
`ENNReal.ofReal a` is the nonnegative truncation of a, embedded in [0,∞].
Define A_0(q,S)=absStudent(T_0(q,S),H_0(q,S)), and
A_x(q,S)=absStudent(T_x(q,S),H_x(q,S)). These are `rawAR` and `adjustedAR`.

For g:A_P→[0,∞], `quantile P g α` is the least member of

    {t∈{g(S):S∈A_P}:1-α≤p_P(S↦g(S)≤t)},

if that finite candidate set is nonempty, and ∞ otherwise. Acceptance in the
raw case is A_0(W_{β,S},S)≤quantile(P,R↦A_0(W_{β,S},R),α), where the
response vector is held at the observed W_{β,S} while R is rerandomized.
`accepted` is this predicate; `coverage` is its probability over S∈A_P.
`adjustedAccepted` and `adjustedCoverage` replace A_0 by A_x.

For the algorithm sections, `QuadraticAR` is the record of six arbitrary real
coefficients (a,b,c,d,e,f), with constructor `.mk` and the six projections.
Its curve is F_Q(β)=(aβ²+bβ+c)/(dβ²+eβ+f) (`arFunction`).
`ARRegular Q` is the conjunction, for every real β, of dβ²+eβ+f>0 and
aβ²+bβ+c≥0. In particular F_Q is a continuous nonnegative real function.

Given M curves g_m:ℝ→ℝ, `mcCritical g α β`, written q(β), is the least
element of the finite set

    {t∈{sqrt(g_m(β)):m∈Fin M}:
           (1-α)M≤|{m:sqrt(g_m(β))≤t}|},

and is 0 if this set is empty. Multiplicities enter through the count, even
though the candidate values form a set. `mcIndices g α β` is exactly
{m:sqrt(g_m(β))=q(β)}. `mcSet f g α` is
{β:sqrt(f(β))≤q(β)}. A crossing is a real β for which there are indices s,t
with g_s≠g_t as whole functions and g_s(β)=g_t(β) (`crossing`); identical
curves do not count as crossings. `IntersectionList g J` means the finite real
list J is strictly increasing (`List.Pairwise (<)`) and β∈J iff β is a crossing,
for every real β.

`RecordedPiece M` is precisely a triple (l,u,m) with l,u∈[-∞,+∞] (`EReal`)
and m∈Fin M. `.mk` constructs the triple and `.left`, `.right`, `.index`
project it; the record alone imposes no interval or quantile condition.
`closedInterval l u` is {β∈ℝ:l≤(β:EReal)≤u}. `pieceSet f g p` is
{β:l≤β≤u and f(β)≤g_m(β)}. `returnedSet` is the union of these sets over
the finite list of recorded triples, expressed as an existential over list
membership.

## SAP.P002b.T21

Source: `Challenge/Part1.lean:34-47`, `Defs/WholeW2.lean:12-34`,
`Defs/Part8.lean:11-26`, and the finite-population/regression definitions above.
The docstring describes a corrected uniform upper-tail assertion with an inner
limit superior and an ordinary outer right-hand limit.

Quantifiers are, in order: every k:ℕ and every real δ,e,A,B,r,α; assuming
k>0, δ<1, e>0, A>0, B>0, 0<r≤1/2, and 0<α<1; there exists u∈[0,∞]
such that u≤1, the following right-hand convergence holds, and u≤α.

Here is the complete model predicate (`Xi`). For any n and model (y,d,n1,x),
let τ=bar_C(y(·,true)-y(·,false)). Define c_a=c_I(w_a(τ)) (`psi`) by the
OLS rule above and e_a(i)=w_a(τ)(i)-Σ_s u_i(s)c_a(s) (`residual`). Then
the model is in Xi iff all the following hold:

1. n≥2, 0<n1<n; monotone receipt; C is nonempty.
2. rn≤n1≤(1-r)n, inequalities after casting n,n1 to ℝ.
3. Cov(e_true,e_false)≥-δ sqrt(V(e_true)) sqrt(V(e_false)). These are
   whole-population covariance and variances with denominator n-1, not
   covariance restricted to C.
4. For each a∈Bool,
   sqrt(sqrt((Σ_i e_a(i)^4)/n))≤B sqrt(V(e_a)). This is the expansion of
   `fourthNorm`, with no additional centering inside `fourthNorm`.
5. For each j∈K, Σ_i x_i(j)=0 and (Σ_i x_i(j)^4)/n≤A.
6. For every b:K→ℝ,
   e Σ_j b(j)²≤(Σ_i(Σ_j x_i(j)b(j))²)/n.
   This expands `normSq` and is the positive Rayleigh lower bound for the
   covariate second-moment matrix.

Let z_α be the real infimum of
{z:ofReal(1-α/2)≤N(0,1)((-∞,z])}. This is
`standardNormalCritical`, using Mathlib's `gaussianReal 0 1`, the Gaussian
probability measure with mean zero and variance one. There is no standard
deviation/variance ambiguity because the second argument is 1. For each n and
real κ define U_n(κ)∈[0,∞] as follows (`adjustedTailSupremum`): first take the
supremum over every real β, then the supremum over every model in Xi at size n
whose τ equals β, of

    ofReal p_P(S↦ z_α-κ<0 or
                       A_x(W_{β,S},S)>ofReal(z_α-κ)).

Both suprema are complete-lattice suprema in [0,∞]. The convergence asserted is

    lim_{κ→0, κ>0} limsup_{n→∞} U_n(κ)=u,  0≤u≤α (<1).

The Lean filters are respectively `nhdsWithin 0 (Set.Ioi 0)`, `atTop` on ℕ,
and `nhds u` in [0,∞]. The inner limit superior is the infimum over N of
the supremum of U_n over n≥N. All n∈ℕ occur, including 0 and 1; Xi is empty
at those sizes, so their suprema are zero and they do not affect the limsup.
There is no assertion that the inner ordinary limit exists. The existence of a
finite outer limit and its bound are both conclusions, not assumptions.

Junk/convention audit: finite means are zero on empty sets by real division by
zero; nonempty C and valid designs prevent that here for the LATE and actual
arms. n≥2 prevents division by n or n-1 being zero. Arm counts n1,n0 are
positive on A_P. All sample variance and fourth-power arguments of square
roots are nonnegative. `Real.sqrt` is zero on negative inputs in general, but
that branch is not used here. The model Rayleigh bound with e>0 and centered
covariates makes the population augmented Gram invertible; sample-arm Grams
can be singular and use the fixed minimizer convention. The final zero-vector
OLS fallback is unreachable by finite least-squares existence. An arbitrary
singular minimizer is substantive: slopes, unlike fitted responses, can depend
on the choice. The docstring explicitly mentions this choice. Sample variance
can be zero; `absStudent` deliberately assigns 0 to 0/0 and ∞ to nonzero/0,
so this case is not discarded. For a hypothetical negative variance input its
nonzero branch would yield ofReal(|t|/0)=0, but the sum-of-squares formulas
exclude it. The normal-quantile infimum is nonempty and bounded below for
0<α<1, so the real `sInf` default for empty/unbounded-below sets is excluded.
Negative cutoffs are handled by the explicit disjunct, preserving a strict
upper tail even though ofReal truncates negative reals. Empty Xi suprema equal
0 by the bottom of [0,∞]; all probabilities and suprema are ≤1, so no
unbounded-real limsup default is involved. There is no conversion of ∞ to a
real. No Bochner integral of a statistic, logarithm, real exponent, partial
list operation, integer subtraction, or empty coordinate type occurs. The
Gaussian definition uses its genuine integrable density, with positive variance.

## SAP.P002b.T22

Source: `Challenge/Part1.lean:49-57`, `Defs/WholeW1.lean:68-117`, and
`Defs/Part4.lean:12-97`. The docstring concerns completed **corrected** runs,
and termination for every admissible history-dependent choice policy.

Quantifiers in order: every M:ℕ, Qf:ℝ⁶, Qg:Fin M→ℝ⁶, α:ℝ; assumptions
M>0, 0<α<1, ARRegular Qf and ARRegular Qg_m for every m; then every
J:List ℝ with `IntersectionList g J` and J≠[]. Put f=F_Qf and g_m=F_Qg_m.
There is no data-generation assumption. The conclusion is a conjunction:

* For every function choose:(List of triples)→ℝ→Fin M, if, for every history
  and every real sample β, choose(history,β)∈mcIndices(g,α,β), then there
  exists a finite list pieces following that policy and satisfying the run
  conditions and the whole contract below.
* Every finite list pieces satisfying the run conditions, independently of any
  prescribed policy, satisfies that same contract.

The run conditions (`Algorithm2Run`, expanded) are: J is exactly the sorted
crossing list, J≠[], pieces≠[], and the first triple has l=-∞ and index in
mcIndices(g,α,min(J)-1). For every position i in pieces, with p=pieces[i],
form

    C_p={β∈ℝ:p.l<β and ∃m, g_m≠g_{p.m} and g_m(β)=g_{p.m}(β)}.

If C_p is nonempty, p.u must equal its least real element; otherwise p.u=+∞.
For the last position, the next optional piece is none, and p.u must be +∞.
For any other position the next piece q must have q.l=p.u≠+∞, and its index
must be a quantile index at (p.u+e)/2 if e is the first element of J strictly
larger than p.u, or at p.u+1 if no such element remains. This expands both
the `if` and option `match` in `Algorithm2Step`. It imposes only sample-point
index validity; validity throughout the interval is a conclusion.

Following the policy (`PolicyAlgorithm2Run`) additionally requires that the
index of pieces[i] equal choose(pieces.take(i),s_i), with s_0=min(J)-1 and
s_i equal to the same next sample computed from pieces[i].l for i>0.
`nextAlgorithm2Sample` is exactly the filtering/head/midpoint rule just given.

The whole contract (`Algorithm2WholeContract`) asserts all seven clauses:

1. length(pieces)≤length(J)+1.
2. The right endpoints of pieces are strictly increasing in their list order.
3. Every right endpoint is +∞ or a real crossing in J.
4. Every real β belongs to at least one recorded closed interval.
5. On each recorded closed interval, including each finite endpoint, its index
   belongs to mcIndices(g,α,β).
6. For each triple (l,u,m), {β:l≤β≤u and f(β)≤g_m(β)} equals
   {β:sqrt(f(β))≤q(β)}∩{β:l≤β≤u}.
7. The union of those pieces equals {β:sqrt(f(β))≤q(β)}.

No probability law on simulated assignments occurs in this deterministic
statement; it is pointwise in an arbitrary regular family. Existence of J is
not a conclusion of this particular theorem. The J=[] branch is excluded.

Junk/convention audit: real division in F_Q is totalized at zero in general,
but ARRegular excludes zero and negative denominators at every real β. It
also excludes negative inputs to the square roots in the empirical quantile
and confidence set. M>0 and 0<α<1 make the finite quantile candidate set
nonempty; its fallback 0 is unreachable. Identical curves are intentionally
omitted from crossing tests, preventing infinitely many artificial crossings.
`EReal.toReal` sends both infinities to 0. In `Algorithm2Step` and
`nextAlgorithm2Sample` it is used on actual real crossings, so neither infinity
is converted. J.head! would default to 0 on an empty list, but J≠[] prevents
that. The filtered E.head! is evaluated only in its nonempty branch. The
optional next list entry is none exactly at the last finite-list position;
it is not replaced by a default triple. Mathematically nonempty C_p has a
least point because it is a subset of the finite crossing list; the run
requires the least-point fact, not `sInf` of an arbitrary set. No n, OLS,
Bochner integral, log, real power, Nat truncated subtraction or limsup occurs.
Natural lengths, i+1, take and list lookup have their usual finite meanings.

## SAP.P002b.T23

Source: `Challenge/Part1.lean:59-61`, `Defs/Part6.lean:30-42`,
`Defs/Part4.lean:61-73,99-146`, and the shared expansions above.
The docstring describes equality of the chosen squared curve with the squared
empirical critical value on closed Algorithm 1/3 gaps, and correctness of each
returned piece. The definition calls this corrected (H.1).

Quantifiers in order: every M:ℕ, Qf:ℝ⁶, Qg:Fin M→ℝ⁶, α:ℝ; assuming
M>0, 0<α<1, DataGeneratedCoefficients(Qf,Qg), ARRegular Qf, and
ARRegular Qg_m for every m; then every real list J and every list pieces of
triples; assuming J≠[] and Algorithm1Run(g,α,J,pieces); for every p in
pieces, both of the following hold:

* For every real β with p.l≤β≤p.u, p.m∈mcIndices(g,α,β) and
  g_{p.m}(β)=q(β)².
* {β:p.l≤β≤p.u and f(β)≤g_{p.m}(β)} equals
  {β:sqrt(f(β))≤q(β)}∩{β:p.l≤β≤p.u}.

Here f=F_Qf and g_m=F_Qg_m. `Algorithm1Run` expands into these three
assumptions: J is exactly the strictly increasing list of crossings; the
endpoint-pair list extracted from pieces is

    zip([-∞] ++ map(coe,J), map(coe,J) ++ [+∞]);

and for each recorded triple p, its index is a quantile index at the sample
`gapSample p.l p.u`. This sample is 0 for (-∞,+∞), u-1 for (-∞,u),
l+1 for (l,+∞), and (l+u)/2 for finite endpoints. Thus index validity is
assumed only at one interior sample, not throughout the closed gap. The list
equality forces all consecutive gaps, in order, exactly once. The separate
J≠[] assumption excludes the single-gap/no-crossing branch.

The existential hypothesis `DataGeneratedCoefficients` has the following full
expansion. There exist n,k:ℕ, population/covariates (y,d,n1,x), a Boolean
adjusted, an observed subset O, and a family T_m of simulated subsets, such
that n≥2, 0<n1<n, receipt is monotone, C≠∅, |O|=n1 and |T_m|=n1 for
every m. If adjusted=true, then k>0, Σ_i x_i(j)=0 for every coordinate j,
and both G_R and G_{Rᶜ} have nonzero determinants for R=O and every R=T_m.
There are no further x/rank assumptions in the false branch. Put
Y=Y_O and D_i=b(d_O(i)). For either branch define a cross-variance:

    Hcross_0(Y,D,S)=rP²(1-rP)² [Σ_{i∈S}(Y_i-bar_S(Y))(D_i-bar_S(D))/n1²
                         +Σ_{i∈Sᶜ}(Y_i-bar_{Sᶜ}(Y))(D_i-bar_{Sᶜ}(D))/n0²],
    Hcross_x(Y,D,S)=Σ_{i∈S}(Y_i-u_i·c_S(Y))(D_i-u_i·c_S(D))/n1²
                         +Σ_{i∈Sᶜ}(Y_i-u_i·c_{Sᶜ}(Y))(D_i-u_i·c_{Sᶜ}(D))/n0².

These expand `rawVarianceCross` and `adjustedVarianceCross`. Using h=0 or x
according to the Boolean, form

    Q(S)=(T_h(D,S)², -2 T_h(Y,S)T_h(D,S), T_h(Y,S)²,
           H_h(D,S), -2 Hcross_h(Y,D,S), H_h(Y,S)).

This is the full expansion of `rawCoefficients`, `adjustedCoefficients` and
`dataCoefficients`. Finally require Qf=Q(O) and Qg_m=Q(T_m) for every m.
The witness asserts membership of each T_m in the design support; it asserts
no independence or distribution, because the conclusion is deterministic for
the fixed family.

Junk/convention audit: ARRegular excludes quadratic denominator zero and
negative square-root arguments. The existence witness has valid nonempty
design arms; all n,n-1,n1,n0 divisions actually used are well defined in the
ordinary sense. The raw branch does not require covariates; the adjusted
branch requires ordinary inverses in all generating arms, so the OLS choice
and fallback are excluded there. The squared critical value is an ordinary
finite real square, not a conversion from ∞. Empty quantile candidates and
M=0 are excluded. `gapSample` uses EReal.toReal; ordered consecutive real
crossings with -∞/+∞ exterior endpoints ensure its infinity conversion never
contributes a junk value: the both-infinite branch returns the chosen sample
0 directly, and the other branches convert finite endpoints. Every finite
gap is nonempty and its midpoint is strictly interior. Empty J and pieces
cannot satisfy these hypotheses. k=0 is possible in a raw generating model;
its slope sums are empty, but no slope assertion is needed in that branch.
There is no limsup, log, rpow, Bochner integral, unattained infimum, or partial
list-head operation in this target's closure.

## SAP.P002b.T24

Source: `Challenge/Part1.lean:63-65`, `Defs/Part6.lean:44-54`, and the shared
finite-population/regression expansions. The docstring calls the OLS
coefficients and the adjusted statistic affine in the hypothesized effect and
says that the Wald ratio zeroes the statistic.

Quantifiers in order: every implicit n,k:ℕ, every P=(y,d,n1,x), every subset
S⊆I, every two arbitrary real vectors Y,D:I→ℝ, and every real β. Assumptions
are n≥2, 0<n1<n, |S|=n1, det(G_S)≠0, det(G_{Sᶜ})≠0. The conclusion is
the conjunction:

1. For each Boolean a, with R=S if a=true and R=Sᶜ if a=false,
   c_R(Y-βD)=c_R(Y)-β c_R(D), equality of every intercept/slope coordinate.
2. T_x(Y-βD,S)=T_x(Y,S)-β T_x(D,S).
3. If T_x(D,S)≠0, then
   T_x(Y-[T_x(Y,S)/T_x(D,S)]D,S)=0.

The last implication is not a hypothesis needed for clauses 1 and 2.
The response and receipt vectors need not come from P, nor be binary. There
is no monotonicity, nonempty C, centering of x, positive k, or residual
variance assumption. All coefficients are the inverse-normal-equation
coefficients defined above. No `adjustedAR` or studentized ratio occurs in
the elaborated statement or its closure: the asserted zero is of the real
adjusted contrast T_x. The affine assertion in β has the response/receipt
fits fixed as its intercept and slope vectors.

Junk/convention audit: both actual arms have positive sizes and their Gram
determinants are nonzero, so no group-mean zero division, singular inverse,
least-squares choice, or final OLS fallback affects these conclusions. The
Wald division is guarded by a nonzero denominator. n1,n0,n are positive;
no popVar division occurs in this closure. k=0 is permitted: the slope sum
is zero and the coefficient type still has its intercept, so the theorem
includes the intercept-only arm means as a genuine case. There is no
studentization, square root, quantile, integral, extended infinity, limsup,
log, rpow, or truncated subtraction. Natural sizes and cardinalities are
cast injectively to ℝ before arithmetic.

## SAP.P002b.T25

Source: `Challenge/Part1.lean:67-69`, `Defs/Part6.lean:56-64`, and all shared
finite-population/statistic/quantile/regression expansions above.
The docstring asserts baseline recovery and both finite-sample coverage lower
bounds under a constant additive effect.

Quantifiers in order: every implicit n,k:ℕ, every model P=(y,d,n1,x), and
every β∈ℝ; assuming n≥2, 0<n1<n, receipt monotone, C≠∅, and, for every
i∈I, y(i,true)=y(i,false)+β. The conclusion has three parts:

1. For every subset S⊆I (not only those of size n1),
   W_{β,S}=i↦y(i,false) as functions on I.
2. bar_C(y(·,true)-y(·,false))=β.
3. For every α∈ℝ with 0<α<1, both

       p_P(S↦A_0(W_{β,S},S)≤quantile(P,R↦A_0(W_{β,S},R),α))≥1-α,
       p_P(S↦A_x(W_{β,S},S)≤quantile(P,R↦A_x(W_{β,S},R),α))≥1-α.

All quantiles here use the full randomization support, not a finite Monte
Carlo simulation, normal critical value, or asymptotic approximation. In each
quantile the vector W_{β,S} is held fixed while R varies. Under part 1 this
vector is the same baseline for all S, giving a genuine finite distribution
quantile argument. No conclusion says coverage equals 1-α; ties can make it
larger. The additive-effect hypothesis is on both receipt-indexed potential
outcomes of every unit, including noncompliers. There is no condition on k,
covariate centering, arm rank, or positive variance.

Junk/convention audit: valid design makes A_P nonempty and its probability
denominator positive, and C≠∅ prevents the LATE being the empty-mean default.
The universal recovery claim on all subsets uses neither a sample mean nor
a fit, so even empty or full S introduces no undefined quantity in that
part. Actual statistics and quantiles use only |S|=n1, hence nonempty arms
and nonzero n1,n0,n. Both H_0 and H_x are nonnegative sums of squares.
They can vanish, and the [0,∞]-valued studentization explicitly retains
0/0=0 and nonzero/0=∞. A quantile can legitimately be ∞; comparisons then
remain in [0,∞] (in particular ∞≤∞), without applying toReal to ∞.
The candidate set is nonempty for 0<α<1 since the greatest attained statistic
has probability one. Thus the empty-candidate fallback ∞ is not used.
Singular arm Grams are allowed; OLS uses a fixed genuine least-squares
minimizer. Fitted values and RSS are well defined even when coefficients
are nonunique. The adjusted contrast can depend on which singular minimizer
was fixed, but finite-sample quantile validity applies to that same fixed
statistic in both the observation and all rerandomizations. The final
zero-vector fallback is unreachable by least-squares existence. k=0 is
allowed with an empty slope sum and one intercept coordinate. No variance
n-1 denominator is used in this target. No real sInf/sSup, limsup, log,
rpow, Bochner integral, partial list operation, or Nat subtraction occurs.

## Generated closure entries

In addition to the bodies expanded above, `closure.json` lists
`augmented.match_1` and `Algorithm2Step.match_1`; their printed bodies are
ordinary `Option.casesOn` eliminators and add no assumptions or fallback values.
The listed `T21WholeStatement._proof_1`, `standardNormalCritical._proof_1`,
`T20WholeStatement._proof_1`, and `gapSample._proof_1` all have printed type
`(1+1).AtLeastTwo` and proof `Nat.instAtLeastTwoHAddOfNat 1`. They certify
the numeral 2 used as a divisor; they contain no statistical assertions.
In particular the occurrence of `T20WholeStatement._proof_1` in the T22
closure does not introduce the assumptions or conclusions of T20.
