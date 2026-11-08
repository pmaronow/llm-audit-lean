# Blind reading

Saved before opening `claims.json` or `record.json`. Sources read: the five
Challenge declarations and docstrings, `closure.json`, every source declaration
in their closures, and the generated auxiliary declarations printed by
`scratch/BlindCheck.lean`. The Challenge stubs are accepted as certified
statements; their `sorry` bodies are not being audited.

## Shared notation, fully expanded

Here are finite-sum abbreviations used below, not additional assumptions.
`Fin N` is the type of natural numbers less than the natural number `N`.
A treatment vector is a function `z : Fin N → Bool`; `true` means treated.
Potential outcomes are arbitrary real numbers `y(i,z)` indexed by a subject and
the entire binary vector. They permit interference and dependence on outside
subjects.

A `FiniteDistribution α` is just a finite set `A ⊆ α` and a total real-valued
function `w : α → ℝ`. `IsDistribution` means `w(x)>0` for every `x∈A` and
`Σ[x∈A] w(x)=1`; values outside `A` are ignored. Its expectation of `h` is
`Σ[x∈A] w(x)h(x)`; its probability of a predicate `P` is
`Σ[x∈A] (if P(x) then w(x) else 0)`. The pushforward under `g` has distinct
atoms `g(A)` and mass at `b` equal to the sum of `w(x)` over `g(x)=b`.

For an assignment law `(A,w)`, subject `i`, and Boolean `a`, write
`A_ia={z∈A : z(i)=a}`, `k_ia=|A_ia|`,
`p_ia=Σ[z∈A_ia]w(z)`, and `M_ia=Σ[z∈A_ia]w(z)y(i,z)`.
The unweighted support average is `U_ia=(Σ[z∈A_ia]y(i,z))/k_ia`;
the weighted own-arm average is `C_ia=M_ia/p_ia`.
Positive arms means `p_ia>0` for every `i∈S` and both `a`.
Conditional uniformity means, for every `i∈S`, both `a`, and `z∈A_ia`,
`w(z)/p_ia=1/k_ia`.

Put `n=|S|`, `n_a(z)=Σ[i∈S]1_{z(i)=a}`, and
`T_a(z)=Σ[i∈S]1_{z(i)=a}y(i,z)`. The difference of means is
`D(z)=T_true(z)/n_true(z)-T_false(z)/n_false(z)`. The window contrast of
any real array `f(i,a)` is
`B(f)=(Σ[i∈S](f(i,true)-f(i,false)))/n`.

For a measurable space Ω, a measure μ, and a predicate P,
`eventProbability μ P` is `(μ {ω : P(ω)}).toReal`, the real conversion of an
extended nonnegative measure. A probability measure means `μ(Ω)=1`.
Almost everywhere means that the exceptional set has μ-measure zero.
For a real function h the event conditional mean is
`(∫_{P} h dμ)/(μ(P)).toReal`, where the numerator is the Bochner integral
against the restricted measure.

For a score vector `x : Fin N → ℝ`, treatment is `z(i)=true ↔ 0≤x(i)`.
Inside the window means `-b≤x(i)≤b`, including both endpoints. The window
subjects are the finite set of indices satisfying these inequalities.
The empirical CDF on S at t is `(Σ[i∈S]1_{x(i)≤t})/n`.

`CorrectedLocalConditions μ X b S v` means precisely:

1. Every real coordinate `ω↦X(ω,i)` is measurable, including outside S.
2. For every population index i, the probability of
   `-b≤X(ω,i)≤b` is 1 if `i∈S` and 0 otherwise.
3. For every bijection `σ:S→S`, the event
   `∀i∈S, X(ω,i)=v(σ(i))` has probability `1/n!`.

The predicate alone does not assert injectivity of v, positivity of b,
probability normalization of μ, or an interior treated count; the relevant
theorems assert these separately.

## SAP.P014.T2

Location: `SAP/P014/Challenge/Part1.lean:14–21`; statement definitions:
`SAP/P014/Defs/WholeW1.lean:14–111`.

The theorem is a conjunction of the following two universally quantified
assertions, at an arbitrary universe level for Ω.

**Assignment assertion.** First quantify Ω with a measurable space, a natural
N, a probability measure μ on Ω, and a function
`Z:Ω→(Fin N→Bool)`. Assume Z is measurable. Next quantify a finite subset
`S⊆Fin N`, arbitrary potential outcomes y, and a natural m. Assume, in order,
`0<m`, `m<n`, `n_true(Z(ω))=m` almost everywhere, and, for every `i∈S`,
`Pr(Z(i)=true)=m/n`.

Define `A` to be *all* binary vectors z with `Pr(Z=z)>0` and
`w(z)=Pr(Z=z)` for every binary vector z. This is a finite set because the
population is finite. The conclusion asserts all of the following:

1. `(A,w)` is a normalized, strictly positive-on-atoms finite law, and
   `p_ia>0` for both arms of every `i∈S`.
2. For every such i and a, `p_ia=Pr(Z(i)=a)`,
   `C_ia=(∫_{Z(i)=a}y(i,Z(ω))dμ)/Pr(Z(i)=a)`, and both
   `ω↦y(i,Z(ω))` and `ω↦1_{Z(i)=a}y(i,Z(ω))` are integrable.
3. For every `i∈S`, `p_i,true=m/n` and `p_i,false=(n-m)/n`, with real
   subtraction in this and the following denominators.
4. On each z∈A, and also almost surely for z=Z(ω),
   `n_true(z)=m`, `n_false(z)=n-m`, both counts are positive, and
   `D(z)=T_true(z)/m-T_false(z)/(n-m)`.
5. For every i∈S and a,
   `∫1_{Z(i)=a}y(i,Z)dμ=M_ia=p_ia C_ia`.
   In particular `M_i,true=(m/n)C_i,true` and
   `M_i,false=((n-m)/n)C_i,false`.
6. `D∘Z` is integrable, and its integral equals each of
   - `Σ[z∈A]w(z)D(z)`;
   - `(Σ[i∈S]M_i,true)/m-(Σ[i∈S]M_i,false)/(n-m)`;
   - `(1/m)(m/n)Σ[i∈S]C_i,true
      -(1/(n-m))((n-m)/n)Σ[i∈S]C_i,false`;
   - `(Σ[i∈S](C_i,true-C_i,false))/n`.
7. That last bracketed mean is also
   `((Σ[i∈S]C_i,true)-(Σ[i∈S]C_i,false))/n`.

**Score assertion.** Quantify Ω, its measurable space, N, probability μ,
`X:Ω→Fin N→ℝ`, real b, finite S, `v:S→ℝ`, and natural m. Assume,
in order, `b>0`, v injective, every v(i) in [-b,b], `0<m<n`, exactly m
of the v(i) nonnegative, and the three corrected local conditions expanded
above. Conclude that thresholding X gives m treated window subjects almost
surely, each window subject has treatment probability m/n, and **for every
potential-outcome array y** all conclusions 1–7 of the assignment assertion
hold for this threshold assignment. There is no fixed-outside, independent-
outside, or no-interference premise.

**Junk conventions and possible effects.** Real division by zero is zero.
The generic conditional-mean and difference-of-means definitions would
therefore assign artificial values to absent arms. Here `0<m<n` forces
`n,m,n-m>0`; the conclusions also explicitly assert every relevant arm
probability and count positive. No such artificial value enters the identity.
Finite sums and finite-state potential outcomes have finite values; measurability
of Z makes all their compositions measurable and integrable on probability μ.
The Bochner integral is zero for a nonintegrable function, but integrability
is asserted, and follows independently from the finite domain. `toReal(∞)=0`
cannot arise since μ is a probability measure. An empty population or window
cannot satisfy `0<m<n`; Ω cannot be empty under a probability measure.
The subtype S is genuinely nonempty. Factorials are positive, and all natural
casts in real denominators preserve positivity. There is no truncated
subtraction in this statement's numeric formulas. There are no logs, roots,
real powers, extrema, limits, partial functions, or default-valued selections.

The docstring describes the weighted identity and its score-law sufficient
conditions, including arbitrary dependence of the outside allocation.

## SAP.P014.T8

Location: `SAP/P014/Challenge/Part1.lean:58–60`; definition:
`SAP/P014/Defs/Part5.lean:97–99`, depending only on the contrast at
`SAP/P014/Defs/Part1.lean:70–71`.

For every natural N, finite `S⊆Fin N`, and arbitrary array
`f:Fin N→Bool→ℝ`, assume S is nonempty. Then

`(Σ[i∈S](f(i,true)-f(i,false)))/(|S|:ℝ)
 = ((Σ[i∈S]f(i,true))-(Σ[i∈S]f(i,false)))/(|S|:ℝ)`.

There are no random variables, potential-outcome restrictions, or probabilistic
assumptions. This is finite-sum distributivity. Quantification is N, S, f,
then the implication from S nonempty.

**Junk conventions and possible effects.** The nonempty premise gives a
positive denominator after the natural-to-real cast. No empty-index or
division-by-zero convention enters this theorem. Without the premise both
sides would still be zero by Lean's empty-sum and zero-division conventions,
but that is not its asserted domain. N=0 supplies no nonempty S and is
vacuous only for that individual specialization. No integrals, infinities,
truncated subtraction, logs, roots, powers, extrema, limits, or partial
functions occur. The docstring accurately states this algebraic identity.

## SAP.P014.T3

Location: `SAP/P014/Challenge/Part1.lean:23–29`; definitions:
`SAP/P014/Defs/Part4.lean:43–109`.

This is a conjunction of five assertions. All finite-law notation has the
explicit sum and support-set meanings given above.

1. **Conditional uniformity.** Quantify natural N, a finite assignment law
   `(A,w)` with strictly positive supported masses summing to 1, then S, y,
   and natural m. Assume, in order, `0<m<n`, `n_true(z)=m` for every z∈A,
   `p_i,true=m/n` for every i∈S, and
   `w(z)/p_ia=1/k_ia` for every i∈S, Boolean a, and z∈A_ia.
   Conclude that every A_ia is nonempty, `U_ia=C_ia` on both arms of S,
   `Σ[z∈A]w(z)D(z)=B(U)`, and
   `B(U)=((Σ[i∈S]U_i,true)-(Σ[i∈S]U_i,false))/n`.
2. **Full-law uniformity.** For every natural N and valid finite assignment
   law `(A,w)`, then every finite S, if `w(z)=1/|A|` for every z∈A, conclude
   `w(z)/p_ia=1/k_ia` for every i∈S, a, and z∈A_ia. There is no requirement
   that both arms be nonempty in this assertion alone.
3. **Fixed outside treatment.** Quantify Ω at arbitrary universe level with
   its measurable space, N, probability μ, scores X, real b, finite S,
   v:S→ℝ, and an assignment law `(A,w)`; assume it is a valid finite law.
   Next quantify an entire fixed binary vector c, arbitrary y, and natural m.
   Assume `b>0`, injective v inside [-b,b], `0<m<n`, exactly m nonnegative
   entries of v, corrected local conditions, the exact assignment-law equality
   `Pr(threshold(X)=z)=(if z∈A then w(z) else 0)` **for every binary z**,
   and almost surely `threshold(X)(i)=c(i)` for every i outside S.
   For a permutation σ of S define the binary vector qσ by thresholding
   `v(σ(i))` on S and using c(i) outside. Conclude:
   - `|A|=choose(n,m)`;
   - every z∈A is produced by exactly `m!(n-m)!` permutations σ,
     has mass `m!(n-m)!/n!=1/choose(n,m)`, and has m treated S subjects;
   - each i∈S has `p_i,true=m/n`, the law is conditionally uniform on S,
     and `Σ[z∈A]w(z)D(z)=B(U)`;
   - every binary z agreeing with c outside S and having m treated S
     subjects belongs to A, has the same permutation multiplicity, and has
     mass `1/choose(n,m)`.
   The premise fixes outside treatments almost surely, not outside scores.
4. **No interference.** Quantify natural N, a valid finite assignment law,
   then S, y, natural m. Assume `0<m<n`, fixed supported treated count m,
   common treatment probabilities m/n, and, for every i∈S and all binary
   z,z', `z(i)=z'(i) → y(i,z)=y(i,z')`. Conclude, for every i∈S, a,
   and every binary z with z(i)=a, `U_ia=y(i,z)` and `C_ia=y(i,z)`;
   also `Σ[z∈A]w(z)D(z)=B(U)`. This no-interference premise only constrains
   outcomes of subjects in S, but compares all full assignments.
5. **Necessity for equality for every outcome.** For every natural N and
   valid finite assignment law, then subject i and Boolean a, assume `p_ia>0`
   and **for every full potential-outcome array y**, `U_ia=C_ia`. Conclude
   `w(z)/p_ia=1/k_ia` for every z∈A_ia. The universally quantified outcome
   array in the premise precedes the conclusion's quantification over z;
   equality for one observed outcome is not the premise.

**Junk conventions and possible effects.** In assertions 1, 3, and 4,
`0<m<n`, positive supported masses, and common propensities imply positive
window size, both arm counts, and both own-arm probabilities. In 5 positivity
of p_ia ensures a nonempty own-arm support. Thus the U, C, D, and contrast
denominators used for substantive equalities are nonzero. In 2 an empty arm
makes the assertion about z∈A_ia vacuous, with no evaluation at any z; this
does not grant positivity and is used only together with other premises
elsewhere. A normalized finite law cannot have empty A. Empty N or S may
occur in 2, giving harmless vacuous conditional uniformity; the interior-m
parts exclude them. The permutation type has one identity even for empty S,
not zero permutations. Natural subtraction `S.card-m` in factorials is
truncated subtraction, but `m<n` makes it equal the ordinary positive
integer difference. `choose(n,m)>0` in this range, as are factorials.
The real control denominators elsewhere use real subtraction. `toReal(∞)=0`
in the local-law premise cannot occur for probability μ. All needed score
events are measurable under coordinate measurability. There are no Bochner
integrals, unbounded extrema, limits, logs, roots, real powers, partial
functions, or default-valued choices in this closure.

The docstring mentions all five assertions. Its phrase about full assignment
uniformity means uniformity on the actual supported full binary vectors;
the fixed-outside assertion identifies that support with all m-treated
window assignments extended by c.

## SAP.P014.T7

Location: `SAP/P014/Challenge/Part1.lean:52–56`; definitions:
`SAP/P014/Defs/Part5.lean:69–95`.

The theorem conjoins a general assertion, a local-randomization assertion,
and three finite examples.

**General assertion.** For every Ω at arbitrary universe level with its
measurable space, N, probability μ, arbitrary `X:Ω→Fin N→ℝ`, and finite
S, let L be the literal property
`∀i∈S, ∀j∈S, Pr(X(i)=X(j))=0`. Let C be its distinct-indices version
`∀i∈S, ∀j∈S, i≠j → Pr(X(i)=X(j))=0`.
Conclude, all together:

- `L ↔ S=∅`;
- for every i∈S, `Pr(X(i)=X(i))=1`;
- `L ↔ (C ∧ ∀i∈S, Pr(X(i)=X(i))=0)`;
- for every natural m, if `0<m<n` then `2≤n`, S is nonempty, and L fails.

There is no measurability premise on X in this general assertion: the
diagonal equality events are exactly Ω regardless, and the off-diagonal
identities here merely repeat the same set-measure expressions on either
side. The measures remain finite even for any nonmeasurable events.

**Local assertion.** Quantify Ω with a measurable space, N, probability μ,
scores X, real b, S, v:S→ℝ, natural m. Assume, in order, `b>0`, `2≤n`,
injectivity of v, every v(i) inside [-b,b], `0<m<n`, exactly m nonnegative
values of v, and the three corrected local conditions expanded above.
Then every two different subtype indices i,j∈S have
`Pr(X(i)=X(j))=0`.

**Finite examples.** Set `S={0,1,2}⊆Fin 4`; its cardinality is 3. Put the
uniform law of mass 1/6 on the six indices 0 through 5. Each of the following
three six-row score arrays has zero tie probability for every different pair
of indices in S:

```
scores1:
(-2,-1, 1, 3)  (-2, 1,-1,-3)  (-1,-2, 1,-3)
(-1, 1,-2,-3)  ( 1,-2,-1,-3)  ( 1,-1,-2,-3)

scores5:
( 1,-1,-2,3)   (-1, 1,-2,3)   (-1,-2, 1,3)
(-1,-2, 1,4)   (-1,-2, 1,5)   (-1,-2, 1,6)

scores9:
(-1,-1/2, 1/2, 2)  (-1, 1/2,-1/2,-2)  (-1/2,-1, 1/2,-2)
(-1/2,1/2,-1,-2)   (1/2,-1,-1/2,-2)   (1/2,-1/2,-1,-2)
```

Here zero probability means the finite weighted indicator sum is zero,
not an independently assumed property of the rows.

**Junk conventions and possible effects.** The general assertion deliberately
includes the empty-window case; universal quantifiers over that window are
vacuous, exactly as the equivalence states. For positive interior counts
empty windows and populations are impossible. Probability normalization
precludes an empty sample space and prevents `toReal(∞)=0`; diagonal event
probability is genuinely 1. The local assertion's factorial denominator is
positive, and all literal constants 1/6 and 1/2 are nonzero-denominator real
divisions. No conditional averages or other zero-denominator divisions occur
in this closure. There is no truncated subtraction, integral, log, root,
real power, extremum, limit, or partial-function default. Finite row indexing
is total on the specified Fin types and cannot select an out-of-range row.

Generated closure declarations `localThree._proof_1`,
`scores1._proof_1`, `scores1._proof_2`, `scores5._proof_1`,
`scores5._proof_2`, and `uniformSix._proof_1` were printed. They are just
proofs that 4 is nonzero or that the finite numeral bounds 2,3,4,5,6
are at least two, used to elaborate finite literals. They introduce no
additional randomization or statistical assumptions.

## SAP.P014.T4

Location: `SAP/P014/Challenge/Part1.lean:31–34`; definition:
`SAP/P014/Defs/Part3.lean:39–50`.

There are no input hypotheses or external universal parameters. This is a
conjunction of explicit facts about the six-row example, and hence a concrete
counterexample assertion rather than a bare negation of a universal formula.

Use N=4, `S={0,1,2}`, b=2, sample indices `Fin 6` with all atoms and
weight 1/6, and the `scores1` rows displayed in the T7 section. Define
`z(ω)` by thresholding scores at zero. The theorem first asserts that the
sample law and its pushforward assignment law are valid finite distributions.
It asserts the following printed-local-conditions predicate:

1. For every supported row, its score-window subjects at b=2 are exactly S.
2. There exists a single function `F:ℝ→ℝ` such that for every supported row
   and every t the empirical CDF `(Σ[i∈S]1_{X(ω,i)≤t})/3` equals F(t).
3. For every supported row ω, the probability of the **entire four-coordinate
   vector** being X(ω) is `1/3!=1/6`.
4. Every different i,j in S have zero tie probability (the diagonal is
   expressly excluded by the definition's docstring).
5. For every supported row, its treated count in S is positive and less than 3.

It asserts the exact equality of threshold assignments with these six vectors,
in row order:
`(F,F,T,T), (F,T,F,F), (F,F,T,F), (F,T,F,F), (T,F,F,F), (T,F,F,F)`.
Their pushforward law therefore has four **distinct** binary atoms:
`(F,F,T,T)` and `(F,F,T,F)` each of mass 1/6, and
`(F,T,F,F)` and `(T,F,F,F)` each of mass 1/3.

For **every** permutation σ of `Fin 3`, the probability that the first
three coordinates equal `(-2,-1,1)∘σ` is 1/6. Thus it expressly asserts
uniform local score permutations in addition to the printed predicate.
It also asserts that every supported assignment has exactly one treated S
subject, every S subject has treatment probability 1/3, and both own-arm
probabilities are positive for each S subject.

Define the potential outcomes by `y(i,z)=0` if i=3, and otherwise 1 if z(3)
is true and 0 if z(3) is false. In particular the three window subjects have
identical outcomes depending on the outside treatment. The final conclusions
are

`Σ[z∈A]w(z)[T_true(z)/n_true(z)-T_false(z)/n_false(z)]=0`,

`(Σ[i∈S]((Σ[z∈A_i,true]y(i,z))/|A_i,true|
         -(Σ[z∈A_i,false]y(i,z))/|A_i,false|))/3=-1/18`,

and inequality of these two quantities. The target averages count distinct
supported full binary assignments once each; they do not count score rows,
and they do not weight the assignments by probability.

**Junk conventions and possible effects.** All laws and scores are finite
and explicit; strict positive masses and normalization are asserted rather
than assumed. Both arm probabilities are positive and the treated count is
one of three, so all arm, support-cardinality, CDF, contrast, and sample-mean
denominators are nonzero. Every factorial denominator is positive. Thus
Lean's `x/0=0` cannot explain the mismatch. Pushforward aggregates repeated
binary vectors; it does not discard their probability mass. The finite
function literals have valid Fin indices, with no overflow/default case.
Natural cardinal casts are exactly 3, 6, or positive arm-support sizes.
No `toReal`, Bochner integral, truncated subtraction, logarithm, root, real
power, supremum/infimum, limit, or partial function occurs.

In addition to the shared finite-literal auxiliary proofs listed under T7,
the closure includes `T1Statement._proof_1`, `._proof_2`, and `._proof_6`.
These were printed and are just proofs that 2, 6, and 18 are at least two,
used in numeral elaboration. The parent T1 statement is not a premise of T4.

The Challenge docstring says the printed claim itself is false. The blind
mathematical content established here is precisely the concrete mismatch
between an estimator expectation and unweighted support target under the
explicit conditions above; identifying which external assertion this
contradicts must wait for the canonical claim.
